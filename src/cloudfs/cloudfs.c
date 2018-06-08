/*
 * @cloudfs.c
 * 
 * HingOn Miu (hmiu)
 * Carnegie Mellon University
 */


#include <ctype.h>
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <fuse.h>
#include <getopt.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/xattr.h>
#include <openssl/md5.h>
#include <time.h>
#include <unistd.h>
#include "cloudapi.h"
#include "cloudfs.h"
#include "dedup.h"
#include "snapshot-api.h"
#include <libtar.h>
#include <ftw.h>

#define UNUSED __attribute__((unused))

/*
 * Struct for essential info of file system
 */
static struct cloudfs_state state_;

/*
 * Stream pointer for log file
 */
FILE *logfile;

/*
 * Rabin-fingerprint structure pointer
 */
rabinpoly_t *rp;

/*
 * s3 filename to match
 */
char *s3_key_to_match;

/*
 * Indicator of whether s3 key is in cloud
 */
int s3_key_in_cloud;

/*
 * Print error message and returns negative errno
 */
static int UNUSED cloudfs_error(char *error_str) {
  int retval = -errno;
  fprintf(stderr, "CloudFS Error: %s\n", error_str);
  // negative errno
  return retval;
}

/*
 * Convert fuse file path to s3 bucket file path
 */
static void fuse_to_s3(char *s3_path, char *fuse_path) {
  int i = 0;
  while (fuse_path[i] != '\0' && i < (MAX_PATH_LEN - 1)) {
    // turn / to +
    if (fuse_path[i] == '/')
      s3_path[i] = '+';
    else 
      s3_path[i] = fuse_path[i];
    i++;
  }
  // makes sure string is null terminated
  s3_path[i] = '\0';
}

/*
 * Convert normal file path to fuse file path
 */
static void normal_to_fuse(char *fuse_path, char *path) {
  strcpy(fuse_path, "");
  // copies the mount point of ssd
  strcpy(fuse_path, state_.ssd_path);
  char *tmp = path;
  // skips the /
  if (tmp[0] == '/')
    tmp++;
  strcat(fuse_path, tmp);
}

/*
 * Create snapshot file 
 */
static int create_snapshot_file() {
  char *path = "/.snapshot";
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // create read-only file
  unlink(fuse_path);
  int fd = open(fuse_path, O_RDONLY | O_CREAT, S_IRUSR);
  if (fd == -1)
    return cloudfs_error("[create_snapshot_file] open");
  close(fd);
  // create ssd files for storing snapshot timestamps
  char *path1 = ".snapshot_list";
  char fuse_path1[MAX_PATH_LEN];
  normal_to_fuse(fuse_path1, path1);
  fd = creat(fuse_path1, S_IRWXU | S_IRWXG | S_IRWXO);
  close(fd);
  char *path2 = ".snapshot_list_count";
  char fuse_path2[MAX_PATH_LEN];
  normal_to_fuse(fuse_path2, path2);
  fd = creat(fuse_path2, S_IRWXU | S_IRWXG | S_IRWXO);
  close(fd);
  // initialize timestamp count as 0
  FILE *f = fopen(fuse_path2, "wb");
  char *count = "0";
  fwrite(count, strlen(count), sizeof(char), f);
  fclose(f);
  return 0; 
}

/*
 * Print directory for debugging 
 */
void print_dir(char *path) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // open directory
  DIR *dp = opendir(fuse_path);
  struct dirent *de;
  while ((de = readdir(dp)) != NULL) {
    fprintf(logfile, "%s\n", de->d_name);
  }
  // close directory
  closedir(dp);
  return;
}

/***************************** hashtable functions ********************************/

/*
 * Create hashtable in ssd
 */
static int create_hashtable() {
  // create a hidden hashtable folder
  char *ht_path = "/.hashtable";
  char ht_fuse_path[MAX_PATH_LEN];
  normal_to_fuse(ht_fuse_path, ht_path);
  // remove the hidden hashtable folder if it exists
  DIR *dp = opendir(ht_fuse_path);
  if (dp != NULL) {
    struct dirent *de;
    int found = 0;
    // traverse all files in directory
    while ((de = readdir(dp)) != NULL) {
      char path[MAX_PATH_LEN];
      strcpy(path, ht_path);
      strcat(path, "/");
      strcat(path, de->d_name);
      char fuse_path[MAX_PATH_LEN];
      normal_to_fuse(fuse_path, path);
      // remove all files within
      unlink(fuse_path);
    }
    closedir(dp);
    rmdir(ht_fuse_path);
  }
  // create the hidden folder
  int retval = mkdir(ht_fuse_path, S_IRWXU | S_IRWXG | S_IRWXO);
  if (retval == -1) {
    return cloudfs_error("[create_hashtable] mkdir");
  }
  return 0;
}

/*
 * Insert a md5 hash to hashtable along with segment length
 */
static int insert_hashtable(char *md5, size_t segment_len) {
  char *ht_path = "/.hashtable";
  char ht_fuse_path[MAX_PATH_LEN];
  normal_to_fuse(ht_fuse_path, ht_path);
  // open hashtable directory
  DIR *dp = opendir(ht_fuse_path);
  if (dp == NULL) {
    return cloudfs_error("[insert_hashtable] opendir");
  }  
  struct dirent *de;
  int found = 0;
  // traverse all files in hashtable
  while ((de = readdir(dp)) != NULL) {
    // check if the md5 hash already exists
    if (!strncmp(de->d_name, md5, 2*MD5_DIGEST_LENGTH)) {
      char path[MAX_PATH_LEN];
      strcpy(path, ht_path);
      strcat(path, "/");
      strncat(path, md5, 2*MD5_DIGEST_LENGTH);
      char fuse_path[MAX_PATH_LEN];
      normal_to_fuse(fuse_path, path);
      char tmp[1024];
      FILE *f = fopen(fuse_path, "r");
      if (f == NULL)
        return cloudfs_error("[insert_hashtable] fopen");
      if (fgets(tmp, 1024, f) == NULL)
        return cloudfs_error("[insert_hashtable] fgets");
      fclose(f);
      // clear reference count
      truncate(fuse_path, 0);
      // parse the file to get reference count
      int count = strtol(tmp, NULL, 10); 
      // update the reference count
      count++;
      sprintf(tmp, "%d", count);
      int fd = open(fuse_path, O_WRONLY, S_IRWXU | S_IRWXG | S_IRWXO);
      int retval = write(fd, tmp, strlen(tmp));
      if (retval == -1) {
        return cloudfs_error("[insert_hashtable] write");
      }
      close(fd);
      found = 1;
      break;
    }
  }
  // close hashtable
  closedir(dp);
  // create new file with md5 as filename and count 1 as extended attribute
  if (!found) {
    char path[MAX_PATH_LEN];
    strcpy(path, ht_path);
    strcat(path, "/");
    strncat(path, md5, 2*MD5_DIGEST_LENGTH);
    char fuse_path[MAX_PATH_LEN];
    normal_to_fuse(fuse_path, path);
    // create a new file with its name as md5 hash
    int fd = creat(fuse_path, S_IRWXU | S_IRWXG | S_IRWXO);
    if (fd == -1) {
      return cloudfs_error("[insert_hashtable] creat");
    }
    int count = 1;
    char tmp[16];
    sprintf(tmp, "%d", count);
    // initialize reference count as 1
    int retval = write(fd, tmp, strlen(tmp));
    if (retval == -1) {
      return cloudfs_error("[insert_hashtable] write");
    }
    close(fd);
  }
  // returns true if newly inserted 
  return (!found);
}

/*
 * Delete a md5 hash from hashtable
 */
static int delete_hashtable(char *md5) {
  char *ht_path = "/.hashtable";
  char ht_fuse_path[MAX_PATH_LEN];
  normal_to_fuse(ht_fuse_path, ht_path);
  char path[MAX_PATH_LEN];
  strcpy(path, ht_path);
  strcat(path, "/");
  strncat(path, md5, 2*MD5_DIGEST_LENGTH);
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  char tmp[1024];
  FILE *f = fopen(fuse_path, "r");
  if (f == NULL)
    return cloudfs_error("[delete_hashtable] fopen");
  if (fgets(tmp, 1024, f) == NULL)
    return cloudfs_error("[delete_hashtable] fgets");
  fclose(f);
  // clear reference count
  truncate(fuse_path, 0);
  // parse the file to get reference count
  int count = strtol(tmp, NULL, 10); 
  // decrement reference count
  count--;
  if (count == 0) {
    // delete file if reference count hits 0
    int retval = unlink(fuse_path);
    if (retval == -1) {
      return cloudfs_error("[delete_hashtable] unlink");
    }
    // delete segment in cloud
    cloud_delete_object("bucket", md5);
    cloud_print_error();
  }
  else {
    sprintf(tmp, "%d", count);
    int fd = open(fuse_path, O_WRONLY, S_IRWXU | S_IRWXG | S_IRWXO);
    int retval = write(fd, tmp, strlen(tmp));
    if (retval == -1) {
      return cloudfs_error("[delete_hashtable] write");
    }
    close(fd);
  }
  return 0;
}

/********************* functions referenced from cloud-example.c ******************/

int incr_count(const char *key, time_t modified_time, uint64_t size) {
  insert_hashtable(key, 0);
  return 0;
}

int list_bucket(const char *key, time_t modified_time, uint64_t size) {
  if (!strcmp(key, s3_key_to_match))
    // flag the in-memory global to show the key-to-match exists in cloud
    s3_key_in_cloud = 1;
  return 0;
}

int list_service(const char *bucketName) {
  return 0; 
}

static FILE *outfile;
int get_buffer(const char *buffer, int bufferLength) {
  return fwrite(buffer, 1, bufferLength, outfile);  
}

static FILE *infile;
int put_buffer(char *buffer, int bufferLength) {
  return fread(buffer, 1, bufferLength, infile);
}

/*
 * Check whether the segment with given md5 hash is in cloud
 */
static int segment_in_cloud(char *md5) {
  s3_key_to_match = md5;
  s3_key_in_cloud = 0;
  cloud_list_bucket("bucket", list_bucket);
  return s3_key_in_cloud;
}

/********************* functions referenced from rabin-example.c ******************/

/*
 * Convert a md5 hash from type unsigned char * to char *
 */
void convert_md5(char *c_md5, unsigned char *uc_md5) {
  int b;
  // reset the memory to 0
  memset(c_md5, 0, 2*MD5_DIGEST_LENGTH + 1);
  for(b = 0; b < MD5_DIGEST_LENGTH; b++)
    sprintf(c_md5+2*b, "%02x", uc_md5[b]);
  // makes sure the string is null terminated
  c_md5[2*MD5_DIGEST_LENGTH] = '\0';
}

/*
 * Upload a file's segments to s3 cloud
 */
int upload_to_cloud(char *fuse_path) {
  // open the file to upload
  int fd = open(fuse_path, O_RDONLY);
  if (fd == -1) {
    return cloudfs_error("[upload_to_cloud] open");
  }
  MD5_CTX ctx;
  unsigned char md5[MD5_DIGEST_LENGTH];		
  int new_segment = 0;
  int len, segment_len = 0, b;
  char buf[1024];
  int bytes;
  MD5_Init(&ctx);
  infile = fopen(fuse_path, "rb");
  int num_segments = 0;
  long offset = 0;
  // initialize the md5 hashes list
  char *md5_list[4096];
  while( (bytes = read(fd, buf, sizeof buf)) > 0 ) {
    char *buftoread = (char *)&buf[0];
    while ((len = rabin_segment_next(rp, buftoread, bytes, &new_segment)) > 0) {
      MD5_Update(&ctx, buftoread, len);
      segment_len += len;		
      if (new_segment) {
        MD5_Final(md5, &ctx);
        // stores md5
        char *m = (char *)calloc(128, sizeof(char));
        if (m == NULL) {
          return cloudfs_error("[upload_to_cloud] calloc");
        }
        convert_md5(m, md5);
        fseek(infile, offset, SEEK_SET);
        // put segment to cloud and update reference count in hashtable
        if (insert_hashtable(m, segment_len)) {
          cloud_put_object("bucket", m, segment_len, put_buffer);
          cloud_print_error();
        }
        offset += segment_len;
        strcat(m, " ");
        char tmp[16];
        // store segment length along with md5 hash
        sprintf(tmp, "%d", segment_len);
        strcat(m, tmp);
        strcat(m, "\n");
        md5_list[num_segments] = m;
        num_segments++;
        MD5_Init(&ctx);
        segment_len = 0;
      }
      buftoread += len;
      bytes -= len;
      if (!bytes) {
        break;
      }
    }
    if (len == -1) {
      return cloudfs_error("[upload_to_cloud] rabin_segment_next");
    }
  }
  MD5_Final(md5, &ctx);
  // stores md5
  char *m = (char *)calloc(128, sizeof(char));
  if (m == NULL) {
    return cloudfs_error("[upload_to_cloud] calloc");
  }
  convert_md5(m, md5);
  fseek(infile, offset, SEEK_SET);
  // put segment to cloud and update reference count in hashtable
  if (insert_hashtable(m, segment_len)) {
    cloud_put_object("bucket", m, segment_len, put_buffer);
    cloud_print_error();
  }
  offset += segment_len;
  strcat(m, " ");
  char tmp[16];
  // store segment length along with md5 hash
  sprintf(tmp, "%d", segment_len);
  strcat(m, tmp);
  strcat(m, "\n"); 
  md5_list[num_segments] = m;
  num_segments++;
  
  fclose(infile);
  rabin_reset(rp);

  // clean ssd file content
  truncate(fuse_path, 0);

  // put md5 to ssd file in order
  FILE *f = fopen(fuse_path, "a+");
  if (f == NULL) {
    return cloudfs_error("[upload_to_cloud] fopen");
  }
  int j;
  for (j = 0; j < num_segments; j++) {
    int retval = fwrite(md5_list[j], sizeof(char), strlen(md5_list[j]), f);
    if (retval == -1) {
      return cloudfs_error("[upload_to_cloud] fwrite");
    }
    free(md5_list[j]);
  }

  fclose(f);
  return 0;
}

/****************************** VFS functions *********************************/

/*
 * Get file attributes
 */
int cloudfs_getattr(const char *path UNUSED, struct stat *statbuf UNUSED) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // get file attributes
  int retval = lstat(fuse_path, statbuf);
  if (retval == -1) {
    return cloudfs_error("[getattr] lstat");
  }
  // get file extended attributes
  struct stat statbuf2;
  memset(&statbuf2, 0, sizeof(statbuf2));
  retval = lgetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2));
  // check if file is in ssd
  if (retval != -1 && statbuf->st_size != statbuf2.st_size) {
    // only overwrite stat when file is not in ssd
    statbuf->st_dev = statbuf2.st_dev;
    statbuf->st_ino = statbuf2.st_ino;
    statbuf->st_mode = statbuf2.st_mode;
    statbuf->st_nlink = statbuf2.st_nlink;
    statbuf->st_uid = statbuf2.st_uid;
    statbuf->st_gid = statbuf2.st_gid;
    statbuf->st_rdev = statbuf2.st_rdev;
    statbuf->st_size = statbuf2.st_size;
    statbuf->st_blksize = statbuf2.st_blksize;
    statbuf->st_blocks = statbuf2.st_blocks;
    statbuf->st_atime = statbuf2.st_atime;
    statbuf->st_mtime = statbuf2.st_mtime;
    statbuf->st_ctime = statbuf2.st_ctime;
  }
  return 0;
}

/*
 * Create new file, or open a file
 */
int cloudfs_mknod(const char *path, mode_t mode, dev_t rdev) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  int retval = 0;
  if (S_ISREG(mode)) {
    retval = open(fuse_path, O_CREAT | O_EXCL | O_WRONLY, mode);
    if (retval >= 0)
      retval = close(retval);
  }
  else if (S_ISFIFO(mode))
    retval = mkfifo(fuse_path, mode);
  else
    retval = mknod(fuse_path, mode, rdev);
  if (retval == -1)
    return cloudfs_error("[mknod] mknod");
  return retval;
}

/*
 * Create new directory
 */
int cloudfs_mkdir(const char *path, mode_t mode) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  int retval = mkdir(fuse_path, mode);
  if (retval == -1) {
    return cloudfs_error("[mkdir] mkdir");
  }
  return 0;
}

/*
 * Remove file and unlink
 */
int cloudfs_unlink(const char *path) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // get file attributes
  struct stat statbuf;
  memset(&statbuf, 0, sizeof(statbuf));
  int retval = lstat(fuse_path, &statbuf);
  if (retval == -1) {
    return cloudfs_error("[unlink] lstat");
  }
  // check extended attritbute
  struct stat statbuf2;
  memset(&statbuf2, 0, sizeof(statbuf2));
  retval = lgetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2));
  // check if file is placed on cloud
  if (retval != -1 && statbuf.st_size != statbuf2.st_size) {
    if (state_.no_dedup) {
      char s3_path[MAX_PATH_LEN];
      fuse_to_s3(s3_path, fuse_path);
      // delete file content in cloud
      cloud_delete_object("bucket", s3_path);
      cloud_print_error();
    }
    else {
      // get directory
      char dir_fuse_path[MAX_PATH_LEN];
      strcpy(dir_fuse_path, fuse_path);
      int j;
      for (j = strlen(dir_fuse_path) - 1; j >= 0; j--) {
        if (dir_fuse_path[j] == '/')
          break;
      }
      dir_fuse_path[j + 1] = '\0';
      // check remaining files to for corruption
      DIR *dp = opendir(dir_fuse_path);
      if (dp == NULL) {
        return cloudfs_error("[unlink] opendir");
      }
      int corrupted = 1;
      struct dirent *de;
      // check if this is the last file to remove
      while ((de = readdir(dp)) != NULL) {
        if (!strcmp(de->d_name, "lost+found") ||
            !strcmp(de->d_name, ".hashtable") ||
            !strcmp(de->d_name, ".snapshot") ||
            !strcmp(de->d_name, "..") ||
            !strcmp(de->d_name, ".") ||
            !strcmp(de->d_name, path + 1))
          continue;
        corrupted = 0;
      }
      closedir(dp);
 
      // fetch md5 hashes list of the file
      FILE *f = fopen(fuse_path, "r");
      if (f == NULL) {
        return cloudfs_error("[unlink] fopen");
      }
      char md5[1024];
      memset(md5, 0, 1024);
      while (fgets(md5, 1024, f) != NULL) {
        md5[2*MD5_DIGEST_LENGTH] = '\0';
        delete_hashtable(md5);
        if (corrupted && segment_in_cloud(md5)) {
          //cloud_delete_object("bucket", md5);
          //cloud_print_error();
        }
      }
      fclose(f);
    }
  }
  // unlink file
  retval = unlink(fuse_path);
  if (retval == -1) {
    return cloudfs_error("[unlink] unlink");
  }
  return 0;
}

/*
 * Remove directory
 */
int cloudfs_rmdir(const char *path) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  int retval = rmdir(fuse_path);
  if (retval == -1) {
    return cloudfs_error("[rmdir] rmdir");
  }
  return 0;
}

/*
 * Change file permission as given mode
 */
int cloudfs_chmod(const char *path, mode_t mode) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // change file permission
  int retval = chmod(fuse_path, mode);
  if (retval == -1) {
    return cloudfs_error("[chmod] chmod");
  }
  // get current file stat
  struct stat statbuf;
  retval = lstat(fuse_path, &statbuf);  
  if (retval == -1) {
    return cloudfs_error("[chmod] lstat");
  }
  // check extended attritbute
  struct stat statbuf2;
  memset(&statbuf2, 0, sizeof(statbuf2));
  retval = lgetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2));
  // check if file is in ssd
  if (retval != -1 && statbuf.st_size != statbuf2.st_size) {
    // only update extended attribute when file is not in ssd
    statbuf2.st_mode = statbuf.st_mode;
    statbuf2.st_ctime = statbuf.st_ctime;
    // change permissions to make sure extended attribute can be updated
    retval = chmod(fuse_path, statbuf.st_mode | S_IRWXU | S_IRWXG | S_IRWXO);
    if (retval == -1) {
      return cloudfs_error("[chmod] chmod");
    }
    retval = lsetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2), 0);
    if (retval == -1) {
      return cloudfs_error("[chmod] lsetxattr");
    }
    // change permissions back
    retval = chmod(fuse_path, statbuf.st_mode);
    if (retval == -1) {
      return cloudfs_error("[chmod] chmod");
    }
  }
  return 0;
}

/*
 * Truncate a file to given length
 */
int cloudfs_truncate(const char *path, off_t length) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // get current file stat
  struct stat statbuf;
  memset(&statbuf, 0, sizeof(statbuf));
  int retval = lstat(fuse_path, &statbuf);  
  if (retval == -1) {
    return cloudfs_error("[truncate] lstat");
  }
  // check extended attritbute
  struct stat statbuf2;
  memset(&statbuf2, 0, sizeof(statbuf2));
  retval = lgetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2));
  // check if file is in ssd
  if (retval == -1 || (retval != -1 && statbuf.st_size == statbuf2.st_size)) {
    // file content is in ssd, truncate normally
    int retval2 = truncate(fuse_path, length);
    if (retval2 == -1) {
      return cloudfs_error("[truncate] truncate");
    }
    
    if (retval != -1) {
      // get current file stat
      memset(&statbuf, 0, sizeof(statbuf));
      retval = lstat(fuse_path, &statbuf);  
      if (retval == -1) {
        return cloudfs_error("[truncate] lstat");
      }
      // update time
      statbuf2.st_mode = statbuf.st_mode;
      statbuf2.st_size = statbuf.st_size;
      statbuf2.st_ctime = statbuf.st_ctime;
      statbuf2.st_mtime = statbuf.st_mtime;
      // no need to swap permissions because truncate() checked already
      retval = lsetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2), 0);
      if (retval == -1) {
        return cloudfs_error("[truncate] lsetxattr");
      }
    }
  }
  else {
    // statbuf.st_size != statbuf2.st_size
    // file not in ssd, try to truncate file in cloud
    if (state_.no_dedup) {
      // fetch file from cloud to ssd
      char s3_path[MAX_PATH_LEN];
      fuse_to_s3(s3_path, fuse_path);
      outfile = fopen(fuse_path, "wb");
      cloud_get_object("bucket", s3_path, get_buffer);
      cloud_print_error();
      fclose(outfile);
      // truncate the ssd file
      retval = truncate(fuse_path, length);
      if (retval == -1) {
        return cloudfs_error("[truncate] truncate");
      }
      // upload the file back to cloud
      infile = fopen(fuse_path, "rb");
      cloud_put_object("bucket", s3_path, length, put_buffer);
      cloud_print_error();
      fclose(infile);
      // clear ssd file content
      truncate(fuse_path, 0);
      // update the new size
      statbuf2.st_size = length;
      retval = lsetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2), 0);
      if (retval == -1)
        return cloudfs_error("[truncate] lsetxattr");
    }
    else {
      // need to read segment(s) from cloud
      // read continuous segments in cloud
      size_t segment_start = 0;
      size_t segment_end = 0;
      // create a hidden random file to store each fetched segment 
      char *tmp_path = "/.random";
      char tmp_fuse_path[MAX_PATH_LEN];
      // create tmp file
      normal_to_fuse(tmp_fuse_path, tmp_path);
      int fd = creat(tmp_fuse_path, S_IRWXU | S_IRWXG | S_IRWXO);
      if (fd == -1) {
        return cloudfs_error("[truncate] creat");
      }
      close(fd);
      // read md5 list
      FILE *f = fopen(fuse_path, "r");
      if (f == NULL) {
        return cloudfs_error("[truncate] fopen");
      }
      // fetch the md5 hashes list from file
      char *md5_list[4096];
      char md5_buf[1024];
      int num_segments = 0;
      while (fgets(md5_buf, 1024, f) != NULL) {
        char *m = (char *)calloc(strlen(md5_buf) + 1, sizeof(char));
        strcpy(m, md5_buf);
        md5_list[num_segments] = m;
        num_segments++;
      }
      fclose(f);
      // clean up the ssd file
      truncate(fuse_path, 0);
      // recalculate md5 of each written segment
      f = fopen(fuse_path, "a");
      int j;
      for (j = 0; j < num_segments; j++) {
        char *md5 = md5_list[j];
        // parse the md5 hash and segment length
        size_t segment_len = strtol(md5 + 2 * MD5_DIGEST_LENGTH, NULL, 10); 
        //size_t segment_len = get_segment_len(md5);
        segment_end += segment_len;
        md5[2 * MD5_DIGEST_LENGTH] = '\0';
        // check if the segment includes the wanted length to truncate
        if (segment_end <= length) {
          // append original md5 hashes to file if before the wanted range
          md5[2 * MD5_DIGEST_LENGTH] = ' ';
          fwrite(md5, sizeof(char), strlen(md5), f);
        }
        else if (segment_start < length) {
          // recalculate md5 hash and append new hash to file if includes the wanted length
          outfile = fopen(tmp_fuse_path, "wb");
          // fetch the segment from cloud to the hidden random file created
          cloud_get_object("bucket", md5, get_buffer);
          cloud_print_error();
          fclose(outfile);
          // update the reference count in hashtable
          delete_hashtable(md5);
          // apply the truncate to the segment downloaded
          truncate(tmp_fuse_path, length - segment_start);
          // recalculate md5 hash of new segment and upload to s3 cloud
          upload_to_cloud(tmp_fuse_path);
          FILE *f2 = fopen(tmp_fuse_path, "r");
          if (f2 == NULL) {
            return cloudfs_error("[truncate] fopen");
          }
          char md52[1024];
          // append the new md5 hashes to file
          while (fgets(md52, 1024, f2) != NULL)
            fwrite(md52, sizeof(char), strlen(md52), f);
          fclose(f2);
          // clear the hidden random file
          truncate(tmp_fuse_path, 0);
        }
        else {
          // do not append these exceeded length md5 hashes
          // update the reference count in hashtable
          delete_hashtable(md5);
        }
        free(md5);
        segment_start = segment_end;
      }
      fclose(f);
      // remove the random file
      unlink(tmp_fuse_path);
      // fix file size
      statbuf2.st_size = length;
      retval = lsetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2), 0);
      if (retval == -1)
        return cloudfs_error("[truncate] lsetxattr");
    }
    memset(&statbuf, 0, sizeof(statbuf));
    retval = lstat(fuse_path, &statbuf);  
    if (retval == -1) {
      return cloudfs_error("[truncate] lstat");
    }
    // update time
    statbuf2.st_mode = statbuf.st_mode;
    statbuf2.st_size = statbuf.st_size;
    statbuf2.st_ctime = statbuf.st_ctime;
    statbuf2.st_mtime = statbuf.st_mtime;
    // no need to swap permissions because truncate() checked already
    retval = lsetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2), 0);
    if (retval == -1) {
      return cloudfs_error("[truncate] lsetxattr");
    }
  }

  return 0;
}

/*
 * Open a file
 */
int cloudfs_open(const char *path, struct fuse_file_info *fi) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // open the file
  int fd = open(fuse_path, fi->flags);
  if (fd == -1) {
    return cloudfs_error("[open] open");
  }
  // get current file stat
  struct stat statbuf;
  memset(&statbuf, 0, sizeof(statbuf));
  int retval = lstat(fuse_path, &statbuf);  
  if (retval == -1) {
    return cloudfs_error("[open] lstat");
  }
  // check extended attritbute
  struct stat statbuf2;
  memset(&statbuf2, 0, sizeof(statbuf2));
  retval = lgetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2));
  // check if file is in ssd
  if (retval != -1 && statbuf.st_size != statbuf2.st_size) {
    // the file is not in ssd
    // change permissions to make sure file is writable
    retval = chmod(fuse_path, statbuf.st_mode | S_IRWXU | S_IRWXG | S_IRWXO);
    if (retval == -1) {
      return cloudfs_error("[open] chmod");
    }
    // fetch file content from cloud
    if (state_.no_dedup) {    
      char s3_path[MAX_PATH_LEN];
      fuse_to_s3(s3_path, fuse_path);
      outfile = fopen(fuse_path, "wb");
      cloud_get_object("bucket", s3_path, get_buffer);
      cloud_print_error();
      fclose(outfile);
    }
    // fix modification time and access time
    struct timespec ts[2];
    ts[0].tv_sec = statbuf2.st_atime;
    ts[0].tv_nsec = 0;
    ts[1].tv_sec = statbuf2.st_mtime;
    ts[1].tv_nsec = 0;
    retval = utimensat(0, fuse_path, ts, 0);
    if (retval == -1) {
      return cloudfs_error("[open] utimensat");
    }
    // change permissions back
    retval = chmod(fuse_path, statbuf.st_mode);
    if (retval == -1) {
      return cloudfs_error("[open] chmod");
    }
  }
  // update file handle
  fi->fh = fd;
  return 0;
}

/*
 * Read a file
 */
int cloudfs_read(const char *path, char *buf, size_t size, off_t offset, struct fuse_file_info *fi) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // get current file stat
  struct stat statbuf;
  memset(&statbuf, 0, sizeof(statbuf));
  int retval = lstat(fuse_path, &statbuf);  
  if (retval == -1) {
    return cloudfs_error("[read] lstat");
  }
  // check extended attritbute
  struct stat statbuf2;
  memset(&statbuf2, 0, sizeof(statbuf2));
  retval = lgetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2));
  // check if file is in ssd
  if (retval == -1 || (retval != -1 && statbuf.st_size == statbuf2.st_size) || state_.no_dedup) {
    // file content is in ssd, read normally
    retval = pread(fi->fh, buf, size, offset);
    if (retval == -1) {
      return cloudfs_error("[read] pread");
    }
  }
  else {
    // need to read segment(s) from cloud
    // change permissions to make sure file is writable
    retval = chmod(fuse_path, statbuf.st_mode | S_IRWXU | S_IRWXG | S_IRWXO);
    if (retval == -1) {
      return cloudfs_error("[read] chmod");
    }
    // read continuous segments in cloud
    size_t segment_start = 0;
    size_t segment_end = 0;
    size_t bytes_read = 0;
    // create a hidden random file to store each fetched segment 
    char *tmp_path = "/.random";
    char tmp_fuse_path[MAX_PATH_LEN];
    normal_to_fuse(tmp_fuse_path, tmp_path);
    int fd = creat(tmp_fuse_path, S_IRWXU | S_IRWXG | S_IRWXO);
    if (fd == -1) {
      return cloudfs_error("[read] open");
    }
    close(fd);
    // read the md5 hashes list from file
    FILE *f = fopen(fuse_path, "r");
    if (f == NULL) {
      return cloudfs_error("[read] fopen");
    }
    char *md5_cache_list[4096];
    char *seg_cache_list[4096];
    // initialize the cache arrays
    int k;
    for (k = 0; k < 4096; k++) {
      md5_cache_list[k] = NULL;
      seg_cache_list[k] = NULL;
    }
    int num_segments_cached = 0;
    char md5[1024];
    while (fgets(md5, 1024, f) != NULL) {
      // parse the file to get segment length
      size_t segment_len = strtol(md5 + 2 * MD5_DIGEST_LENGTH, NULL, 10); 
      segment_end += segment_len;
      md5[2 * MD5_DIGEST_LENGTH] = '\0';
      // check if the segment is within the range to read
      if (segment_end > offset && segment_start < (offset + size)) {
        outfile = fopen(tmp_fuse_path, "wb");
        // fetch segment from cloud or memory
        int h;
        int found_cache = 0;
        for (h = 0; h < num_segments_cached; h++){
          // check if cached before
          if (md5_cache_list[h] != NULL && !strcmp(md5_cache_list[h], md5)) {
            found_cache = 1;
            break;
          }
        }
        if (found_cache) {
          // fetch segment from in-memory cache
          fwrite(seg_cache_list[h], 1, segment_len, outfile);
        }
        else {
          // fetch segment from cloud
          cloud_get_object("bucket", md5, get_buffer);
          cloud_print_error();
          // cache the segment to memory
          char *md5_cache = (char *)calloc(strlen(md5) + 1, sizeof(char));
          char *seg_cache = (char *)calloc(segment_len, sizeof(char));
          if (md5_cache != NULL && seg_cache != NULL) {
            strcpy(md5_cache, md5);
            fd = open(tmp_fuse_path, O_RDONLY, S_IRWXU | S_IRWXG | S_IRWXO);
            pread(fd, seg_cache, segment_len, 0);
            close(fd);
            md5_cache_list[num_segments_cached] = md5_cache;
            seg_cache_list[num_segments_cached] = seg_cache;
            num_segments_cached++;
          }
        }
        fclose(outfile);
        // write the wanted portion of segment to buffer from the hidden random file created
        off_t left = (segment_start > offset) ? segment_start : offset;
        off_t right = (segment_end < (offset + size)) ? segment_end : (offset + size);
        size_t pread_size = right - left;
        off_t pread_offset = (offset <= segment_start) ? 0 : offset - segment_start;
        fd = open(tmp_fuse_path, O_RDONLY, S_IRWXU | S_IRWXG | S_IRWXO);
        retval = pread(fd, buf + bytes_read, pread_size, pread_offset);
        close(fd);
        // check if read failed
        if (retval == -1) {
          return cloudfs_error("[read] pread");
        }
        // clear the hidden random file
        truncate(tmp_fuse_path, 0);
        bytes_read += retval;
      }
      segment_start = segment_end;
    }
    fclose(f);
    unlink(tmp_fuse_path);
    int w;
    // clear caches
    for (w = 0; w < num_segments_cached; w++) {
      free(md5_cache_list[w]);
      free(seg_cache_list[w]);
    }
    // fix modification time and access time
    struct timespec ts[2];
    ts[0].tv_sec = statbuf2.st_atime;
    ts[0].tv_nsec = 0;
    ts[1].tv_sec = statbuf2.st_mtime;
    ts[1].tv_nsec = 0;
    retval = utimensat(0, fuse_path, ts, 0);
    if (retval == -1) {
      return cloudfs_error("[read] utimensat");
    }
    // change permissions back
    retval = chmod(fuse_path, statbuf.st_mode);
    if (retval == -1) {
      return cloudfs_error("[read] chmod");
    }
    retval = bytes_read;
  }

  return retval;
}

/*
 * Write a file
 */
int cloudfs_write(const char *path, const char *buf, size_t size, off_t offset, struct fuse_file_info *fi) {
  // installed snapshots are read-only
  if ((strlen(path) >= strlen("snapshot_") &&
      !strncmp(path, "snapshot_", strlen("snapshot_"))) ||
      (strlen(path) >= strlen("/snapshot_") &&
      !strncmp(path, "/snapshot_", strlen("/snapshot_"))))
    return -1;
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // get current file stat
  struct stat statbuf;
  memset(&statbuf, 0, sizeof(statbuf));
  int retval = lstat(fuse_path, &statbuf);  
  if (retval == -1) {
    return cloudfs_error("[write] lstat");
  }
  // check extended attritbute
  struct stat statbuf2;
  memset(&statbuf2, 0, sizeof(statbuf2));
  retval = lgetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2));
  // check if file is in ssd
  if (retval == -1 || (retval != -1 && statbuf.st_size == statbuf2.st_size) || state_.no_dedup) {
    // file content is in ssd, write normally
    retval = pwrite(fi->fh, buf, size, offset);
    if (retval == -1) {
      return cloudfs_error("[write] pread");
    }
  }
  else {
    // need to read segment(s) from cloud
    // change permissions to make sure file is writable
    retval = chmod(fuse_path, statbuf.st_mode | S_IRWXU | S_IRWXG | S_IRWXO);
    if (retval == -1) {
      return cloudfs_error("[write] chmod");
    }
    // read continuous segments in cloud
    size_t segment_start = 0;
    size_t segment_end = 0;
    size_t bytes_written = 0;
    // create a hidden random file to store each fetched segment 
    char *tmp_path = "/.random";
    char tmp_fuse_path[MAX_PATH_LEN];
    // create tmp file
    normal_to_fuse(tmp_fuse_path, tmp_path);
    int fd = creat(tmp_fuse_path, S_IRWXU | S_IRWXG | S_IRWXO);
    if (fd == -1) {
      return cloudfs_error("[write] open");
    }
    close(fd);
    // read md5 list
    FILE *f = fopen(fuse_path, "r");
    if (f == NULL) {
      return cloudfs_error("[write] fopen");
    }
    // fetch the md5 hashes list from file
    char *md5_list[4096];
    char md5_buf[1024];
    int num_segments = 0;
    while (fgets(md5_buf, 1024, f) != NULL) {
      char *m = (char *)calloc(strlen(md5_buf) + 1, sizeof(char));
      strcpy(m, md5_buf);
      md5_list[num_segments] = m;
      num_segments++;
    }
    fclose(f);
    // clean up the ssd file
    truncate(fuse_path, 0);
    // recalculate md5 of each written segment
    f = fopen(fuse_path, "a");
    int j;
    for (j = 0; j < num_segments; j++) {
      char *md5 = md5_list[j];
      // parse the md5 hash and segment length
      size_t segment_len = strtol(md5 + 2 * MD5_DIGEST_LENGTH, NULL, 10); 
      //size_t segment_len = get_segment_len(md5);
      segment_end += segment_len;
      md5[2 * MD5_DIGEST_LENGTH] = '\0';
      // check if the segment is within the wanted range to write
      if (segment_end > offset && segment_start < (offset + size)) {
        outfile = fopen(tmp_fuse_path, "wb");
        // fetch the segment from cloud to the hidden random file created
        cloud_get_object("bucket", md5, get_buffer);
        cloud_print_error();
        fclose(outfile);
        // update the reference count in hashtable
        delete_hashtable(md5);
        // apply the write to the segment downloaded
        off_t left = (segment_start > offset) ? segment_start : offset;
        off_t right = (segment_end < (offset + size)) ? segment_end : (offset + size);
        size_t pread_size = right - left;
        off_t pread_offset = (offset <= segment_start) ? 0 : offset - segment_start;
        fd = open(tmp_fuse_path, O_WRONLY, S_IRWXU | S_IRWXG | S_IRWXO);
        retval = pwrite(fd, buf + bytes_written, pread_size, pread_offset);
        close(fd);
        if (retval == -1) {
          return cloudfs_error("[write] pread");
        }
        // recalculate md5 hash of new segment and upload to s3 cloud
        upload_to_cloud(tmp_fuse_path);
        FILE *f2 = fopen(tmp_fuse_path, "r");
        if (f2 == NULL) {
          return cloudfs_error("[write] fopen");
        }
        char md52[1024];
        // append the new md5 hashes to file
        while (fgets(md52, 1024, f2) != NULL)
          fwrite(md52, sizeof(char), strlen(md52), f);
        fclose(f2);
        // clear the hidden random file
        truncate(tmp_fuse_path, 0);
        bytes_written += retval;
      }
      else {
        // append original md5 hashes to file if not in wanted range
        md5[2 * MD5_DIGEST_LENGTH] = ' ';
        fwrite(md5, sizeof(char), strlen(md5), f);
      }
      free(md5);
      segment_start = segment_end;
    }
    // check the wanted range to write exceeds original file size
    if ((offset + size) > segment_end) {
        // apply the exceeded writes to an empty file
        fd = open(tmp_fuse_path, O_WRONLY, S_IRWXU | S_IRWXG | S_IRWXO);
        retval = pwrite(fd, buf + bytes_written, size - bytes_written, 0);
        close(fd);
        if (retval == -1) {
          return cloudfs_error("[write] pread");
        }
        // cacluate the md5 hashes of the exceeded writes
        upload_to_cloud(tmp_fuse_path);
        FILE *f2 = fopen(tmp_fuse_path, "r");
        if (f2 == NULL) {
          return cloudfs_error("[write] fopen");
        }
        char md52[1024];
        // append new md5 hashes to file
        while (fgets(md52, 1024, f2) != NULL)
          fwrite(md52, sizeof(char), strlen(md52), f);
        fclose(f2);
        // clear the hidden random file
        truncate(tmp_fuse_path, 0);
        bytes_written += retval;
    }
    fclose(f);
    // remove the random file
    unlink(tmp_fuse_path);
    // fix file size
    size_t new_size = (statbuf2.st_size > (offset + size)) ? statbuf2.st_size : (offset + size);
    statbuf2.st_size = new_size;
    retval = lsetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2), 0);
    if (retval == -1)
      return cloudfs_error("[write] lsetxattr");
    // change permissions back
    retval = chmod(fuse_path, statbuf.st_mode);
    if (retval == -1) {
      return cloudfs_error("[write] chmod");
    }
    // set return value to bytes changed
    retval = bytes_written;
  }

  // flag file as written
  int written_flag = 1;
  int retval2 = lsetxattr(fuse_path, "user.written", &written_flag, sizeof(written_flag), 0);
  if (retval2 == -1) {
    return cloudfs_error("[write] lsetxattr");
  }
  return retval;
}

/*
 * Close a file
 */
int cloudfs_release(const char *path, struct fuse_file_info *fi) {
  char s3_path[MAX_PATH_LEN];
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  fuse_to_s3(s3_path, fuse_path);
  // get current file stat
  struct stat statbuf;
  memset(&statbuf, 0, sizeof(statbuf));
  int retval = lstat(fuse_path, &statbuf);  
  if (retval == -1) {
    return cloudfs_error("[release] lstat");
  }
  // check extended attritbute
  struct stat statbuf2;
  memset(&statbuf2, 0, sizeof(statbuf2));
  // change permissions to make sure file can be updated
  retval = chmod(fuse_path, statbuf.st_mode | S_IRWXU | S_IRWXG | S_IRWXO);
  if (retval == -1) {
    return cloudfs_error("[release] chmod");
  }
  retval = lgetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2));
  if (retval == -1) {
    // previously in ssd
    if (statbuf.st_size > state_.threshold) {
      // move content of big file to cloud
      if (state_.no_dedup) {
        infile = fopen(fuse_path, "rb");
        cloud_put_object("bucket", s3_path, statbuf.st_size, put_buffer);
        cloud_print_error();
        fclose(infile);
        truncate(fuse_path, 0);
      }
      else {
        upload_to_cloud(fuse_path);
      }
      // update the file stat
      retval = lsetxattr(fuse_path, "user.stat", &statbuf, sizeof(statbuf), 0);
      if (retval == -1) {
        return cloudfs_error("[release] lsetxattr");
      }
    }
    else {
      // still going to be in ssd
    }
  }
  else {
    // previously on cloud
    if (state_.no_dedup) {
      if (statbuf.st_size > state_.threshold) {
        // check if need to update big file in cloud
        int buf;
        retval = lgetxattr(fuse_path, "user.written", &buf, 0);
        if (retval == -1) {
          // no change is made to file, no need to communicate with s3 server
          // change permissions to make sure file can be updated
          // remove the file content in ssd
          truncate(fuse_path, 0);
          // update the file stat
          retval = lsetxattr(fuse_path, "user.stat", &statbuf, sizeof(statbuf), 0);
          if (retval == -1)
            return cloudfs_error("[release] lsetxattr");
        }
        else {
          // update the changes to cloud
          infile = fopen(fuse_path, "rb");
          cloud_put_object("bucket", s3_path, statbuf.st_size, put_buffer);
          cloud_print_error();
          fclose(infile);
          // remove the file content in ssd
          truncate(fuse_path, 0);
          // update the file stat
          retval = lsetxattr(fuse_path, "user.stat", &statbuf, sizeof(statbuf), 0);
          if (retval == -1)
            return cloudfs_error("[release] lsetxattr");
        }
      }
      else {
        // big file gets smaller, move file to ssd
        cloud_delete_object("bucket", s3_path);
        cloud_print_error();
        // remove the extended attribute
        retval = lremovexattr(fuse_path, "user.stat");
        if (retval == -1) {
          return cloudfs_error("[release] lremovexattr");
        }
      }
    }
    else {
      // deduplication enabled  
      if (statbuf2.st_size > state_.threshold) {
        // do nothing, because segments stay in cloud
      }
      else {
        // big file gets smaller, move segments back to ssd
        //TODO: remove segments from cloud
        // remove the extended attribute
        retval = lremovexattr(fuse_path, "user.stat");
        if (retval == -1) {
          return cloudfs_error("[release] lremovexattr");
        }
      } 
    }
  } 
  int buf;
  retval = lgetxattr(fuse_path, "user.written", &buf, 0);
  if (retval != -1) {
    // remove written flag since content is already flushed
    retval = lremovexattr(fuse_path, "user.written");
    if (retval == -1) {
      return cloudfs_error("[release] lremovexattr");
    }
  }
  // change permissions back
  retval = chmod(fuse_path, statbuf.st_mode);
  if (retval == -1) {
    return cloudfs_error("[release] chmod");
  }
 
  // close the file
  retval = close(fi->fh);
  if (retval == -1) {
    return cloudfs_error("[release] close");
  }
  return 0;
}

/*
 * Set file extended attributes
 */
int cloudfs_setxattr(const char *path, const char *name, const char *value, size_t size, int flags) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  int retval = lsetxattr(fuse_path, name, value, size, flags);
  if (retval == -1) {
    return cloudfs_error("[setxattr] lsetxattr");
  }
  return retval;
}

/*
 * Get file extended attributes
 */
int cloudfs_getxattr(const char *path, const char *name, char *value, size_t size) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  int retval = lgetxattr(fuse_path, name, value, size);
  if (retval == -1) {
    return cloudfs_error("[getxattr] lgetxattr");
  }
  return retval;
}

/*
 * Open directory
 */
int cloudfs_opendir(const char *path, struct fuse_file_info *fi) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // open directory
  DIR *dp = opendir(fuse_path);
  if (dp == NULL) {
    return cloudfs_error("[opendir] opendir");
  }
  // get the file descriptor of directory stream
  fi->fh = dirfd(dp);
  return 0;
}

/*
 * Read directory
 */
int cloudfs_readdir(const char *path, void *buf, fuse_fill_dir_t filler, off_t offset, struct fuse_file_info *fi) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // open directory
  DIR *dp = opendir(fuse_path);
  if (dp == NULL) {
    return cloudfs_error("[readdir] opendir");
  }
  struct dirent *de;
  while ((de = readdir(dp)) != NULL) {
    // skips lost+found folder
    if (!strcmp(de->d_name, "lost+found"))
      continue;
    // skips hidden hashtable folder
    if (!strcmp(de->d_name, ".hashtable"))
      continue;
    // skips snapshot file
    if (!strcmp(de->d_name, ".snapshot"))
      continue;
    // get the stat of each file
    struct stat statbuf;
    memset(&statbuf, 0, sizeof(statbuf));
    statbuf.st_ino = de->d_ino;
    statbuf.st_mode = de->d_type << 12;
    if (filler(buf, de->d_name, &statbuf, 0))
      break;
  }
  // close directory
  closedir(dp);
  return 0;
}

/*
 * Initializes the FUSE file system (cloudfs) by checking if the mount points
 * are valid, and if all is well, it mounts the file system ready for usage.
 *
 */
void *cloudfs_init(struct fuse_conn_info *conn UNUSED) {
  cloud_init(state_.hostname);
  cloud_print_error();
  // create bucket in s3 server
  cloud_create_bucket("bucket");
  cloud_print_error();
  // initialize rabin fingerprinting
  rp = NULL;
  if (!state_.no_dedup) {
    // rabin-example.c uses half of avg as min and twice of avg as max
    rp = rabin_init(state_.rabin_window_size, state_.avg_seg_size, state_.avg_seg_size / 2, state_.avg_seg_size * 2); 
    if (rp == NULL) { 
      return NULL;
    }
    // create hashtable of md5<->count mappings
    create_hashtable();
    // create .snapshot file
    create_snapshot_file();
  }
  return NULL;
}

/*
 * Clean up file system
 */
void cloudfs_destroy(void *data UNUSED) {
  // delete s3 bucket
  cloud_delete_bucket("bucket");
  // free rabin fingerprinting structure
  if (!state_.no_dedup)
    rabin_free(&rp);
  cloud_destroy();
}

/*
 * Access the file with given mode
 */
int cloudfs_access(const char *path, int mode) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  int retval = access(fuse_path, mode);
  if (retval == -1) {
    return cloudfs_error("[access] access");
  }
  return 0;
}

/*
 * Create a file with given mode
 */
int cloudfs_create(const char *path, mode_t mode, struct fuse_file_info *fi) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  int fd = creat(fuse_path, mode);
  if (fd == -1) {
    return cloudfs_error("[create] creat");
  }
  // keep file descriptor
  fi->fh = fd;
  return 0;
}

/*
 * Set timestamps of a file
 */
int cloudfs_utimens(const char *path, const struct timespec ts[2]) {
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // set timestamps
  int retval = utimensat(0, fuse_path, ts, 0);
  if (retval == -1) {
    return cloudfs_error("[utimens] utimensat");
  }
  // get current file stat
  struct stat statbuf;
  memset(&statbuf, 0, sizeof(statbuf));
  retval = lstat(fuse_path, &statbuf);  
  if (retval == -1) {
    return cloudfs_error("[utimens] lstat");
  }
  // check extended attritbute
  struct stat statbuf2;
  memset(&statbuf2, 0, sizeof(statbuf2));
  retval = lgetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2));
  // check if file is in ssd
  if (retval != -1 && statbuf.st_size != statbuf2.st_size) {
    // update extended attribute only when file is not in ssd
    statbuf2.st_atime = statbuf.st_atime;
    statbuf2.st_mtime = statbuf.st_mtime;
    // no need to swap permissions because utimesat() checked already
    retval = lsetxattr(fuse_path, "user.stat", &statbuf2, sizeof(statbuf2), 0);
    if (retval == -1) {
      return cloudfs_error("[utimens] lsetxattr");
    }
  }
  return 0;
}

/*
 * Global tar file pointer (for passing it to nftw helper function)
 */
TAR *t;

/*
 * Global tar file name (for passing it to nftw helper function)
 */
char tar_path[MAX_PATH_LEN];

/*
 * Repair the extended attribute of large file after untar (nftw helper function) 
 */
int fix_ext(const char *fpath, const struct stat *sb, int typeflag, struct FTW *ftwbuf) {
  int len = strlen(fpath);
  // skip those files without "_ext"
  if (len < 4 || strcmp(fpath + len - 4, "_ext"))
    return 0;
  struct stat statbuf;
  memset(&statbuf, 0, sizeof(statbuf));
  // read ext file to get statbuf
  FILE *f = fopen(fpath, "rb");
  fread(&statbuf, sizeof(statbuf), 1, f);
  fclose(f);
  // remove ext file
  unlink(fpath);
  char fuse_path[MAX_PATH_LEN];
  strcpy(fuse_path, fpath);
  fuse_path[len - 4] = '\0';
  // calculate size from suming the segmen length
  FILE *f2 = fopen(fuse_path, "r");
  char tmp[1024];
  int size = 0;
  while (fgets(tmp, 1024, f2) != NULL)
    size += strtol(tmp + 2 * MD5_DIGEST_LENGTH, NULL, 10); 
  fclose(f2);
  statbuf.st_size = size;
  // set extended attribute of large file
  lsetxattr(fuse_path, "user.stat", &statbuf, sizeof(statbuf), 0);
  return 0; 
}

/*
 * Append each file/directory to tar file (nftw helper function)
 */
int append_tar(const char *fpath, const struct stat *sb, int typeflag, struct FTW *ftwbuf) {
  int len = strlen(fpath);
  int i;
  // get '/' location
  for (i = len - 1; i >= 0; i--) {
    if (fpath[i] == '/')
      break;
  }
  if (i == len - 1)
    return 0;
  // get fuse(ssd) relative path
  char *fuse_path = fpath + i + 1;
  // get snapshot_folder path
  char snapshot_folder[MAX_PATH_LEN]; 
  strcpy(snapshot_folder, state_.ssd_path);
  strcat(snapshot_folder, "snapshot_");
  // skip all following files (do not tar them)
  if (!strcmp(fuse_path, "lost+found") ||
      !strcmp(fuse_path, ".snapshot") ||
      !strcmp(fuse_path, ".hashtable") ||
      !strcmp(fuse_path, "..") ||
      !strcmp(fuse_path, ".") ||
      !strncmp(fpath, snapshot_folder, strlen(snapshot_folder)) ||
      !strncmp(fpath, state_.ssd_path, strlen(fpath)) ||
      !strcmp(fuse_path, tar_path))
    return 0;
  // tar file/directory
  tar_append_file(t, fpath, fpath + strlen(state_.ssd_path));
  struct stat statbuf;
  memset(&statbuf, 0, sizeof(statbuf));
  // check if it has extended attribute
  int retval = lgetxattr(fpath, "user.stat", &statbuf, sizeof(statbuf));
  if (retval == -1)
    return 0;
  char ext_path[MAX_PATH_LEN];
  strcpy(ext_path, fpath);
  strcat(ext_path, "_ext");
  // create a ext file for this file
  FILE *f = fopen(ext_path, "wb");
  fwrite(&statbuf, sizeof(statbuf), 1, f);
  fclose(f);
  // tar the ext file
  tar_append_file(t, ext_path, ext_path + strlen(state_.ssd_path));
  // remove the ext file
  unlink(ext_path);
  return 0; 
}

/*
 * Remove file/directory (nftw helper function) 
 */
int remove_dir(const char *fpath, const struct stat *sb, int typeflag, struct FTW *ftwbuf) {
  if (typeflag == FTW_F || typeflag == FTW_SL || typeflag == FTW_SLN)
    // remove file
    unlink(fpath);
  else if (typeflag == FTW_D || typeflag == FTW_DNR || typeflag == FTW_DP)
    // remove directory
    rmdir(fpath);
  else
    return -1;
  return 0; 
}

/*
 * Delete a selected timestamp from snapshots
 */
void delete_snapshot(char *timestamp) {
  char *path = ".snapshot_list";
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // traverse all snapshots
  FILE *f = fopen(fuse_path, "rb");
  char *list[CLOUDFS_MAX_NUM_SNAPSHOTS];
  int list_count = 0;
  char tmp[1024];
  // store the snapshots temporarily
  while (fgets(tmp, 1024, f) != NULL) {
    char *m = (char *)calloc(128, sizeof(char));
    strcpy(m, tmp);
    list[list_count] = m;
    list_count++;
  }
  fclose(f);
  // clear file content
  truncate(fuse_path, 0);
  f = fopen(fuse_path, "ab");
  int i;
  int new_count = 0;
  // find if the selected timestamp is included
  for (i = 0; i < list_count; i++) {
    if (!strncmp(list[i], timestamp, strlen(timestamp))) {
      list[i][strlen(timestamp)] = '\0';
      // remove the snapshot file from cloud
      cloud_delete_object("bucket", list[i]);
      cloud_print_error();
    }
    else {
      // write all other timestamp back to file
      fwrite(list[i], strlen(list[i]), sizeof(char), f);
      new_count++;
    }
    free(list[i]);
  } 
  fclose(f);
  // update timestamp count
  char *path2 = ".snapshot_list_count";
  char fuse_path2[MAX_PATH_LEN];
  normal_to_fuse(fuse_path2, path2);
  truncate(fuse_path2, 0); 
  char tmp3[1024];
  sprintf(tmp3, "%d", new_count); 
  f = fopen(fuse_path2, "wb");
  fwrite(tmp3, strlen(tmp3), sizeof(char), f);
  fclose(f);
}

/*
 * Delete all timestamps after a selected timestamp 
 */
void delete_future_snapshots(char *timestamp) {
  char *path = ".snapshot_list";
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // traverse all snapshots
  FILE *f = fopen(fuse_path, "rb");
  char *list[CLOUDFS_MAX_NUM_SNAPSHOTS];
  int list_count = 0;
  char tmp[1024];
  // store all timestamps tempararily
  while (fgets(tmp, 1024, f) != NULL) {
    char *m = (char *)calloc(128, sizeof(char));
    strcpy(m, tmp);
    list[list_count] = m;
    list_count++;
  }
  fclose(f);
  // clear file content
  truncate(fuse_path, 0);
  f = fopen(fuse_path, "ab");
  int i;
  // find the selected timestamp
  for (i = 0; i < list_count; i++) {
    fwrite(list[i], strlen(list[i]), sizeof(char), f);
    if (!strncmp(list[i], timestamp, strlen(timestamp))) {
      free(list[i]);
      int j;
      // remove all afterwards timestamp from cloud
      for (j = i+1; j < list_count; j++) {
        list[j][strlen(timestamp)] = '\0';
        cloud_delete_object("bucket", list[j]);
        cloud_print_error();
        free(list[j]);
      }     
      return;
    }
    free(list[i]);
  } 
  fclose(f);
}

/*
 * Insert selected timestamp 
 */
int insert_snapshot(char *timestamp) {
  char *path1 = ".snapshot_list";
  char fuse_path1[MAX_PATH_LEN];
  normal_to_fuse(fuse_path1, path1);
  char *path2 = ".snapshot_list_count";
  char fuse_path2[MAX_PATH_LEN];
  normal_to_fuse(fuse_path2, path2);
  // get timestamp count
  FILE *f = fopen(fuse_path2, "r");
  char tmp1[1024];
  fgets(tmp1, 1024, f);
  fclose(f);
  // clear count
  truncate(fuse_path2, 0);
  // parse count
  int count = strtol(tmp1, NULL, 10); 
  if (count >= CLOUDFS_MAX_NUM_SNAPSHOTS)
    // cannot insert more snapshots
    return -1;
  // insert the snapshot  
  char tmp2[1024];
  strcpy(tmp2, timestamp);
  strcat(tmp2, "\n");
  f = fopen(fuse_path1, "ab");
  fwrite(tmp2, strlen(tmp2), sizeof(char), f);
  fclose(f);
  // increment count
  count++;
  char tmp3[1024];
  sprintf(tmp3, "%d", count); 
  f = fopen(fuse_path2, "wb");
  fwrite(tmp3, strlen(tmp3), sizeof(char), f);
  fclose(f);
  return 0;
}

/*
 * List all timestamps 
 */
void list_snapshots(unsigned long *data) {
  char *path = ".snapshot_list";
  char fuse_path[MAX_PATH_LEN];
  normal_to_fuse(fuse_path, path);
  // traverse all snapshots
  FILE *f = fopen(fuse_path, "rb");
  char tmp[1024];
  int i = 0;
  while (fgets(tmp, 1024, f) != NULL) {
    // parse each timestamp to unsigned long
    data[i] = strtoul(tmp, NULL, 10); 
    i++;
  }
  fclose(f);
}

/*
 * Manage snapshots 
 */
UNUSED int cloudfs_ioctl(UNUSED const char *path, int cmd, UNUSED void *arg, 
                         UNUSED struct fuse_file_info *fi, 
                         UNUSED unsigned int flags, void *data) {
  char fuse_root_path[MAX_PATH_LEN];
  char fuse_tar_path[MAX_PATH_LEN];
  char install_path[MAX_PATH_LEN];
  char fuse_install_path[MAX_PATH_LEN];
  suseconds_t timestamp;
  int retval;
  struct stat statbuf;
  struct dirent *de;
  DIR *dp;
  int found;
  switch(cmd) {
    case CLOUDFS_SNAPSHOT:
      // get fuse root path
      normal_to_fuse(fuse_root_path, "/");
      // get timestamp in number of microseconds
      struct timeval tv;
      gettimeofday(&tv, NULL);
      // get the last 3 digits of seconds and convert to microseconds
      // 1 second is 1 million microseconds
      timestamp = (tv.tv_sec % 1000) * 1000000 + tv.tv_usec;
      *((suseconds_t *) data) = timestamp;
      // set tar file path
      sprintf(tar_path, "%lu", timestamp);
      // insert the timestamp
      if (insert_snapshot(tar_path) == -1)
        // cannot create new snapshot
        return -1;
      normal_to_fuse(fuse_tar_path, tar_path);
      // tar metadata and small files
      retval = tar_open(&t, fuse_tar_path, NULL, O_WRONLY | O_CREAT, S_IRWXU | S_IRWXG | S_IRWXO, TAR_GNU);
      if (retval == -1) {
        return cloudfs_error("[ioctl] tar_open");
      }
      // tar each file/directory recursively
      nftw(fuse_root_path, append_tar, 1, FTW_DEPTH);
      retval = tar_close(t);
      if (retval == -1) {
        return cloudfs_error("[ioctl] tar_close");
      }
      // get tar file size
      memset(&statbuf, 0, sizeof(statbuf));
      retval = lstat(fuse_tar_path, &statbuf);
      if (retval == -1) {
        return cloudfs_error("[ioctl] lstat");
      }
      // upload the tar file to cloud
      infile = fopen(fuse_tar_path, "rb");
      cloud_put_object("bucket", tar_path, statbuf.st_size, put_buffer);
      cloud_print_error();
      fclose(infile);
      unlink(fuse_tar_path);
      // update all reference count by 1
      cloud_list_bucket("bucket", incr_count);
      break;
    case CLOUDFS_RESTORE:
      // get timestamp
      timestamp = *((suseconds_t *) data);
      sprintf(tar_path, "%lu", timestamp);
      normal_to_fuse(fuse_tar_path, tar_path);
      // check if timestamp exists
      if (!segment_in_cloud(tar_path))
        // cannot find snapshot
        return -1;
      // delete all future snapshots
      delete_future_snapshots(tar_path);
      // get fuse root path
      normal_to_fuse(fuse_root_path, "/");
      // remove all metadata/small files
      dp = opendir(fuse_root_path);
      while ((de = readdir(dp)) != NULL) {
        if (!strcmp(de->d_name, "lost+found") ||
            !strcmp(de->d_name, ".snapshot") ||
            !strcmp(de->d_name, "..") ||
            !strcmp(de->d_name, "."))
          continue;
        mode_t mode = de->d_type << 12;
        if (S_ISREG(mode)) {
          char fuse_tmp[MAX_PATH_LEN];
          normal_to_fuse(fuse_tmp, de->d_name);
          // remove file
          unlink(fuse_tmp);
        }
        if (S_ISDIR(mode)) {
          char fuse_tmp[MAX_PATH_LEN];
          normal_to_fuse(fuse_tmp, de->d_name);
          // post-order traversal to remove all files/directories
          nftw(fuse_tmp, remove_dir, 1, FTW_DEPTH);
        }
      }
      closedir(dp);
      // get tar file from cloud 
      creat(fuse_tar_path, S_IRWXU | S_IRWXG | S_IRWXO);
      outfile = fopen(fuse_tar_path, "wb");
      cloud_get_object("bucket", tar_path, get_buffer);
      cloud_print_error();
      fclose(outfile);
      // untar files to ssd root
      retval = tar_open(&t, fuse_tar_path, NULL, O_RDONLY, S_IRWXU | S_IRWXG | S_IRWXO, TAR_GNU);
      if (retval == -1) {
        return cloudfs_error("[ioctl] tar_open");
      }
      retval = tar_extract_all(t, fuse_root_path); 
      if (retval == -1) {
        return cloudfs_error("[ioctl] tar_extract_all");
      }
      retval = tar_close(t);
      if (retval == -1) {
        return cloudfs_error("[ioctl] tar_close");
      }
      // remove tar file
      unlink(fuse_tar_path);
      // fix extended attributes of large files
      nftw(fuse_root_path, fix_ext, 1, FTW_DEPTH);
      break;
    case CLOUDFS_DELETE:
      // get timestamp
      timestamp = *((suseconds_t *) data);
      sprintf(tar_path, "%lu", timestamp);
      // get install folder
      strcpy(install_path, "snapshot_");
      strcat(install_path, tar_path);
      // get fuse root path
      normal_to_fuse(fuse_root_path, "/");
      // open root directory
      dp = opendir(fuse_root_path);
      // check if already installed
      found = 0;
      while ((de = readdir(dp)) != NULL) {
        if (!strcmp(de->d_name, install_path)) {
          // already installed
          found = 1;
        }
      }
      closedir(dp);
      // cannot delete installed snapshot
      if (found)
        return -1;
      // delete timestamp
      delete_snapshot(tar_path);
      break;
    case CLOUDFS_SNAPSHOT_LIST:
      // list snapshots
      list_snapshots(data);
      break;
    case CLOUDFS_INSTALL_SNAPSHOT:
      // get timestamp
      timestamp = *((suseconds_t *) data);
      sprintf(tar_path, "%lu", timestamp);
      normal_to_fuse(fuse_tar_path, tar_path);
      // get install folder
      strcpy(install_path, "snapshot_");
      strcat(install_path, tar_path);
      // check if timestamp exists
      if (!segment_in_cloud(tar_path))
        // cannot find snapshot
        return -1;
      // get fuse root path
      normal_to_fuse(fuse_root_path, "/");
      // open root directory
      dp = opendir(fuse_root_path);
      // check if already installed
      while ((de = readdir(dp)) != NULL) {
        if (!strcmp(de->d_name, install_path)) {
          // already installed
          closedir(dp);
          return -1;
        }
      }
      // create install folder
      normal_to_fuse(fuse_install_path, install_path);
      mkdir(fuse_install_path, S_IRWXU | S_IRWXG | S_IRWXO);
      // get tar file from cloud 
      creat(fuse_tar_path, S_IRWXU | S_IRWXG | S_IRWXO);
      outfile = fopen(fuse_tar_path, "wb");
      cloud_get_object("bucket", tar_path, get_buffer);
      cloud_print_error();
      fclose(outfile);
      // untar files to snapshot folder
      retval = tar_open(&t, fuse_tar_path, NULL, O_RDONLY, S_IRWXU | S_IRWXG | S_IRWXO, TAR_GNU);
      if (retval == -1) {
        return cloudfs_error("[ioctl] tar_open");
      }
      retval = tar_extract_all(t, fuse_install_path); 
      if (retval == -1) {
        return cloudfs_error("[ioctl] tar_extract_all");
      }
      retval = tar_close(t);
      if (retval == -1) {
        return cloudfs_error("[ioctl] tar_close");
      }
      // remove tar file
      unlink(fuse_tar_path);
      // fix extended attributes of large files
      nftw(fuse_install_path, fix_ext, 1, FTW_DEPTH);
      break;
    case CLOUDFS_UNINSTALL_SNAPSHOT:
      // get timestamp
      timestamp = *((suseconds_t *) data);
      sprintf(tar_path, "%lu", timestamp);
      // get installed folder
      strcpy(install_path, "snapshot_");
      strcat(install_path, tar_path);
      // get fuse root path
      normal_to_fuse(fuse_root_path, "/");
      // open root directory
      dp = opendir(fuse_root_path);
      // check if already installed
      found = 0;
      while ((de = readdir(dp)) != NULL) {
        if (!strcmp(de->d_name, install_path)) {
          // already installed
          found = 1;
        }
      }
      closedir(dp);
      // not installed
      if (!found)
        return -1;
      // remove snapshot directory
      normal_to_fuse(fuse_install_path, install_path);
      nftw(fuse_install_path, remove_dir, 1, FTW_DEPTH);
      break;
  }
  return 0;
}

/*
 * Functions supported by cloudfs 
 */
static struct fuse_operations cloudfs_operations = {
    /**** complete list of VFS functions ****/
    .getattr        = cloudfs_getattr,
    //.readlink       = cloudfs_readlink,
    .mknod          = cloudfs_mknod,
    .mkdir          = cloudfs_mkdir,
    .unlink         = cloudfs_unlink,
    .rmdir          = cloudfs_rmdir,
    //.symlink        = cloudfs_symlink,
    //.rename         = cloudfs_rename,
    //.link           = cloudfs_link,
    .chmod          = cloudfs_chmod,
    //.chown          = cloudfs_chown,
    .truncate       = cloudfs_truncate,
    .open           = cloudfs_open,
    .read           = cloudfs_read,
    .write          = cloudfs_write,
    //.statfs         = cloudfs_statfs,
    //.flush          = cloudfs_flush,
    .release        = cloudfs_release,
    //.fsync          = cloudfs_fsync,
    .setxattr       = cloudfs_setxattr,
    .getxattr       = cloudfs_getxattr,
    //.listxattr      = cloudfs_listxattr,
    //.removexattr    = cloudfs_removexattr,
    .opendir        = cloudfs_opendir,
    .readdir        = cloudfs_readdir,
    //.releasedir     = cloudfs_releasedir,
    //.fsyncdir       = cloudfs_fsyncdir,
    .init           = cloudfs_init,
    .destroy        = cloudfs_destroy,
    .access         = cloudfs_access,
    .create         = cloudfs_create,
    //.ftruncate      = cloudfs_ftruncate,
    //.fgetattr       = cloudfs_fgetattr,
    //.lock           = cloudfs_lock,
    .utimens        = cloudfs_utimens,
    //.bmap           = cloudfs_bmap,
    .ioctl          = cloudfs_ioctl
    //.poll           = cloudfs_poll,
    //.write_buf      = cloudfs_write_buf,
    //.read_buf       = cloudfs_read_buf,
    //.flock          = cloudfs_flock,
    //.fallocate      = cloudfs_fallocate
};

/*
 * Start Cloudfs
 */
int cloudfs_start(struct cloudfs_state *state, const char* fuse_runtime_name) {
  int argc = 0;
  char* argv[10];
  argv[argc] = (char *) malloc(128 * sizeof(char));
  strcpy(argv[argc++], fuse_runtime_name);
  argv[argc] = (char *) malloc(1024 * sizeof(char));
  strcpy(argv[argc++], state->fuse_path);
  argv[argc++] = "-s"; // set the fuse mode to single thread
  //argv[argc++] = "-f"; // run fuse in foreground 

  state_  = *state;
  // initialize log file
  logfile = fopen("/tmp/cloudfs.log", "w");
  setvbuf(logfile, NULL, _IOLBF, 0);
  // start fuse file system
  int fuse_stat = fuse_main(argc, argv, &cloudfs_operations, NULL);
    
  return fuse_stat;
}


