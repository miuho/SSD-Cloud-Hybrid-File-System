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
#include <time.h>
#include <unistd.h>
#include "cloudapi.h"
#include "../cloudfs/cloudfs.h"

int list_bucket(const char *key, time_t modified_time, uint64_t size) {
  fprintf(stdout, "%s %lu %llu\n", key, modified_time, size);
  return 0;
}

int list_service(const char *bucketName) {
  fprintf(stdout, "%s\n", bucketName);
  return 0; 
}

static FILE *outfile;
int get_buffer(const char *buffer, int bufferLength) {
  return fwrite(buffer, 1, bufferLength, outfile);  
}

static FILE *infile;
int put_buffer(char *buffer, int bufferLength) {
  fprintf(stdout, "put_buffer %d \n", bufferLength);
  return fread(buffer, 1, bufferLength, infile);
}

int test() {
  printf("Start test!\n");

  cloud_init("localhost:8888");
  cloud_print_error();
  cloud_list_service(list_service);
  cloud_print_error();

  printf("Create bucket\n");
  cloud_create_bucket("test");
  cloud_print_error();

  cloud_list_service(list_service);
  cloud_print_error();

  printf("Put object\n");
  infile = fopen("./README", "rb");
  if(infile == NULL)
  {
    printf("File not found.");
    return 1;
  }
  struct stat stat_buf;
  lstat("./README", &stat_buf);
  cloud_put_object("test", "helloworld", stat_buf.st_size, put_buffer);
  fclose(infile);
  cloud_print_error();

  printf("List bucket test:\n");
  cloud_list_bucket("test", list_bucket);

  printf("Get object:\n");
  outfile = fopen("/tmp/README", "wb");
  cloud_get_object("test", "helloworld", get_buffer);
  fclose(outfile);
  cloud_print_error();

  printf("Delete object:\n");
  cloud_delete_object("test", "helloworld");
  cloud_print_error();

  printf("List bucket test:\n");
  cloud_list_bucket("test", list_bucket);
  cloud_print_error();

  printf("Delete bucket test:\n");
  cloud_delete_bucket("test");
  cloud_print_error();

  printf("List service:\n");
  cloud_list_service(list_service);

  printf("End test!\n");

  cloud_destroy();
  return 0;
}

int main() {
  return test();
}
