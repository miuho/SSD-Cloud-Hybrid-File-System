#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <limits.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <openssl/md5.h>
#include "dedup.h"

void usage(const char *program)
{
	printf("\n");
	printf("This program divides the file into segments using\n");
	printf("Rabin fingerprinting technique. It prints out the\n");
	printf("segment lengths and their the MD5 sums.\n\n");
	printf("Usage : %s -f <file> -a <avg-segment-size> \n", program);
	printf("           -i <min-segment-size> -x <max-segment-size>\n");
	printf("           -w <rabin-window-size>\n\n");
	printf("Incase no file is specified, input will be read from stdin.\n\n");
}

int main(int argc, const char *argv[])
{
	int window_size = 48 ;
	int avg_seg_size = 4096;
	int min_seg_size = 2048;
	int max_seg_size = 8192;
	char fname[PATH_MAX] = {0};

	int c;
	while ((c = getopt(argc, (char * const*)argv, "f:w:a:i:x:")) != -1) {
		switch (c) {
		case 'f': 
			strncpy(fname, optarg, sizeof fname);
			break; 
		case 'w':
			window_size = atoi(optarg);
			break;
		case 'a':
			avg_seg_size = atoi(optarg);
			break;
		case 'i':
			min_seg_size = atoi(optarg);
			break;
		case 'x':
			max_seg_size = atoi(optarg);
			break;
		default:
			usage(argv[0]);
			exit(1);
		}
	}

	int fd;
	if (fname[0]) {
		fd = open(fname, O_RDONLY);
		if (fd == -1) {
			perror("open failed:");
			exit(2);
		}
	} else {
		/* Use stdin if filename was not specified */
		fd = STDIN_FILENO;
	}

	
	/*
	printf("Window size                : %d\n", window_size);
	printf("Avg segment size requested : %d\n", avg_seg_size);
	printf("Min segment size requested : %d\n", min_seg_size);
	printf("Max segment size requested : %d\n", max_seg_size);
	printf("Reading file %s\n", fname);	
	*/
	
	rabinpoly_t *rp = rabin_init( window_size, avg_seg_size, 
								  min_seg_size, max_seg_size);

	if (!rp) {
		fprintf(stderr, "Failed to init rabinhash algorithm\n");
		exit(1);
	}


	MD5_CTX ctx;
	unsigned char md5[MD5_DIGEST_LENGTH];		
	int new_segment = 0;
	int len, segment_len = 0, b;
	char buf[1024];
	int bytes;

	MD5_Init(&ctx);
	while( (bytes = read(fd, buf, sizeof buf)) > 0 ) {
		char *buftoread = (char *)&buf[0];
		while ((len = rabin_segment_next(rp, buftoread, bytes, 
											&new_segment)) > 0) {
			MD5_Update(&ctx, buftoread, len);
			segment_len += len;
			
			if (new_segment) {
				MD5_Final(md5, &ctx);

				printf("%u ", segment_len);
				for(b = 0; b < MD5_DIGEST_LENGTH; b++)
					printf("%02x", md5[b]);
				printf("\n");

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
			fprintf(stderr, "Failed to process the segment\n");
			exit(2);
		}
	}
	MD5_Final(md5, &ctx);

	printf("%u ", segment_len);
	for(b = 0; b < MD5_DIGEST_LENGTH; b++) {
		printf("%02x", md5[b]);
	}
	printf("\n");

	rabin_free(&rp);

	return 0;
}
