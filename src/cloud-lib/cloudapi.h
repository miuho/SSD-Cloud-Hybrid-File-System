#ifndef __CLOUD_API_H__
#define __CLOUD_API_H__

#include "libs3.h"

// Call back functions for read/write objects and list buckets
typedef int(* put_filler_t) (char *buffer, int bufferLength);

typedef int(* get_filler_t) (const char *buffer, int bufferLength);

typedef int(* list_bucket_filler_t) (const char *key, time_t modified_time,
                                     uint64_t size);

typedef int(* list_service_filler_t) (const char *bucketName);

// Call cloud_init before creating connection to S3 server
S3Status cloud_init(const char* hostname);

// cloud_destroy must be called once per program for each call to cloud_init
void cloud_destroy();

// Print out return status of libs3 client library to stdout
// It help show the error message after each libs3 call 
void cloud_print_error();

// Basic S3 APIs: LIST, PUT, GET, DELETE   
S3Status cloud_list_service(list_service_filler_t filler);

S3Status cloud_create_bucket(const char *bucketName);

S3Status cloud_delete_bucket(const char *bucketName);

S3Status cloud_list_bucket(const char *bucketName,
                           list_bucket_filler_t filler);

S3Status cloud_put_object(const char *bucketName, const char *key,
                          uint64_t contentLength, put_filler_t filler);

S3Status cloud_get_object(const char *bucketName, const char *key,
                          get_filler_t filler);

S3Status cloud_delete_object(const char *bucketName, const char *key);

#endif
