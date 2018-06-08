/** **************************************************************************
 * This file is modified from s3.c in libs3
 * 
 * libs3 is free software: you can redistribute it and/or modify it under the
 * terms of the GNU General Public License as published by the Free Software
 * Foundation, version 3 of the License.
 *
 * In addition, as a special exception, the copyright holders give
 * permission to link the code of this library and its programs with the
 * OpenSSL library, and distribute linked combinations including the two.
 *
 * You should have received a copy of the GNU General Public License version 3
 * along with libs3, in a file named COPYING.  If not, see
 * <http://www.gnu.org/licenses/>.
 *
 ************************************************************************** **/

#include <ctype.h>
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
#define UNUSED __attribute__((unused))

#if CLOUD_LOCAL_DEBUG

#else

//S3 global options ------------------------------------------------------------
static int showResponsePropertiesG = 0;
static S3Protocol protocolG = S3ProtocolHTTP;
static S3UriStyle uriStyleG = S3UriStylePath;
static S3CannedAcl cannedAcl = S3CannedAclPrivate;

static const char accessKeyIdG[16] = "";
static const char secretAccessKeyG[16] = "";



// Request results, saved as globals -------------------------------------------

static int statusG = 0;
static char errorDetailsG[4096] = { 0 };

// response properties callback ------------------------------------------------

// This callback does the same thing for every request type: prints out the
// properties if the user has requested them to be so
static S3Status responsePropertiesCallback
    (const S3ResponseProperties *properties, void *callbackData)
{
    (void) callbackData;

    if (!showResponsePropertiesG) {
        return S3StatusOK;
    }

#define print_nonnull(name, field)                                 \
    do {                                                           \
        if (properties-> field) {                                  \
            printf("%s: %s\n", name, properties-> field);          \
        }                                                          \
    } while (0)
    
    print_nonnull("Content-Type", contentType);
    print_nonnull("Request-Id", requestId);
    print_nonnull("Request-Id-2", requestId2);
    if (properties->contentLength > 0) {
        printf("Content-Length: %lld\n", 
               (unsigned long long) properties->contentLength);
    }
    print_nonnull("Server", server);
    print_nonnull("ETag", eTag);
    if (properties->lastModified > 0) {
        char timebuf[256];
        time_t t = (time_t) properties->lastModified;
        // gmtime is not thread-safe but we don't care here.
        strftime(timebuf, sizeof(timebuf), "%Y-%m-%dT%H:%M:%SZ", gmtime(&t));
        printf("Last-Modified: %s\n", timebuf);
    }
    int i;
    for (i = 0; i < properties->metaDataCount; i++) {
        printf("x-amz-meta-%s: %s\n", properties->metaData[i].name,
               properties->metaData[i].value);
    }

    return S3StatusOK;
}


// response complete callback ------------------------------------------------

// This callback does the same thing for every request type: saves the status
// and error stuff in global variables
static void responseCompleteCallback(S3Status status,
                                     const S3ErrorDetails *error, 
                                     void *callbackData)
{
    (void) callbackData;

    statusG = status;
    // Compose the error details message now, although we might not use it.
    // Can't just save a pointer to [error] since it's not guaranteed to last
    // beyond this callback
    int len = 0;
    if (error && error->message) {
        len += snprintf(&(errorDetailsG[len]), sizeof(errorDetailsG) - len,
                        "  Message: %s\n", error->message);
    }
    if (error && error->resource) {
        len += snprintf(&(errorDetailsG[len]), sizeof(errorDetailsG) - len,
                        "  Resource: %s\n", error->resource);
    }
    if (error && error->furtherDetails) {
        len += snprintf(&(errorDetailsG[len]), sizeof(errorDetailsG) - len,
                        "  Further Details: %s\n", error->furtherDetails);
    }
    if (error && error->extraDetailsCount) {
        len += snprintf(&(errorDetailsG[len]), sizeof(errorDetailsG) - len,
                        "%s", "  Extra Details:\n");
        int i;
        for (i = 0; i < error->extraDetailsCount; i++) {
            len += snprintf(&(errorDetailsG[len]), 
                            sizeof(errorDetailsG) - len, "    %s: %s\n", 
                            error->extraDetails[i].name,
                            error->extraDetails[i].value);
        }
    }
}


S3Status cloud_init(const char* hostname) {
  return S3_initialize("s3", S3_INIT_ALL, hostname);
}

void cloud_destroy() {
  S3_deinitialize();
}

void cloud_print_error()
{
  if (statusG < S3StatusErrorAccessDenied) {
    fprintf(stderr, "Return status: %s\n", S3_get_status_name(statusG));
  }
  else {
    fprintf(stderr, "Return status: %s\n", S3_get_status_name(statusG));
    fprintf(stderr, "%s\n", errorDetailsG);
  }
}

// List Services --------------------------------------------------------------

typedef struct list_service_data
{
  list_service_filler_t filler;
} list_service_data;


static S3Status listServiceCallback(const char *ownerId UNUSED, 
                                    const char *ownerDisplayName UNUSED,
                                    const char *bucketName,
                                    int64_t creationDate UNUSED, void *callbackData)
{
  list_service_data *data = (list_service_data *) callbackData;

  data->filler(bucketName);

  return S3StatusOK;
}

S3Status cloud_list_service(list_service_filler_t filler)
{
  list_service_data data;

  data.filler = filler;

  S3ListServiceHandler listServiceHandler =
  {
    { &responsePropertiesCallback, &responseCompleteCallback },
    &listServiceCallback
  };

  S3_list_service(protocolG, accessKeyIdG, secretAccessKeyG, 0, 0, 
                  &listServiceHandler, &data);

  return statusG;
}



S3Status cloud_create_bucket(const char *bucketName) {
  S3ResponseHandler responseHandler =
  {
    &responsePropertiesCallback, &responseCompleteCallback
  };

  S3_create_bucket(protocolG, accessKeyIdG, secretAccessKeyG,
                   0, bucketName, cannedAcl, 0, 0,
                   &responseHandler, 0);
  return statusG;
}

S3Status cloud_delete_bucket(const char *bucketName) {
  S3ResponseHandler responseHandler =
  {
    &responsePropertiesCallback, &responseCompleteCallback
  };

  S3_delete_bucket(protocolG, uriStyleG, accessKeyIdG, secretAccessKeyG,
                   0, bucketName, 0, &responseHandler, 0);
  return statusG;
}

// List bucket ----------------------------------------------------------------

typedef struct list_bucket_callback_data
{
    int isTruncated;
    char nextMarker[1024];
    int keyCount;
    list_bucket_filler_t filler;
} list_bucket_callback_data;

static S3Status listBucketCallback(int isTruncated, const char *nextMarker,
                                   int contentsCount, 
                                   const S3ListBucketContent *contents,
                                   int commonPrefixesCount UNUSED,
                                   const char **commonPrefixes UNUSED,
                                   void *callbackData)
{
    list_bucket_callback_data *data = 
        (list_bucket_callback_data *) callbackData;

    data->isTruncated = isTruncated;
    // This is tricky.  S3 doesn't return the NextMarker if there is no
    // delimiter.  Why, I don't know, since it's still useful for paging
    // through results.  We want NextMarker to be the last content in the
    // list, so set it to that if necessary.
    if ((!nextMarker || !nextMarker[0]) && contentsCount) {
        nextMarker = contents[contentsCount - 1].key;
    }
    if (nextMarker) {
        snprintf(data->nextMarker, sizeof(data->nextMarker), "%s", 
                 nextMarker);
    }
    else {
        data->nextMarker[0] = 0;
    }

    int i;
    for (i = 0; i < contentsCount; i++) {
        const S3ListBucketContent *content = &(contents[i]);
        data->filler(content->key, content->lastModified, content->size);
    }

    data->keyCount += contentsCount;

    return S3StatusOK;
}

S3Status cloud_list_bucket(const char *bucketName, list_bucket_filler_t filler) {
  S3BucketContext bucketContext =
  {
    0,
    bucketName,
    protocolG,
    uriStyleG,
    accessKeyIdG,
    secretAccessKeyG
  };

  S3ListBucketHandler listBucketHandler =
  {
    { &responsePropertiesCallback, &responseCompleteCallback },
    &listBucketCallback
  };

  list_bucket_callback_data data;

  const char *prefix = 0, *marker = 0, *delimiter = 0;
  int maxkeys = 0;
  snprintf(data.nextMarker, sizeof(data.nextMarker), "%s", marker);
  data.filler = filler;

  do {
    data.isTruncated = 0;
    S3_list_bucket(&bucketContext, prefix, data.nextMarker,
                   delimiter, maxkeys, 0, &listBucketHandler, &data);
    if (statusG != S3StatusOK) {
        break;
    }
  } while (data.isTruncated);

  return statusG;
}

// Put object -----------------------------------------------------------------
typedef struct put_object_callback_data
{
    uint64_t offset;
    uint64_t remainingLength;
    uint64_t contentLength;
    put_filler_t filler;
    int noStatus;
} put_object_callback_data;

static int putObjectDataCallback(int bufferSize, char *buffer,
                                 void *callbackData)
{
    put_object_callback_data *data = 
        (put_object_callback_data *) callbackData;
    
    int ret = 0;

    if (data->remainingLength) {
        int toRead = ((data->remainingLength > (unsigned) bufferSize) ?
                      (unsigned) bufferSize : data->remainingLength);
        ret = data->filler(buffer, toRead);
    }

    data->offset += ret;
    data->remainingLength -= ret;

    if (data->remainingLength && !data->noStatus) {
        // Avoid a weird bug in MingW, which won't print the second integer
        // value properly when it's in the same call, so print separately
        printf("%llu bytes remaining ", 
               (unsigned long long) data->remainingLength);
        printf("(%d%% complete) ...\n",
               (int) (((data->contentLength - 
                        data->remainingLength) * 100) /
                      data->contentLength));
    }

    return ret;
}

S3Status cloud_put_object(const char *bucketName, const char *key,
                          uint64_t contentLength, put_filler_t filler) {

    S3BucketContext bucketContext =
    {
        0,
        bucketName,
        protocolG,
        uriStyleG,
        accessKeyIdG,
        secretAccessKeyG
    };

    S3PutProperties putProperties =
    {
        NULL, 
        NULL,
        NULL,
        NULL,
        NULL,
        -1,
        cannedAcl,
        0,
        NULL 
    };

    S3PutObjectHandler putObjectHandler =
    {
        { &responsePropertiesCallback, &responseCompleteCallback },
        &putObjectDataCallback
    };

    put_object_callback_data data;

    data.offset = 0;
    data.contentLength = data.remainingLength = contentLength;
    data.filler = filler;
    data.noStatus = 0;

    S3_put_object(&bucketContext, key, contentLength, &putProperties, 0,
                  &putObjectHandler, &data);

    return statusG;
}

// Get object -----------------------------------------------------------------

static S3Status getObjectDataCallback(int bufferSize, const char *buffer,
                                      void *callbackData)
{
    get_filler_t filler = (get_filler_t) callbackData;

    int wrote = filler(buffer, (uint64_t) bufferSize);

    return ((wrote <  bufferSize) ? 
            S3StatusAbortedByCallback : S3StatusOK);
}

S3Status cloud_get_object(const char *bucketName, const char *key,
                    get_filler_t filler) {

  uint64_t startByte = 0, byteCount = 0;
  int64_t ifModifiedSince = -1, ifNotModifiedSince = -1;
  const char *ifMatch = 0, *ifNotMatch = 0;

  S3BucketContext bucketContext =
  {
      0,
      bucketName,
      protocolG,
      uriStyleG,
      accessKeyIdG,
      secretAccessKeyG
  };

  S3GetConditions getConditions =
  {
      ifModifiedSince,
      ifNotModifiedSince,
      ifMatch,
      ifNotMatch
  };

  S3GetObjectHandler getObjectHandler =
  {
      { &responsePropertiesCallback, &responseCompleteCallback },
      &getObjectDataCallback
  };

  S3_get_object(&bucketContext, key, &getConditions, startByte,
                byteCount, 0, &getObjectHandler, filler);

  return statusG;
}

S3Status cloud_delete_object(const char *bucketName, const char *key) {
  S3BucketContext bucketContext =
  {
      0,
      bucketName,
      protocolG,
      uriStyleG,
      accessKeyIdG,
      secretAccessKeyG
  };

  S3ResponseHandler responseHandler =
  { 
      0,
      &responseCompleteCallback
  };

  S3_delete_object(&bucketContext, key, 0, &responseHandler, 0);

  return statusG;
}

#endif
