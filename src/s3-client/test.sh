export S3_ACCESS_KEY_ID=
export S3_SECRET_ACCESS_KEY= 
export S3_HOSTNAME=localhost:8888
./build/bin/s3 -u list
./build/bin/s3 -u create flyer
./build/bin/s3 -u list
./build/bin/s3 -u list flyer
./build/bin/s3 -u put flyer/gosh filename=./a.out
./build/bin/s3 -u list flyer
./build/bin/s3 -u get flyer/gosh filename=./b.out
./build/bin/s3 -u list flyer
./build/bin/s3 -u delete flyer/gosh
./build/bin/s3 -u delete flyer
./build/bin/s3 -u list
