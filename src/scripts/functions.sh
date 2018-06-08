#!/bin/bash
CLOUDFSOPTS=""

function collect_stats()
{
  # flush fs buffers
  sync
  # sometimes s3server takes time to update the stats, so sleep
  sleep 1
  vmstat -d|grep ^sdb
  echo "cloud`curl http://localhost:8888/admin/stat 2> /dev/null| tail -1`"
  echo "timestamp `date +\"%s\"`" 
}

function calc_stats()
{
  if [ ! -f $1 ]; then
    echo "\nERROR: logfile '$1' does not exist\n"
	return
  fi

  for keyword in sdb cloud timestamp; do
    awk "BEGIN { line = 0 } 
    /^$keyword/ { ++line ; nfields=NF ; 
	              for(i=2; i<=NF; ++i) { data[line,i]=\$i }
                }
		END { printf(\"$keyword \");
		       for (i=2; i<=nfields; ++i) { 
                   printf(\"%d \",data[2,i]-data[1,i]) } 
                   printf(\"\\n\"); 
             }" $1
  done
}

function get_ssd_reads() { calc_stats $1|grep sdb|cut -d" " -f2; }
function get_ssd_writes() { calc_stats $1|grep sdb|cut -d" " -f6; }
function get_ssd_read_sectors() { calc_stats $1|grep sdb|cut -d" " -f4; }
function get_ssd_write_sectors() { calc_stats $1|grep sdb|cut -d" " -f8; }

function get_cloud_requests() { calc_stats $1|grep cloud|cut -d" " -f2; }
function get_cloud_read_bytes() { calc_stats $1|grep cloud|cut -d" " -f3; }
function get_cloud_current_usage(){ cat $1| grep cloud|tail -1|cut -d" " -f4;}
function get_cloud_max_usage() { cat $1|grep cloud|tail -1|cut -d" " -f5;}

function calculate_cloud_cost() 
{
  STATFILE=$1
  nread=`get_cloud_read_bytes $STATFILE`
  nreq=`get_cloud_requests $STATFILE`
  ncapacity=`get_cloud_max_usage $STATFILE`
  result=$(echo "scale=10; $ncapacity*0.000000091 + $nreq*0.01 + $nread*0.000000114" | bc -q 2>/dev/null)
  echo $result
}
#
# Prints the result string (and exits if test fails)
# Takes an argument: 0 indicates a passing test and 
# any other vaule indicates failure
#    
function print_result()
{
	if [ $1 -ne 0 ]; then
		echo "FAILED!!!"
		echo "Please see $LOG_DIR for further details"
		exit 1
	else
		echo "PASSED!!!"
	fi
}

function untar()
{
	FILE=$1
	DIR=$2
	echo "Untaring $FILE into $DIR ..."
	tar --atime-preserve --directory $DIR -xvzf $FILE > /dev/null
	if [ $? -ne 0 ];then
		echo "Unable to untar the $FILE into $DIR. Stopping the test."
		exit 1;
	fi
}

function process_args()
{
	OPTIONS=`getopt -o a:t:S:w:c:do --long ssd-size:,threshold:,avg-seg-size:,rabin-window-size:,cache-size:,no-dedup,no-cache -n '$0' -- "$@"`

	if [ $? != 0 ]; then
		echo "parsing options failed. Exiting."
		usage
		exit 1
	fi

	eval set -- "$OPTIONS"

	while true; do
		case "$1" in
		-a|--ssd-size) CLOUDFSOPTS+=" $1 $2"; SSDSIZE=$2; shift 2;;
		-t|--threshold) CLOUDFSOPTS+=" $1 $2";THRESHOLD=$2; shift 2;;
		-S|--avg-seg-size) CLOUDFSOPTS+=" $1 $2"; AVGSEGSIZE=$2; shift 2;;
		-w|--rabin-window-size) CLOUDFSOPTS+=" $1 $2"; RABINWINDOWSIZE=$2; shift 2;;
		-c|--cache-size) CLOUDFSOPTS+=" $1 $2"; CACHESIZE=$2; shift 2;;
    -d|--no-dedup) CLOUDFSOPTS+=" $1"; NODEDUP=1; shift 1;;
    -o|--no-cache) CLOUDFSOPTS+=" $1"; NOCACHE=1; shift 1;;
		-h|-\?) usage; exit 1;;
		*)break;;
		esac
	done

  if [ "$CLOUDFSOPTS" != "" ]; then
    echo "cloudfs will be passed following options : $CLOUDFSOPTS"
  else
    echo "cloudfs will be started with default options"
  fi
}

function reinit_env()
{
  echo ""
  echo "Re-initializing environment..."

  $SCRIPTS_DIR/reset.sh

  nohup python $SCRIPTS_DIR/../s3-server/s3server.pyc > /dev/null 2>&1 &
  if [ $? -ne 0 ]; then
    echo "Unable to start S3 server"
    exit 1
  fi
  # wait for s3 to initialize
  echo "Waiting for s3 server to initialize (sleep 5)..."
  sleep 5

  $SCRIPTS_DIR/cloudfs_controller.sh m $CLOUDFSOPTS
  if [ $? -ne 0 ]; then
    echo "Unable to start cloudfs"
    exit 1
  fi
}
