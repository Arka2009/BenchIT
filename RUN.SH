#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: RUN.SH 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/RUN.SH $
# For license details see COPYING in the package base directory
#####################################################################
# Shellscript runing kernels
#
#  The script sets the environment-variable CONFIGURE_MODE to RUN
#  and then starts tools/configure which sets up the variables
#  needed to run the binary located in the ./bin/ folder.
#####################################################################

# Go to RUN.SH directory
cd "`dirname ${0}`" || exit 1

# Set configure mode
CONFIGURE_MODE="RUN"

# Load the definitions
. ./tools/configure

# Check if BENCHIT_KERNELBINARY is a directory
# -> Java kernel -> cd and set BENCHIT_KERNELBINARY to "$JVM JBI"
if [ -d "${BENCHIT_KERNELBINARY}" ]; then
   cd "${BENCHIT_KERNELBINARY}"
   export CLASSPATH="${CLASSPATH}:`pwd`"
   # add BENCHIT_LD_LIBRARY_PATH to LD_LIBRARY_PATH to allow Java-kernels to use the JNI-Libraries
   export LD_LIBRARY_PATH="${LD_LIBRARY_PATH}:${BENCHIT_LD_LIBRARY_PATH}"
   BENCHIT_KERNELBINARY="${BENCHIT_JAVA} -cp ${CLASSPATH} JBI"
fi

# Check for existence of selected environment
if [ ! -f ${BENCHITROOT}/tools/environments/${BENCHIT_ENVIRONMENT} ]; then
   printf "BenchIT: Your selected environment \"${BENCHIT_ENVIRONMENT}\" can not be found.\n"
   printf "         Execution of the kernel aborted.\n\n"
   exit 1
fi

# Execute kernel
#echo ${BENCHIT_ENVIRONMENT}
#echo "Amaity: ChkPnt 1"
#exit 1
. ${BENCHITROOT}/tools/environments/${BENCHIT_ENVIRONMENT}

