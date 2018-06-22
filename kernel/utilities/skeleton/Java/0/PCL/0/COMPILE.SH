#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: COMPILE.SH 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/Java/0/PCL/0/COMPILE.SH $
# For license details see COPYING in the package base directory
#####################################################################
# Kernel: java pcl kernel skeleton
#####################################################################

# If kernel name string is set, this COMPILE.SH is sourced
# from the global COMPILE.SH. If it's not set, the user
# executed this script directly so we need to call configure.
if [ -z "${BENCHIT_KERNELNAME}" ]; then
	# Go to COMPILE.SH directory
	cd `dirname ${0}` || exit 1

	# Set configure mode
	CONFIGURE_MODE="COMPILE"

	# Load the definitions
	. ../../../../../../../tools/configure
fi

# check wether compilers and libraries are available
if [ -z "${BENCHIT_JAVAC}" ]; then
	echo "No Java compiler specified - check \$BENCHIT_JAVAC"
	exit 1
fi

BENCHIT_COMPILER="${BENCHIT_JAVAC}"
BENCHIT_COMPILERFLAGS="${BENCHIT_JAVAC_FLAGS_HIGH}"
BENCHIT_JAVAKERNELCLASS="SkeletonPCLKernelMain"

BENCHIT_COMMENT="Plain skeleton for Java kernels using the PCL"
export BENCHIT_COMMENT

export BENCHIT_COMPILER BENCHIT_COMPILERFLAGS BENCHIT_JAVAKERNELCLASS

#
# ENVIRONMENT HASHING - creates jbi/BIEnvHash.java
#
cd ${BENCHITROOT}/tools/
set > tmp.env
./fileversion >> tmp.env
./envhashbuilder
cd ${KERNELDIR}

DEST="${BENCHIT_KERNELBINARY}"
if [ ! -d ${DEST} ]; then
	mkdir ${DEST}
fi

rm -f ${DEST}/*.class
rm -f ${DEST}/*.java

cp -f SkeletonPCLDataObject.java ${DEST}
cp -f SkeletonPCLWork.java ${DEST}
cp -f ${BENCHIT_JAVAKERNELCLASS}.java ${DEST}
cp -f ${BENCHITROOT}/jbi/*.java ${DEST}

cd ${DEST}

# compile
printf "${BENCHIT_COMPILER} ${BENCHIT_COMPILERFLAGS} *.java\n"
${BENCHIT_COMPILER} ${BENCHIT_COMPILERFLAGS} *.java
rm -f *.java

