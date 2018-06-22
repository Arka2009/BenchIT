#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: run.sh 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/Java/0/PCL/0/run.sh $
# For license details see COPYING in the package base directory
#####################################################################
# Kernel: java pcl kernel skeleton
# Shellscript running java kernels
#####################################################################

if [ -z "${BENCHITROOT}" ]; then
	# running stand-alone
	java JBI $@
else
	"${JVM}" JBI $@
fi

