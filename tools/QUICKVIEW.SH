#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: QUICKVIEW.SH 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/tools/QUICKVIEW.SH $
# For license details see COPYING in the package base directory
#####################################################################
# Shell script using gnuplot to display resultfile(s)
#####################################################################

#cd `dirname ${0}` || exit 1
#cd ../output

# remove eps-files and *.gp-files without corresponding *.bit-file
#rm -f *.eps

if [ "$1" = "" ]
then
   echo "QUICKVIEW: No file to view entered"
   echo "           Usage: ./QUICKVIEW <outputfile1.bit>"
   exit
fi

while [ "$1" != "" ]
do
   FOLDER=`dirname $1`
   FILE=`basename $1`
   cd $FOLDER
   gnuplot "${FILE}.gp"
   { gv "${FILE}.gp.eps" || gview "${FILE}.gp.eps" ||  echo "QUICKVIEW: Ghostview not found. Could not display ${FILE}.gp.eps"; } &
   shift
done

