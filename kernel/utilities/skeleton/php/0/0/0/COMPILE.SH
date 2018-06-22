#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: COMPILE.SH 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/php/0/0/0/COMPILE.SH $
# For license details see COPYING in the package base directory
#####################################################################
# Kernel: php kernel skeleton
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
if [ -z "${BENCHIT_CC}" ]; then
	echo "No C compiler specified - check \$BENCHIT_CC"
	exit 1
fi

BENCHIT_COMMENT="C skeleton kernel"
export BENCHIT_COMMENT

BENCHIT_COMPILER="${BENCHIT_CC}"
BENCHIT_COMPILERFLAGS="${BENCHIT_CC_C_FLAGS} ${BENCHIT_CC_C_FLAGS_HIGH}"
BENCHITC_COMPILER="${BENCHIT_CC} ${BENCHIT_CC_C_FLAGS} ${BENCHIT_CC_C_FLAGS_STD} ${BENCHIT_INCLUDES} ${BENCHIT_DEFINES}"
BENCHIT_LINKER_FLAGS="${BENCHIT_CC_L_FLAGS} ${BENCHIT_LIB_PTHREAD}"

export BENCHIT_COMPILER BENCHIT_COMPILERFLAGS

#
# ENVIRONMENT HASHING - creates bienvhash.c
#
cd ${BENCHITROOT}/tools/
set > tmp.env
./fileversion >> tmp.env
./envhashbuilder
cd ${KERNELDIR}

#
# FIRST STAGE: COMPILE
#
printf "${BENCHIT_COMPILER} ${BENCHIT_COMPILERFLAGS} ${BENCHIT_INCLUDES} ${BENCHIT_DEFINES} -c kernel_main.c\n"
${BENCHIT_COMPILER} ${BENCHIT_COMPILERFLAGS} ${BENCHIT_INCLUDES} ${BENCHIT_DEFINES} -c kernel_main.c

printf "${BENCHITC_COMPILER} -c ${BENCHITROOT}/benchit.c\n"
${BENCHITC_COMPILER} -c ${BENCHITROOT}/benchit.c

printf "${BENCHITC_COMPILER} -c ${BENCHITROOT}/tools/benchscript.c\n"
${BENCHITC_COMPILER} -c ${BENCHITROOT}/tools/benchscript.c

#
# SECOND STAGE: LINK
# note that the executable main is located in the main directory
#
printf "${BENCHIT_COMPILER} ${BENCHIT_COMPILERFLAGS} -o ${BENCHIT_KERNELBINARY} *.o ${BENCHIT_CC_L_FLAGS}\n"
${BENCHIT_COMPILER} ${BENCHIT_COMPILERFLAGS} -o ${BENCHIT_KERNELBINARY} *.o ${BENCHIT_LINKER_FLAGS}

#
# REMOVE *.o FILES
#
rm -f ${KERNELDIR}/*.o

#
# CHANGE TO THE MAIN DIRECTORY
#
cd ${BENCHITROOT}

