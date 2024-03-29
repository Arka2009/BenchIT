 #!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: COMPILE.SH 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/C/0/0/simple/COMPILE.SH $
# For license details see COPYING in the package base directory
#####################################################################
# Kernel: simple Variant of the c-Skeleton
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

BENCHIT_COMMENT="Simple C kernel"
export BENCHIT_COMMENT

# set up c-compiler
BENCHIT_COMPILER="${BENCHIT_CC}"
BENCHIT_COMPILERFLAGS="${BENCHIT_CC_C_FLAGS} ${BENCHIT_CC_C_FLAGS_HIGH}"
BENCHITC_COMPILER="${BENCHIT_CC} ${BENCHIT_CC_C_FLAGS} ${BENCHIT_CC_C_FLAGS_STD} ${BENCHIT_INCLUDES} ${BENCHIT_DEFINES}"
C_COMPILE="${BENCHIT_COMPILER} ${BENCHIT_COMPILERFLAGS} ${BENCHIT_DEFINES} ${BENCHIT_INCLUDES} -c"

L_FLAGS="${BENCHIT_CC_L_FLAGS}"
C_LINK="${BENCHIT_COMPILER} ${BENCHIT_COMPILERFLAGS} -o ${BENCHIT_KERNELBINARY} *.o ${BENCHIT_CC_L_FLAGS}"

export BENCHIT_COMPILER BENCHIT_COMPILERFLAGS L_FLAGS

#
# ENVIRONMENT HASHING - creates bienvhash.c
#
cd ${BENCHITROOT}/tools/
set > tmp.env
./fileversion >> tmp.env
./envhashbuilder
cd ${KERNELDIR}

#
# COMPILE
#
printf "${C_COMPILE} simple.c\n"
${C_COMPILE} simple.c
printf "${C_COMPILE} kernel_main.c\n"
${C_COMPILE} kernel_main.c
printf "${BENCHITC_COMPILER} -c \"${BENCHITROOT}/benchit.c\"\n"
${BENCHITC_COMPILER} -c ${BENCHITROOT}/benchit.c

#
# SECOND STAGE: LINK
# note that the executable is located in the main directory
#
printf "${C_LINK}\n"
${C_LINK}

#
# REMOVE *.o FILES
#
rm -f ${KERNELDIR}/*.o

#
# CHANGE TO THE MAIN DIRECTORY
#
cd ${BENCHITROOT}

