#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: COMPILE.SH 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/kernel/utilities/skeleton/F77/0/0/simple/COMPILE.SH $
# For license details see COPYING in the package base directory
#####################################################################
# Kernel: simple Variant of the Fortran-Skeleton
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

if [ -z "${BENCHIT_F77}" ]; then
	echo "No F77 compiler specified - check \$BENCHIT_F77"
	exit 1
fi


BENCHIT_COMMENT="Simple Fortran kernel"
export BENCHIT_COMMENT

BENCHIT_F_COMPILERFLAGS="${BENCHIT_F77_C_FLAGS} ${BENCHIT_F77_C_FLAGS_HIGH}"
BENCHIT_COMPILER="${BENCHIT_F77}"
BENCHIT_COMPILERFLAGS="${BENCHIT_F_COMPILERFLAGS}"
export BENCHIT_COMPILER BENCHIT_COMPILERFLAGS



##########################

BENCHIT_F_COMPILER="${BENCHIT_F77}"
BENCHIT_F_COMPILER="${BENCHIT_F_COMPILER} ${BENCHIT_F77_C_FLAGS}"
BENCHIT_F_COMPILER="${BENCHIT_F_COMPILER} ${BENCHIT_F77_C_FLAGS_HIGH}"
BENCHIT_F_COMPILER="${BENCHIT_F_COMPILER} ${BENCHIT_INCLUDES}"
BENCHIT_F_COMPILER="${BENCHIT_F_COMPILER} ${BENCHIT_DEFINES}"

BENCHIT_C_COMPILER="${BENCHIT_CC}" 
BENCHIT_C_COMPILER="${BENCHIT_C_COMPILER} ${BENCHIT_CC_C_FLAGS}"   
BENCHIT_C_COMPILER="${BENCHIT_C_COMPILER} ${BENCHIT_CC_C_FLAGS_HIGH}"
BENCHIT_C_COMPILER="${BENCHIT_C_COMPILER} ${BENCHIT_INCLUDES}"
BENCHIT_C_COMPILER="${BENCHIT_C_COMPILER} ${BENCHIT_DEFINES}"

##########################



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
printf "\n"
printf "###########"
printf "\n"
printf "# COMPILE #"
printf "\n"
printf "###########"
printf "\n"
sync

printf "${BENCHIT_F_COMPILER} -c simple.f -o simplef.o \n"
${BENCHIT_F_COMPILER} -c simple.f -o simplef.o
printf "\n"

printf "${BENCHIT_C_COMPILER} -c simple.c -o simplec.o\n"
${BENCHIT_C_COMPILER} -c simple.c -o simplec.o
printf "\n"

printf "${BENCHIT_C_COMPILER} -c kernel_main.c\n"
${BENCHIT_C_COMPILER} -c kernel_main.c
printf "\n"

printf "${BENCHIT_C_COMPILER} -c \"${BENCHITROOT}/benchit.c\"\n"
${BENCHIT_C_COMPILER} -c ${BENCHITROOT}/benchit.c
printf "\n"

#
# SECOND STAGE: LINK
# note that the executable is located in the main directory
#
printf "\n"
printf "########"
printf "\n"
printf "# LINK #"
printf "\n"
printf "########"
printf "\n"
sync

printf "${BENCHIT_F_COMPILER} -o ${BENCHIT_KERNELBINARY} *.o ${BENCHIT_F77_L_FLAGS}\n"
${BENCHIT_F_COMPILER} -o ${BENCHIT_KERNELBINARY} *.o ${BENCHIT_F77_L_FLAGS}
printf "\n"


#
# REMOVE *.o FILES
#
rm -f ${KERNELDIR}/*.o

#
# CHANGE TO THE MAIN DIRECTORY
#
cd ${BENCHITROOT}

