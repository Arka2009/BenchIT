#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: COMPILE.SH 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/COMPILE.SH $
# For license details see COPYING in the package base directory
#####################################################################
# Shellscript compiling kernels
#
#  The script sets the environment-variable CONFIGURE_MODE to COMPILE
#  and then starts tools/configure which sets up the variables
#  needed by the COMPILE.SH's of the kernels.
#####################################################################

showAndExecute()
{
	set -f
	echo $1
	sync
	set +f
  $1
  retval=$?
	sync
  return $retval
}

LastChecked=""

checkCompilerAvailability()
{
	if [ "$LastChecked" != "$1" ]; then
		printf "Checking for compiler \"$1\"... "
		sync
		if { "${BENCHITROOT}/tools/features" have $1 ;} then
			echo "OK"
		else
			printf "\nCompiler \"$1\" not found. Cannot continue without it!\n"
			cleanupAndExit 98
		fi
		sync
	fi
}

checkLinkerAvailability()
{
	if [ "$LastChecked" != "$1" ]; then
		printf "Checking for linker \"$1\"... "
		sync
		if { "${BENCHITROOT}/tools/features" have $1 ;} then
			echo "OK"
		else
			printf "\Linker \"$1\" not found. Cannot continue without it!\n"
			cleanupAndExit 99
		fi
		sync
	fi
}

# Go to COMPILE.SH directory
cd "`dirname ${0}`" || exit 1

# Set configure mode
CONFIGURE_MODE="COMPILE"

# Switch for cmdlineparams to enable scan for missing LOCAL_BENCHITBINARY
COMPILE_GLOBAL=1

# Load the definitions
. ./tools/configure

if [ "${KERNELDIR}" = "${BENCHITROOT}" ]; then
	# Global COMPILE.SH was called without a target
	printf "\nERROR: No kernel for compile specified.\n"
	printf "Use COMPILE.SH -h to view the syntax of this command.\n\n"
	exit 1
fi

#Fix casing
if [ "${HLL}" = "Java" ]; then
	HLL="JAVA"
fi

# figure out compiler versions
if [ ${BENCHIT_CC} ] && [ "${BENCHIT_CC}" != "" ] && { "${BENCHITROOT}/tools/features" have ${BENCHIT_CC} ;}
then
#### for compiler version uncomment the following lines
#  	getCompilerVersion ${BENCHIT_CC}
#  	if [ "${?}" -eq 0 ]
#  	then
#  		BENCHIT_CC_COMPILER_VERSION="${BENCHIT_COMPILER_VERSION}"
#  	fi
#  export BENCHIT_CC_COMPILER_VERSION
####
  export BENCHIT_COMPILETIME_CC="${BENCHIT_CC}"
fi

if ([ "${HLL}" = "CXX" ] || [ "${HLL}" = "C++" ]) && [ ${BENCHIT_CXX} ] && [ "${BENCHIT_CXX}" != "" ] && { "${BENCHITROOT}/tools/features" have ${BENCHIT_CXX} ;}
then
#### for compiler version uncomment the following lines
#  	getCompilerVersion ${BENCHIT_CXX}
#  	if [ "${?}" -eq 0 ]
#  	then
#  		BENCHIT_CXX_COMPILER_VERSION="${BENCHIT_COMPILER_VERSION}"
#  	fi
#  export BENCHIT_CXX_COMPILER_VERSION
####
  export BENCHIT_COMPILETIME_CXX="${BENCHIT_CXX}"
fi

if [ "${HLL}" = "CPP" ] && [ ${BENCHIT_CXX} ] && [ "${BENCHIT_CXX}" != "" ] && { "${BENCHITROOT}/tools/features" have ${BENCHIT_CXX} ;}
then
#### for compiler version uncomment the following lines
#  	getCompilerVersion ${BENCHIT_CXX}
#  	if [ "${?}" -eq 0 ]
#  	then
#  		BENCHIT_CXX_COMPILER_VERSION="${BENCHIT_COMPILER_VERSION}"
#  	fi
#  export BENCHIT_CXX_COMPILER_VERSION
####
  export BENCHIT_COMPILETIME_CXX="${BENCHIT_CXX}"
fi

if [ "${HLL}" = "F77" ] && [ ${BENCHIT_F77} ] && [ "${BENCHIT_F77}" != "" ] && { "${BENCHITROOT}/tools/features" have ${BENCHIT_F77} ;}
then
#### for compiler version uncomment the following lines
#  	getCompilerVersion ${BENCHIT_F77}
#  	if [ "${?}" -eq 0 ]
#  	then
#  		BENCHIT_F77_COMPILER_VERSION="${BENCHIT_COMPILER_VERSION}"
#  	fi
#  export BENCHIT_F77_COMPILER_VERSION
####
  export BENCHIT_COMPILETIME_F77="${BENCHIT_F77}"
fi

if [ "${HLL}" = "F90" ] && [ ${BENCHIT_F90} ] && [ "${BENCHIT_F90}" != "" ] && { "${BENCHITROOT}/tools/features" have ${BENCHIT_F90} ;}
then
#### for compiler version uncomment the following lines
#  	getCompilerVersion ${BENCHIT_F90}
#  	if [ "${?}" -eq 0 ]
#  	then
#  		BENCHIT_F90_COMPILER_VERSION="${BENCHIT_COMPILER_VERSION}"
#  	fi
#  export BENCHIT_F90_COMPILER_VERSION
####
  export BENCHIT_COMPILETIME_F90="${BENCHIT_F90}"
fi

if [ "${HLL}" = "F95" ] && [ ${BENCHIT_F95} ] && [ "${BENCHIT_F95}" != "" ] && { "${BENCHITROOT}/tools/features" have ${BENCHIT_F95} ;}
then
#### for compiler version uncomment the following lines
#  	getCompilerVersion ${BENCHIT_F95}
#  	if [ "${?}" -eq 0 ]
#  	then
#  		BENCHIT_F95_COMPILER_VERSION="${BENCHIT_COMPILER_VERSION}"
#  	fi
#  export BENCHIT_F95_COMPILER_VERSION
####
  export BENCHIT_COMPILETIME_F95="${BENCHIT_F95}"
fi

# Normally this will be set automaticly if necessary
LOCAL_LINKER=""
# Files to be deleted after compile & link
LOCAL_FILES_TO_COPY=""
LOCAL_FILES_TO_DELETE=""

# The compiler configuration for the kernel (the actual worker used by the entry module) Just use this for JAVA
# Valid compiler values are: "C", "CXX", "C++", "MPICC", "MPICXX" , "CUDA", "F77", "F90", "F95", "JAVA", real name (e.g. "gcc") or variable (e.g. "${BENCHIT_F95}")
# Flags XX_C_FLAGS, XX_L_FLAGS, XX_FLAGS_STD/HIGH, INCLUDES, DEFINES are automaticly added if alias is used
# Files need to be seperated by space as needed by compiler

# For java this is usually "*.java"
# If you have an extern kernel or are compiling this yourself, leave it empty
LOCAL_KERNEL_FILES=""
LOCAL_KERNEL_COMPILER=""
LOCAL_KERNEL_COMPILERFLAGS=""

# Linker flags. The kernel compiler is used as the linker!
LOCAL_LINKERFLAGS=""

# The compiler configuration for benchIt and the entry module (the one implementing the benchIt interface)
LOCAL_MODULE_FILES=""
LOCAL_BENCHIT_COMPILER="C"
LOCAL_BENCHIT_COMPILERFLAGS=""

if [ "${HLL}" = "JAVA" ]; then
  USEJAVA=1
	DEST="${BENCHIT_KERNELBINARY}/"
	LOCAL_KERNEL_COMPILER="JAVA"
else
  USEJAVA=0
	DEST="${BENCHITROOT}/bin/"
fi

# Source kernel's COMPILE.SH
# Set the file names and the compiler
# Use a helper variable so the script knows it is executed from this file and not standalone
BENCHIT_COMPILE_SH_IS_CALLED=1
. "${KERNELDIR}/COMPILE.SH"

fix_alias()
{
	case $1 in
   "JAVA") echo "JAVAC" ;;
   "NVCC") echo "CUDA" ;;
   "Java") echo "JAVAC" ;;
   "C") echo "CC" ;;
   "C++") echo "CXX" ;;
   "CPP") echo "CXX" ;;
   *) echo $1 ;;
	esac
}

# Fix aliases
LOCAL_KERNEL_COMPILER=$(fix_alias "$LOCAL_KERNEL_COMPILER")
LOCAL_BENCHIT_COMPILER=$(fix_alias "$LOCAL_BENCHIT_COMPILER")
LOCAL_LINKER=$(fix_alias "$LOCAL_LINKERR")

if [ "${HLL}" = "JAVA" ] && [ "$LOCAL_KERNEL_COMPILER" != "JAVAC" ]; then
	echo "JAVA kernels have to be compiled with JAVA compiler"
	exit 1
fi

if [ "${HLL}" != "JAVA" ] && [ "$LOCAL_KERNEL_COMPILER" = "JAVAC" ]; then
	echo "JAVA compiler detected for a non-JAVA kernel. Please place the kernel according to the specs!"
	exit 1
fi


if [ "${LOCAL_FILES_TO_COPY}" != "" ]; then
	printf "\n##########################\n# GETTING REQUIRED FILES #\n##########################\n"
	set -- junk ${LOCAL_FILES_TO_COPY}
	shift
	FILES_OK=1
	for file; do
		if [ ! -f "${file}" ]; then
			echo "Required file \"${file}\" is missing!"
			FILES_OK=0
		fi
	done
	if [ FILES_OK = 0 ]; then
		exit 1
	fi
	if [ USEJAVA = 1 ]; then
		showAndExecute "cd ${DEST}"
	else
		showAndExecute "cd ${KERNELDIR}"
	fi
	set -- junk ${LOCAL_FILES_TO_COPY}
	shift
	for file; do
		showAndExecute "cp ${file} ./"
	done
fi

cleanup()
{
	printf "\n############\n# CLEAN UP #\n############\n"
	sync
	if [ USEJAVA = 1 ]; then
		showAndExecute "cd ${DEST}"
		showAndExecute "rm -f *.java"
	else
		showAndExecute "cd ${KERNELDIR}"
		# Object files
		showAndExecute "rm -f *.o"
		# Fortran modules
		showAndExecute "rm -f *.mod"
	fi
	if [ "${LOCAL_FILES_TO_DELETE}" != "" ]; then
		showAndExecute "rm -f ${LOCAL_FILES_TO_DELETE}"
	fi
}

cleanupAndExit()
{
	cleanup
	exit $1
}

printf "\n####################\n# CHECKING OPTIONS #\n####################\n"

if [ "${LOCAL_LINKER}" != "" ]; then
	eval tmpLinker=\${BENCHIT_${LOCAL_LINKER}}
	if [ $tmpLinker ]; then
		if [ "$tmpLinker" = "" ]; then
			echo "Linker \"${LOCAL_LINKER}\" not found. Check your LOCALDEF!"
			cleanupAndExit 90
		fi
		LOCAL_LINKER=$tmpLinker
	fi
	checkLinkerAvailability ${LOCAL_LINKER}
fi


# Set up compiler for kernel
if [ "${LOCAL_KERNEL_FILES}" != "" ]; then
	if [ "${LOCAL_KERNEL_COMPILER}" = "" ]; then
		echo "Kernel compiler not specified!"
		cleanupAndExit 91
	else
		eval tmpCompiler=\${BENCHIT_${LOCAL_KERNEL_COMPILER}}
		if [ $tmpCompiler ]; then
			if [ "$tmpCompiler" = "" ]; then
				echo "Kernel compiler \"${LOCAL_KERNEL_COMPILER}\" not found. Check your LOCALDEF!"
				cleanupAndExit 92
			fi
			eval cFlags=\${BENCHIT_${LOCAL_KERNEL_COMPILER}_C_FLAGS}
#			if [ $USEJAVA = 1 ]; then
				eval cFlagsOpt=\${BENCHIT_${LOCAL_KERNEL_COMPILER}_C_FLAGS_HIGH}
#			else
#				eval cFlagsOpt=\${BENCHIT_${LOCAL_KERNEL_COMPILER}_C_FLAGS_STD}
#			fi
			LOCAL_KERNEL_COMPILERFLAGS="${LOCAL_KERNEL_COMPILERFLAGS} ${cFlags} ${cFlagsOpt}"
			eval lFlags=\${BENCHIT_${LOCAL_KERNEL_COMPILER}_L_FLAGS}
			LOCAL_LINKERFLAGS="${LOCAL_LINKERFLAGS} ${lFlags}"
			LOCAL_KERNEL_COMPILER=$tmpCompiler
		fi
		checkCompilerAvailability ${LOCAL_KERNEL_COMPILER}
		if [ "${LOCAL_LINKER}" = "" ]; then
			LOCAL_LINKER=${LOCAL_KERNEL_COMPILER}
		fi
	fi
fi

if [ $USEJAVA = 0 ]; then 
	if [ "${LOCAL_BENCHIT_COMPILER}" = "" ]; then
		echo "Benchit compiler not specified!"
		cleanupAndExit 93
	fi
	if [ "${LOCAL_MODULE_FILES}" = "" ]; then
		echo "Module files not specified!"
		cleanupAndExit 94
	fi
	eval tmpCompiler=\${BENCHIT_${LOCAL_BENCHIT_COMPILER}}
	if [ $tmpCompiler ]; then
		if [ "$tmpCompiler" = "" ]; then
		  echo "Benchit compiler \"${LOCAL_BENCHIT_COMPILER}\" not found. Check your LOCALDEF!"
		  cleanupAndExit 95
		fi
		eval flags=\${BENCHIT_${LOCAL_BENCHIT_COMPILER}_C_FLAGS}
		eval cFlagsOpt=\${BENCHIT_${LOCAL_BENCHIT_COMPILER}_C_FLAGS_HIGH}
		LOCAL_BENCHIT_COMPILERFLAGS="${LOCAL_BENCHIT_COMPILERFLAGS} ${flags} ${cFlagsOpt}"
		if [ "${LOCAL_LINKER}" = "" ]; then
			LOCAL_LINKER=$tmpCompiler
			eval lFlags=\${BENCHIT_${LOCAL_BENCHIT_COMPILER}_L_FLAGS}
			LOCAL_LINKERFLAGS="${LOCAL_LINKERFLAGS} ${lFlags}"
		fi
		LOCAL_BENCHIT_COMPILER=$tmpCompiler
	elif [ "${LOCAL_LINKER}" = "" ]; then
		# Use fallback C linker
		LOCAL_LINKER=${BENCHIT_CC}
		LOCAL_LINKERFLAGS="${LOCAL_LINKERFLAGS} ${BENCHIT_CC_L_FLAGS}"
	fi

	checkCompilerAvailability ${LOCAL_BENCHIT_COMPILER}

	IS_SCRIPT=0
	showAndExecute "cd ${KERNELDIR}"
	# Check if script file is used
	set -- junk ${LOCAL_MODULE_FILES}
	shift
	for file; do
		grep -Fq "bi_script(" ${file}
		if [ $? = 0 ]; then
			IS_SCRIPT=1
		fi
	done

	BENCHIT_FILES="${BENCHITROOT}/benchit.c ${BENCHITROOT}/tools/stringlib.c ${BENCHITROOT}/tools/output.c ${BENCHITROOT}/tools/bitWriter.c ${BENCHITROOT}/tools/gnuWriter.c ${BENCHITROOT}/bienvhash.c"
	if [ $IS_SCRIPT = 1 ]; then
			BENCHIT_FILES="${BENCHIT_FILES} ${BENCHITROOT}/tools/benchscript.c"
			LOCAL_BENCHIT_COMPILERFLAGS="${LOCAL_BENCHIT_COMPILERFLAGS} ${BENCHIT_CPP_PTHREADS}"
			LOCAL_LINKERFLAGS="${LOCAL_LINKERFLAGS} ${BENCHIT_LIB_PTHREAD}"
	elif [ "${LOCAL_KERNEL_FILES}" = "" ]; then
		if [ "${LOCAL_KERNEL_COMPILER}" = "NONE" ]; then
			# No Kernel --> Use parameters of benchit compiler (e.g. used libs)
			LOCAL_KERNEL_COMPILER="${LOCAL_BENCHIT_COMPILER}"
			LOCAL_KERNEL_COMPILERFLAGS="${LOCAL_BENCHIT_COMPILERFLAGS}"
		fi
		echo "Kernel files not specified, assuming you do not have a kernel. Check LOCAL_KERNEL_FILES if this is wrong!"
	fi

	# Set up calls
	BENCHIT_COMPILE="${LOCAL_BENCHIT_COMPILER} ${LOCAL_BENCHIT_COMPILERFLAGS} ${BENCHIT_INCLUDES} ${BENCHIT_DEFINES}"

  KERNEL_COMPILE="${LOCAL_KERNEL_COMPILER} ${LOCAL_KERNEL_COMPILERFLAGS} ${BENCHIT_INCLUDES} ${BENCHIT_DEFINES} -c ${LOCAL_KERNEL_FILES}"
  MODULE_COMPILE="${BENCHIT_COMPILE} -c ${LOCAL_MODULE_FILES}"
	BENCHIT_COMPILE="${BENCHIT_COMPILE} -c ${BENCHIT_FILES}"
  BENCHIT_LINK="${LOCAL_LINKER} -o ${BENCHIT_KERNELBINARY} *.o ${LOCAL_LINKERFLAGS}"
else
	if [ "$BENCHIT_JAVAKERNELCLASS" = "" ] ; then
		BENCHIT_JAVAKERNELCLASS="KernelMain"
		if [ ! -f "${KERNELDIR}/${BENCHIT_JAVAKERNELCLASS}.java" ]; then
      echo "No kernel class set and default class ${BENCHIT_JAVAKERNELCLASS} not found!"
			echo "Use BENCHIT_JAVAKERNELCLASS to set kernel class."
			cleanupAndExit 96
		fi
	fi
	if [ ! -f "${KERNELDIR}/${BENCHIT_JAVAKERNELCLASS}.java" ]; then
      echo "Kernel class ${BENCHIT_JAVAKERNELCLASS} not found!"
			echo "Use BENCHIT_JAVAKERNELCLASS to set kernel class or use the default: KernelMain"
			cleanupAndExit 97
	fi
	if [ "${LOCAL_KERNEL_FILES}" != "*.java" ]; then
		LOCAL_KERNEL_FILES="${LOCAL_KERNEL_FILES} ${BENCHIT_JAVAKERNELCLASS}.java"
  fi

	checkCompilerAvailability ${LOCAL_KERNEL_COMPILER}

	KERNEL_COMPILE="${LOCAL_KERNEL_COMPILER} ${LOCAL_KERNEL_COMPILERFLAGS} *.java"
fi

# Export used compiler config
export LOCAL_KERNEL_COMPILER LOCAL_KERNEL_COMPILERFLAGS

# At this point everything is checked, so proceed with compilation

#
# ENVIRONMENT HASHING - creates BIEnvHash
#
echo "Creating environment hash"
cd "${BENCHITROOT}/tools/"
set > "tmp.env"
./fileversion >> tmp.env
./envhashbuilder

showAndExecute "cd ${KERNELDIR}"
if [ $USEJAVA = 1 ]; then 
	printf "\n###########\n# PREPARE #\n###########\n"
	sync
	if [ ! -d "${DEST}" ]; then
		showAndExecute "mkdir ${DEST}"
	fi

	showAndExecute "rm -f ${DEST}*.class"
	showAndExecute "rm -f ${DEST}*.java"

	showAndExecute "cp -f ${LOCAL_KERNEL_FILES} ${DEST}"
	showAndExecute "cp -f ${BENCHITROOT}/jbi/*.java ${DEST}"
# Build Run.SH
	RUN_FILE="${DEST}/RUN.SH"
	if [ -f ${RUN_FILE} ]; then
		rm $RUN_FILE
	fi
  echo 'if [ -z "${BENCHITROOT}" ]; then' >> ${RUN_FILE}
  echo '   # running stand-alone' >> ${RUN_FILE}
  echo '   java JBI $@' >> ${RUN_FILE}
  echo 'else' >> ${RUN_FILE}
  echo '   "${JVM}" JBI $@' >> ${RUN_FILE}
  echo 'fi' >> ${RUN_FILE}
  chmod +x "${RUN_FILE}"

	showAndExecute "cd ${DEST}"
  
	printf "\n###########\n# COMPILE #\n###########\n"
	sync
  showAndExecute "${KERNEL_COMPILE}"
	if [ $? -ne 0 ]; then
    cleanupAndExit 80
  fi
else
	printf "\n###########\n# COMPILE #\n###########\n"
	sync
	if [ "${LOCAL_KERNEL_FILES}" != "" ]; then
  	showAndExecute "${KERNEL_COMPILE}"
	  if [ $? -ne 0 ]; then
      cleanupAndExit 81
    fi
	fi
  showAndExecute "${MODULE_COMPILE}"
	if [ $? -ne 0 ]; then
    cleanupAndExit 82
  fi
  showAndExecute "${BENCHIT_COMPILE}"
	if [ $? -ne 0 ]; then
    cleanupAndExit 83
  fi
	printf "\n########\n# LINK #\n########\n"
	sync
  showAndExecute "${BENCHIT_LINK}"
	if [ $? -ne 0 ]; then
    cleanupAndExit 84
  fi
fi
cleanup
# CHANGE TO THE MAIN DIRECTORY
showAndExecute "cd ${BENCHITROOT}"
