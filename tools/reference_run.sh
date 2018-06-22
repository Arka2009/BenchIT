#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: reference_run.sh 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/tools/reference_run.sh $
# For license details see COPYING in the package base directory
#####################################################################
# Script which performs a so called BenchIT Reference Run.
#
# All kernels in kernel/_reference_ will be compiled and
# executed.
# You should have edited the c compiler part in your LOCALDEF
# in a proper way before this.
# Best run in runlevel 1 ( init 1 ).
#####################################################################

### variables and helpers

# change to BenchIT folder 
cd `dirname $0`
cd ..

BITPATH=`pwd`				# path to BenchIT root
REFPATH=${BITPATH}/kernel/_reference_	# path to reference kernels
BINPATH=${BITPATH}/bin			# path to kernel binaries
LOG=${BITPATH}/REFRUN.log		# file for logging this run
TMP=${BITPATH}/garbage.tmp		# temporary file needed for resume

RUNLEVEL=`who -r | tr -s " " | cut -f3 -d " "`	# current runlevel
TIMECMD=`which time`				# check if time command is available
ERRORS=0					# variable for errors

# publishing signal handler
trap 'handle_SIGINT' 2


### function declaration

# what to do if user interrupts?:
handle_SIGINT ()
{
	echo -e "\n\033[1;31m...caught SIGINT: exiting!\033[0m"
	rm -f ${TMP}
	exit 1
}


# this function will be run if no arguments are given
# TODO: maybe add some error handling
normal_run ()
{
	prepare		# clean up, etc.
	compile		# compile all reference kernels
	run		# run all compiled kernels
	epilog		# write final status data
	
	exit 0
}


# This function will be executed by the -r argument.
# It tries to find out where was interrupted last time and resumes if possible.
# recompiles all if there were compile errors before
resume ()
{
	runlevel_check

	echo -e "\033[1;34m try to resume last reference run... \033[0m"

	cat ${LOG} | grep "#####" | tr -d "#" | tr -d " " > ${TMP}
	if [ `wc -l ${TMP} | cut -f1 -d " "` -lt 1 ]; then
		echo -e "\033[1;34m ...seems like there were no kernels run before"
		echo -e "---recompiling all in 3 sec.\033[0m"
		sleep 3
		normal_run
		exit 0
	fi

	LAST=`tail -n 1 ${TMP}`
	echo -e "\033[1;34mIt seems ${LAST} was the interrupted kernel\033[0m"

	# deleting correct proceeded kernels
	echo -e "\033[1;34m...deleting correct proceeded kernels\033[0m"
	sleep 2
	LINES=`cat ${TMP} | wc -l`
	LINES=`echo "${LINES} - 1" | bc`
	
	for i in `cat ${TMP}`; do
		LINES=`echo "${LINES} - 1" | bc`
		if [ ${LINES} -eq 0  ]; then
			break
		fi

		echo -e "\033[1;34m...removeing\033[0m ${BINPATH}/$i"
		rm -f "${BINPATH}/$i"
	done

	echo "...resuming" >> ${LOG}
	run
	epilog

	exit 0
}


# The printout when -h or a wrong parameter is given.
print_help ()
{
	echo "Script which performs a so called BenchIT Reference Run."
	echo " "
	echo "usage: $0 [[-r] [-h]]"
	echo " "
	echo "no option: start a fresh reference run"
	echo "-r: try to resume a previouse interrupted session. ${LOG} is needed!"
	echo "-h: print help"
	exit 0
}


# checks the current runlevel and gives possibility to cancel
runlevel_check ()
{
	if [ "${RUNLEVEL}" != "1" ] && [ "${RUNLEVEL}" != "S" ] && [ "${RUNLEVEL}" != "s" ]; then
		echo -e "\033[1;31mAll benchmarks should be run in runlevel 1, S or s!"
		echo -e "Your current runlevel is:\033[0m ${RUNLEVEL}"
		echo -e "I recommend to stop here and switch manually with command\033[1m init 1\033[0m\n"
		echo "Proceed anyway? (y/n): "
		read ANSWER
		while [ "${ANSWER}" != "y" ] && [ "${ANSWER}" != "n" ]; do
			echo -e "\033[1;31mI didn't understand you.\033[0m"
			echo "Proceed anyway? (y/n): "
			read ANSWER
		done

		if [ "${ANSWER}" = "n" ]; then
			echo "... exiting"
			exit 0
		fi
		
	fi

	return 0
}



# STAGE 0: preparing
# normally not run stand alone
prepare ()
{
	rm -f ${LOG}
	echo -e "\033[1;32mSTAGE 0: preparing...\033[0m"

	runlevel_check

	rm -rf ${BINPATH}/_reference_*		# necessary cleanup

	echo "### BenchIT Reference Run ###" > ${LOG}
	echo "Date: `date`" >> ${LOG}
	echo "-----------------------------" >> ${LOG}

	return 0
}


# STAGE 1: compling
# normally not run stand alone
compile ()
{
	echo -e "\033[1;32mSTAGE 1: compiling...\033[0m"
	echo "Compiler warnings/errors per kernel" >> ${LOG}

	for i in `find ${REFPATH} -name PARAMETERS`; do
		echo `dirname $i` >> ${LOG}
		rm -f ${TMP}
		./COMPILE.SH `dirname $i` 2> ${TMP}
		if [ ! $? -eq 0 ] || [ -s ${TMP} ]; then
			echo -e "\033[1;31mErrors appeared during compilation of `dirname $i`!"
			echo -e "See\033[0m ${LOG} \033[1;31mfor further information\n"
			cat ${TMP} >> ${LOG}
			echo "...exiting"
			exit 1
		fi
	done

	return 0
}


# STAGE 2: running
# normally not run stand alone
run ()
{
	echo -e "\033[1;32mSTAGE 2: running...\033[0m"
	echo "Status information to kernel runs:" >> ${LOG}
	
	#   create run command
	if [ -z ${TIMECMD} ]; then
		RUNCMD=./RUN.SH
	else
		RUNCMD="${TIMECMD} -a -o ${LOG} -f \"Command: %C\nElapsed wall clock time: %E s\nCPU time in kernel mode:\t%S s\nCPU time in user mode:\t%U s\nCPU time in percent: %P\nData usage: %D Kb\nAvg. total memory: %K Kb\nMax used memory: %M Kb\nStack size (Kb): %p\nPage faults (real): %F\nPage faults (without I/O): %R\nFS inputs: %I\nFS outputs: %O\nSwaped: %W times\nContext switches: %c\nContext switches (voluntary): %w\nSignals received: %k\nSocket msg received: %r\nSocket msg send: %s\nExited with: %x\" ./RUN.SH"

	fi

	#   main run loop
	for i in `ls ${BINPATH} | grep _reference_`; do
		echo "##### $i #####" >> ${LOG}
		eval "${RUNCMD} ${BINPATH}/$i"
		if [ ! $? -eq 0 ]; then
			echo -e "\033[1;31mErrors appeared during execution of $i!"
			echo -e "See\033[0m ${LOG} \033[1;31mfor further information"
			echo " "
			echo "...exiting"
			exit 1
		fi
	done

	return 0
}



# STAGE 3: epilog
# normally not run stand alone
epilog ()
{
	echo -e "\033[1;32mSTAGE 3: epilog...\033[0m"
	echo "Reference Run ended `date`" >> ${LOG}

	echo "There were ${ERRORS} errors or warnings during reference run!" >> ${LOG}
	if [ ${ERRORS} -gt 0 ]; then
		echo -e "\033[1;31mThere were ${ERRORS} during reference run!"
		echo -e "Please check ${LOG} for further information.\033[0m"
	fi

	# short cleanup
	rm -f ${TMP}

	return 0
}


##############################################################################
### main part

# proceeding arguments:
while getopts rh OPT ; do
        case ${OPT} in
          r) resume ;;
	  h) print_help ;;
          *) print_help ;;
        esac
done


# no arguments given?:
# start normal run
normal_run


exit 0

