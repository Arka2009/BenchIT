#!/bin/sh
#####################################################################
# BenchIT - Performance Measurement for Scientific Applications
# Contact: developer@benchit.org
#
# $Id: ITANIUM 1 2009-09-11 12:26:19Z william $
# $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/tools/environments/ITANIUM $
# For license details see COPYING in the package base directory
#####################################################################

########################################################################
# FIRST PART: ASSEMBLE COMMAND
########################################################################

execute_cmd="${BENCHIT_KERNELBINARY} ${BENCHIT_KERNELBINARY_ARGS}"

if [ "${BENCHIT_RUN_USE_MPI}" = "1" ]; then
	execute_cmd="mpirun -np ${BENCHIT_NUM_PROCESSES} ${execute_cmd}"
fi

########################################################################
# SECOND PART: SAVE ENVIRONMENT IF NECESSARY
########################################################################

env | grep BENCHIT | sed -e 's/^\([^=]*\)=\(.*\)$/export \1=\"\2\"/g'> ${BENCHITROOT}/${BENCHIT_KERNELNAME}_env

########################################################################
# THIRD PART: EXECUTE AND CLEANUP
########################################################################

batch_cmd="qsub"
#### usage
# qsub [-a date_time] [-A account_string] [-c { c[=<INTERVAL>] | s | n }]
# [-C directive_prefix] [-d path] --D path] [-e path] [-h] [-I] [-j oe] [-k {oe}]
# [-l resource_list] [-m {abe}] [-M user_list] [-N jobname] [-o path]
# [-p priority] [-q queue] [-r y|n] [-S path] [-u user_list]
# [-W otherattributes=value...] [-v variable_list] [-V ] [-z] [script]

script="${BENCHITROOT}/temp_script_file_${BENCHIT_KERNELNAME}"
# Remove old script if one exists
rm -f ${script}

# Assemble script for submission to the batch system
echo "#!/bin/sh" >> ${script}
echo "#PBS -m e" >> ${script}
echo "#PBS -l ncpus=${BENCHIT_NUM_CPUS}" >> ${script}

if [ -n "${BENCHIT_RUN_QUEUETIMELIMIT}" ]; then
	qtimelimit=$((${BENCHIT_RUN_QUEUETIMELIMIT}))
else
	# Extend BenchIT timelimit by 10% for queueing
	qtimelimit=$((${BENCHIT_RUN_TIMELIMIT} * 11 / 10))
fi
echo "#PBS -l walltime=${qtimelimit}" >> ${script}

if [ -n "${BENCHIT_RUN_MAX_MEMORY}" ]; then
	echo "#PBS -l mem=${BENCHIT_RUN_MAX_MEMORY}" >> ${script}
fi

if [ -n "${BENCHIT_RUN_REDIRECT_CONSOLE}" ]; then
	echo "#PBS -o ${BENCHIT_RUN_REDIRECT_CONSOLE}" >> ${script}
fi

#echo "#PBS -M email" >> ${script}
echo "#PBS -d ${BENCHITROOT}" >> ${script}
echo "#PBS -j oe" >> ${script}
echo "#PBS -q extralongq" >> ${script}
if [ -n "${BENCHIT_RUN_COREDUMPLIMIT}" ]; then
	batch_cmd="${batch_cmd} -C ${BENCHIT_RUN_COREDUMPLIMIT}"
	echo "limit coredumpsize ${BENCHIT_RUN_COREDUMPLIMIT}" >> ${script}
else
	echo "limit coredumpsize 0" >> ${script}
fi

echo "cd ${BENCHITROOT}" >> ${script}
echo ". ./${BENCHIT_KERNELNAME}_env" >> ${script}
echo "${execute_cmd}" >> ${script}

if [ "${BENCHIT_RUN_CLEAN}" = "1" ]; then
	echo "rm -f ${BENCHIT_KERNELBINARY}" >> ${script}
	echo "rm ${script}" >> ${script}
fi

chmod +x ${script}

# Submit job to the batch system
batch_cmd="${batch_cmd} ${script}"
if [ "$BENCHIT_RUN_TEST" != "1" ]; then
	${batch_cmd}
else
	echo ${batch_cmd}
	echo "---------------------------------------------------------"
	echo "cat ITANIUM temporary script:"
	cat ${script}
	echo "---------------------------------------------------------"
fi

