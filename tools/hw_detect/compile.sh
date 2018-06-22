#DEFINES="-DARMv7"
gcc -o glibc_version glibc_version.c
GLIBC_VERSION=`./glibc_version`
if [ "${GLIBC_VERSION}" != "not found" ]; then
 echo "         checking for glibc version:        found version ${GLIBC_VERSION}"
 if [ "`./glibc_version 2.3.4`" = "ok" ] && [ -r "/usr/include/sched.h" ];then 
   DEFINES="${DEFINES} -DAFFINITY"
   echo "         checking for sched_setaffinity:    ok"
 else
   echo "         checking for sched_setaffinity:    failed"
 fi
 if [ "`./glibc_version 2.6`" = "ok" ] && [ -r "/usr/include/utmpx.h" ];then 
   DEFINES="${DEFINES} -DSCHED_GETCPU"
   echo "         checking for sched_getcpu():       ok"
 else
   echo "         checking for sched_getcpu():       failed"
 fi
else
 echo "         checking for glibc version:        not found"
 echo "         checking for sched_setaffinity:    failed"
 echo "         checking for sched_getcpu():       failed"
fi
rm ./glibc_version

echo '#include "properties.h"' > properties.c
echo 'const info_t cpu_data[CPU_DATA_COUNT] = {' >> properties.c
cat properties.list | awk -v FS="\t*"  '$1 !~ /^#/ {if($5 == "n/a") NODE=-1; else NODE=$5; print "{\""$1".*\", "$2", "$3", \""$4"\", "NODE"},";}' >> properties.c
echo '};' >> properties.c

CPU_DATA_COUNT=`cat properties.c | wc -l`
CPU_DATA_COUNT=$((CPU_DATA_COUNT - 3)) # number of array elements

echo 'const archshrt_t archshrt_data[ARCH_SHORT_COUNT] = {' >> properties.c
cat arch_short.list | awk -v FS="\t*"  '$1 !~ /^#/ {print "{\""$1"\", "$2", \""$3"\"},";}' >> properties.c
echo '};' >> properties.c

ARCH_SHORT_COUNT=`cat properties.c | wc -l`
ARCH_SHORT_COUNT=$((ARCH_SHORT_COUNT - CPU_DATA_COUNT - 5))

cat properties.h.template | sed 's!\(#define CPU_DATA_COUNT \)[0-9]*!\1'$CPU_DATA_COUNT'!' | sed 's!\(#define ARCH_SHORT_COUNT \)[0-9]*!\1'$ARCH_SHORT_COUNT'!' > properties.h

gcc -o cpuinfo ${DEFINES} -Wall architecture.c properties.c x86.c generic.c -lm

#gcc -o cpuinfo ${DEFINES} -Wall architecture.c properties.c arm.c generic.c -lm
