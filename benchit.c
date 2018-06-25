/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: benchit.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://william@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/benchit.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* Main program of the BenchIT-project
 *******************************************************************/

#ifdef USE_MPI
#include <mpi.h>
#endif

#ifdef __cplusplus
extern "C" {
#endif

#include <stdio.h>
#include <errno.h>

/* This is for `size_t'. */
#include <stddef.h>

/* This is for different calculations. E.g for logarithmic axis */
#include <math.h>

/* This is for a lot of String work concat and so on... */
#include <string.h>

/* used for typeconversion e.g. atoi string to integer */
#include <stdlib.h>

/* main posix header */
#include <unistd.h>

/* This is for catching SIG_INT and SIG_TERM*/
#include <signal.h>

#include <ctype.h>
#include <math.h>

/* if this is compiled for a MPI-kernel,
 * somewhere you got to set -DUSE_MPI as compiler flag
 * to include mpi-header
 */

/* if this is compiled for a OpenMP-kernel,
 * somewhere you got to set -DUSE_OMP as compiler flag
 * to include OpenMP-header
 */
#ifdef USE_OMP
#include <omp.h>
#endif

/* if PAPI should be used,
 * somewhere you got to set -DUSE_PAPI as compiler flag
 */
#ifdef USE_PAPI
#include <papi.h>
#endif

/* used for timers */
#include <time.h>
#include <sys/time.h>
#include <sys/stat.h>
#include <sys/types.h>

/* used for BenchIT */
#include "interface.h"

#include "tools/bienvhash.h"
#include "tools/stringlib.h"
#include "tools/output.h"
#include "tools/bitWriter.h"

/* used for BenchIT version number (year) */
#ifndef BENCHIT_MAJOR
#define BENCHIT_MAJOR 2013 /**< Major version number used by fileinfo.c */
#endif

/* used for BenchIT version number (month) */
#ifndef BENCHIT_MINOR
#define BENCHIT_MINOR 00 /**< Minor version number used by fileinfo.c */
#endif

/* used for BenchIT version number (day) */
#ifndef BENCHIT_SUBMINOR
#define BENCHIT_SUBMINOR 00 /**< Subminor version number used by fileinfo.c */
#endif

/* Every kernel on every problemsize will be run (Accuracy+1) times */
#undef DEFAULT_ACCURACY
#define DEFAULT_ACCURACY 2 /**< If the LOCALDEF does not define an accuracy number -
                2 will be used which will result in 2 repetitions
                of each measurementstep */

/* the time-limit in seconds. when more time has passed, the measurement is interrupted */
#undef DEFAULT_TIMELIMIT
#define DEFAULT_TIMELIMIT 600  /**< Number of seconds after which a measurment is stoped
                  (should be set in PARAMETERS) */

/*name of the file where progress information is stored to*/
static char* progf = NULL;
/*file descriptor to the file where progress information is stored to */
static FILE* prog_file = NULL;

/*
 * boolean for standalone-applictation
 */
int bi_standalone = 0; /**< is this a standalone binary to be used without benchit-environment*/

/* For more detailed output of what's going on. */
int verbose = 0; /**< be more communicative */

static double bi_gettimeofday(void);
static double bi_gettimeofday_improved(void);
double (*bi_gettime)() = bi_gettimeofday_improved;

double dTimerGranularity;
double dTimerOverhead;
double dStartTimerOverhead;
double d_bi_start_sec; /**< start time */
double biStartTime;

// Times relative to programm start (improved precision)
double biStartTimeAbs;
double biStopTimeAbs;

static void safe_exit(int code);
static void selectTimer(void);

static void createDirStructureOrExit(const char *dirstr) {
	int err = createDirStructure(dirstr);
	if (err != 0)
		safe_exit(err);
}

void allocYAxis(bi_info *theInfo) {
	theInfo->yaxistexts = (char**) calloc((size_t)theInfo->numfunctions, sizeof(char*));
	if (theInfo->yaxistexts == 0) {
		fprintf(stderr, "Allocation of yaxistexts failed.\n");
		fflush(stderr);
		exit(127);
	}
	theInfo->selected_result = (int*) calloc((size_t)theInfo->numfunctions, sizeof(int));
	if (theInfo->selected_result == 0) {
		fprintf(stderr, "Allocation of outlier direction failed.\n");
		fflush(stderr);
		exit(127);
	}
	theInfo->legendtexts = (char**) calloc((size_t)theInfo->numfunctions, sizeof(char*));
	if (theInfo->legendtexts == 0) {
		fprintf(stderr, "Allocation of legendtexts failed.\n");
		fflush(stderr);
		exit(127);
	}
	theInfo->base_yaxis = (int*) calloc((size_t)theInfo->numfunctions, sizeof(int));
	if (theInfo->base_yaxis == 0) {
		fprintf(stderr, "Allocation of base yaxis failed.\n");
		fflush(stderr);
		exit(127);
	}
}

/*!@brief Print list and explanation of command line args on stdout
 *        and exit the program.
 */
static void printHelpAndExit() {
	printf("Usage: <executable> [option]...\n\n");
	printf("Where option can be:\n");
	printf(" -h, --help\t\t\t");
	printf("show this help screen\n");
	printf(" -d, --dumpTable\t\t");
	printf("print the environment variables stored in the internal"
			"\n\t\t\t\tHashTable to stdout\n");
	printf(" -o, --output-dir=DIR\t\t");
	printf("write result files into DIR (requires absolute path)\n");
	printf(" -S, --standalone\t\t");
	printf("don't read _input_*\n");
	printf(" -p, --parameter-file=PAR_FILE\t");
	printf("read parameters from PAR_FILE at runtime\n");
	printf(" -q, --quiet\t\t\t");
	printf("suppress all messages to stdout and stderr\n");
	printf(" -v, --verbose\t\t\t");
	printf("print more messages about what the program is doing\n");
	printf(" -V, --version\t\t\t");
	printf("print version information\n");

	fflush(stdout);
	safe_exit(0);
}

/*!@brief Extract values for recognized options.
 *
 * Checks if at position pos in argv is an option in whether
 * short or long version. If hasValue is greater than 0 the
 * pointer value will be set to the start of the value string
 * and the varibale pos will be increased.
 * If argv[i] is a short option the value is expected in argv[i+1].
 * If argv[i] is a long option, the value is that part of argv[i]
 * that follows the first occuring = sign.
 * @param[in] argv the argv array.
 * @param[in] pos the postion in argv to look at.
 * @param[in] argc the number of elements in argv.
 * @param[in] sOpt the short version of the option.
 * @param[in] lOpt the long version of the option.
 * @param[in] hasValue 0 if option without value, 1 or greater if with value.
 * @param[in,out] value pointer to the value char array.
 * @return 1 if successful match and retrieval of value, 0 else.
 */
static int isOption(char** argv, int *pos, int argc, char sOpt, const char *lOpt, int hasValue, char **value) {
	/*
	 retval is the return value for this function
	 len is the length of the poss entry in argv.
	 */
	int retval = 0, len = -1;
	/* reset value */
	*value = 0;
	/* if there is no argument number pos return 0 */
	if (argv[*pos] == 0)
		return retval;
	/* else get the length of the argument */
	len = lengthc(argv[*pos]) + 1;
	/* if the pos' arguments first char is not a '-' return 0 */
	if (argv[*pos][0] != '-')
		return retval;
	/* now try to match option
	 * ! short Options MUST have length 2 ('-' plus a single character)
	 */
	if (len == 2) {
		/* short option */
		/* if there was some strange stuff used as short Option return 0 */
		if (sOpt == 0)
			return retval;
		/* if there is no Value needed for this option, but a value is passed return 0 */
		if (hasValue > 0 && *pos + 1 >= argc)
			return retval;
		/* if it is found */
		if (argv[*pos][1] == sOpt) {
			/* short option hit */
			/* if it needs a value, set it */
			if (hasValue == 1)
				*value = argv[++*pos];
			/* but always return 1 */
			retval = 1;
		}
		/* if it is not found return 0 */
		else
			return retval;
	}
	/*
	 * ! long options MUST have length >2 (- plus at least 2 chars)
	 */
	else if (len > 2 && lOpt != 0) {
		char * lOptNonConst = strdup(lOpt);
		/* long option */
		/* STR_LEN is passed from a header (string.h?) */
		char sub[STR_LEN];
		/* position */
		int eqPos = -1;
		/* fill the string sub with 0s (NOT with '0's) */
		memset(sub, 0, STR_LEN);
		/* if there is no lOpt passed */
		if (lOpt == 0)
			return retval;
		/* if the argument doesn't start with a dash '-' */
		if (argv[*pos][1] != '-')
			return retval;
		/* if it needs a value, they must be separated by a = : -option=value */
		/* always point separation between arguments: */
		if (hasValue == 1) {
			eqPos = indexOf(argv[*pos], '=', 1);
		} else {
			eqPos = len + 1;
		}
		/* if it is too short (only a single char) return 0 */
		if (eqPos < 3)
			return retval;
		/* extract option name */
		/* if the option name cannot be found in the option
		 * (sub=argv[*pos].substring(2,eqPos))
		 * subString sub is a substring of argv[*pos] beginning with the 2nd char to the eqPos' char
		 * if the creation of this substring fails retun 0 */
		if (substring(argv[*pos], sub, 2, eqPos) != 1)
			return retval;
		/* if the subString is to short return false */
		if (strlen(sub) == 0)
			return retval;
		/* compare the strings 0 means no differences */

		if (comparec(sub, lOptNonConst) == 0) {
			/* long option hit */
			/* if it needs a value (-option=value), set it */
			if (hasValue == 1)
				*value = &argv[*pos][eqPos + 1];
			/* but always return 0 */
			retval = 1;
		}
		freeCheckedC(&lOptNonConst);
	}
	/* if nothing is found return 0; */
	else
		return retval;
	return retval;
}

/*!@brief Parse commandline arguments.
 *
 * Checks the arguments for recognizable input. Does not use
 * getopt for compatibility reasons. See documentation of
 * printUsage() for detailed info about recognized options.
 * @param argc argc from main()
 * @param argv argv from main()
 */
static void checkCommandLine(int argc, char **argv) {
	/* for incrementing over arguments */
	int i;
	/* increment over arguments:
	 * (all possible arguments should be checked here)
	 * check: is this an available option? */
	for (i = 1; i < argc; i++) {
		/* value of the option (if it needs one) */
		char *value = 0;
		/* shall the help be printed? */
		if (isOption(argv, &i, argc, 'h', "help", 0, &value) == 1) {
			printHelpAndExit();
			continue;
		}
		/* shall the environment be dumped? */
		if (isOption(argv, &i, argc, 'd', "dumpTable", 0, &value) == 1) {
			bi_dumpTable();
			fflush(stdout);
			safe_exit(0);
			continue;
		}
		/* shall the output-dir be setted? */
		if (isOption(argv, &i, argc, 'o', "output-dir", 1, &value) == 1) {
			bi_put(bi_strdup("BENCHIT_RUN_OUTPUT_DIR"), value);
			continue;
		}
		/* shall another parameter file be used? */
		if (isOption(argv, &i, argc, 'p', "parameter-file", 1, &value) == 1) {
			bi_put(bi_strdup("BENCHIT_PARAMETER_FILE"), value);
			bi_readParameterFile(value);
			continue;
		}
		/* shall there be no printing? */
		if (isOption(argv, &i, argc, 'q', "quiet", 0, &value) == 1) {
			if (freopen("/dev/null", "w", stdout) == NULL ) {
				printf("BenchIT: Error: could not remap stdout to /dev/null.\n");
				fflush(stdout);
				safe_exit(1);
			}
			if (freopen("/dev/null", "w", stderr) == NULL ) {
				printf("BenchIT: Error: could not remap stderr to /dev/null.\n");
				fflush(stdout);
				safe_exit(1);
			}
			continue;
		}
		/* shall we use verbose mode? */
		if (isOption(argv, &i, argc, 'v', "verbose", 0, &value) == 1) {
			verbose = 1;
			continue;
		}
		/* or print the version? */
		if (isOption(argv, &i, argc, 'V', "version", 0, &value) == 1) {
			printf("BenchIT version %d.%d.%d\n", BENCHIT_MAJOR, BENCHIT_MINOR, BENCHIT_SUBMINOR);
			fflush(stdout);
			safe_exit(0);
		}
		/* or shall we run this as standalone? */
		if (isOption(argv, &i, argc, 'S', "standalone", 0, &value) == 1) {
			bi_standalone = 1;
			if (isOption(argv, &i, argc, 'o', "output-dir", 1, &value) == 0) {
				value = (char*) malloc(300 * sizeof(char));
				if (getcwd(value, 290) == NULL ) {
					printf(" [FAILED]\nBenchIT: Couldn't create output directory: ./output.\n");
					safe_exit(127);
				}
				if (value[strlen(value) - 1] == '/')
					strcat(value, "output");
				else
					strcat(value, "/output");
				bi_put(bi_strdup("BENCHIT_RUN_OUTPUT_DIR"), value);
				freeCheckedC(&value);
			}
			continue;
		}
		/* if this point of the loop is reached, the argument
		 is not a recognized option */
		printf("BenchIT: Unknown argument: %s\n", argv[i]);
		safe_exit(1);
	}
}

/*!@brief Safely exit BenchIT.
 *
 * Cleans up MPI, Vampir and progress file before exit is called.
 * COMMENTS: set -DVAMPIR_TRACE while compiling to clean vampir-trace to!
 * @param code The exitcode to use with exit().
 */
static void safe_exit(int code) {
#ifdef USE_MPI
	if (code == 0)
	MPI_Finalize();
	else
	MPI_Abort(MPI_COMM_WORLD, code);
#endif
#ifdef VAMPIR_TRACE
	(void) _vptleave(300);
	(void) _vptflush();
#endif

	if (prog_file != NULL ) {
		fclose(prog_file);
		unlink(progf);
	}

	exit(code);
}

/*!@brief Generate a new todoList with problemsizes for computation by the
 *        kernel.
 *
 * PRE: in the first call todo and done are arrays with all values=0
 * max = maximumproblemsize = length of the arrays
 * todo[0] and done[0] remain unchanged by the calling party
 * done[i] indicates, that the problemsize i has already been calculated
 * POST:
 * Short: todo is a new array of problemsizes to be calculated
 * the array is terminated with a 0
 * Long:
 *    after calling this function todo[i] (i!=0) will contain the problemsize(s),
 *    which shall be computed in the next step(s). It is NOT said how many todo-problemsizes are returned!
 *    todos after the last valid todo[i] will contain a problemsize of 0
 * functions returns true if new problems could be generated, false if not
 * COMMENTS: todo[0] is used to store the number of calls of the function get_new_problems
 * done[0] iw used to store whether we are done or not, done[0]=1 means, that get_new_problems
 * will return true with the next call
 * @return 1 if new todoList could be generated\n
 *         0 if there are no problemsizes left.
 */
static int get_new_problems(int *todo, int *done, int max) {
	/* todo[0] contains the number of calls of this function. */
	/* heres another call, so increment it */
	/* though we are filling first the middle problemsize, then the ones at quarters */
	/* and so on, we check for the half/quarter/eighth, which is computed by max/(2^num_ofCall) */
	int stepsize = (int) (max / (int) pow(2, (++todo[0])));
	/* those are used for for loops, explained later */
	int i = 0, k = 1, inc = 0;
	/* when in the last call of this function done[0] was NOT set, there is still sth. to do */
	int ret = !done[0];
	/* but if it was set in the last call, we're done */
	if (ret == 0)
		return ret;
	IDL(1, printf("Entering get_new_problems for %d. time\n", todo[0]));
	/* if the difference is small enough (dont compute for 1/(2^1024)-parts) */
	/* go to linear stepping */
	if (stepsize < (0.05 * max))
		stepsize = 1;
	/* if linear measurement is used, do linear stepping too :P */
#ifdef LINEAR_MEASUREMENT
	stepsize = 1;
#endif
	/* if we take every following problemsize... */
	if (stepsize == 1)
		/* ... we should also set inc(rement) to 1, to reach all problemsizes */
		inc = 1;
	/* if we are still in the pattern which computes first the half problemsize, then the quarter and three-quarter, ...   */
	else
		/* if e.g. it is the 2nd call of the function, the middle problemsize has been solved. */
		/* BUT now we have to solve those at the quarter and three-quarter */
		/* so stepsize is (1/4)*problemsizemax, but inc is (1/2)*problemsizemax */
		/* to reach (1/4)*problemsizemax AND (3/4)*problemsizemax :) */
		inc = 2 * stepsize;
	/* now compute the problemsizes, which shall be generated */
	/* the first will be k[1], the 2nd k[2] and so on */
	for (i = stepsize; i <= max; i += inc) {
		if (done[i] != 1)
			todo[k++] = i;
	}
	/* the first item after all todo-problemsizes is set to 0 */
	/* maybe in the last step we had to compute more then in this step */
	todo[k] = 0;
	/* if stepsize is 1, means, that all remaining problemsizes were written */
	/* into the todo field */
	if (stepsize == 1)
		done[0] = 1;
	/* if we have a larger stepsize: don't do the measurement for largest problemsize */
	/* this time */
	else if (todo[k - 1] == max)
		todo[k - 1] = 0; /*remove max from todo unless stepsize=1*/
	IDL(2, printf("todoList="));
	for (i = 1; i <= max; i++)
		IDL(2, printf(" %d", todo[i]));
	IDL(2, printf("\n"));
	IDL(1, printf("Leaving get_new_problems.\n"));
	return ret;
}

/**
 * variables used by main(), analyse_results() and write_results()
 * defined static to not be visible in other source-files (avoid multiple declarations)
 */
/*
 *
 */
static void *mcb;
/*
 * variables:
 * rank: used for MPI, will be the rank of the MPI-process or 0 if no MPI is used
 * offset: how many functions are measured by bi_entry
 * timelimit: timelimit for running the benchmark, if exceeding this limit, it will be stopped
 * accuracy: how often every kernel is measured
 * dataPointCt: number of data points per function including x value(=numMeasurements*(accuracy+1)+1)
 */
static int rank, offset = 0, curTodoIndex = 1, w = 1, flag = 0, i, j, n = 0, timelimit, accuracy, dataPointCt, numDataPointsPerX;
/*
 * info about the kernel, will be filled by kernel
 */
static bi_info theInfo;
/*
 * will contain all results of all bi_entry_call
 * x|func1_1|func1_2...func1_n|func2_1|func2_2... with n=accuracy+1
 */
static double *allResults = NULL;

static void cleanUp(int err){
	bi_cleanup(mcb);
	freeCheckedD(&allResults);
	safe_exit(err);
}

/**
 * Finishes Benchit: Write results (checked), bi_cleanup kernel, free allResults,
 */
static void finish(int err){
	if(rank==0){
		write_results(theInfo, allResults, accuracy + 1, bi_standalone);
		printf("BenchIT: Finishing...\n");
		fflush(stdout);
	}
	cleanUp(err);
}

/**
 * Signal handler for SIGINT
 */
static void sigint_handler(int signum) {
	char c = '\0', *p = NULL;
	int interactive = 0, exitcode = 0;

	/* ignore further signals while handling */
	signal(signum, SIG_IGN );

	if (rank == 0) {
		p = bi_getenv("BENCHIT_INTERACTIVE", 0);
		interactive = atoi(p);
		if (interactive) {
			printf("\nBenchIT: Received SIGINT (Ctrl-C). Do you really want to quit? [y/n]: ");
			fflush(stdout);
			c = (char) fgetc(stdin);
			fflush(stdin);
		} else {
			printf("\nBenchIT: Received SIGINT (Ctrl-C).\n");
			c = 'y';
			exitcode = 1;
		}
	}
#ifdef USE_MPI
	MPI_Bcast(&c, 1, MPI_CHAR, 0,MPI_COMM_WORLD);
#endif
	if (c == 'y' || c == 'Y') {
		if (rank == 0) {
			printf("BenchIT: Aborting...\n");
			fflush(stdout);
		}
		finish(exitcode);
	} else {
		/* read remaining input */
		if (rank == 0)
			while (fgetc(stdin) != '\n')
				;
		/* reinstall handler */
		signal(SIGINT, sigint_handler);
	}
}

/**
 * Signal handler for SIGTERM,
 */
static void sigterm_handler(int signum) {
	/* ignore further signals as we are going to quit anyway */
	signal(signum, SIG_IGN );
	if (rank == 0) {
		fflush(stdout);
		printf("\nBenchIT: Received SIGTERM, Aborting...\n");
		fflush(stdout);
	}
	finish(1);
}

/**
 * Abort function that should be used by the kernels instead of doing an exit(err)
 */
void bi_abort(int err) {
	if (rank == 0) {
		fflush(stdout);
		printf("\nBenchIT: Received Abort, Aborting...\n");
		fflush(stdout);
	}
	finish(err);
}

/*!@brief Monstrous main function doing everything BenchIT consists of.
 *
 * This function initializes the kernel, runs the measurements and writes
 * the result-file.
 * @param argc Standard main argument.
 * @param argv Standard main argument.
 * @return 0 on success, >0 on failure.
 */
int main(int argc, char** argv) {
#ifdef USE_MPI
	/*
	 * will contain the number of MPI processes
	 */
	int size;
#endif
#ifdef USE_PAPI
	int papi_ver;
#endif
	/*
	 * todoList: what problemsizes have to be calculated
	 * doneList: what problemsizes have been calculated
	 */
	int *todoList = NULL, *doneList = NULL;
	/*
	 * will contain results temporarily of one bi_entry_call for one problemsize
	 */
	double *tmpResults = NULL;
	/*
	 * variables are used for check, how long this process is running
	 */
	double totalstart = 0, time2 = 0;
	/*
	 * is the timelimit reached?
	 */
	int timelimit_reached = 0;
	/* iterator vor the progress output */
	int percent;
	/*
	 * errno.h dosn't set errno to 0, so a check !=0 would fail
	 */errno = 0;
	/*****************************************************************************
	 * Initialization
	 */
	/* start VAMPIR */
#ifdef VAMPIR_TRACE
	(void) _vptsetup();
	(void) _vptenter(300);
#endif
	/* start MPI */
#ifdef USE_MPI
	IDL(2,printf("MPI_Init()..."));
	MPI_Init(&argc,&argv);
	MPI_Comm_rank(MPI_COMM_WORLD,&rank);
	MPI_Comm_size(MPI_COMM_WORLD,&size);
	IDL(2,printf(" [OK]\n"));
#else
	/* set rank to 0 becaues only one process exists */
	rank = 0;
	/* size=1; */
#endif
#ifdef USE_PAPI
	IDL(2,printf("PAPI_library_init()..."));
	papi_ver = PAPI_library_init(PAPI_VER_CURRENT);
	if (papi_ver != PAPI_VER_CURRENT) safe_exit(1);
	IDL(2,printf(" [OK]\n"));
#endif
	/* initialize hashtable for environment variables */
	bi_initTable();
	/* and fill it */
	bi_fillTable();
	/* check the command line arguments for flags */
	checkCommandLine(argc, argv);
	d_bi_start_sec = (double) ((long long) bi_gettimeofday());
	/* getting timer granularity and overhead */
	/* these variables can also be accessed by the kernel */
	dTimerOverhead = 0.0;
	dTimerGranularity = 1.0;
	/* select MPI-timer or standard timer or... */
	selectTimer();
	/* only first process shall write this */
	if (rank == 0) {
		printf("BenchIT: Timer granularity: %.9g ns\n", dTimerGranularity * 1e9);
		printf("BenchIT: Timer overhead: %.9g ns\n", dTimerOverhead * 1e9);
	}
	/* get the time limit */
	char* p = bi_getenv("BENCHIT_RUN_TIMELIMIT", 0);
	/* if the environment variable is set use it */
	if (p != 0){
		timelimit = atoi(p);
		freeCheckedC(&p);
	/* if not, use standard */
	}else
		timelimit = DEFAULT_TIMELIMIT;
	/* the same for this environment variable */
	p = bi_getenv("BENCHIT_RUN_ACCURACY", 0);
	if (p != 0){
		accuracy = atoi(p);
		freeCheckedC(&p);
	}else
		accuracy = DEFAULT_ACCURACY;
	/* prompt info */
	if (rank == 0) {
		printf("BenchIT: Getting info about kernel...");
		fflush(stdout);
	}
	/* fill theInfo with 0s (NOT '0's) */
	(void) memset(&theInfo, 0, sizeof(theInfo));
	/* get info from kernel */
	bi_getinfo(&theInfo);
	/* offset: number of functions from kernel +1 */
	offset = theInfo.numfunctions + 1;
	dataPointCt = theInfo.num_measurements * (accuracy + 1);
	numDataPointsPerX = (accuracy + 1) * theInfo.numfunctions + 1;
	/* print info */
	if (rank == 0) {
		printf(" [OK]\nBenchIT: Getting starting time...");
		fflush(stdout);
	}
	/* starting time used for timelimit */
	totalstart = bi_gettimeofday();
	/* print info */
	if (rank == 0) {
		char *kernelString = bi_getenv("BENCHIT_KERNELNAME", 1);
		printf(" [OK]\nBenchIT: Selected kernel: \"%s\"\n", kernelString != 0 ? kernelString : "NULL");
		fflush(stdout);
		printf("BenchIT: Initializing kernel...");
		fflush(stdout);
	}

	/* initialize kernel */
#ifdef BENCHIT_ECOLAB_DEBUG
	BENCHIT_ECOLAB_PRINT("Initializing Kernel");
#endif
	mcb = bi_init(theInfo.num_measurements);
	/* print info */
	if (rank == 0) {
		printf(" [OK]\n");
		fflush(stdout);
		printf("BenchIT: Allocating memory for results...");
		fflush(stdout);
		/* all results, which will be measured for one problemsize */
		allResults = (double*) malloc((size_t) theInfo.num_measurements * (size_t) numDataPointsPerX * sizeof(double));
		//Reset all values to x=0 (not measured) and y=invalid to detect aborts
		for (i = 0; i < theInfo.num_measurements; i++) {
			//x
			allResults[i * numDataPointsPerX] = INVALID_MEASUREMENT;
			//y
			for (j = 1; j < numDataPointsPerX; j++)
				allResults[i * numDataPointsPerX + j] = INVALID_MEASUREMENT;
		}
		/* results, which will be measured with a single call of bi_entry */
		tmpResults = (double*) calloc((size_t) offset, sizeof(double));
		//Init results
		int error = initResults(theInfo);
		/* if a malloc didnt work */
		if (allResults == 0 || tmpResults == 0 || error != 0) {
			printf(" [FAILED]\n");
			printf(" allResults: %lx, tmpResults: %lx, initError: %lx \n", (unsigned long) allResults, (unsigned long) tmpResults,
					(unsigned long) error);
			cleanUp(1);
		} else {
			printf(" [OK]\n");
			fflush(stdout);
		}

	}
	/* build list for done problemsizes and todo problemsizes */
	todoList = (int*) calloc((size_t) theInfo.num_measurements + 2, sizeof(int));
	doneList = (int*) calloc((size_t) theInfo.num_measurements + 1, sizeof(int));
	/* did malloc work? */
	if (todoList == 0 || doneList == 0) {
		printf(" [FAILED]\n");
		cleanUp(1);
	}

	/* setup signalhandlers */
	signal(SIGINT, sigint_handler);
	signal(SIGTERM, sigterm_handler);
	/*****************************************************************************
	 * Measurement
	 */
	/* print info */
	if (rank == 0) {
		printf("BenchIT: Measuring...\n");
		fflush(stdout);
	}
	if (rank == 0 && DEBUGLEVEL == 0) {
		if (bi_getenv("BENCHIT_PROGRESS_DIR", 0) != NULL && strcmp(bi_getenv("BENCHIT_PROGRESS_DIR", 0), "") && !bi_standalone) {
			size_t size = strlen(bi_getenv("BENCHITROOT", 0)) + strlen(bi_getenv("BENCHIT_PROGRESS_DIR", 0))
					+ strlen(bi_getenv("BENCHIT_KERNELNAME", 0)) + 25;
			char* tmp;
			progf = (char*) calloc(size, 1);
			sprintf(progf, "%s", bi_getenv("BENCHIT_PROGRESS_DIR", 0));
			if (progf[0] != '/') {
				memset(progf, 0, size);
				sprintf(progf, "%s/%s", bi_getenv("BENCHITROOT", 0), bi_getenv("BENCHIT_PROGRESS_DIR", 0));
			}
			createDirStructureOrExit(progf);
			memset(progf, 0, size);
			progf += strlen(bi_getenv("BENCHITROOT", 0)) + 1;
			tmp = progf;
			if (progf[0] == '\"')
				tmp++;

			sprintf(progf, "%s", bi_getenv("BENCHIT_PROGRESS_DIR", 0));

			if (progf[strlen(progf) - 1] == '\"')
				progf[strlen(progf) - 1] = '\0';
			if (progf[strlen(progf) - 1] != '/')
				progf[strlen(progf)] = '/';

			progf += strlen(progf);
			sprintf(progf, "%s_", bi_getenv("BENCHIT_KERNELNAME", 0));
			progf += strlen(bi_getenv("BENCHIT_KERNELNAME", 0)) + 1;
			sprintf(progf, "%018.6f", bi_gettimeofday());

			if (tmp[0] != '/') {
				tmp--;
				tmp[0] = '/';
				tmp -= strlen(bi_getenv("BENCHITROOT", 0));
				strncpy(tmp, bi_getenv("BENCHITROOT", 0), strlen(bi_getenv("BENCHITROOT", 0)));
			}

			progf = tmp;

			prog_file = fopen(progf, "w");

			if (prog_file != NULL ) {
				printf("BenchIT: writing progress information to file: %s\n", progf);
				fprintf(prog_file, "progress: 0%%\n");
				fflush(prog_file);
			} else
				printf("could not create file for writing progress information\n");
		}
		printf("progress scale (percent):\n");
		printf("0--------20--------40--------60--------80-------100\n");
		printf("progress:\n");

		fflush(stdout);
	}

	/* as long as there are still some problems (todo-/done-lists can be created) to measure */
	/* and we didnt exceed the timelimit do */
	while (get_new_problems(todoList, doneList, theInfo.num_measurements) && !timelimit_reached) {
		/* do accuracy+1 measurement */
		for (w = 0; w <= accuracy; w++) {
			/* as long as ther is something in the todoList and the time limit isn't reached do measure */
			curTodoIndex = 0;
			while ((todoList[++curTodoIndex] != 0) && !timelimit_reached) {
				int curProblemSize = todoList[curTodoIndex];
				IDL(2, printf("Testing with problem size %d\n", curProblemSize));

				/* if MPI is used, set a barrier to synchronize */
#ifdef USE_MPI
				if (theInfo.kernel_execs_mpi1 != 0) MPI_Barrier(MPI_COMM_WORLD);
#endif
				IDL(2, printf(" entering(%d)...\n", rank));

				/* do measurement for non-MPI or first MPI-process */
				if (rank == 0)
					flag = bi_entry(mcb, curProblemSize, tmpResults);
				else {
					if ((theInfo.kernel_execs_mpi1 != 0) || (theInfo.kernel_execs_mpi2 != 0))
						flag = bi_entry(mcb, curProblemSize, 0);
					else {
						printf("\nBenchIT: Warning: Maybe you should check the bi_getinfo funktion\n");
						printf("\nBenchIT:          infostruct->kernel_execs_mpi1 = 0 AND\n");
						printf("\nBenchIT:          infostruct->kernel_execs_mpi2 = 0 ???\n");
					}
				}

				/* for timelimit check */
				time2 = bi_gettimeofday();
				IDL(2, printf(" leaving(%d)...\n", rank));

				/* was sth else then 0 returned? */
				if (flag != 0) {
					/* finalize ;) */
					if (rank == 0)
						printf(" [FAILED]\nBenchIT: Internal kernel error. \n");
					cleanUp(1);
				} else {
					/* if everything is fine: */
					/* say: this problemsize is done */
					doneList[curProblemSize] = 1;
				}

				/* only the first one needs to do this */
				if (rank == 0) {
					IDL(3, printf("tmpResults="));
					for (i = 0; i < offset; i++) {
						IDL(3, printf(" %g", tmpResults[i]))
					}
					IDL(3, printf("\n"));
					//holds index of current x
					int curRow = numDataPointsPerX * (curProblemSize - 1);
					if (w == 0)
						allResults[curRow] = tmpResults[0];
					for (i = 0; i < theInfo.numfunctions; i++) {
						//accuracy+1: values per function; w: current run; +1: skip over x
						allResults[curRow + i * (accuracy + 1) + w + 1] = tmpResults[i + 1];
					}
				}
				/* another barrier for synchronization */
#ifdef USE_MPI
				if (theInfo.kernel_execs_mpi1 != 0) MPI_Barrier(MPI_COMM_WORLD);
#endif

				/* timelimit reached? */
				if ((timelimit > 0) && ((time2 - totalstart) > timelimit)) {
					if (rank == 0)
						printf("[BREAK]\nBenchIT: Total time limit reached. Stopping measurement.");
					timelimit_reached = 1;
					break;
				}

				/* write progress information to file if available */
				if ((rank == 0) && (DEBUGLEVEL == 0)) {
					n++;
					for (percent = 100; percent >= 0; percent -= 2) {
						if (100 * n / dataPointCt >= percent && 100 * (n - 1) / dataPointCt < percent)
							printf(".");
					}
					fflush(stdout);
					if ((100 * n / dataPointCt != 100 * (n - 1) / dataPointCt) && prog_file != NULL ) {
						if (truncate(progf, 0) == 0)
							fprintf(prog_file, "progress: %i%%\n", 100 * n / (theInfo.num_measurements * (accuracy + 1)));
						fflush(prog_file);
					}
				}
			} /* while (todoList...)*/
		} /* for(w=-1;w<accuracy;w++) */
		IDL(2, printf("...OK\n"));
	} /* while (get_new_pr...)*/
	IDL(0,printf("\n"));
	finish(0);
	return 0;
}

/*!@brief Starts the measurement timer
 *
 * This function is basicly a wrapper for bi_gettime() but also allows for using bi_stopTimer()
 *
 * @return The current timestamp as returned by bi_gettime
 */
double bi_startTimer() {
	biStartTimeAbs = bi_gettimeofday_improved();
	biStartTime = bi_gettime();
	return biStartTime;
}

/*!@brief Stops the measurement timer and returns the elapsed seconds
 *
 * Calculates the elapsed time since the start if bi_startTimer
 * WARNING: Results are undefined without a previous call to bi_startTimer.
 *          Do NOT mix with calls of bi_gettime
 *
 * @return The elapsed time cleaned by overhead or INVALID_MEASUREMENT if below granularity
 */
double bi_stopTimer() {
	double stopTime = bi_gettime();
	double diff = stopTime - biStartTime - dStartTimerOverhead;
	biStopTimeAbs = biStartTimeAbs + diff;
	if (diff < dTimerGranularity) {
		return INVALID_MEASUREMENT;
	}
	return diff;
}

/*!@brief Stops the measurement timer and returns the elapsed seconds.
 * Additionally returns timestamps of start/stop in startStop[2]
 *
 * Calculates the elapsed time since the start if bi_startTimer and prepares the system to get the consumed energy
 * WARNING: Results are undefined without a previous call to bi_startTimer.
 *          Do NOT mix with calls of bi_gettime
 *
 * @return The elapsed time cleaned by overhead or INVALID_MEASUREMENT if below granularity
 */
double bi_getStartStopTime(double *startStop) {
	double diff = bi_stopTimer();
	startStop[0] = biStartTimeAbs;
	startStop[1] = biStopTimeAbs;
	return 0;
}

/*!@brief Returns the elapsed time since the "epoch" (1/1/1970) in seconds
 *
 * This function is just a wrapper which combines the two integers of the
 * timeval struct to a double value.
 * @return The elapsed time since the epoch in seconds.
 */
static double bi_gettimeofday() {
	struct timeval time;
	gettimeofday(&time, (struct timezone *) 0);
	return (double) time.tv_sec + (double) time.tv_usec * 1.0e-6;
}

/*!@brief Returns the elapsed time since program start in seconds.
 *
 * This function has improved precision over bi_gettimeofday(), because the
 * amount of seconds is smaller and that leaves more space for the fractional
 * part of the double value.
 * @return The elapsed time since program start in seconds.
 */
static double bi_gettimeofday_improved() {
	struct timeval time;
	gettimeofday(&time, (struct timezone *) 0);
	return ((double) time.tv_sec - d_bi_start_sec) + (double) time.tv_usec * 1.0e-6;
}

/*!@brief Determines the granularity of a given timer function.
 * @param[in] timer Pointer to the timer function that shall be evaluated.
 * @return The minimum time in seconds that the given timer function can
 *         distinguish.
 * @TODO: you could add additional timers here but you should also add it to getTimerOverhead/selectTimer!
 */
static double getTimerGranularity(double (*timer)()) {
	int i;
	double t1, t2, gran = 1.0;
	/* first time */
	t2 = timer();
	/* do thousand times for more exact measurement */
	for (i = 1; i < 10000; i++) {
		/* new timer set to old timer */
		t1 = t2;
		/* while the returned value is the same as the old one
		 * Unfortunately floating point subtraction can produce results !=0 when subtracting two identical
		 * numbers, to filter senseless values (like 1.0e-10 ns) we check if the result is within the range
		 * of double relativly to the greater operand t2*/
		while ((t2 - t1) <= t2 * 1.0e-15)
			t2 = timer();
		/* if the step between the old and the new time is the lowest ever, set it as granularity.*/
		if ((t2 - t1) < gran)
			gran = t2 - t1;
	}
	/* found timer */
	if (timer == bi_gettimeofday_improved) {
	}

#ifdef USE_PAPI
	/* found timer */
	else if(timer == PAPI_gettime)
	{
	}
#endif

#ifdef USE_OMP
	/* found timer and set the granularity to the one, which is given by the OpenMP-lib */
	else if(timer == omp_get_wtime)
	{
		gran = omp_get_wtick();
	}
#endif

#ifdef USE_MPI
	/* found timer and set the granularity to the one, which is given by the mpi-lib */
	else if(timer == MPI_Wtime)
	{
		gran = MPI_Wtick();
	}
#endif
	/* unsupported timer */
	else {
		(void) fprintf(stderr, "BenchIT: getTimerGranularity(): Unknown timer\n");
		(void) fflush(stderr);
		(void) safe_exit(127);
	}
	return gran;
}

/*!@brief Determines the overhead of a call to a given timer function.
 * @param[in] timer Pointer to the timer function that shall be evaluated.
 * @return The overhead in seconds of one call to the timer function.
 * @TODO: you could add additional timers here but you should also add it to getTimerGranularity/selectTimer!
 */
static double getTimerOverhead(double (*timer)()) {
	double start, stop = 1.0, diff;
	unsigned long long passes = 1000;
	unsigned long long i;

	do {
		passes *= 10;
		start = timer();
		/* stop never has an value of 0.0, this is added to the condition to prevent the compiler from replacing
		 * the whole loop by only one assignment what potentially results in an endless loop as diff will always
		 * be too small to leave the do{...} while(...); loop */
		for (i = 0; i < passes && stop != 0.0; ++i)
			stop = timer();
		diff = stop - start;
	} while (diff < 1000 * dTimerGranularity);
	IDL(3, printf("getTimerOverhead: %lli passes\n", passes));

	return diff / (double) passes;
}

#ifdef USE_PAPI
static double PAPI_gettime(void)
{
	return (double) PAPI_get_real_usec() *1.0e-6;
}
#endif

/*!@brief Determine and select the best timer function.
 *
 * Determines the most precise available timer function and selects it for
 * use in the kernels via the bi_gettime() function.\n
 * Currently supported are gettimeofday() and MPI_Wtime().
 * @TODO: you could add additional timers here but you should also add it to getTimerGranularity/overhead!
 */
static void selectTimer() {
	/* the timer to use
	 * 0 -> use bi_gettimeofday_improved() [default]
	 * 1 -> use PAPI-Timer   (PAPI_gettime()) based on PAPI_get_real_usec()
	 * 2 -> use OpenMP-Timer (omp_get_wtime())
	 * 3 -> use MPI-Timer    (MPI_WTime())
	 */
	int select;

#ifdef USE_MPI
	int mpiRoot = 0, mpiRank;
	/* get own rank */
	MPI_Comm_rank(MPI_COMM_WORLD,&mpiRank);
	/* only the master should do this */
	if(mpiRank == 0)
	{
#endif

	double granularity;

	/* setup default timer */
	granularity = getTimerGranularity(bi_gettimeofday_improved);
	IDL(1, printf("BenchIT: Timer Granularity: bi_gettimeofday_improved: %.9g ns\n", granularity * 1.0e9));
	select = 0;
	dTimerGranularity = granularity;
	bi_gettime = bi_gettimeofday_improved;
	/* get overhead */
	dTimerOverhead = getTimerOverhead(bi_gettime);
	dStartTimerOverhead = getTimerOverhead(bi_startTimer);
	/* testing if another timer has a better granularity */
#ifdef USE_PAPI
	/* get granularity of PAPI-timer */
	granularity = getTimerGranularity(PAPI_gettime);
	IDL(1,printf("BenchIT: Timer Granularity:       PAPI_get_real_usec: %.9g ns\n", granularity * 1.0e9));
	if(granularity < dTimerGranularity)
	{
		select = 1;
		dTimerGranularity = granularity;
		bi_gettime = PAPI_gettime;
		/* get overhead */
		dTimerOverhead = getTimerOverhead(bi_gettime);
		dStartTimerOverhead = getTimerOverhead(bi_startTimer);
	}
#endif

#ifdef USE_OMP
	/* get granularity of OpenMP-timer */
	granularity = getTimerGranularity(omp_get_wtime);
	IDL(1,printf("BenchIT: Timer Granularity:            omp_get_wtime: %.9g ns\n", granularity * 1.0e9));
	if(granularity < dTimerGranularity)
	{
		select = 2;
		dTimerGranularity = granularity;
		bi_gettime = omp_get_wtime;
		/* get overhead */
		dTimerOverhead = getTimerOverhead(bi_gettime);
		dStartTimerOverhead = getTimerOverhead(bi_startTimer);
	}
#endif

#ifdef USE_MPI
	/* get granularity of MPI-timer */
	granularity = getTimerGranularity(MPI_Wtime);
	IDL(1,printf("BenchIT: Timer Granularity:                MPI_Wtime: %.9g ns\n", granularity * 1.0e9));
	/* select MPI-Timer if it is faster */
	if(granularity < dTimerGranularity)
	{
		select = 3;
		dTimerGranularity = granularity;
		bi_gettime = MPI_Wtime;
		/* get overhead */
		dTimerOverhead = getTimerOverhead(bi_gettime);
		dStartTimerOverhead = getTimerOverhead(bi_startTimer);
	}
}
/* send this timer settings to all other nodes */
MPI_Bcast(&select, 1, MPI_INT, mpiRoot,MPI_COMM_WORLD);
MPI_Bcast(&dTimerGranularity, 1, MPI_DOUBLE,mpiRoot,MPI_COMM_WORLD);
MPI_Bcast(&dTimerOverhead, 1, MPI_DOUBLE,mpiRoot,MPI_COMM_WORLD);
MPI_Bcast(&dStartTimerOverhead, 1, MPI_DOUBLE,mpiRoot,MPI_COMM_WORLD);
/* select timer in other nodes */
switch(select)
{
	case 0:
	bi_gettime = bi_gettimeofday_improved;
	if (mpiRank == 0) printf("BenchIT: Using Timer \"bi_gettimeofday_improved\"\n");
	break;
	case 1:
#ifdef USE_PAPI
	bi_gettime = PAPI_gettime;
	if (mpiRank == 0) printf("BenchIT: Using Timer \"PAPI_get_real_usec\"\n");
	break;
#endif
	case 2:
#ifdef USE_OMP
	bi_gettime = omp_get_wtime;
	if (mpiRank == 0) printf("BenchIT: Using Timer \"omp_get_wtime\"\n");
	break;
#endif
	case 3:
	bi_gettime = MPI_Wtime;
	if (mpiRank == 0) printf("BenchIT: Using Timer \"MPI_Wtime\"\n");
	break;
	default:
	(void) fprintf (stderr, "BenchIT: selectTimer(): Unknown timer\n");
	(void) fflush (stderr);
	(void) safe_exit (127);
}
#else
	switch (select) {
	case 0:
		printf("BenchIT: Using Timer \"bi_gettimeofday_improved\"\n");
		break;
	case 1:
		printf("BenchIT: Using Timer \"PAPI_get_real_usec\"\n");
		break;
	case 2:
		printf("BenchIT: Using Timer \"omp_get_wtime\"\n");
		break;
	default:
		fprintf(stderr, "BenchIT: selectTimer(): Unknown timer\n");
		fflush(stderr);
		safe_exit(127);
	}
#endif
}

/*!@brief Reads and copies environment variable with the name supplied in env.
 *
 * If the environment variable ist not defined, the value of exitOnNull
 * determines the behaviour of this function:\n
 * @li @c exitOnNull @c = @c 0: The return value will be @c NULL.
 * @li @c exitOnNull @c = @c 1: Exit BenchIT with an error message.
 * @li @c exitOnNull @c > @c 1: Exit BenchIT with an error message and additionally dump
 *     the environment variable hashtable.
 *
 * @param[in] env The name of the environment variable whose content shall be retrieved.
 * @param[in] exitOnNull Defines how to handle errors.
 * @return Pointer to a copy of the environment variable.
 */
char* bi_getenv(const char *env, int exitOnNull) {
	char *res = 0;
	u_int l = 0;
	/* First try to read from Environment*/
	res = getenv(env);
	if (res != NULL )
		return strdup(res);

	/* If not found look up environment variable in the hashtable. */
	res = bi_get(env, &l);
	if (res != NULL) {
		res = bi_strdup(res);
	} else if (exitOnNull > 0) {
		(void) fprintf(stderr, "BenchIT: bi_getenv(): env. variable %s not defined\n", env);
		(void) fflush(stderr);
		if (exitOnNull > 1)
			bi_dumpTable();
		(void) safe_exit(127);
	}
	return res;
}

/*!@brief Reads and converts environment variable with the name supplied in env
 *        to a long int.
 *
 * If the environment variable ist not defined or if there is an error
 * converting the string to an integer value, the value of exitOnNull determines
 * the behaviour of this function:\n
 * @li @c exitOnNull @c = @c 0: The return value will be @c 0.
 * @li @c exitOnNull @c = @c 1: Exit BenchIT with an error message.
 * @li @c exitOnNull @c > @c 1: Exit BenchIT with an error message and
 *        additionally dump the environment variable hashtable.
 *
 * @param[in] env The name of the environment variable whose content shall be
 *                retrieved.
 * @param[in] exitOnNull Defines how to handle errors.
 * @return Value of env as long int.
 */
long int bi_int_getenv(const char *env, int exitOnNull) {
	/* used for getting environment as string */
	const char *string = 0;
	/* end of the string */
	char *endptr = 0;
	/* what is computed out of the string */
	long int result = 0;
	/* was there an error? */
	int error = 0;
	/* get the environment variable to string */
	string = bi_getenv(env, exitOnNull);
	/* found? */
	if (*string != 0) {
		/* get the numereous meaning (ending char is a 0 (args)) and a decimal meaning (arg3) */
		result = strtol(string, &endptr, 10);
		/* couldnt translate? */
		if (*endptr != 0)
			error++;
	}
	/* couldnt get env? */
	else
		error++;
	/* error? */
	if (error > 0) {
		if (exitOnNull > 0) {
			(void) fprintf(stderr, "BenchIT: bi_int_getenv(): env. variable %s not an int (%s)\n", env, string);
			(void) fflush(stderr);
			if (exitOnNull > 1)
				bi_dumpTable();
			(void) safe_exit(127);
		}
		result = 0;
	}
	/* error or not */
	return result;
}

/*! translates a string to a fractional part
 * @param[in] r a string, which numbers are after '.', including the '.'\
  (which could be any char, though it isn't checked ;))
 * @return the meaning of the String as float
 * COMMENT: Example: In: String ".12345", Out: float 0.12345
 */
static float fracpart(char *r) {
	/* a is total sum, s is actual decimal position */
	float a = 0, s = 1;
	do {
		/* start with 1/10, then 1/100, ... */
		s = s / 10;
		/* next char */
		r++;
		;
		/* if it is a number between 0 and 9 */
		if (('0' <= *r) && (*r <= '9')) {
			/* add this part to total sum */
			a += s * (float) (*r - '0');
		}
		/* until this char isn't a number anymore */
	} while (('0' <= *r) && (*r <= '9'));
	/* return total fractional part */
	return a;
}

/*!@brief Converts $BENCHIT_ARCH_SPEED into float [GHz]
 * @return Clock rate in GHz as float.
 * COMMENT: be careful with this function! The user could write anything in his BENCHIT_ARCH_SPEED
 */
float bi_cpu_freq() { /* get CPU-Freq in GHz */
	char *p, *q;
	/* return value */
	float f;
	/* get the speed (e.g. 3G3 or 200M) */
	p = bi_getenv("BENCHIT_ARCH_SPEED", 0);
	/* wasn't set */
	if (p == NULL )
		return 0.0;
	/* try to translate it to float (will get everything, until the G) */
	f = (float) atof(p);
	/* find G */
	q = strstr(p, "G");
	/* not found? find g */
	if (q == NULL )
		q = strstr(p, "g");
	/* found? */
	if (q != NULL ) {
		/* add the value before the g and the fractional part and return it */
		return f + fracpart(q);
	}
	/* maybe its an M */
	q = strstr(p, "M");
	/* or m */
	if (q == NULL )
		q = strstr(p, "m");
	/* do the same blabla */
	if (q != NULL ) {
		return (f + fracpart(q)) / 1000;
	}
	return f;
}

/*!@brief Tries to confuse the Cache by filling nCacheSize bytes with
 * data and calculating with it
 * @param[in] nCacheSize number of bytes to allocate
 *            (should be a multiple of sizeof(int))
 * @returns a number which can be ignored ;)
 */
int bi_confuseCache(size_t nCacheSize) {
	/* trying to fill the L2-cache with uninteristing stuff */
	int s = 0, *memConfuse;
	size_t i;

	if (nCacheSize == 0)
		return 1;
	memConfuse = (int*) malloc(nCacheSize);
	nCacheSize = nCacheSize / sizeof(int);
	for (i = 0; i < nCacheSize; memConfuse[i++] = 1)
		;
	for (i = nCacheSize / 2; i < nCacheSize; i++)
		s += memConfuse[i] + memConfuse[i - nCacheSize / 2];
	for (i = nCacheSize / 2; i < nCacheSize; i++)
		s += memConfuse[i] + memConfuse[i - nCacheSize / 2];
	for (i = nCacheSize / 2; i < nCacheSize; i++)
		s += memConfuse[i] + memConfuse[i - nCacheSize / 2];
	for (i = nCacheSize / 2; i < nCacheSize; i++)
		s += memConfuse[i] + memConfuse[i - nCacheSize / 2];
	freeCheckedI(&memConfuse);
	return s;
}

/*!@brief Free the given pointer of !=NULL and set it to NULL
 * Prints an error if NULL is given on DEBUGLEVEL>=1
 * DO NOT CALL THIS DIRECTLY! It is called from the other functions to avoid conversion warnings
 * @param[inout] ptr Pointer reference to be freed and set
 */
void freeChecked(void* ptr) {
	if(ptr==NULL){
		IDL(0,printf("ERR: NULL ptr given to freeChecked"));
		return;
	}
	void **ptrRef=ptr;
	if (*ptrRef){
		free(*ptrRef);
		*ptrRef=NULL;
	}else
		IDL(1,printf("HINT: Tried freeing a NULL pointer"));
}

/*!@brief Free the given pointer of !=NULL and set it to NULL
 * Prints an error if NULL is given on DEBUGLEVEL>=1
 * @param[inout] ptr Pointer reference to be freed and set
 */
void freeCheckedD(double** ptr) {
	freeChecked(ptr);
}

/*!@brief Free the given pointer of !=NULL and set it to NULL
 * Prints an error if NULL is given on DEBUGLEVEL>=1
 * @param[inout] ptr Pointer reference to be freed and set
 */
void freeCheckedC(char** ptr) {
	freeChecked(ptr);
}

void freeCheckedI(int** ptr) {
	freeChecked(ptr);
}

/* variables for random number generator */

/*! user defined maximum size of output */
static unsigned long long random_max32, random_max48;

/*!
 * The random number generator uses 2 independent generators and returns the bitwise xor of them
 * both generators use this formula: r(n+1) = ((a * r(n)) +b) mod m
 * the parameters are defined in the bi_random_init() function
 */

/*! parameters for the first generator*/
static unsigned long long random_value1 = 0;
static unsigned long long rand_a1 = 0;
static unsigned long long rand_b1 = 0;
static unsigned long long rand_m1 = 1;
static unsigned long long rand_fix1 = 0;

/*! parameters for the second generator */
static unsigned long long random_value2 = 0;
static unsigned long long rand_a2 = 0;
static unsigned long long rand_b2 = 0;
static unsigned long long rand_m2 = 1;
static unsigned long long rand_fix2 = 0;

/* end variables for random number generator */

/*! @brief returns a 32-Bit pseudo random number
 *  using this function without a prior call to bi_random_init() is undefined!
 *  bi_random32() and bi_random48() share one state so a call to
 *  bi_random32() will affect the next result of bi_random48() and vice versa.
 *  The functions only differ in the output format and the possible range.
 *  @return random number
 */
unsigned int bi_random32() {
	random_value1 = (random_value1 * rand_a1 + rand_b1) % rand_m1;
	random_value2 = (random_value2 * rand_a2 + rand_b2) % rand_m2;
	return (unsigned int) ((random_value1 ^ random_value2) % random_max32);
}

/*! @brief returns a 48-Bit pseudo random number
 *  using this function without a prior call to bi_random_init() is undefined!
 *  bi_random32() and bi_random48()share one state so a call to
 *  bi_random48() will affect the next result of bi_random32() and vice versa.
 *  The functions only differ in the output format and the possible range.
 *  @return random number
 */
unsigned long long bi_random48() {
	random_value1 = (random_value1 * rand_a1 + rand_b1) % rand_m1;
	random_value2 = (random_value2 * rand_a2 + rand_b2) % rand_m2;
	return (random_value1 ^ random_value2) % random_max48;
}

/*! @brief initalizes random number generator
 *  Initializes the random number generator with the values given to the function.
 *  The random number generator uses 2 independent generators and returns the bitwise xor of them.
 *  both generators use this formula: r(n+1) = ((a * r(n)) +b) mod m.
 *  @param[in] start start value for random number generation
 *  @param[in] max the generator will allways return numbers smaller than max
 *                 if max is 0 bi_random32 will return numbers between 0 and 2^32 -1
 *                             bi_random48 will return numbers between 0 and 2^48 -1
 */
void bi_random_init(unsigned long long start, unsigned long long max) {
	/* setting up parameters (direct assignment of long long values causes compiler warning) */
	rand_a1 = 25799ULL;
	rand_b1 = 76546423423ULL;
	rand_m1 = 568563987265559ULL;
	rand_fix1 = 298651465807007ULL;

	rand_a2 = 131ULL;
	rand_b2 = 91723615256891ULL;
	rand_m2 = 338563987265599ULL;
	rand_fix2 = 283167315359180ULL;

	/* setup the max values returned to user*/
	random_max32 = ((unsigned long long) 1) << 32;
	random_max48 = ((unsigned long long) 1) << 48;
	if (max > 0) {
		if (max < random_max32)
			random_max32 = max;
		if (max < random_max48)
			random_max48 = max;
	}

	/* the first generator is initialized with the user defined start value */
	random_value1 = start % rand_m1;
	if (random_value1 == rand_fix1)
		random_value1 = 43277143270890ULL; /* Fixpoint can't be used */

	/* the second generator is initialized with the first random number generated by the first generator*/
	random_value2 = 0;
	random_value2 = bi_random48();
	if (random_value2 == rand_fix2)
		random_value2 = 678157495234ULL; /* Fixpoint can't be used */
}

double bi_get_list_element(int index) {
	int ii = 0;
	bi_list_t *current;

	if (theInfo.listsize < index) {
		printf("list index out of bounds\n");
		return 0.0;
	}
	current = theInfo.list;
	for (ii = 1; ii < index; ii++) {
		current = current->pnext;
	}

	//printf("bi_get_list_element: list[%d] = %f\n", ii, current->dnumber);
	return current->dnumber;
}

double bi_get_list_maxelement() {
	int ii = 0;
	bi_list_t *current = NULL;
	double maximum = 0.0;

	if (theInfo.listsize < 1) {
		printf("no items in list\n");
		return 0.0;
	}
	current = theInfo.list;
	maximum = current->dnumber;
	for (ii = 1; ii < theInfo.listsize; ii++) {
		current = current->pnext;
		maximum = (maximum < current->dnumber) ? current->dnumber : maximum;
	}

	return maximum;
}

double bi_get_list_minelement() {
	int ii = 0;
	bi_list_t *current = NULL;
	double minimum = 0.0;

	if (theInfo.listsize < 1) {
		printf("no items in list\n");
		return 0.0;
	}
	current = theInfo.list;
	minimum = current->dnumber;
	for (ii = 1; ii < theInfo.listsize; ii++) {
		current = current->pnext;
		minimum = (minimum > current->dnumber) ? current->dnumber : minimum;
	}

	return minimum;
}

/*! @brief The function parses a list of numbers in a certain sysntax
 * and returns a chained list with the expanded numbers.
 *  @param[out] count holds the number of elements in the result-list
 *  @param[in] pcstring the string containing the intervalls
 *  @return expanded list of values which is count elements long
 */
void bi_parselist(const char *pcstring) {
#define LONG_TYPE unsigned long long
	/*pointer to the 1st element of the bi_list_t and
	 return value if the function*/
	bi_list_t *pfirst;
	bi_list_t *panchor;
	/*variable for buffering and working*/
	bi_list_t *pelement;
	/*loop variables, variables for memorising
	 series of numbers and raise*/
	LONG_TYPE li, lj, ln, lstartnumber, lendnumber, lraise;
	int icount, negraise;

	/*debugging level 1: mark begin and end of function*/
	if (DEBUGLEVEL > 0) {
		printf("reached function parser\n");
		fflush(stdout);
	}

	/*initializing*/
	li = (LONG_TYPE) 0;
	lj = (LONG_TYPE) 0;
	ln = (LONG_TYPE) 0;
	lstartnumber = (LONG_TYPE) 0;
	lendnumber = (LONG_TYPE) 0;
	lraise = (LONG_TYPE) 0;
	icount = (int) 0;
	negraise = (int) 0;
	pfirst = NULL;
	panchor = NULL;
	errno = 0;
	/*as long as the strings end is not reached do ...*/
	while (pcstring[li] != 0) {
		/*if the beginning of a number is found ...*/
		if (isdigit(pcstring[li])) {
			/*save the number that was found*/
			sscanf((pcstring + li), "%llu", &lstartnumber);
			if (errno != 0) {
				perror("sscanf failed - wrong value type in PARAMETERS\n");
			}
			/*move ahead in the string until the end of the number ...*/
			if(lstartnumber == 0)
				ln = 0;
			else
				ln = (LONG_TYPE) log10((double) lstartnumber);
			li += ln + 1;
			/*whitespaces are ignored*/
			while (isspace(pcstring[li])) {
				li++;
			}
			/*if next character is a minus
			 -> series of numbers is defined*/
			if (pcstring[li] == '-') {
				li++;
				/*whitespaces are ignored*/
				if (isspace(pcstring[li]))
					li++;
				/*if next number if found ...*/
				if (isdigit(pcstring[li])) {
					/*the number is used as
					 the end of the series*/
					sscanf((pcstring + li), "%llu", &lendnumber);
					if (errno != 0) {
						perror("sscanf failed - wrong value type in PARAMETERS\n");
					}
					/*move ahead in the string until the end of the number*/
					if(lendnumber == 0)
						ln = 0;
					else
						ln = (LONG_TYPE) log10((double) lendnumber);
					li += ln + 1;

					/*if there is nothing different defined
					 all numbers between start and and are
					 added to the list*/
					lraise = 1;
					/*whitespaces are ignored*/
					while (isspace(pcstring[li])) {
						li++;
					}
					/* check for attemps to use floats - bad thing */
					if (pcstring[li] == '.') {
						fprintf(stderr, "\nfloating point numbers in PARAMETERS not supported\n");
						safe_exit(1);
					}

					/*if next char is a slash
					 -> raise must be changed to ...*/
					if (pcstring[li] == '/') {
						li++;
						/*whitespaces are ignored*/
						while (isspace(pcstring[li])) {
							li++;
						}
						/* check for neg number starting with "-" */
						negraise = (int) 0; /* reset to non-negative */
						if (pcstring[li] == '-') {
							li++;
							negraise = 1;
						}
						/*... the following number ...*/
						if (isdigit(pcstring[li])) {
							sscanf((pcstring + li), "%llu", &lraise);
							if (errno != 0) {
								perror("sscanf failed - wrong value type in PARAMETERS\n");
							}
							if (lraise == 0) {
								fprintf(stderr, "\nstepsize zero won't work - reset to one\n");
								lraise = 1;
							}
						}
						/*and it needs to be moved ahead
						 until the end of the number*/
						if(lraise == 0)
							ln = 0;
						else
							ln = (LONG_TYPE) log10((double) (lraise));
						li += ln + 1;
						/* check for attemps to use floats - bad thing */
						if (pcstring[li] == '.') {
							fprintf(stderr, "\nfloating point numbers in PARAMETERS not supported\n");
							safe_exit(1);
						}
					}

					/*create a new element ....*/
					pelement = (bi_list_t *) malloc(sizeof(bi_list_t));
					/* remember the first element */
					if (pfirst == NULL )
						pfirst = pelement;
					/* create anchor id nessessary */
					if (panchor == NULL )
						panchor = (bi_list_t *) malloc(sizeof(bi_list_t));
					panchor->pnext = pelement;
					panchor = pelement;
					pelement->dnumber = (double) lstartnumber;
					icount++;

					/* check sanity of found values */
					fflush(stdout);
					fflush(stderr);
					if ((negraise == 0) && (lendnumber < (lstartnumber + lraise))) {
						fprintf(stderr, "\nwrong start-stop/stepsize values");
						fprintf(stderr, "\nyou will only do one measurement\n");
						lendnumber = lstartnumber;
						lraise = 1;
					}
					if ((negraise == 1) && (lstartnumber < (lendnumber + lraise))) {
						fprintf(stderr, "\nwrong start-stop/stepsize values");
						fprintf(stderr, "\nyou will only do one measurement\n");
						lendnumber = lstartnumber;
						lraise = 1;
						negraise = 0;
					}
					fflush(stderr);
					fflush(stdout);

					/*now all desired elements between start
					 and end are added to the list*/
					if (negraise == 0) {
						for (lj = lstartnumber; lj <= lendnumber - lraise; lj += lraise) {
							/*allocate element*/
							pelement = (bi_list_t *) malloc(sizeof(bi_list_t));
							panchor->pnext = pelement;
							panchor = pelement;
							/*create an element with the number
							 (startnumber is already in the list!)*/
							pelement->dnumber = (double) (lj + lraise);
							/*and keep in mind that an element was inserted*/
							icount++;
						}
					} else {
						for (lj = lstartnumber; lj >= lendnumber + lraise; lj -= lraise) {
							/*allocate element*/
							pelement = (bi_list_t *) malloc(sizeof(bi_list_t));
							panchor->pnext = pelement;
							panchor = pelement;
							/*create an element with the number
							 (startnumber is already in the list!)*/
							pelement->dnumber = (double) (lj - lraise);
							/*and keep in mind that an element was inserted*/
							icount++;
						}
					}
				}
			} else {
				/* if the next char is a comma or end is reached */
				if (pcstring[li] == ',' || pcstring[li] == 0) {
					/*create a new element ....*/
					pelement = (bi_list_t *) malloc(sizeof(bi_list_t));
					/* remember the first element */
					if (pfirst == NULL )
						pfirst = pelement;
					/* create anchor id nessessary */
					if (panchor == NULL )
						panchor = (bi_list_t *) malloc(sizeof(bi_list_t));
					panchor->pnext = pelement;
					panchor = pelement;
					pelement->dnumber = (double) lstartnumber;
					icount++;
				} else {
					/* check for attemps to use floats - bad thing */
					if (pcstring[li] == '.') {
						fprintf(stderr, "\nfloating point numbers in PARAMETERS not supported\n");
						safe_exit(1);
					}
				}
			}
		}
		/*if no number is found -> go on in the string */
		else
			li++;
	}

	theInfo.list = pfirst;
	theInfo.listsize = icount;

	/*debugging level 1: mark begin and end of function */
	if (DEBUGLEVEL > 0) {
		fflush(stdout);
		printf("parser created %d entries in list\n", icount);
		/*return the pointer that points to the start of the bi_list_t */
		printf("listsize=%d, value=%f\n", theInfo.listsize, pelement->dnumber);
		printf("completed function parser\n");
		fflush(stdout);
	}
}

/*!@brief Duplicates a given string.
 * @param[in] str The string that shall be copied.
 * @param[in] addCt The number of additional bytes allocated.
 * @return Pointer to the copy of the string.
 */
char* bi_strndup(const char *str, size_t addCt) {
	/* NULL given as str */
	if (str == 0) {
		(void) fprintf(stderr, "BenchIT: bi_strdup(): NULL as argument\n");
		(void) fflush(stderr);
		(void) safe_exit(127);
	}
	size_t len = 1 + strlen(str);
	char *so = malloc(len + addCt);
	if (so)
		memcpy(so, str, len);
	else {
		/* if the space for this copy isn't avail or sth else failed */
		(void) fprintf(stderr, "BenchIT: bi_strdup(): No more core\n");
		(void) fflush(stderr);
		(void) safe_exit(127);
	}
	return so;
}

/*!@brief Duplicates a given string.
 * @param[in] str The string that shall be copied.
 * @return Pointer to the copy of the string.
 */
char* bi_strdup(const char *str) {
	return bi_strndup(str, 0);
}

#ifdef __cplusplus
}
#endif
