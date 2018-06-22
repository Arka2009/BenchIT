#define CPU_DATA_COUNT 345
#define ARCH_SHORT_COUNT 100

typedef struct {
	const char * name;
	const int cores_per_pkg;
	const char * arch_short;
} archshrt_t;

typedef struct {
	const char * name;
	const int family;
	const int model;
	const char * codename;
	const int node;
} info_t;

extern const info_t cpu_data[];
extern const archshrt_t archshrt_data[];

