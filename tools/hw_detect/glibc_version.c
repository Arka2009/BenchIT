#include <string.h>
#include <stdio.h>
#include <unistd.h>
#include <stdlib.h>

typedef unsigned long long Uint64;
typedef unsigned short Uint16;

Uint64 convert_version(char * buf)
{
    int i = 0, max;
    Uint16 ver[4];
    Uint64 result = 0;
    char *pch;
    
    pch = strtok(buf, ".");
    while(pch != NULL && i < 4)
    {
        ver[i++] = atoi(pch);
        pch = strtok(NULL, ".");
    }

    max = i;
    for (i=0;i < max; i++)
    {
        result += ((Uint64)ver[i] << ((Uint64)16*(3-i)));
    }
  
    return result;
}

int main(int argc, char **argv)
{
  Uint64 test, ver;
  char tempver[256];
  
  if(!confstr(_CS_GNU_LIBC_VERSION, tempver, 256)) {
	 printf("not found\n");
  	 return -2;
  }
  

  if (argc==1) printf("%s\n", tempver+6);
  if (argc==2)
  {
  	ver = convert_version(tempver+6);
  	test = convert_version(argv[1]);

  	if(test <= ver) {
  		printf("ok\n");
  		return 0;
  	}
  	else {
  		printf("fail\n");
  		return -1;
  	}
  }
}
