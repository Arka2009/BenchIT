/********************************************************************
 * BenchIT - Performance Measurement for Scientific Applications
 * Contact: developer@benchit.org
 *
 * $Id: fileversion.c 1 2009-09-11 12:26:19Z william $
 * $URL: svn+ssh://molka@rupert.zih.tu-dresden.de/svn-base/benchit-root/BenchITv6/tools/fileversion.c $
 * For license details see COPYING in the package base directory
 *******************************************************************/
/* gets the fileversion and writes them to an environment variable.
 *******************************************************************/

/** @file fileversion.c
* @Brief gets the fileversion and writes them to an environment variable.
*/

#include <sys/stat.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <sys/types.h>
#include <dirent.h>
#include <time.h>

/** replace all existing characters O with character N */
#define REPLACE(STR,O,N) for( index=0; index<strlen(STR); index++) \
                            if( STR[index]==O ) STR[index]=N;
                            
/** str.toUpperCase() ;) to say it in JAVA */
#define UPPERCASE(STR) for( index=0; index<strlen(STR); index++) \
                            STR[index]= (char) toupper(STR[index]);
/**@brief look for BENCHIT_KERNEL_FILE_VERSION_<filename> in files and set
* an ENVIRONMENT VARIABLE for it
*/
int main (void)
{
    /** folder structure */
    DIR *dp;
    struct dirent *ep;
    struct stat statbuf;
    char *buff, *found;
    /** buffer for file content */
    int buffsize=100*1024;
    char temp[100];
    char temp2[100];
    int index;
    FILE *f;
    /* allocate memory for filecontent  */
    buff=(char *) malloc(buffsize);
    if(buff==NULL)
    {
        printf("Unable to allocate %dKB\n", buffsize/1024);
        exit(1);
    }

    /** open actual folder */
    dp = opendir ("./");
    if (dp != NULL)
    {
        while( (ep=readdir(dp))!=NULL )
        {
            /* skip some special candidates */
            /** everything, which starts with . */
            if( ep->d_name[0]=='.' )
                continue;
            /** CVS isnt what we want */
            if( strcmp(ep->d_name,"CVS")==0 )
                continue;
            /** neither are .o files */
            index=strlen(ep->d_name);
            if( ep->d_name[index-2]=='.' && ep->d_name[index-1]=='o' )
                continue;
            /** stat for filename (get information) */
            if( stat(ep->d_name,&statbuf)!=0 )
            {
                /** error! stat not succesful */
                REPLACE( ep->d_name, '.', '_');
                UPPERCASE( ep->d_name);
                printf("BENCHIT_KERNEL_FILE_VERSION_%s='%s (%s)'\n",
                    ep->d_name, "NO REVISION, UNABLE TO STAT", "COULD NOT STAT");
                continue;
            }
            /* stat succesful */
            else
            {
                /** write changes since last time to temp2 */
                strncpy( temp2, ctime(&statbuf.st_mtime), 100);
                for( index=0; index<100; index++)
                    if( temp2[index]<' ' )
                        temp2[index]=0;
                /** maybe enlarge buffer for filecontent */
                if( statbuf.st_size>buffsize )
                {
                    buff=(char *) realloc(buff,statbuf.st_size);
                    if(buff==NULL)
                    {
                        printf("Unable to allocate %dKB\n", buffsize/1024);
                        exit(1);
                    }
                    buffsize=statbuf.st_size;
                }
                /** open file */
                if( (f=fopen(ep->d_name,"r"))==NULL )
                {
                    REPLACE( ep->d_name, '.', '_');
                    UPPERCASE( ep->d_name);
                    printf("BENCHIT_KERNEL_FILE_VERSION_%s='%s (%s)'\n",
                        ep->d_name, "NO REVISION, UNABLE TO OPEN", temp2);
                    continue;
                }
                memset( buff, 0, buffsize);
                /** read complete file */
                if( fread( buff, statbuf.st_size, 1, f)!= 1)
                {
                    REPLACE( ep->d_name, '.', '_');
                    UPPERCASE( ep->d_name);
                    printf("BENCHIT_KERNEL_FILE_VERSION_%s='%s (%s)'\n",
                        ep->d_name, "NO REVISION, UNABLE TO READ", temp2);
                    continue;
                }
                fclose(f);
                /** check for $Revision: */
                found=strstr( buff, "$Revision:");
                if( found==NULL )
                {
                    REPLACE( ep->d_name, '.', '_');
                    UPPERCASE( ep->d_name);
                    printf("BENCHIT_KERNEL_FILE_VERSION_%s='%s (%s)'\n",
                        ep->d_name, "NO REVISION", temp2);
                    continue;
                }
                /** go to the beginning of '$Revision:' */
                found+=10;
                while( *found==' ' )
                    found++;
                index=0;
                memset( temp, 0, 100);
                /** read revision number */
                while( *found!='$' && *found>' ' && index<99 )
                    temp[index++]=*(found++);
                /** okay, write result */
                REPLACE( ep->d_name, '.', '_');
                UPPERCASE( ep->d_name);
                printf("BENCHIT_KERNEL_FILE_VERSION_%s='%s (%s)'\n",
                        ep->d_name, temp, temp2 );

            }
        }
        (void) closedir (dp);
    }
    else
    perror ("Couldn't open the directory");
    free(buff);
    printf("\n");
    return 0;
}

