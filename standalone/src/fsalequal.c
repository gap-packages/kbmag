/* fsalequal.c 30/12/98
 *
 * Test whether the accepted languages of two fsa's are equal.
 *
 * SYNOPSIS: fsalequal [-ip d/s] [-silent] [-v] filename1 filename2\n");
 *
 * Input is from filename1 and filename2, which should contain fsa's.
 * Output to stdout only.
 * Exit code is 0 if languages equal, otherwise 2.
 * Languages can only be equal when the alphabets are.
 * (As usual, exit code 1 denotes an error.)
 *
 * OPTIONS:
 * -ip d/s      input in dense or sparse format - dense is default
 * -v           verbose
 * -silent      no diagnostics
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile;

void  badusage_fsalequal();

/* Functions defined in other files used in this file */
void  fsa_read();
int   fsa_bfs();
int   fsa_min();
boolean fsa_equal();
void  fsa_clear();
int   stringlen();

int 
main (int argc, char *argv[])
{ int arg, ct, n;
  fsa fsa1, fsa2;
  char inf1[100], inf2[100], fsaname[100];
  storage_type ip_store = DENSE;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf1[0] = '\0';
  inf2[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsalequal();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's')
        ip_store = SPARSE;
      else
        badusage_fsalequal();
    }
    else if (strcmp(argv[arg],"-silent")==0)
      kbm_print_level = 0;
    else if (strcmp(argv[arg],"-v")==0)
      kbm_print_level = 2;
    else if (strcmp(argv[arg],"-vv")==0)
      kbm_print_level = 3;
    else {
       if (argv[arg][0] == '-')
         badusage_fsalequal();
       if (strcmp(inf2,""))
         badusage_fsalequal();
       if (strcmp(inf1,"")==0)
         strcpy(inf1,argv[arg]);
       else
         strcpy(inf2,argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf1)==0 || stringlen(inf1)==0)
    badusage_fsalequal();
  if ((rfile = fopen(inf1,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf1);
    exit(1);
  }
  fsa_read(rfile,&fsa1,ip_store,0,0,TRUE,fsaname);
  fclose(rfile);
  if ((rfile = fopen(inf2,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf2);
    exit(1);
  }
  fsa_read(rfile,&fsa2,ip_store,0,0,TRUE,fsaname);
  fclose(rfile);

  if (fsa_minimize(&fsa1)== -1) exit(1);
  if (fsa_bfs(&fsa1)== -1) exit(1);
  if (fsa_minimize(&fsa2)== -1) exit(1);
  if (fsa_bfs(&fsa2)== -1) exit(1);

  if (fsa_equal(&fsa1,&fsa2)) {
    if (kbm_print_level>0)
      printf("#The languages of the automata are equal.\n");
    fsa_clear(&fsa1);
    fsa_clear(&fsa2);
    exit(0);
  }
  else {
    if (kbm_print_level>0)
      printf("#The languages of the automata are NOT equal.\n");
    fsa_clear(&fsa1);
    fsa_clear(&fsa2);
    exit(2);
  }
}

 
void 
badusage_fsalequal (void)
{
    fprintf(stderr,
  "Usage: fsalequal [-ip d/s] [-silent] [-v] filename1 filename2\n");
    exit(1);
}
