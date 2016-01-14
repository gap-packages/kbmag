/* fsareverse.c 18/4/96.
 * Calculates finite state automaton that accepts w_1 if and only if
 * input automaton accepts w_1 read backwards.
 * 11/9/97 added -midfa option which returns the reverse fsa as a labeled MIDFA
 * with initial states the (labeled) singleton accept states of input fsa.
 * 2/5/96 - added -s option to output states of reverse automaton
 * as subsets of original state set.
 * Note: -s and -midfa cannot currently be used together.
 *
 * SYNOPSIS:  fsareverse [-s] [-midfa] [-ip d/s[dr]] [-op d/s]
 *                       [-silent] [-v] [-l/-h] filename
 *
 * Input is from filename, which should contain a fsa.
 * Output is to filename.reverse
 *
 * OPTIONS:
 * -midfa       return the reverse fsa as a labeled MIDFA with initial states
 *              the (labeled) singleton accept states of input fsa.
 * -s		output states as subsets of set of staes of input fsa
 *		(and don't minimize the output fsa).
 * -ip d/s[dr]  input in dense or sparse format - dense is default
 * -op d/s      output in dense or sparse format - default is as in current
 *               value of table->printing_format, in the fsa.
 * -v           verbose
 * -silent      no diagnostics
 * -l/-h        large/huge hash-tables (for big examples)
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_fsareverse();

/* Functions defined in other files used in this file */
void  fsa_read();
fsa  *fsa_reverse();
fsa  *fsa_mireverse();
void  fsa_print();
void  fsa_clear();
int   fsa_minimize();
int   stringlen();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg;
  fsa fsain, *fsareverse;
  char inf[100], outf[100], fsaname[100], tempfilename[100];
  storage_type ip_store = DENSE;
  int dr = 0;
  storage_type op_store = DENSE;
  boolean subsets=FALSE;
  boolean midfa=FALSE;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-s")==0)
      subsets = TRUE;
    else if (strcmp(argv[arg],"-midfa")==0)
      midfa = TRUE;
    else if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsareverse();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's') {
        ip_store = SPARSE;
        if (stringlen(argv[arg]) > 1)
          dr = atoi(argv[arg]+1);
      }
      else
        badusage_fsareverse();
    }
    else if (strcmp(argv[arg],"-op")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsareverse();
      if (strcmp(argv[arg],"d")==0)
        op_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store = SPARSE;
      else
        badusage_fsareverse();
    }
    else if (strcmp(argv[arg],"-silent")==0)
      kbm_print_level = 0;
    else if (strcmp(argv[arg],"-v")==0)
      kbm_print_level = 2;
    else if (strcmp(argv[arg],"-vv")==0)
      kbm_print_level = 3;
    else if (strcmp(argv[arg],"-l")==0)
      kbm_large = TRUE;
    else if (strcmp(argv[arg],"-h")==0)
      kbm_huge = TRUE;
    else {
       if (argv[arg][0] == '-')
         badusage_fsareverse();
       if (strcmp(inf,""))
         badusage_fsareverse();
       strcpy(inf,argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf)==0)
    badusage_fsareverse();
  if (subsets && midfa) {
    fprintf(stderr,
       "Sorry, -s and -midfa cannot currently be called together.\n");
    exit(1);
  }

  strcpy(outf,inf);
  if (midfa)
    strcat(outf,".mireverse");
  else
    strcat(outf,".reverse");

  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
    exit(1);
  }
  fsa_read(rfile,&fsain,ip_store,dr,0,TRUE,fsaname);

  strcpy(tempfilename,inf);
  strcat(tempfilename,"temp_reverse_XXX");
  if (midfa)
    fsareverse = fsa_mireverse(&fsain,op_store,TRUE,tempfilename);
  else
    fsareverse = fsa_reverse(&fsain,op_store,TRUE,subsets,tempfilename);
  if (fsareverse==0) exit(1);

  if (subsets) {
    if (kbm_print_level>1)
      printf("  Number of states of fsareverse = %d.\n",
          fsareverse->states->size);
  }
  else if (midfa) {
    if (kbm_print_level>1)
      printf("  Number of states of fsamireverse before minimisation = %d.\n",
          fsareverse->states->size);
    if (midfa_labeled_minimize(fsareverse)== -1) exit(1);
    if (kbm_print_level>1)
      printf("  Number of states of fsamireverse after minimisation = %d.\n",
          fsareverse->states->size);
  }
  else {
    if (kbm_print_level>1)
      printf("  Number of states of fsareverse before minimisation = %d.\n",
          fsareverse->states->size);
    if (fsa_minimize(fsareverse)== -1) exit(1);
    if (kbm_print_level>1)
      printf("  Number of states of fsareverse after minimisation = %d.\n",
          fsareverse->states->size);
  }

  if (midfa)
    strcat(fsaname,"_mireverse");
  else
    strcat(fsaname,"_reverse");
  wfile = fopen(outf,"w");
  fsa_print(wfile,fsareverse,fsaname);
  fclose(wfile);

  if (kbm_print_level>0)
    printf("#Reverse fsa with %d states computed.\n",
            fsareverse->states->size);

  fsa_clear(fsareverse);
  tfree(fsareverse);
  exit(0);
}
void
badusage_fsareverse()
{
    fprintf(stderr,
 "Usage: fsareverse [-s] [-midfa] [-ip d/s[dr]] [-op d/s]\n");
    fprintf(stderr,"                  [-silent] [-v] [-l/-h] filename\n");
    exit(1);
}
