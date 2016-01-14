/* fsamin.c 27/10/94.
 * 25/1/00 added -s option.
 * Minimises a finite state automaton
 * Can either use stdin/stdout or files.
 *
 * SYNOPSIS:  fsamin [-ip d/s] [-op d/s] [-silent] [-v] [-s] [filename]
 *
 * Input is from filename (or stdin if not specified) ,
 *   which should contain an fsa.
 * Output is to filename.min, or stdout.
 *
 * OPTIONS:
 * -ip d/s      input in dense or sparse format - dense is default
 * -op d/s      output in dense or sparse format - default is as in current
 *               value of table->printing_format, in the fsa.
 * -v           verbose
 * -silent      no diagnostics
 * -l/-h        large/huge hash-tables (for big examples)
 * -s           print out the old state - new state correspondence
 *              to stdout after minimization.
 *
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_fsamin();

/* Functions defined in other files used in this file */
void  fsa_read();
int   fsa_minimize();
void  fsa_print();
void  fsa_clear();
int   stringlen();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg;
  fsa testfsa;
  char inf[100],outf[100],fsaname[100];
  storage_type ip_store = DENSE;
  boolean op_format_set = FALSE;
  storage_type op_format = DENSE;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsamin();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        ip_store = SPARSE;
      else
        badusage_fsamin();
    }
    else if (strcmp(argv[arg],"-op")==0) {
      arg++;
      op_format_set=TRUE;
      if (arg >= argc)
        badusage_fsamin();
      if (strcmp(argv[arg],"d")==0)
        op_format = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_format = SPARSE;
      else
        badusage_fsamin();
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
    else if (strcmp(argv[arg],"-s")==0)
      kbm_print_level = 4;
    else {
       if (argv[arg][0] == '-')
         badusage_fsamin();
       if (strcmp(inf,""))
         badusage_fsamin();
       strcpy(inf,argv[arg]);
    }
    arg++;
  }

  if (stringlen(inf)!=0) {
    strcpy(outf,inf);
    strcat(outf,".min");

    if ((rfile = fopen(inf,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
    }
  }
  else
    rfile = stdin;

  fsa_read(rfile,&testfsa,ip_store,0,0,TRUE,fsaname);

  if (stringlen(inf)!=0)
    fclose(rfile);

  if (kbm_print_level>1)
    printf("  #Number of states of fsa before minimisation = %d.\n",
        testfsa.states->size);
  if (fsa_minimize(&testfsa)== -1) exit(1);
  if (kbm_print_level>1)
    printf("  #Number of states of fsa after minimisation = %d.\n",
        testfsa.states->size);

  if (op_format_set)
    testfsa.table->printing_format = op_format;
  strcat(fsaname,"_min");

  if (stringlen(inf)!=0)
    wfile = fopen(outf,"w");
  else
    wfile = stdout;

  fsa_print(wfile,&testfsa,fsaname);

  if (stringlen(inf)!=0)
    fclose(wfile);
  if (wfile!=stdout && kbm_print_level>0)
    printf("#Minimized fsa with %d states computed.\n",testfsa.states->size);

  fsa_clear(&testfsa);
  exit(0);
}
 
void
badusage_fsamin()
{
    fprintf(stderr,
 "Usage: fsamin [-ip d/s] [-op d/s] [-silent] [-v] [-l/-h] [-s] [filename]\n");
    exit(1);
}
