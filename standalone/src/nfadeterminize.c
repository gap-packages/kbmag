/* nfadeterminize.c 8/9/97.
 * 25/9/98a - added -s option to output states of reverse automaton
 * as subsets of original state set (without minimizing).
 *
 * determinize an fsa and minimize result.
 *
 * SYNOPSIS:  nfadeterminize [-s] [-op d/s] [-silent] [-v] [-l/-h] [filename]
 * Input is from filename (or stdin if not specified),
 * which should contain a fsa.
 * Output is to filename.determinize or stdout.
 *
 * OPTIONS:
 * -s           output states as subsets of set of staes of input fsa
 *              (and don't minimize the output fsa).
 * -op d/s      output in dense or sparse format - default is as in current
 *               value of table->printing_format, in the fsa.
 *  Note: input must be in sparse format, since input is an nfa.
 * -v           verbose
 * -silent      no diagnostics
 * -l/-h        large/huge hash-tables (for big examples)
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_nfadet();

/* Functions defined in other files used in this file */
void  fsa_read();
fsa  *nfa_determinize();
void  fsa_copy();
void  fsa_print();
void  fsa_clear();
void fsa_minimize();
int	stringlen();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg;
  fsa fsain, *fsadeterminize;
  char inf[100], outf[100], fsaname[100], tempfilename[100];
  storage_type ip_store = SPARSE; int dr = 0; /* cannot be changed */
  storage_type op_store = DENSE;
  boolean subsets=FALSE;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf[0] = '\0';
  outf[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-s")==0)
      subsets = TRUE;
    else if (strcmp(argv[arg],"-op")==0) {
      arg++;
      if (arg >= argc)
        badusage_nfadet();
      if (strcmp(argv[arg],"d")==0)
        op_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store = SPARSE;
      else
        badusage_nfadet();
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
         badusage_nfadet();
       if (strcmp(inf,""))
         badusage_nfadet();
       strcpy(inf,argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf)!=0) {
    strcpy(outf,inf);
    strcat(outf,".determinize");

    if ((rfile = fopen(inf,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
    }
  }
  else
    rfile = stdin;
  fsa_read(rfile,&fsain,ip_store,dr,0,TRUE,fsaname);
  if (stringlen(inf)!=0)
    fclose(rfile);

  if (fsain.flags[DFA]) {
    if (kbm_print_level > 0)
      printf("#Note: Input fsa is already deterministic!\n");
    tmalloc(fsadeterminize,fsa,1);
    fsa_init(fsadeterminize);
    fsa_copy(fsadeterminize,&fsain);
  } else {
    strcpy(tempfilename,inf);
    strcat(tempfilename,"temp_mid_XXX");
    fsadeterminize =
        nfa_determinize(&fsain,op_store,TRUE,TRUE,subsets,tempfilename);
  }

  fsa_clear(&fsain);

  if (subsets) {
    if (kbm_print_level>1)
      printf("  #Number of states of fsadeterminize = %d.\n",
          fsadeterminize->states->size);
  }
  else {
    if (kbm_print_level>1)
     printf("  #Number of states of fsadeterminize before minimisation = %d.\n",
          fsadeterminize->states->size);
    fsa_minimize(fsadeterminize);
    if (kbm_print_level>1)
      printf("  #Number of states of fsadeterminize after minimisation = %d.\n",
        fsadeterminize->states->size)  ;
  }

  strcat(fsaname,"_determinize");
  if (stringlen(inf)!=0)
    wfile = fopen(outf,"w");
  else
    wfile=stdout;
  fsa_print(wfile,fsadeterminize,fsaname);
  if (wfile!=stdout && kbm_print_level>0)
    printf("#\"Determinized\" fsa with %d states computed.\n",
	fsadeterminize->states->size);
  if (stringlen(inf)!=0)
    fclose(wfile);

  fsa_clear(fsadeterminize);
  tfree(fsadeterminize);
  exit(0);
}
 
void
badusage_nfadet()
{
    fprintf(stderr,
    "Usage: nfadeterminize [-s] [-op d/s] [-silent] [-v] [-l/-h] [filename]\n");
    exit(1);
}
