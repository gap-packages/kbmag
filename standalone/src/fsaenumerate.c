/* fsaenumerate.c 16/1/95
 * 25/1/99 added -s option, to print number of accept state
 *          reached by each accepted word.
 * 30/12/98 added -l option, to print number of label of accept state
 *          reached by each accepted word.
 * 22/12/98 - allow input/output from stdin, stdout.
 * 20/3/96 - added "-is n" option, to change the initial state of the fsa to
 * n (useful for coset reduction automata).
 *
 * Enumerates the accepted language of a fsa
 *
 * SYNOPSIS:
 *   fsaenumerate [-is n] [-ip d/s] [-bfs/-dfs] min max [-l/-s] [filename]\n");
 *
 * Input is from stdin or filename, which should contain a fsa.
 * Output is to stdout or filename.enumerate, and contains a list of the
 * accepted words of the finite state automaton with lengths l satisfying
 * min <= l <= max.
 * Note that the integers min and max must be specified.
 *
 * OPTIONS:
 * -is n        change initial state of fsa to n
 * -ip d/s      input in dense or sparse format - dense is default
 * -bfs/-dfs	specifies listing according to breadth-first-search of
 *		depth-first-search, resepctively. The latter is default,
 *		and is somewhat quicker, since the bradth-first-search involves
 *		repeated calls of the procedure, for each individual length.
 * -s           For each accepted word printed, the number of the
 *              accept state reached by that word in the fsa is printed as an
 *              extra component to the word.
 * -l           This only applies if the fsa has labeled states.
 *              For each accepted word printed, the label number of the
 *              accept state reached by that word in the fsa is printed as an
 *              extra component to the word.
 *              This is useful when generating Cayley graphs of groups from
 *              the general multiplier.
 */

#include <stdio.h>
#include <stdlib.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_fsaenumerate();

/* Functions defined in other files used in this file */
void  fsa_read();
int   fsa_enumerate();
void  fsa_clear();
boolean is_int();
int   stringlen();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg, min, max, i, n, rv;
  fsa testfsa;
  char inf[100], outf[100], fsaname[100];
  storage_type ip_store = DENSE;
  int stateno=0;
  boolean labels=FALSE;
  boolean bfs, minset, maxset, putcomma;
  

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  minset = maxset = FALSE;
  bfs = FALSE;
  inf[0] = '\0';
  arg = 1;
  n = 0;
  while (argc > arg) {
    if (strcmp(argv[arg], "-is") == 0) {
      arg++;
      if (arg >= argc)
         badusage_fsaenumerate();
      n = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsaenumerate();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's')
        ip_store = SPARSE;
      else
        badusage_fsaenumerate();
    }
    else if (strcmp(argv[arg],"-dfs")==0)
      bfs = FALSE;
    else if (strcmp(argv[arg],"-bfs")==0)
      bfs = TRUE;
    else if (strcmp(argv[arg],"-l")==0) 
      labels = TRUE;
    else if (strcmp(argv[arg],"-s")==0)
      stateno = 1; 
    else {
       if (argv[arg][0] == '-')
         badusage_fsaenumerate();
       if (strcmp(inf,""))
         badusage_fsaenumerate();
       if (!minset) {
         if (!is_int(argv[arg])) badusage_fsaenumerate();
         min = atoi(argv[arg]);
         minset = TRUE;
       }
       else if (!maxset) {
         if (!is_int(argv[arg])) badusage_fsaenumerate();
         max = atoi(argv[arg]);
         maxset = TRUE;
       }
       else strcpy(inf,argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf)==0)
    rfile=stdin;
  else {
    strcpy(outf,inf);
    strcat(outf,".enumerate");
    if ((rfile = fopen(inf,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
    }
  }
  fsa_read(rfile,&testfsa,ip_store,0,0,TRUE,fsaname);
  if (stringlen(inf))
    fclose(rfile);
  strcat(fsaname,".words");

  if (labels && stateno) {
    fprintf(stderr,"Error: cannot use -s and -l together.\n");
    exit(1);
  }
  if (labels) stateno=2;
  if (n>testfsa.states->size) {
    fprintf(stderr,"Error: specified initial state is too large.\n");
    exit(1);
  }
  if (n>0 && testfsa.num_initial>0) {
    testfsa.initial[1]=n;
    /* This may destroy various properties of the automata */
    testfsa.flags[MINIMIZED]=FALSE;
    testfsa.flags[BFS]=FALSE;
    testfsa.flags[ACCESSIBLE]=FALSE;
    testfsa.flags[TRIM]=FALSE;
  }

  if (stringlen(inf))
    wfile = fopen(outf,"w");
  else
    wfile=stdout;
  fprintf(wfile,"%s := [\n",fsaname);

  putcomma = FALSE;
  if (bfs) {
    for (i=min;i<=max;i++) {
      rv = fsa_enumerate(wfile,&testfsa,i,i,putcomma,stateno);
      if (rv== -1) exit(1);
      putcomma = (boolean)rv || putcomma;
    }
  }
  else {
    rv = fsa_enumerate(wfile,&testfsa,min,max,putcomma,stateno);
    if (rv== -1) exit(1);
  }

  fprintf(wfile,"\n];\n");
  if (stringlen(inf))
    fclose(wfile);

  fsa_clear(&testfsa);
  exit(0);
}
 
void
badusage_fsaenumerate()
{
    fprintf(stderr,
"Usage: fsaenumerate [-is n] [-ip d/s] [-bfs/-dfs] min max [-l/-s] [filename]\n"
);
    exit(1);
}
