/* fsaconcat.c 9/2/99.
 * calculates starenation of two finite state automata
 *
 * SYNOPSIS: 
 *      fsastar [-ip d/s[dr]] [-op d/s] [-silent] [-v] filename
 *
 * Input is from filename, which should contain an fsa.
 * Output is to filename.star.
 *
 * OPTIONS:
 * -ip d/s[dr]  input in dense or sparse format - dense is default
 * -op d/s      output in dense or sparse format - default is as in current
 *               value of table->printing_format, in the fsa.
 * -v           verbose
 * -silent      no diagnostics
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_fsastar();

/* Functions defined in other files used in this file */
void  fsa_read();
fsa  *fsa_star();
fsa  *nfa_determinize();
void  fsa_print();
void  fsa_clear();
int   stringlen();
int   fsa_minimize();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg;
  fsa fsain, *fsastarnd, *fsastar;
  char inf[100], outf[100], fsaname[100], tempfilename[100];
  storage_type ip_store = DENSE;
  int dr = 0;
  storage_type op_store = DENSE;


  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsastar();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's') {
        ip_store = SPARSE;
        if (stringlen(argv[arg]) > 1)
          dr = atoi(argv[arg]+1);
      }
      else
        badusage_fsastar();
    }
    else if (strcmp(argv[arg],"-op")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsastar();
      if (strcmp(argv[arg],"d")==0)
        op_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store = SPARSE;
      else
        badusage_fsastar();
    }
    else if (strcmp(argv[arg],"-silent")==0)
      kbm_print_level = 0;
    else if (strcmp(argv[arg],"-v")==0)
      kbm_print_level = 2;
    else if (strcmp(argv[arg],"-vv")==0)
      kbm_print_level = 3;
    else {
       if (argv[arg][0] == '-')
         badusage_fsastar();
       if (strcmp(inf,""))
         badusage_fsastar();
       strcpy(inf,argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf)==0)
    badusage_fsastar();
  strcpy(outf,inf);
  strcat(outf,".star");

  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
    exit(1);
  }
  fsa_read(rfile,&fsain,ip_store,dr,0,TRUE,fsaname);
  fclose(rfile);
  
  fsastarnd = fsa_star(&fsain,TRUE);
  if (fsastarnd==0) exit(1);


  if (fsastarnd->flags[NFA]){
    strcpy(tempfilename,inf);
    strcat(tempfilename,"temp_mid_XXX");
    if (kbm_print_level>1)
      printf("  #Number of states of fsastar before determinimization = %d.\n",
        fsastarnd->states->size);
    fsastar =
        nfa_determinize(fsastarnd,op_store,TRUE,TRUE,FALSE,tempfilename);
    if (fsastar==0) exit(1);
    tfree(fsastarnd);
  }
  else {
    fsastar = fsastarnd;
    fsastar->table->printing_format = op_store;
  }
  if (kbm_print_level>1)
    printf("  #Number of states of fsastar before minimization = %d.\n",
      fsastar->states->size);
  if (fsa_minimize(fsastar)== -1) exit(1);
  if (kbm_print_level>1)
    printf("  #Number of states of fsastar after minimization = %d.\n",
      fsastar->states->size);

  strcat(fsaname,"_star");
  wfile = fopen(outf,"w");
  fsa_print(wfile,fsastar,fsaname);
  fclose(wfile);

  if (kbm_print_level>0)
    printf(
   "#\"Starred\" fsa with %d states computed.\n",fsastar->states->size);

  fsa_clear(fsastar);
  tfree(fsastar);

  exit(0);
}
 
void
badusage_fsastar()
{
    fprintf(stderr,
      "Usage: fsastar [-ip d/s[dr]] [-op d/s] [-silent] [-v] filename\n");
    exit(1);
}
