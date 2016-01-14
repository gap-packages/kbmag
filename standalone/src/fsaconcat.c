/* fsaconcat.c 9/2/99.
 * calculates concatenation of two finite state automata
 *
 * SYNOPSIS:  fsaconcat [-ip d/s[dr]] [-op d/s] [-silent] [-v]
                filename1 filename2 outfilename
 *
 * Input is from filename1 concat filename2, which should contain fsa's.
 * Output is to outfilename
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

void  badusage_fsaconcat();

/* Functions defined in other files used in this file */
void  fsa_read();
fsa  *fsa_concat();
fsa  *nfa_determinize();
void  fsa_print();
void  fsa_clear();
int   stringlen();
int   fsa_minimize();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg;
  fsa fsa1, fsa2, *fsaconcatnd, *fsaconcat;
  char inf1[100], inf2[100], outf[100], fsaname1[100], fsaname2[100],
       tempfilename[100];
  storage_type ip_store = DENSE;
  int dr = 0;
  storage_type op_store = DENSE;


  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf1[0] = '\0';
  inf2[0] = '\0';
  outf[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsaconcat();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's') {
        ip_store = SPARSE;
        if (stringlen(argv[arg]) > 1)
          dr = atoi(argv[arg]+1);
      }
      else
        badusage_fsaconcat();
    }
    else if (strcmp(argv[arg],"-op")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsaconcat();
      if (strcmp(argv[arg],"d")==0)
        op_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store = SPARSE;
      else
        badusage_fsaconcat();
    }
    else if (strcmp(argv[arg],"-silent")==0)
      kbm_print_level = 0;
    else if (strcmp(argv[arg],"-v")==0)
      kbm_print_level = 2;
    else if (strcmp(argv[arg],"-vv")==0)
      kbm_print_level = 3;
    else {
       if (argv[arg][0] == '-')
         badusage_fsaconcat();
       if (strcmp(outf,""))
         badusage_fsaconcat();
       if (strcmp(inf1,"")==0)
         strcpy(inf1,argv[arg]);
       else if (strcmp(inf2,"")==0)
         strcpy(inf2,argv[arg]);
       else
         strcpy(outf,argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf1)==0 || stringlen(inf1)==0 || stringlen(outf)==0)
    badusage_fsaconcat();

  if ((rfile = fopen(inf1,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf1);
    exit(1);
  }
  fsa_read(rfile,&fsa1,ip_store,dr,0,TRUE,fsaname1);
  fclose(rfile);

  if ((rfile = fopen(inf2,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf2);
    exit(1);
  }
  fsa_read(rfile,&fsa2,ip_store,dr,0,TRUE,fsaname2);
  fclose(rfile);
  
  fsaconcatnd = fsa_concat(&fsa1,&fsa2,TRUE);
  if (fsaconcatnd==0) exit(1);


  if (fsaconcatnd->flags[NFA]){
    strcpy(tempfilename,inf1);
    strcat(tempfilename,"temp_mid_XXX");
    if (kbm_print_level>1)
      printf("  #Number of states of fsaconcat before determinimization = %d.\n",
        fsaconcatnd->states->size);
    fsaconcat =
        nfa_determinize(fsaconcatnd,op_store,TRUE,TRUE,FALSE,tempfilename);
    if (fsaconcat==0) exit(1);
    tfree(fsaconcatnd);
  }
  else {
    fsaconcat = fsaconcatnd;
    fsaconcat->table->printing_format = op_store;
  }
  if (kbm_print_level>1)
    printf("  #Number of states of fsaconcat before minimization = %d.\n",
      fsaconcat->states->size);
  if (fsa_minimize(fsaconcat)== -1) exit(1);
  if (kbm_print_level>1)
    printf("  #Number of states of fsaconcat after minimization = %d.\n",
      fsaconcat->states->size);

  base_prefix(fsaname1);
  strcat(fsaname1,"_concat");
  wfile = fopen(outf,"w");
  fsa_print(wfile,fsaconcat,fsaname1);
  fclose(wfile);

  if (kbm_print_level>0)
    printf(
   "#\"Concatenated\" fsa with %d states computed.\n",fsaconcat->states->size);

  fsa_clear(fsaconcat);
  tfree(fsaconcat);

  exit(0);
}
 
void
badusage_fsaconcat()
{
    fprintf(stderr,
      "Usage: fsaconcat [-ip d/s[dr]] [-op d/s] [-silent] [-v]\n");
    fprintf(stderr,
      "       filename1 filename2 outfilename\n");
    exit(1);
}
