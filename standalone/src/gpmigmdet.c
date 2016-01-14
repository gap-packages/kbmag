/* gpmigmdet.c 23/10/95.
 * 6/8/98 large scale reorganisation to omit globals, etc.
 * 16/3/96 - changed command-line syntax to
 * gpmigmdet [options] groupname [cosname]
 * where cosname defaults to "cos".
 * determinizes "migm" machine (which has multiple start-states)
 * - and makes the resulting determistic generalised multiplier "gm"
 * machine.
 *
 *
 * SYNOPSIS:  gpmigmdet [-op d/s] [-silent] [-v] [-l/-h]  groupname [cosname]
 * Input is from groupname.cosname.migm,
 * Output is to groupname.cosname.gm.
 *
 * OPTIONS:
 * -op d/s      output in dense or sparse format - default is sparse
 * -v           verbose
 * -silent      no diagnostics
 * -l/-h        large/huge hash-tables (for big examples)
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage();

/* Functions defined in other files used in this file */
void  fsa_read();
fsa  *migm_determinize();
void  fsa_print();
void  fsa_clear();
int   fsa_labeled_minimize();
int   stringlen();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg;
  fsa fsain, *gpmigmdet;
  char gpname[100], inf[100], outf[100], fsaname[100],
       tempfilename[100];
  storage_type ip_store = DENSE;
  int dr = 0;
  storage_type op_store = SPARSE;
  boolean seengpname, seencosname;


  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  arg = 1;
  seengpname=seencosname=FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg],"-op")==0) {
      arg++;
      if (arg >= argc)
        badusage();
      if (strcmp(argv[arg],"d")==0)
        op_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store = SPARSE;
      else
        badusage();
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
    else if (argv[arg][0] == '-')
      badusage();
    else if (!seengpname) {
      seengpname=TRUE;
      strcpy(gpname,argv[arg]);
    }
    else if (!seencosname) {
      seencosname=TRUE;
      sprintf(inf,"%s.%s",gpname,argv[arg]);
    }
    else
      badusage();
    arg++;
  }
  if (!seengpname)
    badusage();
  if (!seencosname)
    sprintf(inf,"%s.cos",gpname);
  strcpy(outf,inf);
  strcat(inf,".migm");
  strcat(outf,".gm");

  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
    exit(1);
  }
  fsa_read(rfile,&fsain,ip_store,dr,0,TRUE,fsaname);
  fclose(rfile);

  strcpy(tempfilename,inf);
  strcat(tempfilename,"temp_mid_XXX");
  gpmigmdet = migm_determinize(&fsain,op_store,TRUE,tempfilename);
  if (gpmigmdet==0) exit(1);

  if (kbm_print_level>1)
   printf("  #Number of states of gpmigmdet before minimisation = %d.\n",
        gpmigmdet->states->size);
  if (fsa_labeled_minimize(gpmigmdet)== -1) exit(1);
  if (kbm_print_level>1)
    printf(
      "  #Number of states of gpmigmdet after minimisation = %d.\n",
        gpmigmdet->states->size);

  strcat(fsaname,"d");
  wfile = fopen(outf,"w");
  fsa_print(wfile,gpmigmdet,fsaname);
  fclose(wfile);
  if (kbm_print_level>0)
    printf("#\"Determinized\" fsa with %d states computed.\n",
	gpmigmdet->states->size);

  fsa_clear(gpmigmdet);
  tfree(gpmigmdet);
  exit(0);
}
 
void
badusage()
{
    fprintf(stderr,
    "Usage: gpmigmdet [-diff1/-diff2/-diff1c] [-op d/s]\n");
    fprintf(stderr,
   "\t\t    [-silent] [-v] [-l/-h] groupname\n");
    exit(1);
}
