/* gpmigenmult2.c 30/10/95.
 * 8/10/98 large-scale re-organisation.
 * 16/3/96 - changed command-line syntax to
 * gpmigenmult2 [options] groupname [cosname]
 * where cosname defaults to "cos".
 * Calculates the general multiplier with multiple initial states of a
 * short-lex coset automatic group, for words in the generators of length 2.
 * This program assumes that kbprogcos with -wd option and gpmimakefsa
 * have already been run of G.
 *
 * SYNOPSIS:
 * gpmigenmult2 [-ip d/s[dr]] [-op d/s] [-silent] [-v] [-l/-h] 
 *              [-pref prefix] groupname [cosname]
 *
 * Input is from groupname.cosname.migm
 * Output is to groupname.cosname.gm2.
 *
 * OPTIONS:
 * -ip d/s[dr]	input in dense or sparse format - dense is default
 * -op d/s	output in dense or sparse format - sparse is default
 * -v		verbose
 * -silent	no diagnostics
 * -l/-h	large/huge hash-tables (for big examples)
 * -pref prefix Use the string 'prefix' as prefix for subgroup generators
 *              Default is "_x". You MUST use the same prefix in all
 *              runs of gpmigenmult2, gpmimakemult and gpmimakemult2.
 *
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_gpmigenmult2();

/* Functions defined in other files used in this file */
void  fsa_read();
fsa   *fsa_migm2();
int   midfa_labeled_minimize();
void  fsa_print();
void  fsa_clear();
int   stringlen();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg, i, g1, g2;
  fsa migenmult, *migm2ptr;
  char gpname[100], inf[100], outf[100], fsaname[100], tablefilename[100],
       prefix[16];
  storage_type ip_store = DENSE;
  int dr = 0;
  storage_type op_store = SPARSE;
  boolean readback = TRUE;
  boolean seengpname, seencosname;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  strcpy(prefix,"_x");
  arg = 1;
  seengpname=seencosname=FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpmigenmult2();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's') {
        ip_store = SPARSE;
        if (stringlen(argv[arg]) > 1)
          dr = atoi(argv[arg]+1);
      }
      else
        badusage_gpmigenmult2();
    }
    else if (strcmp(argv[arg],"-op")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpmigenmult2();
      if (strcmp(argv[arg],"d")==0)
        op_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store = SPARSE;
      else
        badusage_gpmigenmult2();
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
    else if (strcmp(argv[arg],"-pref")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpmigenmult2();
      strcpy(prefix,argv[arg]);
    }
    else if (strcmp(argv[arg],"-f")==0){
      readback = FALSE;
      fprintf(stderr,"Sorry - readback option not yet available.\n");
      exit(1);
    }
    else if (argv[arg][0] == '-')
      badusage_gpmigenmult2();
    else if (!seengpname) {
      seengpname=TRUE;
      strcpy(gpname,argv[arg]);
    }
    else if (!seencosname) {
      seencosname=TRUE;
      sprintf(inf,"%s.%s",gpname,argv[arg]);
    }
    else
      badusage_gpmigenmult2();
    arg++;
  }
  if (!seengpname)
    badusage_gpmigenmult2();
  if (!seencosname)
    sprintf(inf,"%s.cos",gpname);
  
  strcpy(tablefilename,inf);
  strcat(tablefilename,".migm2_ut");

  strcpy(outf,inf);
  strcat(outf,".migm2");

  strcat(inf,".migm");

  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
  }
  fsa_read(rfile,&migenmult,ip_store,dr,0,TRUE,fsaname);
  fclose(rfile);

  migm2ptr =
     fsa_migm2(&migenmult,op_store,TRUE,tablefilename,readback,prefix);
  if (migm2ptr==0) exit(1);

  if (kbm_print_level>1)
    printf("  #Number of states of migenmult2 = %d.\n",migm2ptr->states->size);

  if (readback){
    if (midfa_labeled_minimize(migm2ptr)==-1) exit(1);
  }
  if (kbm_print_level>1)
    printf("  #Number of states of migenmult2 after minimization = %d.\n",
             migm2ptr->states->size);
  base_prefix(fsaname);
  strcat(fsaname,".gm2");
  wfile = fopen(outf,"w");
  fsa_print(wfile,migm2ptr,fsaname);
  fclose(wfile);

  if (kbm_print_level>0)
    printf("#Generalised length-2 multiplier with %d states computed.\n",
            migm2ptr->states->size);

  fsa_clear(migm2ptr);
  tfree(migm2ptr);
  exit(0);
}
 
void
badusage_gpmigenmult2()
{
    fprintf(stderr,"Usage: \n");
    fprintf(stderr,
      "gpmimigenmult2 [-ip d/s[dr]] [-op d/s] [-silent] [-v] [-l/-h]\n");
    fprintf(stderr,"		[-pref prefix] groupname [cosname].\n");
    exit(1);
}
