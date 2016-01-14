/* gpmimult2.c 10/1/96.
 * 8/10/98 large-scale re-organisation.
 * 16/3/96 - changed command-line syntax to
 * gpmimult [options] groupname [cosname]
 * where cosname defaults to "cos".
 * Calculates a multiple-initial multiplier automaton of a short-lex coset
 * automatic group, for a word in the generators of length 2, using the
 * length-2 general multiple-initial multiplier.
 * This program assumes that kbprogcos with -wd option, gpwacos, gpmigenmult
 * gpmigenmult2 (and preferably gpcheckmult) have already been run of G.
 *
 * SYNOPSIS:
 * gpmimult2 [-ip d/s] [-op d/s] [-silent] [-v] [-l/-h] [-pref prefix] g1 g2
 *           groupname [cosname]
 *
 * Input is from groupname.cosname.migm2
 * and individual 2-generator multipliers to groupname.cosname.mi_g1_g2,
 * where  g1  and  g2  are the generator numbers. 
 *
 * OPTIONS:
 * -ip d/s	input in dense or sparse format - sparse is default
 * -op d/s	output in dense or sparse format - sparse is default
 * -v		verbose
 * -silent	no diagnostics
 * -l/-h	large/huge hash-tables (for big examples)
 * -pref prefix Use the string 'prefix' as prefix for subgroup generators
 *              Default is "_x". You MUST use the same prefix in all
 *              runs of gpmigenmult2, gpmimakemult and gpmimakemult2.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_gpmimult2();

/* Functions defined in other files used in this file */
void  fsa_read();
int   fsa_mimakemult2();
int   mimult_minimize();
void  fsa_print();
void  fsa_clear();
int   stringlen();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg, i, g1, g2;
  fsa migm2;
  char gpname[100], inf[100], outf[100], fsaname[100], prefix[16];
  storage_type ip_store = SPARSE;
  boolean op_format_set = FALSE;
  storage_type op_format = SPARSE;
  boolean seengpname, seencosname;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf[0] = '\0';
  strcpy(prefix,"_x");
  g1 = g2 = 0;
  arg = 1;
  seengpname=seencosname=FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpmimult2();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        ip_store = SPARSE;
      else
        badusage_gpmimult2();
    }
    else if (strcmp(argv[arg],"-op")==0) {
      op_format_set = TRUE;
      arg++;
      if (arg >= argc)
        badusage_gpmimult2();
      if (strcmp(argv[arg],"d")==0)
        op_format = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_format = SPARSE;
      else
        badusage_gpmimult2();
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
        badusage_gpmimult2();
      strcpy(prefix,argv[arg]);
    }
    else {
      if (argv[arg][0] == '-')
        badusage_gpmimult2();
      if (g1==0 && isdigit(argv[arg][0]))
        g1 = atoi(argv[arg]);
      else if (g2==0 && isdigit(argv[arg][0]))
        g2 = atoi(argv[arg]);
      else if (!seengpname) {
        seengpname=TRUE;
        strcpy(gpname,argv[arg]);
      }
      else if (!seencosname) {
        seencosname=TRUE;
        sprintf(inf,"%s.%s",gpname,argv[arg]);
      }
      else
        badusage_gpmimult2();
    }
    arg++;
  }
  if (g1==0 || g2==0 || !seengpname)
    badusage_gpmimult2();
  if (!seencosname)
    sprintf(inf,"%s.cos",gpname);
  sprintf(outf,"%s.mim%d_%d",inf,g1,g2);
  strcat(inf,".migm2");

  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
  }
  fsa_read(rfile,&migm2,ip_store,0,0,TRUE,fsaname);

  if (kbm_print_level>1)
    printf("  #Number of states of migm2 = %d.\n",migm2.states->size);

  base_prefix(fsaname);
  sprintf(fsaname+stringlen(fsaname),".m%d_%d",g1,g2);
  if (fsa_mimakemult2(&migm2,g1,g2,prefix)==-1) exit(1);
  if (mimult_minimize(&migm2)==-1) exit(1);
  if (kbm_print_level>0)
    printf("#Length-2 multiplier with %d states computed.\n",
        migm2.states->size);

  if (op_format_set)
    migm2.table->printing_format = op_format;

  wfile = fopen(outf,"w");
  fsa_print(wfile,&migm2,fsaname);
  fclose(wfile);

  fsa_clear(&migm2);
  exit(0);
}
 
void
badusage_gpmimult2()
{
    fprintf(stderr,
      "Usage: gpmimult2 [-ip d/s] [-op d/s] [-silent] [-v] [-l/-h]\n");
    fprintf(stderr,
    "\t\t[-pref prefix]  g1 g2 groupname [cosname].\n");
    exit(1);
}
