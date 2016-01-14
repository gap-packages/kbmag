/* gpmimult.c 31/10/95.
 * 8/10/98 large-scale re-organisation.
 * 16/3/96 - changed command-line syntax to
 * gpmimult [options] groupname [cosname]
 * where cosname defaults to "cos".
 * This simply calculates minimizes and outputs all multiple-initial
 * multipliers for a short-lex coset automatic group, using the
 * general multiple-initial state multiplier automaton.
 * It assumes that kbprog with -wd option, gpwacos, gpmigenmult
 * (and preferably gpcheckmult)  have already been run of G.
 *
 * SYNOPSIS:
 * gpmimult [-ip d/s] [-op d/s] [-silent] [-v] [-l/-h] [-pref prefix]
 *						  groupname [cosname]
 *
 * Input is from groupname.cosname.migm
 * Output is to groupname.cosname.mim'i' for each generator number i.
 *
 * OPTIONS:
 * -ip d/s	input in dense or sparse format - sparse is default
 * -op d/s	output in dense or sparse format - sparse is default
 * -v		verbose
 * -silent	no diagnostics
 * -l/-h	large/huge hash-tables (for big examples)
 * -pref prefix	Use the string 'prefix' as prefix for subgroup generators
 *              Default is "_x". You MUST use the same prefix in all
 *              runs of gpmigenmult2, gpmimakemult and gpmimakemult2.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_gpmimult();

/* Functions defined in other files used in this file */
void  fsa_read();
int   fsa_mimakemult();
int   mimult_minimize();
void  fsa_print();
void  fsa_clear();
int   stringlen();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg, g, ngens;
  fsa genmult, *mimult;
  char gpname[100], cosgpname[100], inf[100], outf[100], fsaname[100],
       prefix[16];
  storage_type ip_store = SPARSE;
  boolean op_format_set = FALSE;
  storage_type op_format = SPARSE;
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
        badusage_gpmimult();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        ip_store = SPARSE;
      else
        badusage_gpmimult();
    }
    else if (strcmp(argv[arg],"-op")==0) {
      op_format_set = TRUE;
      arg++;
      if (arg >= argc)
        badusage_gpmimult();
      if (strcmp(argv[arg],"d")==0)
        op_format = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_format = SPARSE;
      else
        badusage_gpmimult();
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
        badusage_gpmimult();
      strcpy(prefix,argv[arg]);
    }
    else if (argv[arg][0] == '-')
      badusage_gpmimult();
    else if (!seengpname) {
      seengpname=TRUE;
      strcpy(gpname,argv[arg]);
    }
    else if (!seencosname) {
      seencosname=TRUE;
      sprintf(cosgpname,"%s.%s",gpname,argv[arg]);
    }
    else
      badusage_gpmimult();
    arg++;
  }
  if (!seengpname)
    badusage_gpmimult();
  if (!seencosname)
    sprintf(cosgpname,"%s.cos",gpname);
  
  strcpy(inf,cosgpname);
  strcat(inf,".migm");

  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
  }
  fsa_read(rfile,&genmult,ip_store,0,0,TRUE,fsaname);

  tmalloc(mimult,fsa,1);
  ngens = genmult.states->labels->alphabet_size;

  for (g=0;g<=ngens;g++) {
 /* Form multiplier number g */
    fsa_copy(mimult,&genmult);
    if (fsa_mimakemult(mimult,g,prefix)==-1) exit(1);
    if (mimult_minimize(mimult)==-1) exit(1);

    base_prefix(fsaname);
    sprintf(fsaname+stringlen(fsaname),".mim%d",g);
    sprintf(outf,"%s.mim%d",cosgpname,g);

    if (op_format_set)
      mimult->table->printing_format = op_format;
    wfile = fopen(outf,"w");
    fsa_print(wfile,mimult,fsaname);
    fclose(wfile);

    if (kbm_print_level>0)
      printf(
       "#Multiplier number %d with %d states computed.\n",
        g,mimult->states->size);
    fsa_clear(mimult);
  }

  fsa_clear(&genmult);
  tfree(mimult);
  exit(0);
}
 
void
badusage_gpmimult()
{
    fprintf(stderr,
      "Usage: gpmimult [-ip d/s] [-op d/s] [-silent] [-v] [-l/-h]\n");
    fprintf(stderr,
    "\t\t[-pref prefix]  groupname [cosname].\n");
    exit(1);
}
