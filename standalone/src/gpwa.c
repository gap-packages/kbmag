/* gpwa.c 8/11/94.
 * 15/3/96 amalgamated with gpwacos, to compute word-acceptors for coset
 * automatic structures.
 * Syntax for this is gpwa -cos groupname [cosname]
 * cosname defaults to "cos".
 *
 * Calculates word acceptor of an automatic group G.
 * The input is a word-difference fsa for the group
 * (from a run of kbprog with the -wd option).
 *
 * SYNOPSIS:  gpwa [-op d/s] [-silent] [-v] [-l/-h] [-diff1/-diff2]
 *					[-cos] groupname [cosname]
 *
 * Input is from groupname.diff1 or groupname.diff2
 * or, if -cos, from groupname.cosname.midiff1 or groupname.cosname.midiff2
 * Output is to groupname.wa or groupname.cosname.wa
 *
 * OPTIONS:
 * -cos		Word-acceptor for coset automatic structure
 * -op d/s	output in dense or sparse format - dense is default
 * -v		verbose
 * -silent	no diagnostics
 * -l/-h	large/huge hash-tables (for big examples)
 * -diff1/diff2	take input from groupname.(mi)diff1 or groupname.(mi)diff2
 *		((mi)diff2 is default). Latter needs more space and is
 *		slower, but can sometimes save time later.
 * 
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_gpwa();

/* Functions defined in other files used in this file */
void  fsa_read();
fsa  *fsa_wa();
fsa  *fsa_wa_cos();
void  fsa_minimize();
void  fsa_print();
void  fsa_clear();
int   stringlen();

int 
main (int argc, char *argv[])
{ int arg;
  fsa *fsawd, *gpwa;
  char gpname[100], cosgpname[100], inf[100], outf[100],
       fsaname[100], tempfilename[100];
  storage_type op_store = DENSE;
  boolean diff1_ip, cosets, seengpname, seencosname;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf[0] = '\0';
  arg = 1;
  diff1_ip=cosets=seengpname=seencosname=FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg],"-cos")==0)
      cosets=TRUE;
    else if (strcmp(argv[arg],"-op")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpwa();
      if (strcmp(argv[arg],"d")==0)
        op_store=DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store=SPARSE;
      else
        badusage_gpwa();
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
    else if (strcmp(argv[arg],"-diff1")==0)
      diff1_ip = TRUE;
    else if (strcmp(argv[arg],"-diff2")==0)
      diff1_ip = FALSE;
    else if (argv[arg][0] == '-')
      badusage_gpwa();
    else if (!seengpname) {
      seengpname=TRUE;
      strcpy(gpname,argv[arg]);
    }
    else if (!seencosname) {
      seencosname=TRUE;
      sprintf(cosgpname,"%s.%s",gpname,argv[arg]);
    }
    else
      badusage_gpwa();
    arg++;
  }
  if (!seengpname)
    badusage_gpwa();
  if (cosets && !seencosname)
    sprintf(cosgpname,"%s.cos",gpname);

  if (cosets) strcpy(inf,cosgpname);
  else strcpy(inf,gpname);

  strcpy(outf,inf);
  strcat(outf,".wa");

  strcpy(tempfilename,inf);
  strcat(tempfilename,"temp_wa_XXX");

  if (diff1_ip)
    {if (cosets) strcat(inf,".midiff1"); else strcat(inf,".diff1");}
  else
    {if (cosets) strcat(inf,".midiff2"); else strcat(inf,".diff2");}

  tmalloc(fsawd,fsa,1);

/* We always use dense format for the word-difference machine -
 * this is much faster, and the machine is usually not too big.
 */
  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
    exit(1);
  }
  fsa_read(rfile,fsawd,DENSE,0,0,TRUE,fsaname);
  fclose(rfile);

  gpwa = cosets ? fsa_wa_cos(fsawd,op_store,TRUE,tempfilename) :
                  fsa_wa(fsawd,op_store,TRUE,tempfilename);
  tfree(fsawd);

  if (kbm_print_level>1)
    printf("  #Number of states of gpwa before minimisation = %d.\n",
        gpwa->states->size);
  fsa_minimize(gpwa);
  if (kbm_print_level>1)
    printf("  #Number of states of gpwa after minimisation = %d.\n",
        gpwa->states->size);

  base_prefix(fsaname);
  strcat(fsaname,".wa");
  wfile = fopen(outf,"w");
  fsa_print(wfile,gpwa,fsaname);
  fclose(wfile);

  if (kbm_print_level>0)
    printf("#Word-acceptor with %d states computed.\n",gpwa->states->size);

  fsa_clear(gpwa);
  tfree(gpwa);
  exit(0);
}

void 
badusage_gpwa (void)
{
    fprintf(stderr,
    "Usage: gpwa [-op d/s] [-silent] [-v] [-l/-h] [-diff1/-diff2]\n");
    fprintf(stderr,"\t\t[-cos] groupname[ -cosname]\n");
    exit(1);
}
