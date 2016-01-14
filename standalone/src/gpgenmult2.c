/* gpgenmult2.c 28/11/94.
 * 8/10/98 large-scale re-organisation.
 * Calculates the general multiplier automaton of a short-lex automatic group,
 * for words in the generators of length 2.
 * This program assumes that kbprog with -wd option, gpwa, gpgenmult
 * and preferably gpcheckmult (or gpmakefsa)  have already been run of G.
 *
 * SYNOPSIS:
 * gpgenmult2 [-ip d/s[dr]] [-op d/s] [-silent] [-v] [-l/-h] [-f] groupname
 *
 * Input is from groupname.gm
 * Output is to groupname.gm2, but under the -f option,
 * the unformatted transition table goes to groupname.gm2_ut.
 *
 * OPTIONS:
 * -ip d/s[dr]	input in dense or sparse format - dense is default
 * -op d/s	output in dense or sparse format - sparse is default
 * -v		verbose
 * -silent	no diagnostics
 * -l/-h	large/huge hash-tables (for big examples)
 * -f           read the transition table repeatedly from file while mimimizing.
 *              this avoids storing the large table, but is a little slower.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_gpgenmult2();

/* Functions defined in other files used in this file */
void  fsa_read();
fsa  *fsa_genmult2();
int   fsa_labeled_minimize();
int   fsa_ip_labeled_minimize();
void  fsa_print();
void  fsa_clear();
int   stringlen();

int 
main (int argc, char *argv[])
{ int arg, i, g1, g2;
  fsa genmult, *genmult2ptr;
  char inf[100], outf[100], fsaname[100], tablefilename[100];
  storage_type ip_store = DENSE;
  int dr = 0;
  storage_type op_store = SPARSE;
  boolean readback = TRUE;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpgenmult2();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's') {
        ip_store = SPARSE;
        if (stringlen(argv[arg]) > 1)
          dr = atoi(argv[arg]+1);
      }
      else
        badusage_gpgenmult2();
    }
    else if (strcmp(argv[arg],"-op")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpgenmult2();
      if (strcmp(argv[arg],"d")==0)
        op_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store = SPARSE;
      else
        badusage_gpgenmult2();
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
    else if (strcmp(argv[arg],"-f")==0)
      readback = FALSE;
    else {
       if (argv[arg][0] == '-')
         badusage_gpgenmult2();
       if (strcmp(inf,"")!=0)
         badusage_gpgenmult2();
       else
         strcpy(inf,argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf)==0)
    badusage_gpgenmult2();
  
  strcpy(tablefilename,inf);
  strcat(tablefilename,".gm2_ut");

  strcpy(outf,inf);
  strcat(outf,".gm2");

  strcat(inf,".gm");

  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
  }
  fsa_read(rfile,&genmult,ip_store,dr,0,TRUE,fsaname);
  fclose(rfile);

  genmult2ptr = fsa_genmult2(&genmult,op_store,TRUE,tablefilename,readback);
  if (genmult2ptr==0) exit(1);

  if (kbm_print_level>1)
    printf("  #Number of states of genmult2 = %d.\n",genmult2ptr->states->size);

  if (readback) {
    if (fsa_labeled_minimize(genmult2ptr)==-1) exit(1);
  }
  else {
    if (fsa_ip_labeled_minimize(genmult2ptr)==-1) exit(1);
  }
  if (kbm_print_level>1)
    printf("  #Number of states of genmult2 after minimization = %d.\n",
             genmult2ptr->states->size);
  base_prefix(fsaname);
  strcat(fsaname,".gm2");
  wfile = fopen(outf,"w");
  fsa_print(wfile,genmult2ptr,fsaname);
  fclose(wfile);

  if (kbm_print_level>0)
    printf("#Generalised length-2 multiplier with %d states computed.\n",
            genmult2ptr->states->size);

  fsa_clear(genmult2ptr);
  tfree(genmult2ptr);
  exit(0);
}
 
void 
badusage_gpgenmult2 (void)
{
    fprintf(stderr,"Usage: \n");
    fprintf(stderr,
"gpgenmult2 [-ip d/s[dr]] [-op d/s] [-silent] [-v] [-l/-h] [-f] groupname.\n");
    exit(1);
}
