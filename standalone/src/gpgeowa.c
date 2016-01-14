/* gpgeowa.c 15/4/96.
 * 28/10/98 -n option: output a new 2-variable automaton near_geopairs
 * together with associated difference-machine near_geodiff,
 * which accepts all pairs of geodesics which end at distance at most
 * one apart. This is formed by composing with the generalised
 * multiplier.
 * 29/9/98 large-scale re-organisation. Abolish almost all global variables
 *        and make them components of the rws structure.
 *
 * 5/2/98 change generators from type char to type `gen'.
 * SYNOPSIS:
 * gpgeowa [-op1 d/s] [-op2 d/s] [-silent] [-v] [-l/-h] [-f] [-diff1/-diff2]
 *         [-me maxeqns] [-mwd maxwdiffs] [-n] groupname
 *
 * Input is from groupname.wa and groupname.diff2 (or groupname.diff1)
 * Output is to groupname.geowa, groupname.geodiff and groupname.geopairs
 * Also, a temporary updated diff file for geodesic reduction to
 * shortlex word representative will be output to groupname.tdiff.
 *
 * OPTIONS:
 * -op1 d/s	output of geowa machine in dense or sparse format -
 *              dense is default
 * -op2 d/s	output of geodiff and geopairs machines in dense or sparse
 *		format - sparse is default
 * -v		verbose
 * -silent	no diagnostics
 * -l/-h	large/huge hash-tables (for big examples)
 * -f           read the transition table repeatedly from file while mimimizing.
 *              this avoids storing the large table, but is a little slower.
 * -diff1/diff2 take input from groupname.diff1 or groupname.diff2
 *              (diff2 is default). Latter is usually better.
 * -me  maxeqns  Abort the geodesic word-acceptor checking process after finding
 * 		maxeqns offending words w -  default is MAXEQNS
 * -mwd maxwdiffs
 *              At most maxwdiffs word-differences possible in tdiff machine.
 * -n		output a new 2-variable automaton near_geopairs
 *              together with associated difference-machine near_geodiff,
 *
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"
#define MAXEQNS 512
#define MAXWDIFFS 4096

static FILE *rfile, *wfile;

void  badusage_gpgeowa();
int  (*reduce_word)();

/* Functions defined in other files used in this file */
void  fsa_read();
fsa  *fsa_geopairs();
int  fsa_checkgeowa();
fsa  *fsa_composite();
fsa  *fsa_exists();
fsa  *fsa_diff();
boolean fsa_equal();
void  fsa_copy();
void  fsa_print();
int  fsa_minimize();
int  fsa_ip_minimize();
int  fsa_swap_coords();
void  fsa_clear();
int  diff_reduce();
int  make_full_wd_fsa();
int add_wd_fsa();
int   calculate_inverses();
int fsa_table_dptr_init();
int stringlen();
int genstrlen();
void genstrcpy();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg, i, ct, ngens;
  char inf1[100], inf2[100], inf3[100],
       outf1[100], outf2[100], outf3[100], outf4[100], outf5[100], outf6[100],
       fsaname[100], tempfilename[100];
  int maxeqns, maxwdiffs, numeqns, old_ndiff, *inv;
  fsa  temp, *waptr, *geowaptr, *geodiffptr, *tdiffptr,
       *gmptr, *gpp, *geopairsptr, *tgpp;
  reduction_equation *eqnptr;
  reduction_struct rs_wd;
  storage_type op_store1 = DENSE;
  storage_type op_store2 = SPARSE;
  boolean diff1_ip=FALSE, readback = TRUE;
  boolean near_machine=FALSE;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  maxeqns = MAXEQNS;
  maxwdiffs = MAXWDIFFS;
  inf1[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-op1")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpgeowa();
      if (strcmp(argv[arg],"d")==0)
        op_store1 = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store1 = SPARSE;
      else
        badusage_gpgeowa();
    }
    else if (strcmp(argv[arg],"-op2")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpgeowa();
      if (strcmp(argv[arg],"d")==0)
        op_store2 = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store2 = SPARSE;
      else
        badusage_gpgeowa();
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
    else if (strcmp(argv[arg],"-diff1")==0)
      diff1_ip = TRUE;
    else if (strcmp(argv[arg],"-diff2")==0)
      diff1_ip = FALSE;
    else if (strcmp(argv[arg],"-n")==0)
      near_machine = TRUE;
    else if (strcmp(argv[arg],"-me")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpgeowa();
      maxeqns = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg],"-mwd")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpgeowa();
      maxwdiffs = atoi(argv[arg]);
    }
    else {
       if (argv[arg][0] == '-')
         badusage_gpgeowa();
       if (strcmp(inf1,"")!=0)
         badusage_gpgeowa();
       else
         strcpy(inf1,argv[arg]);
    }
    arg++;
  }
  
  if (stringlen(inf1)==0)
    badusage_gpgeowa();

  if (diff1_ip) {
   /* We need to copy the diff1 machine to the file groupname.tdiff  */
    strcpy(inf2,inf1);
    strcat(inf2,".diff1");
    if ((rfile = fopen(inf2,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf2);
      exit(1);
    }
    fsa_read(rfile,&temp,DENSE,0,0,TRUE,fsaname);
    fclose(rfile);
    strcpy(outf4,inf1);
    strcat(outf4,".tdiff");
    base_prefix(fsaname);
    strcat(fsaname,".tdiff");
    wfile = fopen(outf4,"w");
    fsa_print(wfile,&temp,fsaname);
    fclose(wfile);
  }

  tmalloc(eqnptr,reduction_equation,maxeqns);

  strcpy(tempfilename,inf1);
  strcat(tempfilename,"temp_triples_XXX");

  strcpy(inf2,inf1);
  strcat(inf2,".diff2");
  strcpy(inf3,inf1);
  strcat(inf3,".gm");

  strcpy(outf1,inf1);
  strcat(outf1,".geowa");
  strcpy(outf2,inf1);
  strcat(outf2,".geopairs");
  strcpy(outf3,inf1);
  strcat(outf3,".geodiff");
  strcpy(outf4,inf1);
  strcat(outf4,".tdiff");
  strcpy(outf5,inf1);
  strcat(outf5,".near_geopairs");
  strcpy(outf6,inf1);
  strcat(outf6,".near_geodiff");

  strcat(inf1,".wa");

/* First read in the second-word difference machine for word-reduction */
  tmalloc(rs_wd.wd_fsa,fsa,1);
  if ((rfile = fopen(inf2,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf2);
    exit(1);
  }
  fsa_read(rfile,rs_wd.wd_fsa,DENSE,0,0,TRUE,fsaname);
  fclose(rfile);
  ngens = rs_wd.wd_fsa->alphabet->base->size;
  if (fsa_table_dptr_init(rs_wd.wd_fsa)==-1) exit(1);
  reduce_word=diff_reduce;

  if (!diff1_ip) {
/* Write this fsa to  the temporary file as first approximation to *tdiffptr */
    base_prefix(fsaname);
    strcat(fsaname,".tdiff");
    wfile = fopen(outf4,"w");
    fsa_print(wfile,rs_wd.wd_fsa,fsaname);
    fclose(wfile);
  }

  tmalloc(waptr,fsa,1);
  tmalloc(tdiffptr,fsa,1);

/* Now start the loop to calculate the correct geowaptr and tdiffptr */
  ct=0;
  while (1) {
    ct++;
    /* Read in word-acceptor. */
    if ((rfile = fopen(inf1,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf1);
        exit(1);
    }
    fsa_read(rfile,waptr,DENSE,0,0,TRUE,fsaname);
    fclose(rfile);
    if (ct>1) {
    /* Re-read in tdiffptr */
      rfile=fopen(outf4,"r");
      fsa_read(rfile,tdiffptr,DENSE,0,0,TRUE,fsaname);
      fclose(rfile);
    }
    else {
      /* The first approximation to *tdiffptr is the diff2 machine which we
       * have already read in as *wd_fsa, so we copy it.
       */
      fsa_copy(tdiffptr,rs_wd.wd_fsa);
    }
    geopairsptr = fsa_geopairs(waptr,tdiffptr,op_store2,TRUE,tempfilename,
                               readback);
    if (geopairsptr==0) exit(1);
    if (kbm_print_level>1)
      printf("  #Number of states of geopairs before minimisation = %d.\n",
        geopairsptr->states->size);
    if (readback) {
      if (fsa_minimize(geopairsptr)==-1) exit(1);
    }
    else {
      if (fsa_ip_minimize(geopairsptr)==-1) exit(1);
    }
    if (kbm_print_level>1)
      printf("  #Number of states of geopairs after minimisation = %d.\n",
        geopairsptr->states->size);

    base_prefix(fsaname);
    strcat(fsaname,".geopairs");
    wfile = fopen(outf2,"w");
    fsa_print(wfile,geopairsptr,fsaname);
    fclose(wfile);
    fsa_clear(geopairsptr);

/* Next we form the updated *geowaptr. We read *geopairsptr back in again
 * (since the table format required is usually different).
 */
    rfile=fopen(outf2,"r");
    fsa_read(rfile,geopairsptr,DENSE,0,0,TRUE,fsaname);
    fclose(rfile);

    geowaptr = fsa_exists(geopairsptr,op_store1,TRUE,tempfilename);
    if (geowaptr==0) exit(1);
    if (kbm_print_level>1)
      printf("  #Number of states of geowa before minimisation = %d.\n",
        geowaptr->states->size);

/* We will make the language prefix closed, then output
    if (geowaptr->states->size > 1) {
      tfree(geowaptr->accepting);
      geowaptr->num_accepting=geowaptr->states->size;
    }
*/

    if (fsa_minimize(geowaptr)==-1) exit(1);
    if (kbm_print_level>1)
      printf("  #Number of states of geowa after minimisation = %d.\n",
        geowaptr->states->size);
    base_prefix(fsaname);
    strcat(fsaname,".geowa");
    wfile = fopen(outf1,"w");
    fsa_print(wfile,geowaptr,fsaname);
    fclose(wfile);
    fsa_clear(geowaptr);

/* Now we read *geowaptr and *tdiffptr back in for the correctness
 * test on the former.
 */
    rfile=fopen(outf1,"r");
    fsa_read(rfile,geowaptr,DENSE,0,0,TRUE,fsaname);
    fclose(rfile);
    rfile=fopen(outf4,"r");
    fsa_read(rfile,tdiffptr,DENSE,0,maxwdiffs,TRUE,fsaname);
    fclose(rfile);
    numeqns = fsa_checkgeowa(geowaptr,tdiffptr,eqnptr,maxeqns);
    if (numeqns==-1) exit(1);
    if (numeqns==0) {
      if (kbm_print_level>0)
        printf("#Geodesic word-acceptor with %d states computed.\n",
            geowaptr->states->size);
      fsa_clear(geowaptr);
      fsa_clear(tdiffptr);
      break; /* Correctness test passed */
    }
    else {
      fsa_clear(geowaptr);
/* We are going to reduce the words returned to their shortlex normal form,
 * then adjoin the associated word-differences to *tdiffptr.
 */
      tfree(geowaptr); tfree(geopairsptr);
      if (kbm_print_level>1)
        printf("  #Updating geodesic word-difference machine.\n");
      old_ndiff = tdiffptr->states->size;
      if (calculate_inverses(&inv,ngens,&rs_wd)==-1) exit(1);
      for (i=0;i<numeqns;i++) {
        tmalloc(eqnptr[i].rhs,gen,genstrlen(eqnptr[i].lhs)+1);
        genstrcpy(eqnptr[i].rhs,eqnptr[i].lhs);
        reduce_word(eqnptr[i].rhs,&rs_wd);
        if (add_wd_fsa(tdiffptr,eqnptr+i,inv,TRUE,&rs_wd)==-1) exit(1);
        tfree(eqnptr[i].lhs) tfree(eqnptr[i].rhs)
      }
      if (make_full_wd_fsa(tdiffptr,inv,old_ndiff+1,&rs_wd)==-1) exit(1);
      tfree(inv);
      if (kbm_print_level>1)
        printf("  #Geodesic word-difference machine now has %d states.\n",
                 tdiffptr->states->size);
      base_prefix(fsaname);
      strcat(fsaname,".tdiff");
      wfile = fopen(outf4,"w");
      fsa_print(wfile,tdiffptr,fsaname);
      fclose(wfile);
      fsa_clear(tdiffptr);
    }
  }
  tfree(waptr);
  tfree(geowaptr);
  tfree(tdiffptr);

  /* The current *geopairsptr accepts (w1,w2) if w1=w2, w1 and w2 are
   * geodesics, and w2 is accepted by the word-acceptor.
   * To get it to accept ALL pairs of equal geodesics, we form the
   * composite of itself with its transpose.
   */
  tmalloc(gpp,fsa,1);
  tmalloc(tgpp,fsa,1);
  rfile=fopen(outf2,"r");
  fsa_read(rfile,gpp,DENSE,0,0,TRUE,fsaname);
  fclose(rfile);
  fsa_copy(tgpp,gpp);
  if (fsa_swap_coords(tgpp)==-1) exit(1);
  tfree(geopairsptr);
  geopairsptr=fsa_composite(gpp,tgpp,op_store2,FALSE,tempfilename,
							    readback);
  if (geopairsptr==0) exit(1);
  if (kbm_print_level>1)
    printf("  #Number of states of final geopairs before minimisation = %d.\n",
        geopairsptr->states->size);
  if (readback){
    if (fsa_minimize(geopairsptr)==-1) exit(1);
  }
  else {
    if (fsa_ip_minimize(geopairsptr)==-1) exit(1);
  }
  if (kbm_print_level>1)
    printf("  #Number of states of final geopairs after minimisation = %d.\n",
        geopairsptr->states->size);
  if (kbm_print_level>0)
    printf("#Geodesic pairs machine with %d states computed.\n",
        geopairsptr->states->size);

  base_prefix(fsaname);
  strcat(fsaname,".geopairs");
  wfile = fopen(outf2,"w");
  fsa_print(wfile,geopairsptr,fsaname);
  fclose(wfile);
  fsa_clear(geopairsptr);

/* Now form the geodesic word-difference machine */
  rfile=fopen(outf2,"r");
  fsa_read(rfile,geopairsptr,DENSE,0,0,TRUE,fsaname);
  fclose(rfile);
  geodiffptr=fsa_diff(geopairsptr,&rs_wd,op_store2);
  fsa_clear(geopairsptr);
  tfree(geopairsptr);

  base_prefix(fsaname);
  strcat(fsaname,".geodiff");
  wfile = fopen(outf3,"w");
  fsa_print(wfile,geodiffptr,fsaname);
  fclose(wfile);
  if (kbm_print_level>0)
    printf("#Geodesic difference machine with %d states computed.\n",
            geodiffptr->states->size);
  fsa_clear(geodiffptr);
  tfree(geodiffptr);
  if (!near_machine) {
    fsa_clear(gpp);
    tfree(gpp);
    fsa_clear(tgpp);
    tfree(tgpp);
    fsa_clear(rs_wd.wd_fsa);
    tfree(rs_wd.wd_fsa);
    tfree(eqnptr);
    exit(0);
  }

  /* Finally, we form near_geopairs, which accepts pairs of geodesics
   * that finish distance at most one apart. To do this we form the
   * composite gpp * gm * tgpp. 
   */
  rfile=fopen(inf3,"r");
  tmalloc(gmptr,fsa,1);
  fsa_read(rfile,gmptr,DENSE,0,0,TRUE,fsaname);
  fclose(rfile);
  /* first compose gpp with gm */
  geopairsptr=fsa_composite(gpp,gmptr,op_store2,TRUE,tempfilename,
							    readback);
  if (geopairsptr==0) exit(1);
  tfree(gpp);
  tfree(gmptr);
  if (kbm_print_level>1)
    printf("  #Number of states of first composite = %d.\n",
        geopairsptr->states->size);
  if (readback){
    if (fsa_minimize(geopairsptr)==-1) exit(1);
  }
  else {
    if (fsa_ip_minimize(geopairsptr)==-1) exit(1);
  }
  if (kbm_print_level>1)
    printf("  #Number of states of first composite after minimisation = %d.\n",
        geopairsptr->states->size);

  /* write *geopairsptr and re-read to get dense storage type */
  base_prefix(fsaname);
  strcat(fsaname,".near_geopairs");
  wfile = fopen(outf5,"w");
  fsa_print(wfile,geopairsptr,fsaname);
  fclose(wfile);
  fsa_clear(geopairsptr);
  rfile=fopen(outf5,"r");
  fsa_read(rfile,geopairsptr,DENSE,0,0,TRUE,fsaname);
  fclose(rfile);

  /* now compose result with tggp */
  gpp=fsa_composite(geopairsptr,tgpp,op_store2,TRUE,tempfilename,
							    readback);
  tfree(geopairsptr);
  tfree(tgpp);
  if (gpp==0) exit(1);
  if (kbm_print_level>1)
    printf("  #Number of states of near geopairs before minimisation = %d.\n",
        gpp->states->size);

  /* write *gpp and re-read to get dense storage type */
/*
  wfile = fopen(outf5,"w");
  fsa_print(wfile,gpp,fsaname);
  fclose(wfile);
  fsa_clear(gpp);
  rfile=fopen(outf5,"r");
  fsa_read(rfile,gpp,DENSE,0,0,TRUE,fsaname);
  fclose(rfile);
*/

/* Form the near geodesic word-difference machine */
/*
  geodiffptr=fsa_diff(gpp,&rs_wd,op_store2);
  base_prefix(fsaname);
  strcat(fsaname,".near_geodiff");
  wfile = fopen(outf6,"w");
  fsa_print(wfile,geodiffptr,fsaname);
  fclose(wfile);
  if (kbm_print_level>0)
    printf("#Geodesic difference machine with %d states computed.\n",
            geodiffptr->states->size);
  fsa_clear(geodiffptr);
  tfree(geodiffptr);
*/

  if (readback){
    if (fsa_minimize(gpp)==-1) exit(1);
  }
  else {
    if (fsa_ip_minimize(gpp)==-1) exit(1);
  }
  if (kbm_print_level>1)
    printf("  #Number of states of near geopairs after minimisation = %d.\n",
        gpp->states->size);
  if (kbm_print_level>0)
    printf("#Geodesic near pairs machine with %d states computed.\n",
        gpp->states->size);

  wfile = fopen(outf5,"w");
  fsa_print(wfile,gpp,fsaname);
  fclose(wfile);
  fsa_clear(gpp);
  tfree(gpp);

  fsa_clear(rs_wd.wd_fsa);
  tfree(rs_wd.wd_fsa);
  tfree(eqnptr);
  exit(0);
}
 
void
badusage_gpgeowa()
{
    fprintf(stderr,
     "Usage: gpgeowa [-op1 d/s] [-op2 d/s] [-silent] [-v] [-l/-h] [-f]\n");
    fprintf(stderr,
 "          [-diff1/-diff2] [-me maxeqns] [-mwd maxwdiffs] [-n] groupname\n");
    exit(1);
}
