/* gpcheckmult.c 18/11/94.
 *
 * 6/8/98 large scale reorganisation to omit globals, etc.
 * 5/2/98 change generators from type char to type `gen'.
 * 26/9/96 - New option -wtlex (this was already in V1 of kbmag) to deal with
 *        the wtlex ordering case. This uses a different word-reduction
 *        and needs to read in the weights from the original file.
 *        For the moment this is not usable with the -cos option.
 *
 * 1/8/96  - output a file gpname.kbprog.exitcode containing a GAP statement
 *        giving the exit code - for use with GAP interface
 *
 * 15/3/96 changed syntax of -cos call to
 * gpmakefsa -cos groupname [cosname]
 * where cosname defaults to "cos".
 *
 * 26/2/96 added option -ow (output words).
 * If it finds an error, it does not correct diff2, but outputs the
 * a list containing the culprit words and the associated generators.
 *
 * 22/9/95 - added capability of doing the calculations for coset
 * automatic groups - with the -cos option
 * This program assumes that kbprog, gpwa, gpgenmult have already been
 * run on the group G. 
 * The theory of this checking process for the general multiplier is as
 * follows.
 *
 * For each generator g of G, let M_g be the associated multiplier automaton,
 * and construct the fsa E_g, which accepts word w iff there exists a word x
 * such that M_g accepts (w,x). E_g should equal the word-acceptor W for G.
 * Construct (E_g' and W) to check this. It should have empty language. If not
 * find words w that it accepts, reduce w*g, to x, say, and update the
 * word-difference machine for G used to construct the multipliers, to make
 * it accept the pair (w*g,x).
 *
 * In practice, the function fsa_checkmult does this check on the general
 * multiplier for all g at the same time.
 * Furthermore, it does not need to use the word-acceptor explicitly, since
 * if  w  is not accepted by the word-acceptor, then all pairs (w,y)
 * map to 0, and  w  is never considered.
 *
 * SYNOPSIS:
 * gpcheckmult [-ip d/s[dr]] [-v] [-silent] [-l/-h] [-m maxeqns] 
 *	       [-ow] [-mwd maxwdiffs] [-cos] [-wtlex] groupname [cosname]
 *
 * If -cos is not set,
 * input is from  groupname.gpgenmult, and possibly groupname.diff2
 * (the last only if it requires updating).
 * If -cos is set,
 * input is from  groupname.cosname.gpgenmult, and possibly
 * groupname.cosname.midiff2 (the last only if it requires updating).
 *
 * If no updating is required there is no output.
 * Otherwise output is to groupname.diff2 or groupname.cosname.midiff2,
 * unless -ow is set, in which case it is to groupname.(cosname.)wg.
 *
 * EXIT STATUS:
 * This is 2 if groupname.(cosname.mi)diff2 requires updating, otherwise 0.
 *
 * OPTIONS:
 * -ip d/s[dr]  input in dense or sparse format - dense is default
 * -v           verbose
 * -silent      no diagnostics
 * -l/-h        large/huge hash-tables (for big examples)
 * -m  maxeqns  Abort after finding maxeqns offending words w (see above)
 *              default is MAXNEWEQNS
 * -mwd maxwdiffs
 *		At most maxwdiffs word-differences possible.
 * -ow          If the general multiplier turns out to be incorrect, do
 *              not correct the diff2 machine, but simply output the 
 *              culprit words. More precisely output a file to
 *              groupname.(cosname.)wg (words and generators), containing a
 *              list declaration of the form  ???.wg := [...], where
 *              each term in the list is a 2-element list containing a word
 *              w and a generator a, such that w is not accpeted as a left
 *              hand side by the multiplier for generator a.
 * -cos         Do the calculation for coset automatic groups (by setting
 *              global variable cosets to be TRUE).
 * -wtlex       Use wtlex ordering of words. This only makes a difference if
 *              the diff2 machine is updated. Not usable with -cos option.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"
#define MAXNEWEQNS 512
#define MAXRWSEQNS 1024
#define MAXWDIFFS 4096
#define PREFMARGIN 1024
#define MAXREDUCELEN 4096

static FILE *rfile, *wfile;

void  badusage_gpcheckmult();
int  (*reduce_word)();

/* Functions defined in other files used in this file */
void  fsa_read();
int   fsa_checkmult();
void  fsa_clear();
void  fsa_copy();
int   diff_reduce();
int   diff_reduce_cos();
int   diff_reduce_wl();
int   add_wd_fsa();
int   add_wd_fsa_cos();
void  make_full_wd_fsa();
void  make_full_wd_fsa_cos();
int   calculate_inverses();
int  fsa_table_dptr_init();
int  add_word_to_buffer();
void read_kbinput_simple();
void rws_clear();
int	stringlen();
int	genstrlen();
void genstrcpy();
void genstrcat();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg, i, ct, *inv, old_ndiff, maxneweqns, numeqns, ngens, maxwdiffs;
  fsa  diff2, genmult;
  char gpname[100], cosgpname[100], inf1[100], inf2[100], inf3[100],
       outf[100], outfwg[100], outfec[100], fsaname[100];
  fsa *wd_fsa; /* This is for doing word-reductions in the case that we
              * correct the diff2 machine
              */
  fsa wa;     /* The word-acceptor in the wtlex case */
  int weight[MAXGEN+1]; /* The weights of the generators in the wtlex case */
  gen testword[MAXREDUCELEN]; /* for word reduction */
  char **names; /* generator names in case we need to output words */
  reduction_equation *eqnptr;
  reduction_struct rs_wd;
  storage_type ip_store = DENSE;
  int dr = 0;
  boolean seengpname, seencosname;
  boolean cosets=FALSE;
  boolean wtlex=FALSE;
  rewriting_system  rws;
  boolean outputwords = FALSE;
  int separator=0;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  rws.maxeqns = MAXRWSEQNS;
  maxneweqns = MAXNEWEQNS;
  maxwdiffs = MAXWDIFFS;
  inf1[0] = '\0';
  inf2[0] = '\0';
  outf[0] = '\0';
  arg = 1;
  seengpname=seencosname=FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpcheckmult();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's') {
        ip_store = SPARSE;
        if (stringlen(argv[arg]) > 1)
          dr = atoi(argv[arg]+1);
      }
      else
        badusage_gpcheckmult();
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
    else if (strcmp(argv[arg],"-ow")==0)
      outputwords = TRUE;
    else if (strncmp(argv[arg],"-cos",4)==0)
      cosets = TRUE;
    else if (strcmp(argv[arg],"-m")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpcheckmult();
      maxneweqns = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg],"-mwd")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpcheckmult();
      maxwdiffs = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg],"-wtlex")==0)
      wtlex = TRUE;
    else if (argv[arg][0] == '-')
      badusage_gpcheckmult();
    else if (!seengpname) {
      seengpname=TRUE;
      strcpy(gpname,argv[arg]);
    }
    else if (!seencosname) {
      seencosname=TRUE;
      sprintf(cosgpname,"%s.%s",gpname,argv[arg]);
    }
    else
      badusage_gpcheckmult();
    arg++;
  }
  if (!seengpname)
    badusage_gpcheckmult();
  if (cosets && wtlex) {
    fprintf(stderr,
        "Sorry: -cos and -wtlex options cannot be used together.\n");
    badusage_gpcheckmult();
  }
  if (cosets && !seencosname)
    sprintf(cosgpname,"%s.cos",gpname);

  if (cosets) strcpy(inf1,cosgpname);
  else strcpy(inf1,gpname);

  strcpy(inf2,inf1);
  strcat(inf1,".gm");

  if (cosets) sprintf(outfec,"%s.cm.ec",cosgpname);
  else sprintf(outfec,"%s.cm.ec",gpname);

  if ((rfile = fopen(inf1,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf1);
      exit(1);
  }
  fsa_read(rfile,&genmult,ip_store,dr,0,TRUE,fsaname);
  fclose(rfile);

  tmalloc(eqnptr,reduction_equation,maxneweqns)
  if (cosets)
     separator=rs_wd.separator=genmult.alphabet->base->size+1;
  if ((numeqns =
         fsa_checkmult(&genmult,eqnptr,maxneweqns,cosets,separator)) > 0) {
 /* A multiplier was not valid, so groupname.(mi)diff2 will need updating. */

    if (outputwords) {
    /* We do not update gpname.diff2, but output the offending words. */
      if (cosets) strcpy(outfwg,cosgpname);
      else strcpy(outfwg,gpname);
      strcat(outfwg,".wg");
      wfile=fopen(outfwg,"w");
      base_prefix(fsaname);
      fprintf(wfile,"%s.wg := [\n",fsaname);
      names=genmult.alphabet->base->names;
      for (i=0;i<numeqns;i++) {
        strcpy(kbm_buffer,"  [");
        if (cosets)
          add_word_to_buffer(wfile,eqnptr[i].lhs+1,names);
        else
          add_word_to_buffer(wfile,eqnptr[i].lhs,names);
        strcat(kbm_buffer,",");
        add_word_to_buffer(wfile,eqnptr[i].rhs,names);
        if (i<numeqns-1) strcat(kbm_buffer,"],");
        else strcat(kbm_buffer,"]");
        fprintf(wfile,"%s\n",kbm_buffer);
      }
      fprintf(wfile,"];\n");
      fclose(wfile);
      fsa_clear(&genmult);
      for (i=0;i<numeqns;i++) {
        tfree(eqnptr[i].lhs);
        tfree(eqnptr[i].rhs);
      }
      tfree(eqnptr);
      wfile=fopen(outfec,"w");
      fprintf(wfile,"_ExitCode := 2;\n");
      fclose(wfile);
      exit(2);
    }
    fsa_clear(&genmult);
    if (cosets) strcat(inf2,".midiff2");
    else strcat(inf2,".diff2");
    strcpy(outf,inf2);
    if (kbm_print_level>1)
      printf("  #Altering wd-machine to make it accept new equations.\n");
    if ((rfile = fopen(inf2,"r")) == 0) {
        fprintf(stderr,"Cannot open file %s.\n",inf2);
          exit(1);
    }
    /* We read groupname.(mi)diff2 into diff2,  and then copy it into
     * wd_fsa. The copy is used for reducing words - Not surprisingly,
     * we get problems if we try to alter it while using it at
     * the same time!
     */

    fsa_read(rfile,&diff2,DENSE,0,maxwdiffs,TRUE,fsaname);
    fclose(rfile);
    tmalloc(wd_fsa,fsa,1);
    fsa_copy(wd_fsa,&diff2);
    if (wtlex) { /* we have to read in the weights from the group file */
      if ((rfile = fopen(gpname,"r")) == 0) {
        fprintf(stderr,"Cannot open file %s.\n",gpname);
          exit(1);
      }
      read_kbinput_simple(rfile,TRUE,&rws);
      fclose(rfile);
      /* we only need the weights, which we can simply copy */
      for (i=1;i<=rws.num_gens;i++)
        weight[i] = rws.weight[i];
      weight[rws.num_gens+1]=0; /* padding symbol */
      rws_clear(&rws);
      strcpy(inf3,gpname);
      strcat(inf3,".wa");
      if ((rfile = fopen(inf3,"r")) == 0) {
        fprintf(stderr,"Cannot open file %s.\n",inf3);
          exit(1);
      }
      fsa_read(rfile,&wa,DENSE,0,0,TRUE,fsaname);
      fclose(rfile);
    }
    rs_wd.wd_fsa = wd_fsa;
    reduce_word =
           cosets ? diff_reduce_cos : wtlex ? diff_reduce_wl : diff_reduce;
    if (fsa_table_dptr_init(wd_fsa)==-1) return -1;
    if (fsa_table_dptr_init(&diff2)== -1) return -1;
    if (cosets){
      tmalloc(diff2.is_initial,boolean,maxwdiffs+1);
      for (i=1;i<=maxwdiffs;i++) diff2.is_initial[i]=FALSE;
      for (i=1;i<=diff2.num_initial;i++)
        diff2.is_initial[diff2.initial[i]]=TRUE;
    }
    else if (wtlex){
      rs_wd.wa = &wa;
      rs_wd.weight = weight;
      rs_wd.maxreducelen = MAXREDUCELEN;
    }
/* We need to know the inverses of generators - let's just work them out!  */
    ngens = diff2.alphabet->base->size;
    if (calculate_inverses(&inv,ngens,&rs_wd)==-1) return -1;
    old_ndiff = diff2.states->size;

/* Now add the new equations
 * The right hand side of the equation to be added will be the reduction of
 * the lhs times the generator which is currently in the rhs.
 */
    for (i=0;i<numeqns;i++) {
      genstrcat(eqnptr[i].lhs,eqnptr[i].rhs);
      tfree(eqnptr[i].rhs);
      genstrcpy(testword,eqnptr[i].lhs);
      reduce_word(testword,&rs_wd);
      tmalloc(eqnptr[i].rhs,gen,genstrlen(testword)+1);
      genstrcpy(eqnptr[i].rhs,testword);
      if (cosets) {
        if (add_wd_fsa_cos(&diff2,eqnptr+i,inv,TRUE,&rs_wd)== -1) exit(1);
      }
      else
        if (add_wd_fsa(&diff2,eqnptr+i,inv,TRUE,&rs_wd)== -1) exit(1);
    }
    
    if (cosets) {
      tfree(diff2.initial);
      tmalloc(diff2.initial,int,diff2.num_initial+1);
      ct=0;
      for (i=1;i<=diff2.states->size;i++) if (diff2.is_initial[i])
        diff2.initial[++ct]=i;
      tfree(diff2.is_initial);
      make_full_wd_fsa_cos(&diff2,inv,old_ndiff+1,&rs_wd);
    }
    else
      make_full_wd_fsa(&diff2,inv,old_ndiff+1,&rs_wd);
    if (kbm_print_level>1)
      printf("  #Word-difference machine now has %d states.\n",
               diff2.states->size);

    wfile = fopen(inf2,"w");
    fsa_print(wfile,&diff2,fsaname);
    fclose(wfile);

    tfree(inv);
    fsa_clear(wd_fsa); fsa_clear(&diff2);
    tfree(wd_fsa);
    if (wtlex)
      fsa_clear(&wa);
    for (i=0;i<numeqns;i++) {
      tfree(eqnptr[i].lhs);
      tfree(eqnptr[i].rhs);
    }
    tfree(eqnptr);
    wfile=fopen(outfec,"w");
    fprintf(wfile,"_ExitCode := 2;\n");
    fclose(wfile);
    exit(2);
  }
  else if (numeqns<0) exit(1);

  if (kbm_print_level>0)
    printf("#Validity test on general multiplier succeeded.\n");

  fsa_clear(&genmult);
  tfree(eqnptr);
  wfile=fopen(outfec,"w");
  fprintf(wfile,"_ExitCode := 0;\n");
  fclose(wfile);
  exit(0);
}
 
void
badusage_gpcheckmult()
{
    fprintf(stderr,
     "Usage: gpcheckmult [-ip d/s[dr]] [-silent] [-v] [-l/-h] [-m maxeqns]\n");
    fprintf(stderr,
        "\t\t[-ow] [-mwd maxwdiffs] [-cos] [-wtlex] groupname [cosname]\n");
    exit(1);
}
