/* gpmakefsa.c 11/1/95.
 * 6/8/98 large scale reorganisation to omit globals, etc.
 * 5/2/98 change generators from type char to type `gen'.
 * 15/3/96 changed syntax of -cos call to
 * gpmakefsa -cos groupname [cosname]
 * where cosname defaults to "cos".
 *
 * 24/10/95 - changed method of doing coset calculation to compute
 * multiple-initial state multiplier with fsa_mitriples and then
 * determinise it with migm_determinize, rather than determinize the
 * midiff2 machine first (which tended to produce a machine with
 * large number of states and very dense transition table).
 *
 * 21/9/95 - added capability of doing the calculations for coset
 * automatic groups - with the -cos option
 *
 * This program performs the combined functions of gpwa, gpgenmult and
 * gpcheckmult, to make the finite state automata of a short-lex automatic
 * structure of a group G. It runs them repeatedly, until they pass the
 * correctness test.
 * (In the cosets case, it also uses midiff_determinize.)
 * This program assumes that kbprog (or kbprogcos) with -wd option has already
 * been run of G.
 *
 * SYNOPSIS:
 * gpmakefsa [-opwa d/s] [-opgm d/s] [-opd2 d/s] [-ip d/s[dr]] [-silent] [-v]
 *           [-l/-h] [-diff1/-diff2] [-m maxeqns] [-mwd maxwdiffs] [-ns] [-f]
 *	     [-cos] groupname [cosname]
 *
 * In all of the following comments below, replace "groupname" by
 * "groupname.cosname" in the cosets case.
 * Input is from groupname.diff2, or groupname.midiff2 in cosets case
 *  (and possibly from groupname.diff1 or groupname.midiff1 if -c option
 *   is called).
 * Output is to groupname.wa and groupname.gm (and groupname.migm in
 * cosets case)
 * Also the files groupname.diff2 (or groupname.midiff2), and possibly
 * groupname.diff1 (or groupname.midiff1) if -c called,
 * may be updated by the addition of extra required word-differences.
 *
 * OPTIONS:
 * -opwa d/s	output to groupname.wa in dense or sparse format -
 *              dense is default
 * -opgm d/s	output to groupname.gm in dense or sparse format -
 *              sparse is default
 * -ip d/s[dr]  input of groupname.gm in dense or sparse format -
 *              dense is default
 * -v		verbose
 * -silent	no diagnostics
 * -l/-h	large/huge hash-tables (for big examples)
 * -diff1/diff2	(diff2 is default).
 *		This determines whether groupname.(mi)diff1 or
 *              groupname.(mi)diff2 is used to construct the word-acceptor.
 *		If diff1 is called, then the multiplier is constructed in
 *		"correction" mode. This means that
 *              if an equation is discovered which proves the word-acceptor
 *              to be incorrect, then the first word-difference machine
 *              (which should be in file groupname.(mi)diff1) is updated by
 *              making it accept this equation.
 * -m  maxeqns  Abort the multiplier checking process after finding maxeqns
 * 		offending words w (see above) -  default is MAXEQNS
 * -mwd maxwdiffs
 *              At most maxwdiffs word-differences possible.
 * -ns		Don't stop if nontrivial equation found in word-acceptor
 *		language.
 * -f           read the transition table repeatedly from file while mimimizing.
 *              this avoids storing the large table, but is a little slower.
 * -cos         Do the calculation for coset automatic groups (by setting
 *              global variable cosets to be TRUE).
 *
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"
#define MAXEQNS 512
#define MAXWDIFFS 4096
#define PREFMARGIN 1024

static FILE *rfile, *wfile;

void  badusage_gpmakefsa();
int   (*reduce_word)();

/* Functions defined in other files used in this file */
void  fsa_read();
fsa  *fsa_wa();
fsa  *fsa_wa_cos();
fsa  *fsa_triples();
fsa  *fsa_mitriples();
int   fsa_checkmult();
void  fsa_print();
int   fsa_minimize();
int   fsa_ip_minimize();
int   fsa_labeled_minimize();
int   fsa_ip_labeled_minimize();
int   midfa_labeled_minimize();
void  fsa_clear();
void  fsa_copy();
int   diff_reduce();
int   diff_reduce_cos();
void  make_full_wd_fsa();
void  make_full_wd_fsa_cos();
int   add_wd_fsa();
int   add_wd_fsa_cos();
int   calculate_inverses();
int   fsa_table_dptr_init();
fsa   *migm_determinize();
int   stringlen();
int   stringlen();
int   genstrlen();
void  genstrcpy();
void  genstrcat();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int arg, i, ct, *inv, ngens, maxwdiffs, numeqns, old_ndiff;
  fsa *wa, diff1, diff2, *genmultptr, migenmult;
  char gpname[100], cosgpname[100], inf1[100], inf2[100], outf1[100],
       outf2[100], outf2mi[100], fsaname[100], tempfilename[100];
  int maxeqns1, maxeqns2;
  reduction_equation *eqnptr;
  reduction_struct rs_wd;
  fsa *wd_fsa; /* This is for word-reduction in the case that we correct
              * the diff1 or diff2 machine.
              * It will be in groupname.diff2 or groupname.midiff2.
              */
  boolean cosets=FALSE;
  int separator=0;
  boolean correction = FALSE;
  storage_type op_store_wa = DENSE;
  storage_type op_store_gm = SPARSE;
  storage_type ip_store = DENSE;
  int dr = 0;
  boolean eqnstop = TRUE;
  boolean foundeqns;
  boolean readback = TRUE;
  boolean calc_wa, calc_gm;
  gen * rhscos; /* for reducing words when cosets is true */
  boolean diff1_ip, seengpname, seencosname;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  maxeqns1 = 0;
  maxeqns2 = MAXEQNS;
  maxwdiffs = MAXWDIFFS;
  inf1[0] = '\0';
  arg = 1;
  diff1_ip=seengpname=seencosname=FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg],"-opwa")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpmakefsa();
      if (strcmp(argv[arg],"d")==0)
        op_store_wa = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store_wa = SPARSE;
      else
        badusage_gpmakefsa();
    }
    else if (strcmp(argv[arg],"-opgm")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpmakefsa();
      if (strcmp(argv[arg],"d")==0)
        op_store_gm = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store_gm = SPARSE;
      else
        badusage_gpmakefsa();
    }
    else if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpmakefsa();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's') {
        ip_store = SPARSE;
        if (stringlen(argv[arg]) > 1)
          dr = atoi(argv[arg]+1);
      }
      else
        badusage_gpmakefsa();
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
    else if (strncmp(argv[arg],"-cos",4)==0)
      cosets = TRUE;
    else if (strcmp(argv[arg],"-diff1")==0)
      correction = diff1_ip = TRUE;
    else if (strcmp(argv[arg],"-diff2")==0)
      correction = diff1_ip = FALSE;
    else if (strcmp(argv[arg],"-m")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpmakefsa();
      maxeqns2 = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg],"-mwd")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpmakefsa();
      maxwdiffs = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg],"-ns")==0)
      eqnstop = FALSE;
    else if (strcmp(argv[arg],"-f")==0) {
      if (cosets) {
        fprintf(stderr,
             "Sorry, filestore option is unavailable for in cosets case.\n");
        exit(1);
      }
      readback = FALSE;
    }
    else if (argv[arg][0] == '-')
      badusage_gpmakefsa();
    else if (!seengpname) {
      seengpname=TRUE;
      strcpy(gpname,argv[arg]);
    }
    else if (!seencosname) {
      seencosname=TRUE;
      sprintf(cosgpname,"%s.%s",gpname,argv[arg]);
    }
    else
      badusage_gpmakefsa();
    arg++;
  }
  if (!seengpname)
    badusage_gpmakefsa();
  if (cosets && !seencosname)
    sprintf(cosgpname,"%s.cos",gpname);

  if (cosets) strcpy(inf1,cosgpname);
  else strcpy(inf1,gpname);
  
  strcpy(tempfilename,inf1);
  strcat(tempfilename,"temp_fsa_XXX");

  strcpy(inf2,inf1);
  strcpy(outf1,inf1);
  strcpy(outf2,inf1);
  if (diff1_ip) {
    if (cosets) strcat(inf1,".midiff1");
    else strcat(inf1,".diff1");
  }
  else {
    if (cosets) strcat(inf1,".midiff2");
    else strcat(inf1,".diff2");
  }
  if (cosets) strcat(inf2,".midiff2");
  else strcat(inf2,".diff2");

  strcat(outf1,".wa");
  if (cosets) {
    strcpy(outf2mi,outf2); strcat(outf2mi,".migm");
  }
  strcat(outf2,".gm");

  calc_wa = TRUE;
  while (calc_wa) {
  /* First read in word-difference machine for calculating word-acceptor,
   * from groupname.(mi)diff1 (if -diff1 flag set) or groupname.(mi)diff2
   */
    if ((rfile = fopen(inf1,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf1);
      exit(1);
    }
    fsa_read(rfile,&diff2,DENSE,0,0,TRUE,fsaname);
    fclose(rfile);
  
  /* Now calculate word-acceptor */
    wa = cosets ?
      fsa_wa_cos(&diff2,op_store_wa,TRUE,tempfilename) :
      fsa_wa(&diff2,op_store_wa,TRUE,tempfilename);
  
    if (kbm_print_level>1)
      printf("  #Number of states of word-acceptor before minimisation = %d.\n",
          wa->states->size);
    if (fsa_minimize(wa)== -1) exit(1);
    if (kbm_print_level>1)
      printf("  #Number of states of word-acceptor after minimisation = %d.\n",
          wa->states->size);
  
    base_prefix(fsaname);
    strcat(fsaname,".wa");
    wfile = fopen(outf1,"w");
    fsa_print(wfile,wa,fsaname);
    fclose(wfile);

    if (kbm_print_level>0)
      printf("#Word-acceptor with %d states computed.\n",wa->states->size);

    fsa_clear(wa);

    calc_wa = FALSE;
    calc_gm = TRUE;
    while (calc_gm) {
     /* Read in word-acceptor and diff2 machine for calculating multiplier
      */
      if ((rfile = fopen(outf1,"r")) == 0) {
        fprintf(stderr,"Cannot open file %s.\n",outf1);
          exit(1);
      }
      fsa_read(rfile,wa,DENSE,0,0,TRUE,fsaname);
      fclose(rfile);
      if ((rfile = fopen(inf2,"r")) == 0) {
        fprintf(stderr,"Cannot open file %s.\n",inf2);
        exit(1);
      }
      fsa_read(rfile,&diff2,DENSE,0,0,TRUE,fsaname);
      fclose(rfile);
    
      if (correction) {
	maxeqns1 = maxeqns2;
        tmalloc(eqnptr,reduction_equation,maxeqns1)
      }
      else
        eqnptr = 0;
    
     /* Now try to calculate generalised multiplier */
      if (cosets)
        separator=diff2.alphabet->base->size+1;
      genmultptr =
           cosets ? fsa_mitriples(wa,&diff2,op_store_gm,TRUE,tempfilename,
			   eqnptr,maxeqns1,eqnstop,&foundeqns,readback)
                    : fsa_triples(wa,&diff2,op_store_gm,TRUE,tempfilename,
			   eqnptr,maxeqns1,eqnstop,&foundeqns,readback);
    
      if (foundeqns) {
  /*This is the case where the calculation failed and new equations was found.
   * If the -diff1 flag was set, we correct the groupname.(mi)diff1 machine.
   */
        if (correction)  {
          if (kbm_print_level>1)
            printf(
             "  #Altering first wd-machine to make it accept new equations.\n");
        /* Read in diff1 machine from groupname.diff1 */
          if ((rfile = fopen(inf1,"r")) == 0) {
            fprintf(stderr,"Cannot open file %s.\n",inf1);
              exit(1);
          }
          fsa_read(rfile,&diff1,DENSE,0,maxwdiffs,TRUE,fsaname);
          fclose(rfile);
          /* we need the original diff2 machine to do word-reduction-
           * This comes from groupname.diff2 or groupname.midiff2
           */
          if (cosets) {
            tmalloc(diff1.is_initial,boolean,maxwdiffs+1);
            for (i=1;i<=maxwdiffs;i++) diff1.is_initial[i]=FALSE;
            for (i=1;i<=diff1.num_initial;i++)
            diff1.is_initial[diff1.initial[i]]=TRUE;
          }
          rs_wd.wd_fsa = &diff2; /* We use this to do the word-reductions */
	  if (cosets)
            rs_wd.separator = diff2.alphabet->base->size+1;
          reduce_word = cosets ? diff_reduce_cos : diff_reduce;
          if (fsa_table_dptr_init(&diff1)== -1) exit(1);

    /* We need to know the inverses of generators - let's just work them out! */
          ngens = diff1.alphabet->base->size;
          if (calculate_inverses(&inv,ngens,&rs_wd)==-1) exit(1);
    
          i=0;
          if (cosets)
            tmalloc(rhscos,gen,8192);
          while (eqnptr[i].lhs && i<maxeqns1) {
            if (cosets) {
             /* Here we need to re-reduce the lhs, to get the prefix in the
              * subgroup */
              tfree(eqnptr[i].rhs);
              genstrcpy(rhscos,eqnptr[i].lhs);
              reduce_word(rhscos,&rs_wd);
              tmalloc(eqnptr[i].rhs,gen,genstrlen(rhscos)+1);
              genstrcpy(eqnptr[i].rhs,rhscos);
              if (add_wd_fsa_cos(&diff1,eqnptr+i,inv,FALSE,&rs_wd)== -1)
                exit(1);
            }
            else
              if (add_wd_fsa(&diff1,eqnptr+i,inv,FALSE,&rs_wd)== -1)
                exit(1);
            i++;
          }
          if (cosets) {
            tfree(rhscos);
            tfree(diff1.initial);
            tmalloc(diff1.initial,int,diff1.num_initial+1);
            ct=0;
            for (i=1;i<=diff1.states->size;i++) if (diff1.is_initial[i])
              diff1.initial[++ct]=i;
            tfree(diff1.is_initial);
          }
    
          if (kbm_print_level>1)
            printf("  #First word-difference machine now has %d states.\n",
                     diff1.states->size);
    
          wfile = fopen(inf1,"w");
          fsa_print(wfile,&diff1,fsaname);
          fclose(wfile);
    
          tfree(inv);
          fsa_clear(&diff1);
          i=0;
          while (eqnptr[i].lhs && i<maxeqns1) {
            tfree(eqnptr[i].lhs); tfree(eqnptr[i].rhs);
            i++;
          }
          tfree(eqnptr);
        }
        calc_wa = TRUE;
        tfree(wa);
        fsa_clear(&diff2);
        break;
      }
      if (genmultptr==0) exit(1);

     /* At this stage we have successfully calculated the generalised
      * multiplier.
      */
      if (correction)
        tfree(eqnptr);
    
      if (kbm_print_level>1) {
        if (cosets)
          printf(
           "  #Number of states of mi-multiplier before minimisation = %d.\n",
            genmultptr->states->size);
        else
         printf("  #Number of states of multiplier before minimisation = %d.\n",
            genmultptr->states->size);
      }
      if (readback) {
        if (cosets) {
          if (midfa_labeled_minimize(genmultptr)== -1) exit(1);
        }
        else
          if (fsa_labeled_minimize(genmultptr)== -1) exit(1);
      }
      else 
        if (fsa_ip_labeled_minimize(genmultptr)== -1) exit(1);
      if (kbm_print_level>1) {
        if (cosets)
          printf(
           "  #Number of states of mi-multiplier after minimisation = %d.\n",
            genmultptr->states->size);
        else
         printf("  #Number of states of multiplier after minimisation = %d.\n",
            genmultptr->states->size);
      }
    
      base_prefix(fsaname);
      if (cosets) {
        strcat(fsaname,".migm");
        wfile = fopen(outf2mi,"w");
      }
      else {
        strcat(fsaname,".gm");
        wfile = fopen(outf2,"w");
      }
      fsa_print(wfile,genmultptr,fsaname);
      fclose(wfile);

      if (kbm_print_level>0) {
        if (cosets)
          printf("#General mi-multiplier with %d states computed.\n",
                genmultptr->states->size);
        else
          printf("#General multiplier with %d states computed.\n",
                genmultptr->states->size);
      }
    
      fsa_clear(genmultptr);
      calc_gm = FALSE;

      if (cosets) {
      /* Now we read back in the general mi-multiplier and determinize it */
        if ((rfile = fopen(outf2mi,"r")) == 0) {
          fprintf(stderr,"Cannot open file %s.\n",outf2mi);
            exit(1);
        }
        fsa_read(rfile,&migenmult,ip_store,dr,0,TRUE,fsaname);
        fclose(rfile);
        tfree(genmultptr);
        genmultptr = migm_determinize(&migenmult,op_store_gm,TRUE,tempfilename);
        if (kbm_print_level>1)
          printf(
           "  #Number of states of multiplier before minimisation = %d.\n",
            genmultptr->states->size);
        if (fsa_labeled_minimize(genmultptr) == -1) exit(1);
        if (kbm_print_level>1)
          printf(
           "  #Number of states of multiplier after minimisation = %d.\n",
            genmultptr->states->size);
        if (kbm_print_level>0)
          printf("#General multiplier with %d states computed.\n",
                genmultptr->states->size);
        base_prefix(fsaname);
        strcat(fsaname,".gm");
        wfile = fopen(outf2,"w");
        fsa_print(wfile,genmultptr,fsaname);
        fclose(wfile);
      }

      /* Now perform the check on the multiplier - we read it back in, since
       * the storage type has usually changed.
       */

      if ((rfile = fopen(outf2,"r")) == 0) {
        fprintf(stderr,"Cannot open file %s.\n",outf2);
          exit(1);
      }
      fsa_read(rfile,genmultptr,ip_store,dr,0,TRUE,fsaname);
      fclose(rfile);
    
      if (cosets)
        separator=genmultptr->alphabet->base->size+1;
      tmalloc(eqnptr,reduction_equation,maxeqns2)

      if ((numeqns =
             fsa_checkmult(genmultptr,eqnptr,maxeqns2,cosets,separator)) > 0) {
     /* A multiplier was not valid, so groupname.diff2 will need updating. */
    
        fsa_clear(genmultptr);
        if (kbm_print_level>1)
          printf(
            "  #Altering second wd-machine to make it accept new equations.\n");
        /* We read it into diff2,  and then copy it into
         * wd_fsa. The copy is used for reducing words - Not surprisingly,
         * we get problems if we try to alter it while using it at
         * the same time!
         */
        if ((rfile = fopen(inf2,"r")) == 0) {
            fprintf(stderr,"Cannot open file %s.\n",inf2);
              exit(1);
        }
        fsa_read(rfile,&diff2,DENSE,0,maxwdiffs,TRUE,fsaname);
        fclose(rfile);
        tmalloc(wd_fsa,fsa,1);
        fsa_copy(wd_fsa,&diff2);
        reduce_word = cosets ? diff_reduce_cos : diff_reduce;
        rs_wd.wd_fsa = wd_fsa;
        if (fsa_table_dptr_init(wd_fsa)== -1) exit(1);
        if (fsa_table_dptr_init(&diff2)== -1) exit(1);
        if (cosets) {
          tmalloc(diff2.is_initial,boolean,maxwdiffs+1);
          for (i=1;i<=maxwdiffs;i++) diff2.is_initial[i]=FALSE;
          for (i=1;i<=diff2.num_initial;i++) 
            diff2.is_initial[diff2.initial[i]]=TRUE;
          rs_wd.separator=separator;
        }
    /* We need to know the inverses of generators - let's just work them out! */
        ngens = diff2.alphabet->base->size;
        if (calculate_inverses(&inv,ngens,&rs_wd)==-1) exit(1);
        old_ndiff = diff2.states->size;
    
    /* Now add the new equations
     * The right hand side of the equation to be added will be the reduction of
     * the lhs times the generator which is currently in the lhs.
     */
        for (i=0;i<numeqns;i++) {
          genstrcat(eqnptr[i].lhs,eqnptr[i].rhs);
          tfree(eqnptr[i].rhs);
 /* In the cosets case, we need to allow some extra room for the reduction
  * of the word, since it might acquire a long prefix in the subgroup.
  */
          if (cosets) 
            tmalloc(eqnptr[i].rhs,gen,PREFMARGIN+genstrlen(eqnptr[i].lhs))
          else
            tmalloc(eqnptr[i].rhs,gen,1+genstrlen(eqnptr[i].lhs));
          genstrcpy(eqnptr[i].rhs,eqnptr[i].lhs);
          reduce_word(eqnptr[i].rhs,&rs_wd);
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
          printf("  #Second word-difference machine now has %d states.\n",
                   diff2.states->size);
    
        wfile = fopen(inf2,"w");
        fsa_print(wfile,&diff2,fsaname);
        fclose(wfile);
    
        tfree(inv);
        fsa_clear(wd_fsa); tfree(wd_fsa);
        for (i=0;i<numeqns;i++) {
          tfree(eqnptr[i].lhs); tfree(eqnptr[i].rhs);
        }
        calc_gm = TRUE;
        tfree(genmultptr);
        fsa_clear(&diff2);
      }
      else {
        if (kbm_print_level>0)
           printf("#Validity test on general multiplier succeeded.\n");
        fsa_clear(genmultptr);
      }
      tfree(eqnptr);
    }
  }

  tfree(wa);
  tfree(genmultptr);
  exit(0);
}
 
void
badusage_gpmakefsa()
{
    fprintf(stderr,
     "Usage: gpmakefsa [-opwa d/s] [-opgm d/s] [-ip d/s[dr]]\n");
    fprintf(stderr,
 "\t\t [-silent] [-v] [-l/-h] [-diff1/-diff2] [-m maxeqns]\n");
    fprintf(stderr,
      "\t\t [-mwd maxwdiffs] [-ns] [-f] [-cos] groupname [cosname].\n");
    exit(1);
}
