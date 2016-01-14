/* kbprog.c

2/6/98  - large-scale re-organisation. Abolish almost all global variables
          and make them components of the rws structure.
17/1/98 - changes resulting from intorduction of `gen' type in palce of
          char for generators.

8/8/96  - -ve option to print all equations as found to stdout.
  - -vv option for more diagnostic output.

8/1/96  - output a file gpname.kbprog.exitcode containing a GAP statement
          giving the exit code - for use with GAP interface

6/5/96  - introduced -vwd option (verbose word-differences) to output
          new word-differences as they are found, together with the
          reduction equation that they come from.

29/5/95 - introduced -mo option to limit length of overlap length in
          processed pairs.

27/3/95 - introduced Rabin-Karp as alternative reduction procedure for
  longer left hand sides, + associated "-rk minlen mineqns" option.

14/3/95 - introduced -ro option to resume, but re-including the original
          equations

3/3/95 - started introduction of wtlex and wreathprod orderings.

31/1/95 - bug corrected due to building full table when one lhs is a prefix
of another. Patch by doing repeated tidyings before building full table.
Also introduced variable lostinfo - this is set true if an equation is dicarded
because it is too long during tidying - when this haapens, the monoid may have
changed.
Warning message printed at end when this occurs.

18/1/95 various reorganisation - extra components to rws structure
 (including test1, test2 -> rws.testword1,rws.testword2).
 automatic doubling of maxslowhistoryspace when required
 option -mrl n  to set maxreducelen
 file rwsio.c reorganised and split into rwsio.c and rwsio2.c.

13/1/95 introduced exit code 0 for "successful" completeion.

24/12/94 introduced variable current_maxstates -
unlike maxstates, this may be increased (doubled) if necessary.
If maxstates is set explicitly, then current_maxstates and maxstates are
equal. Otherwise, the initial value of current_maxstates is determined
by allotting INIT_FSASPACE space to the reduction automaton.

21/12/94 introduced wd_record array to remember progress of calculation and
try to decide when to stop; also options -mt and -hf (see below).

9/11/94 introduced options -v, -silent for verbosity of output - same in
all other programs.

6/10/94 - reduction algorithms moved to file reduce.c
Also rws structure introduced.

27/9/94 -
(i) Changed field-name generators to generatorOrder in input/output files.
(ii) Introduced -op option to output prefixes corresponding to states of fsa.

22/9/94 -
(i) introduced boolean array done.
For i an equation number, done[i] true means that equation number i has
been processed. So if done[i] and done[j] are both true, then there is no
need to test for overlaps. This is mainly useful when re-running. 
(ii) The option -r (resume) to take input from group.kbprog, presumed
to be output of a previous run.
(iii) -cn confnum option introduced. If more than this number of pairs
of equations.eqns are tested for overlaps with no new equations.eqns being
discovered, then a fast check for confluence is made using routine conf_check.
confnum=0 switches this test off.

This is the version with GAP input/output by dfh starting 13/9/94
(using some ideas and code by Peter Proehle of 9/5/94)
A new feature - not all generators need have inverses listed, but all
listed inverses must be 2-sided, and the inv_of function must be involutory.
Only generators with inverses will be cancelled in the routine "insert".

!! options added by dfh starting 30/3/94. 
   -mlr maxlenleft maxlenright
   Only equations with lhs having length at most maxlenleft,
   rhs having length at most maxlenright are stored.

   -sort maxoplen
   Output rules up to length of lhs up to maxoplen in increasing order of length
   of lhs. (maxoplen=0 means no maximum)

   Some changes were made to this code by Jamie P. Curmi during
   February/March 1992.

NEW SYNOPSIS (for GAP version)
    kbprog  [-r] [-ro] [-t tidyint] [-me maxeqns] [-ms maxstates]
    [-sort maxoplen] [-mlr maxlenleft maxlenright]
    [-mo maxoverlaplen] [-mrl maxreducelen]
    [-lex] [-rec] [-rtrec] [-wtlex] [-wreath]
    [-cn confnum] [-op] [-mt min_time] [-hf halting_factor]
    [-rk minlen mineqns] [-wd] [-vwd] [-mwd maxwdiffs]
    [-v] [-ve] [-vv] [-silent] groupname

OPTIONS
     -r    Resume. Take input from groupname.kbprog - output also
    goes to groupname.kbprog and overwrites input.

     -ro  Resume. Take input from groupname.kbprog, and also re-read
    the original equations from groupname and append them
    to the end - output also goes to groupname.kbprog and
    overwrites input.

     -t      tidyint
      Set the value of rws.tidyint equal to tidyint.

     -me    maxeqns
    At most maxeqns equations are allowed. If more are
    generated, tidying up and output occur.

     -ms    maxstates
    At most maxstates states are allowed in the fsa.
    If more are generated, tidying up and output occur.

     -sort  maxoplen
    The equations are sorted into increasing length order
    before output. Only those with lhs up to length maxoplen
    are output. maxoplen=0 means no restriction.

     -mlr   maxlenleft maxlenright
    Only equations with lhs and rhs of lengths at most
    maxlenleft and maxlenright are stored.

     -mo    maxoverlaplen
    Only overlaps of total length at most maxoverlaplen are
    processed.

     -lex  Short-lexicographical ordering
    ** THE DEFAULT SETTING **
      This is the original ordering used in kbprog.c.
    The ordering is lexicographic, with longer words having
    higher order than shorter words.

     -rec  Recursive Path ordering
    ordering based on that described in the book "Confluent String
    Rewriting" by Matthias Jantzen, Defn 1.2.14, page 24.
    The algorithm is described at the header of 'rec_compare'

     -rtrec  Recursive Path ordering
    ordering based on that described in the book "Confluent String
    Rewriting" by Matthias Jantzen, Defn 1.2.14, page 24.
    The algorithm is described at the header of 'rt_rec_compare'
    rtrec orders from the right of the words, whereas
    rec orders from the left - sometimes one is more
    efficient than the other in particular examples.

    -wtlex  Weighted short-lexicographical ordering
    A generalisation of shortlex. All genertors have a weight
    (specified in the input file), and the weightsof the generators
    in a word are added up to determine the "length" of the word.
    So shortlex is the special case where all weights are 1.

    -wreath  Wreath product ordering, as defined in Sims' book.
    A generalisation of recursive, where the generators have
    levels, and words in genertators at a fixed level are
    compared using shortlex. Recursive is the special case
    where the levels are 1,2,3,...

    -cn      confnum
    If confnum pairs of equations are processed for overlaps
    and no new equations are discovered, then a fast
    confluence test is performed. Setting confnum=0 turns this
    off.
    -mt     min_time
    -hf      halting_factor
    Only applies when word-differences are being computed.
    (Roughly) if halting_factor is set to be > 0, and
    the number of equations and the number of states
    has increased by more than halting_factor percent since the
    number of word-differences was last less than what it now is,
    and at least min_time seconds have elapsed, then halt.
    Alternatively, halt irrespective of elapsed time if number of
    equations has increased by 2*halting_factor percent.
    These conditions are highly experimental.
    -op    The states of the fsa correspond to prefixes of the left
    hand sides of equations When this option is set, these
    prefixes are output as state-names.
    -rk     minlen mineqns
    When there are at least mineqns equations, start using the
    Rabin-Karp reduction method on left-hand-sides having length
    at least minlen
    -wd    After each tidying, calculate word-differences and re-order
    equations so that those which result in the word-difference
    fsa changing get higher priority in the Knuth-Bendix.
    On completeion, the word-difference machines are output
    instead of the updated rewriting system.
    -vwd        (verbose word-differences) out put new word-differences
                as they are found, together with the equation they come from.
    -mwd    maxwdiffs
    Set the maximum number of worddiffs to be maxwdiffs.

    -silent  No output to stdout.
    -v    Verbose output.
    -ve         Print all equations as found with overlap information.
    -vv         Very verbose output - print more diagnostic information.


EXIT STATUS:
  0 if completion is successful, in the sense that either a confluent set
  is produced, or the halting-factor conditions are satsified when word-
  differences are being computed. This is for use in the "automata" shellscript.
  1 for badusage_kbprog, failure of malloc, etc.,
  2 if there is output, but completion is not successful in the sense above.

CHANGES TO KBPROG
      The orderings options -red, -rtred above.  I have tried to make the code
      as easy as possible to modify in case new ordering options are to be
      included (such as weighted lexicographical ordering) in the future.

      The code has been 'beautified' using a C-Beautifier on our system.
      This helped with my understanding of the algorithms, and
      modifications.    - J.P.Curmi (1992)

*/


#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <sys/times.h>

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"

#ifdef SYSTEMV
#define HZTIME     100
#else
#define HZTIME    60
#endif
#define MAXREDUCELENFAC 200
#define MAXCYCLES  16384

#define  USAGE\
  "Usage: kbprog [-r] [-ro] [-t tidyint] [-me maxeqns] [-ms maxstates]\n\
  [-sort maxoplen] [-mlr maxlenleft maxlenright] [-mo maxoverlaplen]\n\
  [-mrl maxreducelen] [-v] [-ve] [-vv] [-silent]\n\
  [-lex] [-rec] [-rtrec] [-wtlex] [-wreath]\n\
  [-wd] [-vwd] [-mwd maxwdiffs] [-mt min_time] [-hf halting_factor]\n\
  [-rk minlen mineqns] [-cn confnum] [-op] groupname\n"

boolean kbm_onintr; /* set true on interrupt signal */
static char  inf[100],   /* name of input file */
            outf[100], /* name of output file for rewriting system 
                              = inf.kbprog   */
           outfr[100], /* name of output file for rws.reduction_fsa
           for rewriting system - inf.reduce */
           outf1[100], /* name of output file for first wd-machine 
                              = inf.diff1   */
           outf2[100], /* name of output file for second wd-machine 
                              = inf.diff2   */
           outfec[100], /* name of output file for GAP exit code
                              = inf.kbprog.ec   */
           outflog[100]; /* name of logfile for automata run */
static  FILE  *rfile, *wfile;

/* Functions defined in this file: */
void read_kbprog_command();
void interrupt_kbprog();
void output_and_exit_kbprog();
void badusage_kbprog();

/* Functions used in this file defined in other files: */
void set_defaults();
int  kbprog();
void sort_eqns();
void should_we_halt();
void read_kbinput();
void read_extra_kbinput();
void print_kboutput();
void print_wdoutput();
int initialise_wd_fsa();
void build_wd_fsa();
int  make_full_wd_fsa();
void rws_clear();
void fsa_clear();
void rk_clear();

void
read_kbprog_command(argc,argv,rwsptr)
  int             argc;
  char           *argv[];
  rewriting_system *rwsptr;
{
  int arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg], "-r") == 0) {
      rwsptr->resume = TRUE;
    }
    else if (strcmp(argv[arg], "-ro") == 0) {
      rwsptr->resume = rwsptr->resume_with_orig = TRUE;
    }
    else if (strcmp(argv[arg], "-t") == 0) {
      rwsptr->tidyintset = TRUE;
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->tidyint = atoi(argv[arg]);
                }
    else if (strcmp(argv[arg], "-me") == 0) {
      rwsptr->maxeqnsset = TRUE;
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->maxeqns = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-ms") == 0) {
      rwsptr->maxstatesset = TRUE;
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->maxstates = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-sort") == 0) {
      rwsptr->sorteqns = TRUE;
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->maxoplen = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-mlr") == 0) {
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->maxlenleft = atoi(argv[arg]);
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->maxlenright = atoi(argv[arg]);
      if (rwsptr->maxlenleft<=0 || rwsptr->maxlenright<=0)
                        /* invalid setting */
        rwsptr->maxlenleft=rwsptr->maxlenright=0;
    }
    else if (strcmp(argv[arg], "-mo") == 0) {
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->maxoverlaplen = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-mrl") == 0) {
      rwsptr->maxreducelenset = TRUE;
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->maxreducelen = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-rec") == 0) {
      rwsptr->orderingset = TRUE;
      rwsptr->ordering = RECURSIVE;
    }
    else if (strcmp(argv[arg], "-rtrec") == 0) {
      rwsptr->orderingset = TRUE;
      rwsptr->ordering = RT_RECURSIVE;
    }
    else if (strcmp(argv[arg], "-lex") == 0) {
      rwsptr->orderingset = TRUE;
      rwsptr->ordering = SHORTLEX;  /* DEFAULT! */
    }
    else if (strcmp(argv[arg], "-wtlex") == 0) {
      rwsptr->orderingset = TRUE;
      rwsptr->ordering = WTLEX;
    }
    else if (strcmp(argv[arg], "-wreath") == 0) {
      rwsptr->orderingset = TRUE;
      rwsptr->ordering = WREATHPROD;
    }
    else if (strcmp(argv[arg], "-cn") == 0) {
      rwsptr->confnumset = TRUE;
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->confnum = atoi(argv[arg]);
                }
    else if (strcmp(argv[arg], "-op") == 0) {
      rwsptr->outputprefixes = TRUE;
                }
    else if (strcmp(argv[arg], "-rk") == 0) {
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->rkminlen = atoi(argv[arg]);
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->rkmineqns = atoi(argv[arg]);
      if (rwsptr->rkminlen<=0 || rwsptr->rkmineqns<0)
                        /* invalid setting */
        rwsptr->rkminlen=rwsptr->rkmineqns=0;
    }
    else if (strcmp(argv[arg], "-wd") == 0) {
      rwsptr->worddiffs = TRUE;
    }
                else if (strcmp(argv[arg], "-vwd") == 0) {
                        kbm_print_level *= 7;
                        rwsptr->verboseset = TRUE;
                }
    else if (strcmp(argv[arg], "-mwd") == 0) {
      rwsptr->maxwdiffset = TRUE;
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->maxwdiffs = atoi(argv[arg]);
                }
    else if (strcmp(argv[arg], "-silent") == 0) {
      rwsptr->silentset = TRUE;
      kbm_print_level = 0;
    }
    else if (strcmp(argv[arg], "-v") == 0) {
      kbm_print_level *= 2;
      rwsptr->verboseset = TRUE;
    }
    else if (strcmp(argv[arg], "-vv") == 0) {
      kbm_print_level *= 3;
      rwsptr->verboseset = TRUE;
    }
    else if (strcmp(argv[arg], "-ve") == 0) {
      kbm_print_level *= 5;
      rwsptr->verboseset = TRUE;
    }
    else if (strcmp(argv[arg], "-mh") == 0) {
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->maxhad = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-mt") == 0) {
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->min_time = atoi(argv[arg]);
                }
    else if (strcmp(argv[arg], "-hf") == 0) {
      arg++;
      if (arg >= argc)
        badusage_kbprog();
      rwsptr->halting_factor = atoi(argv[arg]);
                }
    else {
      if (argv[arg][0] == '-')
        badusage_kbprog();
      strcpy(inf, argv[arg]);
      strcpy(outf, inf);
      strcat(outf, ".");
      strcat(outf, "kbprog");
      strcpy(outfec,outf);
      strcat(outfec,".ec");
      strcpy(outfr, inf);
      strcat(outfr,".reduce");
      if (rwsptr->worddiffs){
        strcpy(outf1, inf);
        strcat(outf1, ".");
        strcat(outf1, "diff1");
        strcpy(outf2, inf);
        strcat(outf2, ".");
        strcat(outf2, "diff2");
        strcpy(outflog, inf);
        strcat(outflog, ".");
        strcat(outflog, "log");
      }
    }
    arg++;
  }
  if (stringlen(inf)==0)
    badusage_kbprog();
}

void
interrupt_kbprog()
/* When the program receives an interrupt  signal, it continues until the
 * next tidying, and then stops and outputs.
 */
{
  kbm_onintr = TRUE;
  signal(SIGINT, SIG_DFL);
  signal(SIGKILL, SIG_DFL);
  signal(SIGQUIT, SIG_DFL);
}

main(argc, argv)
  int             argc;
  char           *argv[];
{
  rewriting_system rws;
  rewriting_system *rwsptr;
  int             i, j, k, l;

  setbuf(stdout, (char *) 0);
  setbuf(stderr, (char *) 0);

/* First set some default values of the rewriting-system fields. They may be
 * overridden by command-line or input in file.
 */
  rwsptr= &rws;
  set_defaults(rwsptr,FALSE);
  read_kbprog_command(argc,argv,rwsptr);
  rws.print_eqns = kbm_print_level>2 && kbm_print_level%5==0;

  if (rws.resume) {
      if ((rfile=fopen(outf,"r"))==0){
      fprintf(stderr,"Error: cannot open file %s\n",outf);
        exit(1);
      }
      read_kbinput(rfile,FALSE,rwsptr);
/* If we are re-running from previous output, validity checks on input
 * should not be necessary.
 */
  }
  else {
      if ((rfile=fopen(inf,"r"))==0){
      fprintf(stderr,"Error: cannot open file %s\n",inf);
        exit(1);
      }
      read_kbinput(rfile,TRUE,rwsptr);
  }
  fclose(rfile);

  if (rws.resume_with_orig) {
      if ((rfile=fopen(inf,"r"))==0){
      fprintf(stderr,"Error: cannot open file %s\n",inf);
        exit(1);
      }
      read_extra_kbinput(rfile,FALSE,rwsptr);
      fclose(rfile);
  }

  if (rws.maxlenleft>0) {
    k = rws.maxlenleft>rws.maxlenright ?
      rws.maxlenleft : rws.maxlenright;
    if (rws.maxreducelen>MAXREDUCELENFAC*k)
      rws.maxreducelen=50*k;
  }

  if (rws.worddiffs){
/*
    if (rws.ordering != SHORTLEX) {
            fprintf(stderr,
  "Word-difference calculation only makes sense for the shortlex ordering.\n");
     exit(1);
    }
*/
    if (!rws.confnumset)
      rws.confnum *=8;
/* If we are calculating word-differences, we are not interested in
 * lots of confluence tests.
 */
    for (i=1;i<=rws.num_gens;i++) if (rws.inv_of[i]==0){
      fprintf(stderr,
   "Word-difference calculation requires that all generators have inverses.\n");
      exit(1);
    }
    tmalloc(rws.wd_fsa,fsa,1);
    if (initialise_wd_fsa(
          rws.wd_fsa,rws.reduction_fsa->alphabet,rws.maxwdiffs)==-1)
      exit(1);
    tmalloc(rws.wd_record,struct wdr,MAXCYCLES+1);
    rws.hadct = 0;
    rws.tot_eqns = 0;
  }

  signal(SIGINT, interrupt_kbprog);
  signal(SIGKILL, interrupt_kbprog);
  signal(SIGQUIT, interrupt_kbprog);

  if (kbprog(rwsptr)==-1) exit(1);
  output_and_exit_kbprog(rwsptr);
}

void
output_and_exit_kbprog(rwsptr)
  rewriting_system *rwsptr;
{  int i, j, l, g;
  gen **pref, *w;
  int ndiff1, ndiff2;
  reduction_struct rs_rws;
  rs_rws.rws=rwsptr;
  if (rwsptr->exit_status==1)
    exit(rwsptr->exit_status);
  if (rwsptr->worddiffs){
    rwsptr->new_wd = 0;
    build_wd_fsa(rwsptr->wd_fsa,rwsptr->new_wd,&rs_rws);
    should_we_halt(rwsptr); /* to calculate factors */
    ndiff1 = rwsptr->wd_fsa->states->size;
    wfile = fopen(outf1,"w");
    print_wdoutput(wfile,".diff1",rwsptr);
    fclose(wfile);
    if (make_full_wd_fsa(rwsptr->wd_fsa,rwsptr->inv_of,1,&rs_rws)== -1)
      exit(1);
    ndiff2 = rwsptr->wd_fsa->states->size;
    wfile = fopen(outf2,"w");
    print_wdoutput(wfile,".diff2",rwsptr);
    fclose(wfile);
    fsa_clear(rwsptr->wd_fsa);
    tfree(rwsptr->wd_fsa);
    if (kbm_print_level>0) {
      printf("#Halting with %d equations.\n",rwsptr->num_eqns);
      printf(
                   "#First word-difference machine with %d states computed.\n",
                  ndiff1);
      printf(
                   "#Second word-difference machine with %d states computed.\n",
                  ndiff2);
    }
    if (kbm_print_level>=2) {
      printf("  #eqn_factor=%d, states_factor=%d\n",
          rwsptr->eqn_factor,rwsptr->states_factor);
    }
    if (rwsptr->exit_status==0 && kbm_print_level>0)
    printf("#System is confluent, or halting factor condition holds.\n");
    tfree(rwsptr->wd_record);
    if (rwsptr->rk_on)
      rk_clear(rwsptr);
  }
  else {
    if (rwsptr->sorteqns)
      sort_eqns(rwsptr->maxoplen,rwsptr);
    wfile = fopen(outf,"w");
    print_kboutput(wfile,rwsptr);
    fclose(wfile);
/* We complete the definition of the fsa before printing it */
    strcat(rwsptr->name,".reductionFSA");
    rwsptr->reduction_fsa->states->size = rwsptr->num_states;
    rwsptr->reduction_fsa->num_accepting = rwsptr->num_states;
    if (rwsptr->num_states==1) {
      tmalloc(rwsptr->reduction_fsa->accepting,int,2);
      rwsptr->reduction_fsa->accepting[1]=1;
    }
    if (rwsptr->outputprefixes){
/* In this case we want to output the prefixes of the left-hand sides of
 * equations associated with the states. First we must calculate them.
 */
      rwsptr->reduction_fsa->states->type = WORDS;
      rwsptr->reduction_fsa->states->alphabet_size =
                     rwsptr->reduction_fsa->alphabet->size;
      for (i=1;i<=rwsptr->reduction_fsa->alphabet->size;i++) {
       tmalloc(rwsptr->reduction_fsa->states->alphabet[i],char,
                   stringlen(rwsptr->reduction_fsa->alphabet->names[i])+1);
       strcpy(rwsptr->reduction_fsa->states->alphabet[i],
                                rwsptr->reduction_fsa->alphabet->names[i]);
      }
      tmalloc(rwsptr->reduction_fsa->states->words,gen *,rwsptr->num_states+1);
      pref = rwsptr->reduction_fsa->states->words;
      for (i=1;i<=rwsptr->num_states;i++){
        l = rwsptr->preflen[i];
        w = rwsptr->eqns[rwsptr->prefno[i]].lhs;
/* Copy prefix from w to pref[i] */
        tmalloc(pref[i],gen,l+1);
        for (j=0;j<l;j++)
           pref[i][j] = w[j];
        pref[i][l] = 0;
      }
    }
    wfile = fopen(outfr,"w");
    fsa_print(wfile,rwsptr->reduction_fsa,rwsptr->name);
    fclose(wfile);
    if (kbm_print_level>0)
      printf("#Halting with %d equations.\n",rwsptr->num_eqns);
  }
  rws_clear(rwsptr);
  fsa_clear(rwsptr->reduction_fsa);
        tfree(rwsptr->reduction_fsa);
  if (rwsptr->lostinfo && kbm_print_level>0) {
    printf(
"WARNING: The monoid defined by the presentation may have changed, since\n\
         equations have been discarded.\n\
         If you re-run, include the original equations.\n");
  }
  if (kbm_print_level>1)
    printf("  #Exit status is %d\n",rwsptr->exit_status);
        wfile=fopen(outfec,"w");
        fprintf(wfile,"_ExitCode := %d;\n",rwsptr->exit_status);
        fclose(wfile);
  exit(rwsptr->exit_status);
}

void
badusage_kbprog()
{
  fprintf(stderr, USAGE);
  exit(1);
}
