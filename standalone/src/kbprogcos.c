/* kbprogcos.c

2/6/98  - large-scale re-organisation. Abolish almost all global variables
          and make them components of the rws structure.
17/1/98 - changes resulting from intorduction of `gen' type in place of
          char for generators.

6/5/96  - introduced -vwd option (verbose word-differences) to output
          new word-differences as they are found, together with the
          reduction equation that they come from.
3/4/95 - added option -nho.
15/3/95 - change synopsis from
          kbprogcos [options] filename   to
          kbprogcos [options] groupname [cosname]
    cosname defaults to "cos".
    input from (except with -r, -ro):
    groupname.cosname
          output to:
          groupname.cosname.kbprog, groupname.cosname.reduce   OR
    groupname.cosname.midiff1, groupname.cosname.midiff2.
26/7/95 - started tidying everything up and making stable.
    Symbol for subgroup generator is fixed as _H.
    Made -f option to exit after index is finite and determined.
   (Uses criterion of Sims "Computation with FP Groups", p. 148-9.)
  Only wreathprod ordering is allowed, so all ordering options removed.
  Ordering of generators must be G-generators first, then separator _H,
  the H-generators. Must have
  Level(G-generator) > Level(separator) >= Level(H-generator)
  for all G-gens and H-gens.

24/7/95 - introduce word-difference calculation in cosets context.
Introduce array subwordsG of words in G-generators for subgroup gens.

4/7/95  - copied kbprog.c to this file kbprogcos.c, and started experimental
  work on version for cosets

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
because it is too long during tidying - when this happens, the monoid may have
changed.
Warning message printed at end when this occurs.

18/1/95 various reorganisation - extra components to rws structure
 (including test1, test2 -> rws.testword1,rws.testword2).
 automatic doubling of rws.maxslowhistoryspace when required
 option -mrl n  to set rws.maxreducelen
 file rwsio.c reorganised and split into rwsio.c and rwsio2.c.

13/1/95 introduced exit code 0 for "successful" completeion.

24/12/94 introduced variable current.maxstates -
unlike rws.maxstates, this may be increased (doubled) if necessary.
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
    kbprogcos  [-f] [-r] [-ro] [-t tidyint] [-me maxeqns] [-ms maxstates]
    [-sort maxoplen] [-mlr maxlenleft maxlenright]
    [-mo maxoverlaplen] [-nho] [-mrl maxreducelen]
    [-cn confnum] [-op] [-mt min_time] [-hf halting_factor]
    [-rk minlen mineqns]
    [-wd] [-vwd] [-mwd maxwdiffs] [-v] [-silent] groupname [cosname]

OPTIONS
     -f    Use Sims' criterion (see top of file) to stop when index
    of subgroup becomes finite and determined.
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
     -nho  Do not process overlaps when one of the equations is in the
    subgroup generators alone.
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


EXIT STATUS:
  0 if completion is successful, in the sense that either a confluent set
  is produced, or the halting-factor conditions are satsified when word-
  differences are being computed. This is for use in the "automata" shellscript.
  1 for badusage_kbprogcos, failure of malloc, etc.,
  2 if there is output, but completion is not successful in the sense above.

*/


#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <sys/times.h>

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"

#define MAXREDUCELENFAC 200
#define MAXCYCLES 16384

#define USAGE                                                                  \
  "Usage: kbprogcos [-f] [-r] [-ro] [-t tidyint] [-me maxeqns] [-ms maxstates]\n\
  [-sort maxoplen] [-mlr maxlenleft maxlenright] [-mo maxoverlaplen]\n\
  [-mrl maxreducelen] [-nho] [-v] [-silent]\n\
  [-wd] [-vwd] [-mwd maxwdiffs] [-mt min_time] [-hf halting_factor]\n\
  [-rk minlen mineqns] [-cn confnum] [-op] groupname [cosname]\n"

#define Ggen(x) (x < rwsptr->separator)
#define Hgen(x) (x > rwsptr->separator)

boolean kbm_onintr;
static char gpname[100], /* groupname */
    inf[100],            /* name of input file - groupname.cosname */
    outf[100],           /* name of output file for rewriting system
                                        = inf.kbprog   */
    outfr[100],          /* name of output file for rws->reduction_fsa
                            for rewriting system - inf.reduce */
    outf1[100],          /* name of output file for first wd-machine
                                = inf.midiff1   */
    outf2[100],          /* name of output file for second wd-machine
                                       = inf.midiff2   */
    outflog[100];        /* name of logfile for automata run */
static FILE *rfile, *wfile;

/* Functions defined in this file: */
static void badusage(void);
static void output_and_exit_kbprogcos(rewriting_system *rwsptr);

void read_kbprogcos_command(int argc, char *argv[], rewriting_system *rwsptr)
{
  int arg = 1;
  boolean seencosname = FALSE;
  boolean seengroupname = FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg], "-f") == 0) {
      rwsptr->finitestop = TRUE;
    }
    else if (strcmp(argv[arg], "-r") == 0) {
      rwsptr->resume = TRUE;
    }
    else if (strcmp(argv[arg], "-ro") == 0) {
      rwsptr->resume = rwsptr->resume_with_orig = TRUE;
    }
    else if (strcmp(argv[arg], "-nho") == 0) {
      rwsptr->Hoverlaps = FALSE;
    }
    else if (strcmp(argv[arg], "-t") == 0) {
      rwsptr->tidyintset = TRUE;
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->tidyint = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-me") == 0) {
      rwsptr->maxeqnsset = TRUE;
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->maxeqns = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-ms") == 0) {
      rwsptr->maxstatesset = TRUE;
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->maxstates = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-sort") == 0) {
      rwsptr->sorteqns = TRUE;
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->maxoplen = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-mlr") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->maxlenleft = atoi(argv[arg]);
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->maxlenright = atoi(argv[arg]);
      if (rwsptr->maxlenleft <= 0 || rwsptr->maxlenright <= 0)
        /* invalid setting */
        rwsptr->maxlenleft = rwsptr->maxlenright = 0;
    }
    else if (strcmp(argv[arg], "-mo") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->maxoverlaplen = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-mrl") == 0) {
      rwsptr->maxreducelenset = TRUE;
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->maxreducelen = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-cn") == 0) {
      rwsptr->confnumset = TRUE;
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->confnum = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-op") == 0) {
      rwsptr->outputprefixes = TRUE;
    }
    else if (strcmp(argv[arg], "-rk") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->rkminlen = atoi(argv[arg]);
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->rkmineqns = atoi(argv[arg]);
      if (rwsptr->rkminlen <= 0 || rwsptr->rkmineqns < 0)
        /* invalid setting */
        rwsptr->rkminlen = rwsptr->rkmineqns = 0;
    }
    else if (strcmp(argv[arg], "-wd") == 0) {
      rwsptr->worddiffs = TRUE;
    }
    else if (strcmp(argv[arg], "-vwd") == 0) {
      kbm_print_level = 4;
      rwsptr->verboseset = TRUE;
    }
    else if (strcmp(argv[arg], "-mwd") == 0) {
      rwsptr->maxwdiffset = TRUE;
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->maxwdiffs = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-silent") == 0) {
      rwsptr->silentset = TRUE;
      kbm_print_level = 0;
    }
    else if (strcmp(argv[arg], "-v") == 0) {
      kbm_print_level = 2;
      rwsptr->verboseset = TRUE;
    }
    else if (strcmp(argv[arg], "-vv") == 0) {
      kbm_print_level = 3;
      rwsptr->verboseset = TRUE;
    }
    else if (strcmp(argv[arg], "-mt") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->min_time = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-hf") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->halting_factor = atoi(argv[arg]);
    }
    else if (argv[arg][0] == '-')
      badusage();
    else if (!seengroupname) {
      seengroupname = TRUE;
      strcpy(gpname, argv[arg]);
    }
    else if (!seencosname) {
      seencosname = TRUE;
      sprintf(inf, "%s.%s", gpname, argv[arg]);
    }
    else {
      badusage();
    }
    arg++;
  }
  if (!seengroupname)
    badusage();

  if (!seencosname) /* use default */
    sprintf(inf, "%s.cos", gpname);

  strcpy(outf, inf);
  strcat(outf, ".");
  strcat(outf, "kbprog");
  strcpy(outfr, inf);
  strcat(outfr, ".reduce");
  if (rwsptr->worddiffs) {
    strcpy(outf1, inf);
    strcat(outf1, ".");
    strcat(outf1, "midiff1");
    strcpy(outf2, inf);
    strcat(outf2, ".");
    strcat(outf2, "midiff2");
    strcpy(outflog, inf);
    strcat(outflog, ".");
    strcat(outflog, "log");
  }
}

/* When the program receives an interrupt  signal, it continues until the
 * next tidying, and then stops and outputs.
 */
void interrupt_kbprogcos(int sig)
{
  kbm_onintr = TRUE;
  signal(SIGINT, SIG_DFL);
  signal(SIGKILL, SIG_DFL);
  signal(SIGQUIT, SIG_DFL);
}

int main(int argc, char *argv[])
{
  rewriting_system rws;
  rewriting_system *rwsptr;
  int i, j, k, l;
  gen *lhs, *rhs, *w;
  boolean ss;

  setbuf(stdout, (char *)0);
  setbuf(stderr, (char *)0);

  /* First set some default values of the rewriting-system fields. They may be
   * overridden by command-line or input in file.
   */

  rwsptr = &rws;
  set_defaults(rwsptr, TRUE);
  read_kbprogcos_command(argc, argv, rwsptr);
  rws.print_eqns = kbm_print_level > 2 && kbm_print_level % 5 == 0;

  if (rws.resume) {
    if ((rfile = fopen(outf, "r")) == 0) {
      fprintf(stderr, "Error: cannot open file %s\n", outf);
      exit(1);
    }
    read_kbinput(rfile, FALSE, rwsptr);
    /* If we are re-running from previous output, validity checks on input
     * should not be necessary.
     */
  }
  else {
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Error: cannot open file %s\n", inf);
      exit(1);
    }
    read_kbinput(rfile, TRUE, rwsptr);
  }
  fclose(rfile);

  if (rws.resume_with_orig) {
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Error: cannot open file %s\n", inf);
      exit(1);
    }
    read_extra_kbinput(rfile, FALSE, rwsptr);
    fclose(rfile);
  }

  if (rws.maxlenleft > 0) {
    k = rws.maxlenleft > rws.maxlenright ? rws.maxlenleft : rws.maxlenright;
    if (rws.maxreducelen > MAXREDUCELENFAC * k)
      rws.maxreducelen = 50 * k;
  }

  if (rws.ordering != WREATHPROD) {
    fprintf(stderr, "Error - ordering must be WREATHPROD in cosets program.\n");
    exit(1);
  }

  /* Check all initial equations have correct form  - either equations in
   * Ggens, equations in Hgens, or equations of form _H*Gword = Hword*_H*Gword
   */
  if (!rws.resume)
    for (i = 1; i <= rws.num_eqns; i++) {
      lhs = rws.eqns[i].lhs;
      if (Ggen(*lhs)) {
        /* Equation should be in Ggens only */
        for (j = 1; j < genstrlen(lhs); j++)
          if (!Ggen(lhs[j])) {
            fprintf(stderr, "Error: lhs of equation of incorrect form.\n");
            exit(1);
          }
        rhs = rws.eqns[i].rhs;
        for (j = 0; j < genstrlen(rhs); j++)
          if (!Ggen(rhs[j])) {
            fprintf(stderr, "Error: rhs of equation of incorrect form.\n");
            exit(1);
          }
      }
      if (Hgen(*lhs)) {
        /* Equation should be in Hgens only */
        for (j = 1; j < genstrlen(lhs); j++)
          if (!Hgen(lhs[j])) {
            fprintf(stderr, "Error: lhs of equation of incorrect form.\n");
            exit(1);
          }
        rhs = rws.eqns[i].rhs;
        for (j = 0; j < genstrlen(rhs); j++)
          if (!Hgen(rhs[j])) {
            fprintf(stderr, "Error: rhs of equation of incorrect form.\n");
            exit(1);
          }
      }
      else if (*lhs == rws.separator) {
        /* Equation should be of form _H*Gword = Hword*_H*Gword */
        for (j = 1; j < genstrlen(lhs); j++)
          if (!Ggen(lhs[j])) {
            fprintf(stderr, "Error: lhs of equation of incorrect form.\n");
            exit(1);
          }
        rhs = rws.eqns[i].rhs;
        ss = FALSE;
        for (j = 0; j < genstrlen(rhs); j++)
          if (rhs[j] == rws.separator)
            ss = TRUE;
          else if ((ss && !Ggen(rhs[j])) || (!ss && !Hgen(rhs[j]))) {
            fprintf(stderr, "Error: rhs of equation of incorrect form.\n");
            exit(1);
          }
      }
    }


  /* find rws.maxlhsrellen and rws.maxsubgenlen */
  rws.maxlhsrellen = rws.maxsubgenlen = 0;
  if (rws.worddiffs) {
    tmalloc(rws.subwordsG, gen *, rws.num_gens + 1);
    for (i = 1; i <= rws.num_gens; i++)
      rws.subwordsG[i] = 0;
  }
  for (i = 1; i <= rws.num_eqns; i++) {
    lhs = rws.eqns[i].lhs;
    if (*lhs == rws.separator) {
      if (genstrlen(lhs + 1) > rws.maxsubgenlen)
        rws.maxsubgenlen = genstrlen(lhs + 1);
      if (rws.worddiffs) {
        /* See if we have a definition of a subgroup generator - if so, record
         * it! */
        rhs = rws.eqns[i].rhs;
        if (rhs[1] == rws.separator) {
          j = rhs[0];
          tmalloc(rws.subwordsG[j], gen, genstrlen(lhs) + genstrlen(rhs) - 2);
          genstrcpy(rws.subwordsG[j], lhs + 1);
          l = genstrlen(rhs) - 2;
          if (l > 0) {
            w = rws.subwordsG[j] + genstrlen(rws.subwordsG[j]);
            for (k = 0; k < l; k++)
              w[k] = rws.inv_of[rhs[l + 1 - k]];
            w[l] = '\0';
          }
        }
      }
    }
    else if (Ggen(*lhs) && genstrlen(lhs) > rws.maxlhsrellen)
      rws.maxlhsrellen = genstrlen(lhs);
  }

  if (rws.worddiffs) {
    if (!rws.confnumset)
      rws.confnum *= 8;
    /* If we are calculating word-differences, we are not interested in
     * lots of confluence tests.
     */
    for (i = 1; i <= rws.num_gens; i++)
      if (i != rws.separator && rws.inv_of[i] == 0) {
        fprintf(stderr, "Word-difference calculation requires that all "
                        "generators have inverses.\n");
        exit(1);
      }
    if (!rws.Gislevel || !rws.Hislevel) {
      fprintf(stderr,
              "Word-difference calculation requires that all G-generators\n");
      fprintf(stderr, "and all H-generators have the same levels.\n");
      exit(1);
    }
    for (i = 1; i <= rws.num_gens; i++)
      if (Hgen(i)) {
        if (rws.subwordsG[i] == 0) {
          /* Perhaps its inverse has a definition. */
          if ((j = rws.inv_of[i]) && (w = rws.subwordsG[j])) {
            l = genstrlen(w);
            tmalloc(rws.subwordsG[i], gen, l + 1);
            for (k = 0; k < l; k++)
              rws.subwordsG[i][k] = rws.inv_of[w[l - 1 - k]];
            rws.subwordsG[i][l] = '\0';
          }
          else {
            fprintf(stderr,
                    "Error: Subgroup generator number %d has no definition.\n",
                    i);
            exit(1);
          }
        }
      }
    /* In the cosets situation, the base-alphabet for the word-
     * difference machines contains only the G-generators, so we
     * have to construct this alphabet.
     */
    tmalloc(rws.wd_alphabet, srec, 1);
    rws.wd_alphabet->type = IDENTIFIERS;
    rws.wd_alphabet->size = rws.separator - 1;
    tmalloc(rws.wd_alphabet->names, char *, rws.separator);
    for (i = 1; i < rws.separator; i++) {
      tmalloc(rws.wd_alphabet->names[i], char, genstrlen(rws.gen_name[i]) + 1);
      strcpy(rws.wd_alphabet->names[i], rws.gen_name[i]);
    }
    tmalloc(rws.wd_fsa, fsa, 1);
    if (initialise_wd_fsa_cos(rws.wd_fsa, rws.wd_alphabet, rws.maxwdiffs) == -1)
      exit(1);
    tmalloc(rws.wd_record, struct wdr, MAXCYCLES + 1);
    rws.tot_eqns = 0;
  }

  signal(SIGINT, interrupt_kbprogcos);
  signal(SIGKILL, interrupt_kbprogcos);
  signal(SIGQUIT, interrupt_kbprogcos);

  if (kbprog(rwsptr) == -1)
    exit(1);
  output_and_exit_kbprogcos(rwsptr);
}

static void output_and_exit_kbprogcos(rewriting_system *rwsptr)
{
  int i, j, l;
  gen **pref, *w;
  int ndiff1, ndiff2;
  reduction_struct rs_rws;
  rs_rws.rws = rwsptr;
  rs_rws.separator = rwsptr->separator;
  if (rwsptr->worddiffs) {
    rwsptr->new_wd = 0;
    build_wd_fsa_cos(rwsptr->wd_fsa, rwsptr->new_wd, &rs_rws);
    should_we_halt(rwsptr); /* to calculate factors */
    ndiff1 = rwsptr->wd_fsa->states->size;
    wfile = fopen(outf1, "w");
    print_wdoutput(wfile, ".midiff1", rwsptr);
    fclose(wfile);
    if (make_full_wd_fsa_cos(rwsptr->wd_fsa, rwsptr->inv_of, 1, &rs_rws) == -1)
      exit(1);
    ndiff2 = rwsptr->wd_fsa->states->size;
    wfile = fopen(outf2, "w");
    print_wdoutput(wfile, ".midiff2", rwsptr);
    fclose(wfile);
    fsa_clear(rwsptr->wd_fsa);
    tfree(rwsptr->wd_fsa);
    /* Writing info to a log-file - not sure if we want this at present.
        wfile = fopen(outflog,"w");
        fprintf(wfile,"eqn_factor:\t\t%d\n",rwsptr->eqn_factor);
        fprintf(wfile,"states_factor:\t\t%d\n",rwsptr->states_factor);
        fprintf(wfile,"diff1:\t\t%d\n",ndiff1);
        fprintf(wfile,"diff2:\t\t%d\n",ndiff2);
        fclose(wfile);
    */
    if (kbm_print_level > 0) {
      printf("#Halting with %d equations.\n", rwsptr->num_eqns);
      printf("#First word-difference machine with %d states computed.\n",
             ndiff1);
      printf("#Second word-difference machine with %d states computed.\n",
             ndiff2);
    }
    if (kbm_print_level >= 2) {
      printf("  #eqn_factor=%d, states_factor=%d\n", rwsptr->eqn_factor,
             rwsptr->states_factor);
    }
    if (rwsptr->exit_status == 0 && kbm_print_level > 0)
      printf("#System is confluent, or halting factor condition holds.\n");
    tfree(rwsptr->wd_record);
    if (rwsptr->rk_on)
      rk_clear(rwsptr);
    for (i = 1; i <= rwsptr->num_gens; i++)
      tfree(rwsptr->subwordsG[i]);
    srec_clear(rwsptr->wd_alphabet);
    tfree(rwsptr->wd_alphabet);
    tfree(rwsptr->subwordsG);
  }
  else {
    if (rwsptr->sorteqns)
      typelength_sort_eqns(rwsptr->maxoplen, rwsptr);
    else
      type_sort_eqns_final(rwsptr);
    make_fsa_nice(rwsptr);
    wfile = fopen(outf, "w");
    print_kboutput(wfile, rwsptr);
    fclose(wfile);
    /* We complete the definition of the fsa before printing it */
    strcat(rwsptr->name, ".reductionFSA");
    rwsptr->reduction_fsa->states->size = rwsptr->num_states;
    rwsptr->reduction_fsa->num_accepting = rwsptr->num_states;
    if (rwsptr->num_states == 1) {
      tmalloc(rwsptr->reduction_fsa->accepting, int, 2);
      rwsptr->reduction_fsa->accepting[1] = 1;
    }
    if (rwsptr->outputprefixes) {
      /* In this case we want to output the prefixes of the left-hand sides of
       * equations associated with the states. First we must calculate them.
       */
      rwsptr->reduction_fsa->states->type = WORDS;
      rwsptr->reduction_fsa->states->alphabet_size =
          rwsptr->reduction_fsa->alphabet->size;
      for (i = 1; i <= rwsptr->reduction_fsa->alphabet->size; i++) {
        tmalloc(rwsptr->reduction_fsa->states->alphabet[i], char,
                stringlen(rwsptr->reduction_fsa->alphabet->names[i]) + 1);
        strcpy(rwsptr->reduction_fsa->states->alphabet[i],
               rwsptr->reduction_fsa->alphabet->names[i]);
      }
      tmalloc(rwsptr->reduction_fsa->states->words, gen *,
              rwsptr->num_states + 1);
      pref = rwsptr->reduction_fsa->states->words;
      for (i = 1; i <= rwsptr->num_states; i++) {
        l = rwsptr->preflen[i];
        w = rwsptr->eqns[rwsptr->prefno[i]].lhs;
        /* Copy prefix from w to pref[i] */
        tmalloc(pref[i], gen, l + 1);
        for (j = 0; j < l; j++)
          pref[i][j] = w[j];
        pref[i][l] = 0;
      }
    }
    wfile = fopen(outfr, "w");
    fsa_print(wfile, rwsptr->reduction_fsa, rwsptr->name);
    fclose(wfile);
    if (kbm_print_level > 0)
      printf("#Halting with %d equations.\n", rwsptr->num_eqns);
  }
  rws_clear(rwsptr);
  fsa_clear(rwsptr->reduction_fsa);
  tfree(rwsptr->reduction_fsa);
  if (rwsptr->lostinfo && kbm_print_level > 0) {
    printf(
        "WARNING: The monoid defined by the presentation may have changed, since\n\
         equations have been discarded.\n\
         If you re-run, include the original equations.\n");
  }
  if (kbm_print_level > 1)
    printf("  #Exit status is %d\n", rwsptr->exit_status);
  exit(rwsptr->exit_status);
}

static void badusage(void)
{
  fprintf(stderr, USAGE);
  exit(1);
}
