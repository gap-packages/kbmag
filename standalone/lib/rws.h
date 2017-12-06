/* file rws.h
 * 6/2/98 - large scale re-organisation
 * 9.1.98. change `char' to `gen' for generator type.
 * 1.4.95. components rkminlen, rkmineqns added
 * 6/10/94.
 */

#ifndef KBMAG_RWS_H
#define KBMAG_RWS_H

#include <sys/times.h>

#include "fsa.h"

typedef enum {
  SHORTLEX,
  RECURSIVE,
  RT_RECURSIVE,
  WTLEX,
  WREATHPROD,
  NONE
} kbm_orderings;
/* Default ordering is SHORTLEX, the other is RECURSIVE path ordering.
 * WTLEX is where the generators have weights, and the length i
 * determined by adding up the weights of the generators in the strings.
 * (so SHORTLEX is WTLEX with all weights 1).
 * WREATHPROD is as defined in Sims' book, where generators have levels.
 * Note RECURSIVE is a special case of this, where levels are 1,2,3,...
 * NONE means order equations as they arrive - not very useful ?
 * If more orderings are required, add more constants here and alter
 * the compare routine.
 */

typedef struct {
  gen *lhs;           /* left hand side of equation stored as string */
  gen *rhs;           /* right hand side of equation stored as string */
  boolean done;       /* true if equation has been handled on a earlier run */
  boolean changed;    /* true if changed during tidying up */
  boolean eliminated; /* true if eliminated during tidying up */
} reduction_equation;

typedef struct {
  char name[256];         /* name of system for printing */
  kbm_orderings ordering; /* ordering used on strings */
  int *weight;            /* for wtlex ordering */
  int *level;             /* for wreathprod ordering */
  boolean confluent;      /* true if system has been proved confluent */
  int num_gens;
  int num_eqns;
  int num_inveqns;          /* number of equations at beginning of list
                             * of length 2 and form g*inv_of[g] = 1 */
  int *inv_of;              /* list of inverse numbers of generators */
  char **gen_name;          /* names of generators for printing */
  reduction_equation *eqns; /* list of equations */
  fsa *reduction_fsa;       /* finite state automaton for word reduction */
  int num_states;
  boolean worddiffs;  /* true if computing word-differences */
  fsa *wd_fsa;        /* word-difference machine */
  boolean cosets;     /* true if doing a cosets calculation */
  boolean wd_reorder; /* reorder equations to promote those that
                       * gave rise to new word-diffs -
                       * should be true */
  boolean *new_wd;    /* for recording which equations gave
                       * rise to new word-diffs */
  int maxlenleft;     /* max stored length of lhs of equation */
  int maxlenright;    /* max stored length of rhs of equation */
  int maxoverlaplen;  /* max overlap length processed */
  boolean hadlongoverlap;
  int rkminlen;  /* min length for Rabin-Karp word reduction */
  int rkmineqns; /* min no of eqns for Rabin-Karp reduction */
  boolean rk_on; /* start using Rabin-Karp */
  int *history;  /* state history on reduction */
  int **slowhistory;
  int *slowhistorysp; /* for use in slow-reduction */
  int *preflen;
  int *prefno;            /* for recording prefixes of left-hand-sides
                           * when building reduction fsa. */
  int maxpreflen;         /* max. length of prefix */
  boolean outputprefixes; /* output names of states of reduction fsa */
  gen *testword1;
  gen *testword2;   /* for storing words during reduction */
  boolean sorteqns; /* true if equations are to be sorted
                     * by length before output. */
  int tidyint;      /* tidying up interval */
  int *eqn_no;      /* eqn_no[i]=j means the i-th equation read in becomes
                     * equation number j. (usually i=j) - needed only if the
                     * "done" values are read in.
                     */
  int nneweqns;
  int tot_eqns; /* like rws.num_eqns, but not decreased if we
                 * throw equations away when maxeqns exceeded. */
  int hadct;
  int maxhad;
  int maxoplen;       /* max length of equations output -
                       * only used if sorteqns is true */
  boolean print_eqns; /* print equations as they are generated */
  int maxeqns;        /* maximum number of equations */
  boolean hadmaxeqns; /* true when max. exceeded */
  int confnum;        /* number of tests before fast confluence */
  int oldconfnum;     /* number of tests before fast confluence */
  int maxslowhistoryspace;
  int maxreducelen;      /* max. length allowed when reducing */
  int maxstates;         /* maximum number of states in red. machine */
  int current_maxstates; /* maximum number of states in red. machine */
  boolean double_states; /* do when current_maxstates exceeded */
  int init_fsaspace;     /* initial table space in red. machine */
  int maxwdiffs;
  int exit_status;    /* code for returning on exit */
  boolean tidyon;     /* set when time to tidy */
  boolean tidyon_now; /* set when time to tidy immediately */
  /* The following items are used to record progress of calculation,
   * and for trying to decide when to stop - this is a difficult problem!
   * They are only used when we are calculating word-differences.
   */
  struct wdr {
    int num_eqns;
    int num_states;
    int num_diff;
  } * wd_record; /* one entry for each calculation of word-differences, after
                  * tidying */

  int num_cycles; /* number of times we have been through the
                   * tidying loop */
  int eqn_factor; /* Percentage by which number of equations has increased since
                   * number of word-differences increased. No sense in
                   * halting unless > 0.  */
  int states_factor; /* Percentage by which number of states has increased
                      * since number of word-differences increased.  */
  int halting_factor;
  int min_time;
  boolean halting; /* true when time to halt */
  boolean do_conf_test;
  boolean lostinfo;         /* true when definign relations thrown away */
  boolean resume;           /* true when re-running */
  boolean resume_with_orig; /* true when re-running + original equations */
  /* the next ones are set true when set in command-line, since
   * this overrides settings in the input file.
   */
  boolean tidyintset;
  boolean maxeqnsset;
  boolean maxstatesset;
  boolean orderingset;
  boolean silentset;
  boolean verboseset;
  boolean confnumset;
  boolean maxreducelenset;
  boolean maxwdiffset;
  /* The final few are needed only when cosets is true */
  int separator; /* assumed to be generator with name "_H" */
  int maxlhsrellen;
  int maxsubgenlen;
  int maxcosetlen;
  boolean finitestop;
  boolean Hoverlaps;
  boolean Gislevel;     /* true if all gens. of G have same level */
  boolean Hislevel;     /* true if all gens. of H have same level */
  boolean Hhasinverses; /* true if all H-gens have inverses */
  srec *wd_alphabet;
  gen **subwordsG;
} rewriting_system;

/* The reduction_struct is just a typedef for the second parameter of
 * the word_reduce function, which is sometimes a rewriting system and
 * sometimes a word-difference fsa + separator symbol.
 */
typedef struct {
  rewriting_system *rws;
  fsa *wd_fsa;
  int separator;
  /* the last three are just for weight-lex reduction */
  fsa *wa;
  int *weight;
  int maxreducelen;
} reduction_struct;

void set_separator(rewriting_system *rwsptr);

fsa *fsa_triples(fsa *waptr, fsa *diffptr, storage_type op_table_type,
                 boolean destroy, char *tempfilename,
                 reduction_equation *eqnptr, int maxeqns, boolean eqnstop,
                 boolean *foundeqns, boolean readback);

fsa *fsa_mitriples(fsa *waptr, fsa *diffptr, storage_type op_table_type,
                   boolean destroy, char *tempfilename,
                   reduction_equation *eqnptr, int maxeqns, boolean eqnstop,
                   boolean *foundeqns, boolean readback);

int fsa_checkmult(fsa *multptr, reduction_equation *eqnptr, int maxeqns,
                  boolean cosets, int separator);
fsa *fsa_diff(fsa *fsaptr, reduction_struct *rs_wd, storage_type op_table_type);
fsa *fsa_difflabs(fsa *fsaptr, reduction_struct *rs_wdptr,
                  storage_type op_table_type, boolean destroy,
                  char *tempfilename, boolean readback);

int slow_rws_reduce(gen *w, reduction_struct *rs_rws);

void read_extra_kbinput(FILE *rfile, boolean check, rewriting_system *rwsptr);
void read_kbinput_simple(FILE *rfile, boolean check, rewriting_system *rwsptr);
void read_kbinput(FILE *rfile, boolean check, rewriting_system *rwsptr);

void read_inverses(FILE *rfile, rewriting_system *rwsptr);
void read_gens(FILE *rfile, rewriting_system *rwsptr);
void read_subgens(FILE *rfile, gen **words, boolean names, boolean inverses,
                  rewriting_system *rwsptr);

void set_defaults(rewriting_system *rwsptr, boolean cosets);

void build_quicktable(rewriting_system *rwsptr);
int modify_table(int relno, rewriting_system *rwsptr);
int insert(gen **lhs, gen **rhs, rewriting_system *rwsptr);

/* rabkar.c */
int rk_init(rewriting_system *rwsptr);
void rk_reset(int maxeqns);
void rk_clear(rewriting_system *rwsptr);
void rk_add_lhs(int n, rewriting_system *rwsptr);
int slow_rws_reduce_rk(gen *w, reduction_struct *rs_rws);
boolean slow_check_rws_reduce_rk(gen *w, int i, rewriting_system *rwsptr);

/* rwsreduce.c */
void rws_clear(rewriting_system *rwsptr);
int rws_reduce(gen *w, reduction_struct *rs_rws);
int slow_rws_reduce(gen *w, reduction_struct *rs_rws);
boolean slow_check_rws_reduce(gen *w, int i, rewriting_system *rwsptr);


#endif
