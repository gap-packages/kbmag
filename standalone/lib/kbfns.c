/* kbfns.c  3/6/98
 * 22/5/01 - correct bug in procedure  conf_check when maxoverlaplen
 * is set.
 *
 * 18/2/00 - correct bug initialise inv_of field in set_defaults.
 * As part of large-scale re-organisation, these functions were moved
 * across from src/kbprog.c
 */

#include <sys/time.h>
#include <sys/resource.h>

#define MAXCYCLES 16384
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "externals.h"

#define MAXREDUCELEN 32767
#define MAXREDUCELENFAC 200
#define MAXCYCLES 16384
#define TIDYINT 100
#define MAXEQNS 32767
#define INIT_FSASPACE 262144
#define MAXWDIFFS 512
#define MAXSLOWHISTORYSPACE 131072
#define CONFNUM 500
#define Ggen(x) (x < rwsptr->separator)
#define Hgen(x) (x > rwsptr->separator)

extern boolean kbm_onintr;

int (*reduce_word)(gen *w, reduction_struct *rs_rws); /* The word-reduction
                                                       * function - it can be
                                                       * any of rws_reduce,
                                                       * slow_rws_reduce,
                                                       * slow_rws_reduce_rk.
                                                       */
boolean (*check_reduce_word)(gen *w, int i, rewriting_system *rwsptr);
/* The functionthat checks if a word is reduced.
 * slow_check_rws_reduce or slow_check_rws_reduce_rk
 */

/* Functions defined in this file: */
static void build_fulltable(rewriting_system *rwsptr);
int check_finite(rewriting_system *rwsptr, int max);
int compare(gen *w1, gen *w2, rewriting_system *rwsptr);
int conf_check(rewriting_system *rwsptr);
void consider(int k, int l, rewriting_system *rwsptr);
int tidyup(int crelno, rewriting_system *rwsptr);
int type_sort_eqns(int x, rewriting_system *rwsptr);
int wd_sort_eqns(int x, rewriting_system *rwsptr);

void set_defaults(rewriting_system *rwsptr, boolean cosets)
{
  rwsptr->inv_of = 0;
  rwsptr->maxlenleft = 0;
  rwsptr->maxlenright = 0;
  rwsptr->rkminlen = 0;
  rwsptr->rkmineqns = 0;
  rwsptr->weight = 0;
  rwsptr->level = 0;
  rwsptr->sorteqns = FALSE;
  rwsptr->maxoplen = 0;
  rwsptr->maxoverlaplen = 0;
  rwsptr->ordering = cosets ? WREATHPROD : SHORTLEX;
  rwsptr->tidyint = TIDYINT;
  rwsptr->maxeqns = MAXEQNS;
  rwsptr->maxstates = 0;
  rwsptr->init_fsaspace = INIT_FSASPACE;
  // rwsptr->current_maxstates;    // FIXME: should this be initialized???
  rwsptr->confluent = FALSE;
  rwsptr->confnum = CONFNUM;
  rwsptr->oldconfnum = 0;
  rwsptr->maxslowhistoryspace = MAXSLOWHISTORYSPACE;
  rwsptr->maxreducelen = MAXREDUCELEN;
  rwsptr->maxwdiffs = MAXWDIFFS;
  rwsptr->num_states = 0;
  rwsptr->exit_status = 0;
  rwsptr->tidyon = FALSE;
  rwsptr->tidyon_now = FALSE;
  rwsptr->worddiffs = FALSE;
  rwsptr->halting = FALSE;
  rwsptr->do_conf_test = FALSE;
  rwsptr->lostinfo = FALSE;
  rwsptr->tidyintset = FALSE;
  rwsptr->maxeqnsset = FALSE;
  rwsptr->hadmaxeqns = FALSE;
  rwsptr->maxstatesset = FALSE;
  rwsptr->orderingset = FALSE;
  rwsptr->silentset = FALSE;
  rwsptr->verboseset = FALSE;
  rwsptr->confnumset = FALSE;
  rwsptr->maxreducelenset = FALSE;
  rwsptr->maxwdiffset = FALSE;
  rwsptr->resume = FALSE;
  rwsptr->resume_with_orig = FALSE;
  rwsptr->outputprefixes = FALSE;
  rwsptr->wd_reorder = TRUE;
  rwsptr->double_states = FALSE;
  rwsptr->rk_on = FALSE;
  rwsptr->hadlongoverlap = FALSE;
  rwsptr->new_wd = 0;
  rwsptr->print_eqns = FALSE;
  rwsptr->maxpreflen = 0;
  rwsptr->nneweqns = 0;
  rwsptr->tot_eqns = 0;
  rwsptr->hadct = 0;
  rwsptr->maxhad = 0;
  rwsptr->wd_record = 0;
  rwsptr->num_cycles = 0;
  rwsptr->eqn_factor = 0;
  rwsptr->states_factor = 0;
  rwsptr->min_time = 0;
  rwsptr->halting_factor = 0;
  rwsptr->cosets = cosets;
  rwsptr->separator = 0;
  rwsptr->maxlhsrellen = 0;
  rwsptr->maxsubgenlen = 0;
  rwsptr->maxcosetlen = 0;
  rwsptr->finitestop = FALSE;
  rwsptr->Hoverlaps = cosets, rwsptr->Gislevel = FALSE;
  rwsptr->Hislevel = FALSE;
  rwsptr->Hhasinverses = FALSE;
  rwsptr->wd_alphabet = 0;
  rwsptr->subwordsG = 0;
}

int kbprog(rewriting_system *rwsptr)
{
  int i, j, k, l, cct, onum_eqns, onum_eqnsi;
  reduction_struct rs_rws;
  rs_rws.rws = rwsptr;
  rs_rws.separator = rwsptr->separator;

  /* The general policy is that
   * whenever a new relation is found, it is immediately compared with
   * all of the inverse relations. This seems to be most efficient. It
   * might also be a good idea to immediately compare new relations
   * with any other very short relations. Otherwise, a new relation has
   * to wait in the queue before being compared with the others.
   */
  rwsptr->tidyon = rwsptr->tidyon_now = FALSE;
  tmalloc(rwsptr->history, int, rwsptr->maxreducelen);
  tmalloc(rwsptr->slowhistory, int *, rwsptr->maxreducelen);
  tmalloc(rwsptr->slowhistorysp, int, rwsptr->maxslowhistoryspace);

  if (rwsptr->print_eqns)
    for (k = 1; k <= rwsptr->num_eqns; k++) {
      printf("    #Initial equation number %d:\n", k);
      *kbm_buffer = '\0';
      add_to_buffer(6, "#");
      l = add_word_to_buffer(stdout, rwsptr->eqns[k].lhs, rwsptr->gen_name);
      sprintf(kbm_buffer + strlen(kbm_buffer), " -> ");
      if (l > 0 || strlen(kbm_buffer) > 40) {
        printbuffer(stdout);
        add_to_buffer(8, "");
      }
      add_word_to_buffer(stdout, rwsptr->eqns[k].rhs, rwsptr->gen_name);
      printbuffer(stdout);
    }
  reduce_word = slow_rws_reduce;
  check_reduce_word = slow_check_rws_reduce;
  if (rwsptr->num_eqns == rwsptr->maxeqns) {
    rwsptr->tidyon = TRUE;
    rwsptr->tidyon_now = TRUE;
    kbm_onintr = TRUE;
  }
  else
    for (k = rwsptr->num_inveqns + 1; k <= rwsptr->num_eqns; k++) {
      for (l = 1; l <= rwsptr->num_inveqns; l++) {
        consider(k, l, rwsptr);
        if (rwsptr->exit_status == 1)
          return 0;
        if (rwsptr->tidyon_now)
          break;
        consider(l, k, rwsptr);
        if (rwsptr->exit_status == 1)
          return 0;
        if (rwsptr->tidyon_now)
          break;
      }
      if (rwsptr->tidyon_now)
        break;
    }

  if (kbm_onintr)
    rwsptr->tidyon = rwsptr->tidyon_now = TRUE;
  /* When tidy_on becomes true, we are due to tidy up, but we deal with
   * overlaps with inverse equations first - this can avoid an excessive
   * number of word-differences which later turn out to be redundant.
   * However, if tidy_on_now becomes true, we have too many new equations,
   * and we tidy up immediately.
   */

restart:
  rwsptr->nneweqns = 0;
  cct = 0;
  for (i = rwsptr->num_inveqns + 1; i <= rwsptr->num_eqns; i++) {
    onum_eqnsi = rwsptr->num_eqns;
    for (j = 1; j <= i; j++) {
      if (rwsptr->eqns[i].done && rwsptr->eqns[j].done)
        continue;
      if (rwsptr->tidyon)
        break; /* only there for when i = 1 */
      cct++;
      onum_eqns = rwsptr->num_eqns;
      consider(i, j, rwsptr);
      if (rwsptr->exit_status == 1)
        return 0;
      if (rwsptr->tidyon_now)
        break;
      if (i != j)
        consider(j, i, rwsptr);
      if (rwsptr->exit_status == 1)
        return 0;
      if (rwsptr->tidyon_now)
        break;
      if (rwsptr->num_eqns > onum_eqns)
        /* Compare new relations with inverse
         * relations */
        for (k = onum_eqns + 1; k <= rwsptr->num_eqns; k++) {
          for (l = 1; l <= rwsptr->num_inveqns; l++) {
            consider(k, l, rwsptr);
            if (rwsptr->exit_status == 1)
              return 0;
            if (rwsptr->tidyon_now)
              break;
            consider(l, k, rwsptr);
            if (rwsptr->exit_status == 1)
              return 0;
            if (rwsptr->tidyon_now)
              break;
          }
          if (rwsptr->tidyon_now)
            break;
        }
      if (rwsptr->tidyon)
        break;
    }
    /* If we have more than rwsptr->tidyint new relations since last
     * tidying up, then tidy; that is, go through all relations,
     * remove the redundant ones, and then redefine the FSA. This
     * will usually reduce its number of states. */
    if (kbm_onintr) {
      rwsptr->halting = rwsptr->tidyon = TRUE;
      rwsptr->exit_status = 2;
    }
    if (rwsptr->tidyon) {
      i = tidyup(i, rwsptr) - 1;
      if (rwsptr->exit_status == 1)
        return 0;
      if (rwsptr->cosets && rwsptr->finitestop) {
        build_fulltable(rwsptr);
        k = check_finite(rwsptr, 128);
        if (k) {
          printf("#Coset language has size %d.", k);
          rwsptr->maxoverlaplen =
              rwsptr->maxcosetlen + rwsptr->maxlhsrellen > rwsptr->maxsubgenlen
                  ? rwsptr->maxcosetlen + rwsptr->maxlhsrellen
                  : rwsptr->maxsubgenlen;
          printf(" Setting rws.maxoverlap length to %d.\n",
                 rwsptr->maxoverlaplen);
        }
        build_quicktable(rwsptr);
      }
      if (rwsptr->halting) {
        if (!rwsptr->worddiffs) {
          build_fulltable(rwsptr);
          reduce_word = rws_reduce;
        }
        return 0;
      }
      if (rwsptr->worddiffs) {
        if (rwsptr->wd_reorder)
          tmalloc(rwsptr->new_wd, boolean,
                  rwsptr->num_eqns + 1) else rwsptr->new_wd = 0;
        if (rwsptr->cosets) {
          if (build_wd_fsa_cos(rwsptr->wd_fsa, rwsptr->new_wd, &rs_rws) == -1) {
            rwsptr->exit_status = 1;
            return 0;
          }
        }
        else {
          if (build_wd_fsa(rwsptr->wd_fsa, rwsptr->new_wd, &rs_rws) == -1) {
            rwsptr->exit_status = 1;
            return 0;
          }
        }
        should_we_halt(rwsptr);
        if (rwsptr->halting)
          return 0;
        if (rwsptr->wd_fsa->states->size > rwsptr->maxwdiffs / 2) {
          gen **newwords;
          if (kbm_print_level > 2 && kbm_print_level % 3 == 0)
            printf("    #Increasing rwsptr->maxwdiffs to %d.\n",
                   rwsptr->maxwdiffs * 2);
          rwsptr->maxwdiffs *= 2;
          tmalloc(newwords, gen *, rwsptr->maxwdiffs + 1);
          for (j = 1; j <= rwsptr->wd_fsa->states->size; j++)
            newwords[j] = rwsptr->wd_fsa->states->words[j];
          tfree(rwsptr->wd_fsa->states->words);
          rwsptr->wd_fsa->states->words = newwords;
          tfree(rwsptr->wd_fsa->table->table_data_ptr[0]);
          tfree(rwsptr->wd_fsa->table->table_data_ptr);
          fsa_table_init(rwsptr->wd_fsa->table, rwsptr->maxwdiffs,
                         rwsptr->wd_fsa->alphabet->size);
          tfree(rwsptr->wd_fsa->table->table_data_dptr);
          if (fsa_table_dptr_init(rwsptr->wd_fsa) == -1)
            return -1;
        }
        clear_wd_fsa(rwsptr->wd_fsa);
        if (rwsptr->wd_reorder) {
          i = wd_sort_eqns(i, rwsptr) - 1;
          tfree(rwsptr->new_wd);
        }
      }
      else if (rwsptr->cosets)
        i = type_sort_eqns(i, rwsptr) - 1;
      rwsptr->tidyon = rwsptr->tidyon_now = FALSE;
      rwsptr->nneweqns = 0;
    }
    else if (onum_eqnsi == rwsptr->num_eqns) {
      /* Number of equations has not increased for this i.
       */
      if (rwsptr->confnum > 0 && cct >= rwsptr->confnum) {
        rwsptr->do_conf_test = TRUE;
        i = tidyup(i, rwsptr);
        if (rwsptr->exit_status == 1)
          return 0;
        if (kbm_print_level >= 2)
          printf("  #No new eqns for some time - testing for confluence\n");
        k = conf_check(rwsptr);
        if (rwsptr->exit_status == 1)
          return 0;
        if (k == 1) {
          if (rwsptr->hadlongoverlap && kbm_print_level > 0) {
            printf("#System is not guaranteed confluent, since not all "
                   "overlaps were processed.\n");
          }
          else if (rwsptr->cosets && !rwsptr->Hoverlaps &&
                   kbm_print_level > 0) {
            printf("#System is not guaranteed confluent, as no subgroup "
                   "overlaps were processed.\n");
          }
          else {
            if (kbm_print_level > 0)
              printf("#System is confluent.\n");
            rwsptr->confluent = TRUE;
          }
          return 0;
        }
        else if (k == -1) {
          if (kbm_print_level > 0)
            printf("#System is not confluent - halting because new equations "
                   "are too long.\n");
          return 0;
        }
        else if (rwsptr->halting)
          return 0;
        rwsptr->do_conf_test = FALSE;
        cct = 0;
      }
      else if (rwsptr->rk_on && rwsptr->oldconfnum > 0 &&
               cct >= 8 * rwsptr->oldconfnum) {
        if (kbm_print_level >= 2)
          printf("  #No new eqns for some time - will tidy up\n");
        rwsptr->tidyon = TRUE;
        cct = 0;
      }
    }
    else
      cct = 0;
    rwsptr->eqns[i].done = TRUE;
  }

  /* Algorithm has now completed. */
  if (kbm_print_level >= 2)
    printf("  #Search for overlaps is complete.\n");

  rwsptr->halting = TRUE;
  tidyup(rwsptr->num_eqns, rwsptr);
  if (rwsptr->exit_status == 1)
    return 0;
  k = conf_check(rwsptr);
  if (rwsptr->exit_status == 1)
    return 0;
  if (k == 1) {
    if (rwsptr->hadlongoverlap && kbm_print_level > 0) {
      printf("#System is not guaranteed confluent, since not all overlaps were "
             "processed.\n");
    }
    else if (rwsptr->cosets && !rwsptr->Hoverlaps && kbm_print_level > 0) {
      printf("#System is not guaranteed confluent, as no subgroup overlaps "
             "were processed.\n");
    }
    else {
      if (kbm_print_level > 0)
        printf("#System is confluent.\n");
      rwsptr->confluent = TRUE;
    }
  }
  else if (k == -1 && kbm_print_level > 0)
    printf("#System is not confluent - halting because new equations are too "
           "long.\n");
  else if (k == 0) {
    printf("#Search for overlaps is complete, but system is not confluent.\n");
    if (!kbm_onintr) {
      printf("#Let's try again then!\n");
      rwsptr->halting = FALSE;
      build_quicktable(rwsptr);
      reduce_word = slow_rws_reduce;
      goto restart;
    }
  }
  return 0;
}

/* Look at the words in rwsptr->testword1 and rwsptr->testword2, and remove any
 * common prefixes and suffixes of generators with inverses.
 * If they are not both empty at that stage, then use procedure
 * "compare" to see which word comes first in the ordering.
 * If using shortlex order, and length(bigger)-length(smaller) > 2, then
 * use inverses of generators to transfer generators from testword1 to
 * testword2.  Finally, copy testword1 and testword2 into *lhs, and *rhs
 * (after assigning space).
 * Return value is 0 if lhs and rhs are equal, 1 if the new equation is
 * inserted, and -1 if it is not inserted because it is too long
 * according to maxlenleft and maxlenright.
 */
int insert(gen **lhs, gen **rhs, rewriting_system *rwsptr)
{
  int bigger;
  gen *ptr1, *ptr2, *t1, *t2, *ts, *ptre1, *ptre2, *u1, *u2, *ptrc2a, *ptrc2b;
  int *inv = rwsptr->inv_of;

  ptr1 = rwsptr->testword1;
  ptr2 = rwsptr->testword2;
  if (genstrcmp(ptr1, ptr2) == 0)
    return 0;
  ptre1 = ptr1 + genstrlen(ptr1);
  ptre2 = ptr2 + genstrlen(ptr2);
  while (ptr1 < ptre1)
    if (*ptr1 == *ptr2 && inv[*ptr1])
      *(ptr1++) = *(ptr2++) = 0;
    else
      break;
  if (ptr1 == ptre1 && ptr2 == ptre2)
    return 0;
  if (*ptr1 && *ptr2)
    while (ptre1 > ptr1 && ptre2 > ptr2 &&
           *(ptre1 - 1) == *(ptre2 - 1) &&
           (inv[*(ptre1 - 1)] || *(ptre1 - 1) == rwsptr->separator)) {
      ptre1--;
      ptre2--;
    }
  t1 = ptr1;
  t2 = ptr2;
  *ptre1 = *ptre2 = '\0';

  /* Common prefixes and suffixes have now been stripped.
   * Now make t1 the larger.  */
  if (rwsptr->ordering != NONE)
    bigger = compare(t1, t2, rwsptr);
  else
    bigger = 1;
  if (bigger == 2) {
    ts = t1;
    t1 = t2;
    t2 = ts;
    ts = ptre1;
    ptre1 = ptre2;
    ptre2 = ts;
  }
  /* Now transfer terms from lhs to rhs if possible */
  if (rwsptr->ordering == SHORTLEX) {
    while (genstrlen(t1) > genstrlen(t2) + 2) {
      if (inv[*(ptre1 - 1)] == 0)
        break;
      ptre1--;
      *ptre2 = inv[*ptre1];
      *ptre1 = '\0';
      *(++ptre2) = '\0';
    }
    if (genstrlen(t1) == genstrlen(t2) + 2 && t2[0] && t1[0] > t2[0] &&
        inv[*(ptre1 - 1)]) {
      ptre1--;
      *ptre2 = inv[*ptre1];
      *ptre1 = '\0';
      *(++ptre2) = '\0';
    }
  }
  else if (rwsptr->cosets) {
    ptr1 = t1 - 1;
    while (++ptr1 < ptre1) {
      if (*ptr1 == rwsptr->separator && rwsptr->Hhasinverses) {
        if (ptr1 > t1) {
          ptrc2a = ptre2;
          ptre2 = ptrc2b = ptrc2a + (ptr1 - t1);
          while (ptrc2a >= t2)
            *(ptrc2b--) = *(ptrc2a--);
          while (t1 < ptr1)
            *(ptrc2b--) = rwsptr->inv_of[*(t1++)];
          ptrc2a = 0;
        }
        break;
      }
    }
    u1 = t1;
    ptr1 = t1 - 1;
    while (++ptr1 < ptre1)
      if (*ptr1 == rwsptr->separator) {
        u1 = ptr1 + 1;
        break;
      }
    u2 = t2;
    ptr2 = t2 - 1;
    while (++ptr2 < ptre2)
      if (*ptr2 == rwsptr->separator) {
        u2 = ptr2 + 1;
        break;
      }

    if (genstrcmp(u1, u2) == 0) {
      fprintf(stderr, "Unexpected situation. Could be a bug.\n");
      return 0;
    }

    if ((rwsptr->Gislevel && Ggen(*u1)) || (rwsptr->Hislevel && Hgen(*u1))) {
      while (genstrlen(u1) > genstrlen(u2) + 2) {
        if (rwsptr->inv_of[*(ptre1 - 1)] == 0)
          break;
        ptre1--;
        *ptre2 = rwsptr->inv_of[*ptre1];
        *ptre1 = '\0';
        *(++ptre2) = '\0';
      }
      if (genstrlen(u1) == 2 + genstrlen(u2) && u2[0] && u1[0] > u2[0] &&
          rwsptr->inv_of[*(ptre1 - 1)]) {
        ptre1--;
        *ptre2 = rwsptr->inv_of[*ptre1];
        *ptre1 = '\0';
        *(++ptre2) = '\0';
      }
    }
  }
  if (rwsptr->maxlenleft > 0 && (genstrlen(t1) > rwsptr->maxlenleft ||
                                 genstrlen(t2) > rwsptr->maxlenright))
    return -1;

  /* t1 is biggest according to the ordering, so it becomes the LHS of
   * the new relation.
   */
  tmalloc(*lhs, gen, genstrlen(t1) + 1) ptr1 = t1;
  ptr2 = *lhs;
  while (ptr1 < ptre1)
    *(ptr2++) = *(ptr1++);
  *(ptr2++) = '\0';
  tmalloc(*rhs, gen, genstrlen(t2) + 1) ptr1 = t2;
  ptr2 = *rhs;
  while (ptr1 < ptre2)
    *(ptr2++) = *(ptr1++);
  *(ptr2++) = '\0';

  return 1;
}


/* The left hand sides of the relations k and l are considered for common
 * parts, according to the Knuth-Bendix procedure, and any new relations
 * produced are processed.
 * We look for overlaps of either a suffix of equation k with a prefix of
 * equation l, or of a subword of eqn. k with the whole of eqn. l.
 */
void consider(int k, int l, rewriting_system *rwsptr)
{
  gen *midwd, *ptr1, *ptr2, *ptr, *testwd1, *testwd2;
  boolean ok;
  gen *tw1 = rwsptr->testword1, *tw2 = rwsptr->testword2;
  int mol = rwsptr->maxoverlaplen;
  int ne1;
  int r, n, pl;
  reduction_struct rs_rws;
  rs_rws.rws = rwsptr;
  rs_rws.separator = rwsptr->separator;

  testwd1 = rwsptr->eqns[k].lhs;
  testwd2 = rwsptr->eqns[l].lhs;
  if (rwsptr->cosets && !rwsptr->Hoverlaps &&
      (Hgen(testwd1[genstrlen(testwd1) - 1]) ||
       Hgen(testwd2[genstrlen(testwd2) - 1])))
    return;
  midwd = testwd1;
  pl = 0;
  if (rwsptr->cosets) {
    while (*midwd != '\0') {
      if (*midwd == rwsptr->separator) {
        pl = midwd - testwd1 + 1; /* the subgroup prefix length */
        break;
      }
      midwd++;
    }
  }
  midwd = testwd1;
  while (*midwd != '\0') {
    ne1 = rwsptr->num_eqns + 1;
    if (mol > 0 && (midwd - testwd1 - pl) + genstrlen(testwd2) > mol) {
      /* Any further overlap would exceed the permitted length */
      break;
    }
    ptr1 = midwd;
    ptr2 = testwd2;
    ok = TRUE;
    while (*ptr1 != '\0' && *ptr2 != '\0') {
      if (*ptr1 != *ptr2) {
        ok = FALSE;
        break;
      }
      ptr1++;
      ptr2++;
    }
    if (ok)
    /* An overlap has been found. The new equation
     * for consideration is inserted into words
     * rwsptr->testword1 and rwsptr->testword2. */
    {
      if (*ptr1 == '\0') {
        ptr1 = testwd1 - 1;
        ptr = tw1 - 1;
        while (++ptr1 < midwd)
          *(++ptr) = *ptr1;
        ptr1 = rwsptr->eqns[l].rhs - 1;
        while (*(++ptr1) != '\0')
          *(++ptr) = *ptr1;
        *(++ptr) = '\0';
        ptr1 = rwsptr->eqns[k].rhs - 1;
        ptr = tw2 - 1;
        while (*(++ptr1) != '\0')
          *(++ptr) = *ptr1;
        ptr1 = ptr2 - 1;
        while (*(++ptr1) != '\0')
          *(++ptr) = *ptr1;
        *(++ptr) = '\0';
      }
      else {
        ptr2 = testwd1 - 1;
        ptr = tw1 - 1;
        while (++ptr2 < midwd)
          *(++ptr) = *ptr2;
        ptr2 = rwsptr->eqns[l].rhs - 1;
        while (*(++ptr2) != '\0')
          *(++ptr) = *ptr2;
        ptr2 = ptr1 - 1;
        while (*(++ptr2) != '\0')
          *(++ptr) = *ptr2;
        *(++ptr) = '\0';
        ptr2 = rwsptr->eqns[k].rhs - 1;
        ptr = tw2 - 1;
        while (*(++ptr2) != '\0')
          *(++ptr) = *ptr2;
        *(++ptr) = '\0';
      }
      /* Now reduce rwsptr->testword1 and rwsptr->testword2,
       * using the current relations, and then install
       * them if they are different. */
      if (reduce_word(tw1, &rs_rws) == -1) {
        rwsptr->exit_status = 1;
        return;
      }
      if (reduce_word(tw2, &rs_rws) == -1) {
        rwsptr->exit_status = 1;
        return;
      }
      if (genstrlen(tw1) <= rwsptr->maxreducelen / 2 &&
          genstrlen(tw2) <= rwsptr->maxreducelen / 2 &&
          insert(&(rwsptr->eqns[ne1].lhs), &(rwsptr->eqns[ne1].rhs), rwsptr) >
              0) {
        /* We have a new equation */
        if (rwsptr->print_eqns) {
          printf("    #New equation number %d, from overlap %d, %d:\n", ne1, k,
                 l);
          *kbm_buffer = '\0';
          add_to_buffer(6, "#");
          n = add_word_to_buffer(stdout, rwsptr->eqns[ne1].lhs,
                                 rwsptr->gen_name);
          sprintf(kbm_buffer + strlen(kbm_buffer), "->");
          if (n > 0 || strlen(kbm_buffer) > 40) {
            printbuffer(stdout);
            add_to_buffer(8, "");
          }
          add_word_to_buffer(stdout, rwsptr->eqns[ne1].rhs, rwsptr->gen_name);
          printbuffer(stdout);
        }
        r = modify_table(ne1, rwsptr);
        if (r == -1) {
          tfree(rwsptr->eqns[ne1].lhs) tfree(rwsptr->eqns[ne1].rhs) return;
        }
        if (r == 1) {
          rwsptr->num_eqns++;
          rwsptr->tot_eqns++;
          rwsptr->eqns[ne1].done = FALSE;
          if (ne1 >= rwsptr->maxeqns) {
            if (kbm_print_level > 0)
              printf("#Maximum number of equations exceeded.\n");
            rwsptr->hadmaxeqns = TRUE;
            rwsptr->hadct++;
            rwsptr->tidyon = rwsptr->tidyon_now = TRUE;
            if (!rwsptr->worddiffs || rwsptr->hadct > rwsptr->maxhad) {
              rwsptr->halting = TRUE;
              rwsptr->exit_status = 2;
            }
            /* If we are calculating word-differences we do not
             * always need to stop.
             */
            return;
          }
          /* Decide if it is time to tidy up. */
          if (++rwsptr->nneweqns == rwsptr->tidyint)
            rwsptr->tidyon = TRUE;
          if (rwsptr->nneweqns == 2 * rwsptr->tidyint)
            rwsptr->tidyon_now = TRUE;
        }
      }
    }
    midwd++;
  }
}

/* Remove redundant relations. "crelno" is the current relation being
 * processed.
 * Return value is the new value of crelno, which may have changed as
 * a result of earlier equations being eliminated.
 */
int tidyup(int crelno, rewriting_system *rwsptr)
{
  int i, iv, nnum_eqns, lenl, lenr, totlenl, totlenr, maxlenl, maxlenr, ret;
  boolean moving, retain, red, some_changed;
  gen **newlhs, **newrhs, *testword1 = rwsptr->testword1,
                          *testword2 = rwsptr->testword2;
  reduction_equation **eqn = &(rwsptr->eqns);
  reduction_struct rs_rws;
  rs_rws.rws = rwsptr;
  rs_rws.separator = rwsptr->separator;

  ret = crelno;
repeat:
  tmalloc(newlhs, gen *, rwsptr->num_eqns + 1)
      tmalloc(newrhs, gen *, rwsptr->num_eqns + 1) for (i = 1;
                                                        i <= rwsptr->num_eqns;
                                                        i++)(*eqn)[i]
          .changed = (*eqn)[i].eliminated = FALSE;
  nnum_eqns = 0;
  moving = FALSE;
  some_changed = FALSE;
  totlenl = totlenr = 0;
  maxlenl = maxlenr = 0;
  for (i = 1; i <= rwsptr->num_eqns; i++) {
    genstrcpy(testword1, (*eqn)[i].lhs);
    genstrcpy(testword2, (*eqn)[i].rhs);
    iv = 0;
    red = check_reduce_word(testword1, i, rwsptr);
    if (red) {
      /* LHS is irreducible by other (*eqn) */
      retain = TRUE;
      if (reduce_word(testword2, &rs_rws) == -1) {
        rwsptr->exit_status = 1;
        return -1;
      }
      if (genstrlen(testword2) > rwsptr->maxreducelen / 2)
        iv = -1;
      if (genstrcmp(testword2, (*eqn)[i].rhs)) {
        /* RHS is reducible */
        some_changed = (*eqn)[i].changed = TRUE;
        (*eqn)[i].done = FALSE;
      }
    }
    else {
      /* LHS can be reduced using other equations */
      if (reduce_word(testword1, &rs_rws) == -1) {
        rwsptr->exit_status = 1;
        return -1;
      }
      if (reduce_word(testword2, &rs_rws) == -1) {
        rwsptr->exit_status = 1;
        return -1;
      }
      if (genstrlen(testword1) > rwsptr->maxreducelen / 2 ||
          genstrlen(testword2) > rwsptr->maxreducelen / 2)
        iv = -1;
      retain = genstrcmp(testword1, testword2);
      if (retain) {
        some_changed = (*eqn)[i].changed = TRUE;
        (*eqn)[i].done = FALSE;
      }
    }
    if ((*eqn)[i].changed) {
      if (iv == 0)
        iv = insert(newlhs + i, newrhs + i, rwsptr);
      retain = iv > 0;
      if (iv < 0)
        rwsptr->lostinfo = TRUE;
    }
    if (retain) {
      lenl = genstrlen(testword1);
      lenr = genstrlen(testword2);
      totlenl += lenl;
      totlenr += lenr;
      if (lenl > maxlenl)
        maxlenl = lenl;
      if (lenr > maxlenr)
        maxlenr = lenr;
    }
    else {
      moving = TRUE;
      (*eqn)[i].eliminated = TRUE;
    }
  }
  if (moving || some_changed) {
    moving = FALSE;
    for (i = 1; i <= rwsptr->num_eqns; i++)
      if (!(*eqn)[i].eliminated) {
        nnum_eqns++;
        if ((*eqn)[i].changed) {
          fflush(stdout);
          tfree((*eqn)[i].lhs) tfree((*eqn)[i].rhs)(*eqn)[i].lhs = newlhs[i];
          (*eqn)[i].rhs = newrhs[i];
        }
        if (moving)
        /* "moving" means that some previous
         * relations have not been retained,
         * and so we have to renumber words. */
        {
          fflush(stdout);
          (*eqn)[nnum_eqns].lhs = (*eqn)[i].lhs;
          (*eqn)[nnum_eqns].rhs = (*eqn)[i].rhs;
          (*eqn)[nnum_eqns].done = (*eqn)[i].done;
          (*eqn)[i].lhs = (*eqn)[i].rhs = 0;
          (*eqn)[i].done = FALSE;
        }
        if (i <= crelno)
          ret = nnum_eqns;
      }
      else {
        moving = TRUE;
        if (i <= rwsptr->num_inveqns)
          rwsptr->num_inveqns--;
        fflush(stdout);
        tfree((*eqn)[i].lhs) tfree((*eqn)[i].rhs)
      }
  }
  else
    nnum_eqns = rwsptr->num_eqns;
  /* If any relations have been changed or eliminated, then we
   * completely reconstruct the FSA from scratch.
   * This is not too time consuming provided that we do not
   * tidy up too often.
   */
  if (rwsptr->num_states > rwsptr->current_maxstates) { /* shouldn't happen */
    if (kbm_print_level > 0)
      printf("#Maximum number of states exceeded (why?).\n");
    rwsptr->halting = TRUE;
    rwsptr->exit_status = 2;
  }
  tfree(newlhs) tfree(newrhs) if (moving || some_changed || rwsptr->rk_on)
  {
    rwsptr->tot_eqns -= (rwsptr->num_eqns - nnum_eqns);
    rwsptr->num_eqns = nnum_eqns;
    if (rwsptr->rkmineqns > 0) {
      if (!rwsptr->rk_on && !rwsptr->halting &&
          rwsptr->num_eqns >= rwsptr->rkmineqns) {
        rwsptr->rk_on = TRUE;
        reduce_word = slow_rws_reduce_rk;
        check_reduce_word = slow_check_rws_reduce_rk;
        rwsptr->oldconfnum = rwsptr->confnum;
        rwsptr->confnum = 0;
        if (rk_init(rwsptr) == -1) {
          rwsptr->exit_status = 1;
          return -1;
        }
      }
      else if (rwsptr->rk_on && (rwsptr->num_eqns < rwsptr->rkmineqns ||
                                 (rwsptr->halting && !rwsptr->worddiffs))) {
        rwsptr->rk_on = FALSE;
        reduce_word = slow_rws_reduce;
        check_reduce_word = slow_check_rws_reduce;
        rwsptr->confnum = rwsptr->oldconfnum;
        rk_clear(rwsptr);
      }
    }
    build_quicktable(rwsptr);
    /* On the last time, we need to be certain that the set of equations is
     * reduced, so we repeat.
     */
    if (rwsptr->finitestop || rwsptr->halting || rwsptr->do_conf_test)
      goto repeat;
  }
  if (rwsptr->double_states)
    build_quicktable(rwsptr);
  /* otherwise maxstates won't get doubled! */
  struct rusage tmp;
  getrusage(RUSAGE_SELF, &tmp);
  i = tmp.ru_utime.tv_sec;
  if (kbm_print_level >= 2)
    printf("  #%d eqns; total len: lhs, rhs = %d, %d; %d states; %d secs.\n",
           rwsptr->num_eqns, totlenl, totlenr, rwsptr->num_states, i);
  if (kbm_print_level >= 3)
    printf("            max len: lhs, rhs = %d, %d.\n", maxlenl, maxlenr);

  return ret;
}

void build_quicktable(rewriting_system *rwsptr)
{
  int i;
  int **table;
restart:
  if (rwsptr->double_states) {
    rwsptr->current_maxstates *= 2;
    tfree(rwsptr->reduction_fsa->table->table_data_ptr[0]);
    tfree(rwsptr->reduction_fsa->table->table_data_ptr);
    fsa_table_init(rwsptr->reduction_fsa->table, rwsptr->current_maxstates,
                   rwsptr->num_gens);
    tfree(rwsptr->preflen);
    tfree(rwsptr->prefno);
    tmalloc(rwsptr->preflen, int, rwsptr->current_maxstates + 1);
    tmalloc(rwsptr->prefno, int, rwsptr->current_maxstates + 1);
    rwsptr->double_states = FALSE;
  }
  table = rwsptr->reduction_fsa->table->table_data_ptr;
  if (rwsptr->rk_on)
    rk_reset(rwsptr->maxeqns);
  rwsptr->num_states = 1;
  rwsptr->maxpreflen = 0;
  rwsptr->preflen[1] = rwsptr->prefno[1] = 0;
  for (i = 1; i <= rwsptr->num_gens; i++)
    set_dense_target(table, i, 1, 0);
  for (i = 1; i <= rwsptr->num_eqns; i++) {
    if (modify_table(i, rwsptr) == -1) {
      rwsptr->double_states = TRUE;
      goto restart;
    }
  }
}

/* This version returns a table which only rejects the left hand sides
 * of the rwsptr->eqns themselves.
 * Return value is -1 if rwsptr->current_maxstates is exceeded -  otherwise 1.
 */
int modify_table(int relno, rewriting_system *rwsptr)
{
  int genno, nextgenno, state, x, l, len, i;
  gen *ptr;
  int **table = rwsptr->reduction_fsa->table->table_data_ptr;

  ptr = rwsptr->eqns[relno].lhs;
  len = genstrlen(ptr);
  if (rwsptr->rk_on && len >= rwsptr->rkminlen) {
    rk_add_lhs(relno, rwsptr);
    return 1;
  }
  if (len + rwsptr->num_states > rwsptr->current_maxstates) {
    /* The number of states of the table could exceed the maximum, so we give up
     * immediately - if maxstates is set we stop completely, and otherwise we
     * double rwsptr->current_maxstates after next tidying.
     */
    if (rwsptr->current_maxstates == rwsptr->maxstates) {
      if (kbm_print_level > 0)
        printf("#Maximum number of states exceeded.\n");
      rwsptr->halting = TRUE;
      rwsptr->exit_status = 2;
    }
    else {
      if (kbm_print_level > 2 && kbm_print_level % 3 == 0)
        printf(
            "    #Current_maxstates exceeded - will tidy and increase to %d.\n",
            rwsptr->current_maxstates * 2);
      rwsptr->double_states = TRUE;
    }
    rwsptr->tidyon = rwsptr->tidyon_now = TRUE;
    return -1;
  }
  state = 1;
  genno = *(ptr++);
  l = 0;
  while ((nextgenno = *(ptr++))) {
    l++;
    x = dense_target(table, genno, state);
    if (x < 0)
      return 1;
    /* If that happens, the equation must have a prefix which is also a lhs.
     * We keep the equation for now - it will be reduced on the next tidying.
     */
    if (x == 0) {
      rwsptr->num_states++;
      for (i = 1; i <= rwsptr->num_gens; i++)
        set_dense_target(table, i, rwsptr->num_states, 0);
      rwsptr->preflen[rwsptr->num_states] = l;
      if (l > rwsptr->maxpreflen)
        rwsptr->maxpreflen = l;
      rwsptr->prefno[rwsptr->num_states] = relno;
      x = rwsptr->num_states;
      set_dense_target(table, genno, state, rwsptr->num_states);
    }
    state = x;
    genno = nextgenno;
  }
  set_dense_target(table, genno, state, -relno);
  return 1;
}

/* Extends the table to one rejecting all strings containing a lhs,
 * builds edges in E_2 - E_3 as in Sims' book, p. 118-9.
 */
static void build_fulltable(rewriting_system *rwsptr)
{
  int i, j, k, l;
  gen *w, *we;
  int **table = rwsptr->reduction_fsa->table->table_data_ptr;
  int *preflen = rwsptr->preflen;
  int *prefno = rwsptr->prefno;

  for (i = 1; i <= rwsptr->num_gens; i++)
    if (dense_target(table, i, 1) == 0)
      set_dense_target(table, i, 1, 1);
  for (l = 1; l <= rwsptr->maxpreflen; l++) {
    for (j = 2; j <= rwsptr->num_states; j++)
      if (preflen[j] == l) {
        w = rwsptr->eqns[prefno[j]].lhs;
        we = w + l;
        k = 1;
        while (++w < we)
          k = dense_target(table, *w, k);
        /* k is the image of 1 under the prefix representing state  j,
         * but with its first letter removed. */
        for (i = 1; i <= rwsptr->num_gens; i++)
          if (dense_target(table, i, j) == 0)
            set_dense_target(table, i, j, dense_target(table, i, k));
      }
  }
}

/* Compare words w1 and w2 to see which is bigger according to the ordering.
 * The ordering used here is longer words are bigger, and amongst equal
 * length words, lexicographical ordering according to the order of the
 * generators as input is used. (I use 'bigger' to mean greater in the
 * ordering.)  Returns  0 if w1=w2, 1 if w1 bigger than w2, otherwise 2.
 */
int lex_compare(gen *w1, gen *w2)
{
  int len1, len2, bigger = 0;
  gen *we1;

  len1 = genstrlen(w1);
  len2 = genstrlen(w2);
  we1 = w1 + len1;
  if (len1 > len2)
    bigger = 1;
  else if (len2 > len1)
    bigger = 2;
  else
    while (w1 < we1) {
      if (*w1 > *w2) {
        bigger = 1;
        break;
      }
      else if (*w2 > *w1) {
        bigger = 2;
        break;
      }
      w1++;
      w2++;
    }
  return bigger;
}

/* Compare words w1 and w2 to see which is bigger according to the ordering.
 * The ordering used here is longer words are bigger, where length is computed
 * by adding up the weights of the generators in the words, and amongst equal
 * length words, lexicographical ordering according to the order of the
 * generators as input is used. (I use 'bigger' to mean greater in the
 * ordering.)  Returns  0 if w1=w2, 1 if w1 bigger than w2, otherwise 2.
 */
int wtlex_compare(gen *w1, gen *w2, rewriting_system *rwsptr)
{
  int wtlen1, wtlen2, bigger = 0;
  gen *wp1, *wp2;

  wp1 = w1 - 1;
  wp2 = w2 - 1;
  wtlen1 = wtlen2 = 0;
  while (*(++wp1))
    wtlen1 += rwsptr->weight[*wp1];
  while (*(++wp2))
    wtlen2 += rwsptr->weight[*wp2];
  if (wtlen1 > wtlen2)
    bigger = 1;
  else if (wtlen2 > wtlen1)
    bigger = 2;
  else {
    wp1 = w1;
    wp2 = w2;
    while (*wp1) {
      if (*wp1 > *wp2) {
        bigger = 1;
        break;
      }
      else if (*wp2 > *wp1) {
        bigger = 2;
        break;
      }
      wp1++;
      wp2++;
    }
  }
  return bigger;
}

/* Compare words w1 and w2 to see which is 'bigger' according to the
   ordering. The ordering used here is recursive path ordering (based on
   that described in the book "Confluent String Rewriting" by Matthias Jantzen,
   Defn 1.2.14, page 24).
   Returns 1 if w1 is bigger than w2, 2 if w2 is bigger than w1,
   0 if equal.
   ----------------------------------------------------------------------
   The ordering is as follows:

   let u, v be elements of X*
   u >= v iff one of the following conditions is fulfilled;

   1) u = v      OR
   u = u'a, v = v'b for some a,b elements of X, u',v' elements of X*
   and then:
   2) a = b and u' >= v'    OR
   3) a > b and u  > v'    OR
   4) b > a and u'> v
   ----------------------------------------------------------------------
   Written by : Jamie P. Curmi (February 1992)
   Corrected by : dfh (December 1993) (must return 0 if words are equal).
   Altered by dfh (4.6.94.) to reverse word direction in order,
   and to eliminate recursion.
*/
int rec_compare(gen *w1, gen *w2)
{
  int lastmoved = 0;
  gen *p1, *p2;
  p1 = w1 + genstrlen(w1) - 1;
  p2 = w2 + genstrlen(w2) - 1;
  while (1) {
    if (p1 < w1) {
      if (p2 < w2)
        return lastmoved;
      return 2;
    }
    if (p2 < w2)
      return 1;
    if (*p1 == *p2) {
      p1--;
      p2--;
    }
    else if (*p1 < *p2) {
      p1--;
      lastmoved = 1;
    }
    else if (*p2 < *p1) {
      p2--;
      lastmoved = 2;
    }
  }
}

/* Compare words w1 and w2 to see which is 'bigger' according to the
   ordering. The ordering used here is recursive path ordering (based on
   that described in the book "Confluent String Rewriting" by Matthias Jantzen,
   Defn 1.2.14, page 24).
   Returns 1 if w1 is bigger than w2, 2 if w2 is bigger than w1,
   0 if equal.
   ----------------------------------------------------------------------
   The ordering is as follows:

   let u, v be elements of X*
   u >= v iff one of the following conditions is fulfilled;

   1) u = v      OR
   u = a'u, v = bv' for some a,b elements of X, u',v' elements of X*
   and then:
   2) a = b and u' >= v'    OR
   3) a > b and u  > v'    OR
   4) b > a and u'> v
   ----------------------------------------------------------------------
   Written by : Jamie P. Curmi (February 1992)
   Corrected by : dfh (December 1993) (must return 0 if words are equal).
*/
int rt_rec_compare(gen *w1, gen *w2)
{
  int lastmoved = 0;
  gen *p1, *p2;
  p1 = w1 + genstrlen(w1) - 1;
  p2 = w2 + genstrlen(w2) - 1;
  while (1) {
    if (p1 < w1) {
      if (p2 < w2)
        return lastmoved;
      return 2;
    }
    if (p2 < w2)
      return 1;
    if (*w1 == *w2) {
      w1++;
      w2++;
    }
    else if (*w1 < *w2) {
      w1++;
      lastmoved = 1;
    }
    else if (*w2 < *w1) {
      w2++;
      lastmoved = 2;
    }
  }
}

/* Compare w1 and w2 to see which comes first in the wreath-product ordering
 * (as defined in Sims' book), using the level function rwsptr->level.
 * Note that the recursive ordering is the special case of this with
 * levels 1,2,3,...
 * Returns  0 if w1=w2, 1 if w1 is bigger than w2, otherwise 2.
 */
int wreath_compare(gen *w1, gen *w2, rewriting_system *rwsptr)
{
  int winning = 0, waiting = 0, winning_level = 0, level1, level2;
  gen *p1, *p2;
  p1 = w1 + genstrlen(w1) - 1;
  p2 = w2 + genstrlen(w2) - 1;
  while (1) {
    if (p1 < w1) {
      if (p2 < w2)
        return winning;
      if (winning != 1 || rwsptr->level[*p2] >= winning_level)
        return 2;
      p2--;
      continue;
    }
    if (p2 < w2) {
      if (winning != 2 || rwsptr->level[*p1] >= winning_level)
        return 1;
      p1--;
      continue;
    }
    level1 = rwsptr->level[*p1];
    level2 = rwsptr->level[*p2];
    if (waiting == 1) {
      if (level2 > level1) {
        waiting = 2;
        winning = 1;
        winning_level = 0;
        p1--;
      }
      else if (level2 == level1) {
        waiting = 0;
        if (*p1 > *p2) {
          winning = 1;
          winning_level = level1;
        }
        else if (*p2 > *p1) {
          winning = 2;
          winning_level = level1;
        }
        else if (level1 > winning_level)
          winning_level = 0;
        p1--;
        p2--;
      }
      else {
        if (winning == 1 && level2 >= winning_level) {
          winning = 2;
          winning_level = 0;
        }
        p2--;
      }
    }
    else if (waiting == 2) {
      if (level1 > level2) {
        waiting = 1;
        winning = 2;
        winning_level = 0;
        p2--;
      }
      else if (level2 == level1) {
        waiting = 0;
        if (*p2 > *p1) {
          winning = 2;
          winning_level = level2;
        }
        else if (*p1 > *p2) {
          winning = 1;
          winning_level = level2;
        }
        else if (level2 > winning_level)
          winning_level = 0;
        p1--;
        p2--;
      }
      else {
        if (winning == 2 && level1 >= winning_level) {
          winning = 1;
          winning_level = 0;
        }
        p1--;
      }
    }
    else if (level2 > level1 && level2 >= winning_level) {
      waiting = 2;
      if (winning == 0 || (winning == 2 && level1 >= winning_level)) {
        winning = 1;
        winning_level = 0;
      }
      p1--;
    }
    else if (level1 > level2 && level1 >= winning_level) {
      waiting = 1;
      if (winning == 0 || (winning == 1 && level2 >= winning_level)) {
        winning = 2;
        winning_level = 0;
      }
      p2--;
    }
    else {
      if (*p1 > *p2 && level1 >= winning_level) {
        winning = 1;
        winning_level = level1;
      }
      else if (*p2 > *p1 && level1 >= winning_level) {
        winning = 2;
        winning_level = level1;
      }
      else if (*p1 == *p2 && level1 > winning_level)
        winning_level = 0;
      p1--;
      p2--;
    }
  }
}

/* COMPARE: Compares two words 'w1' and 'w2' to see which is 'bigger'
 * according to the ordering to be used.
 * If more ordering options are to be provided, the new function should
 * be given a different name and called from a 'case' statement in this
 * function.
 * Returns  0 if w1=w2, 1 if w1 is bigger than w2, otherwise 2.
 */
int compare(gen *w1, gen *w2, rewriting_system *rwsptr)
{
  switch (rwsptr->ordering) {

  case RECURSIVE: /* Recursive path ordering */
    return (rec_compare(w1, w2));

  case RT_RECURSIVE: /* Recursive path ordering */
    return (rt_rec_compare(w1, w2));

  case WTLEX: /* Weighted shortlex ordering */
    return (wtlex_compare(w1, w2, rwsptr));

  case WREATHPROD: /* Wreath product ordering */
    return (wreath_compare(w1, w2, rwsptr));

  default: /* shortlex ordering */
    return (lex_compare(w1, w2));
  }
}

/* Performs fast check for confluence.
 * Return value is 1 if confluent, 0 if not confluent and new equations added,
 * and -1 of not confluent but no new equations added because they are longer
 * than allowed by the values of maxlenleft and maxlenright.
 * Algorithm used is index_confluent, from p.117 of Sims' book.
 */
int conf_check(rewriting_system *rwsptr)
{
  int i, st, la, la2, lb, r, iv, beta[MAXREDUCELEN], betar, y[MAXREDUCELEN],
      num_neweqns = 0, mol, pl, n;
  gen *w, *wa, *wb, *wx, *we, *testword1 = rwsptr->testword1,
                              *testword2 = rwsptr->testword2;
  int **table = rwsptr->reduction_fsa->table->table_data_ptr;
  boolean discarded = FALSE, bt;
  int *preflen = rwsptr->preflen;
  reduction_struct rs_rws;

  rs_rws.rws = rwsptr;
  rs_rws.separator = rwsptr->separator;
  mol = rwsptr->maxoverlaplen;

  build_fulltable(rwsptr);
  if (rwsptr->cosets && rwsptr->finitestop && (i = check_finite(rwsptr, 128))) {
    printf("#Coset language has size %d.", i);
    rwsptr->maxoverlaplen =
        rwsptr->maxcosetlen + rwsptr->maxlhsrellen > rwsptr->maxsubgenlen
            ? rwsptr->maxcosetlen + rwsptr->maxlhsrellen
            : rwsptr->maxsubgenlen;
    printf(" Setting rwsptr->maxoverlap length to %d.\n",
           rwsptr->maxoverlaplen);
  }
  mol = rwsptr->maxoverlaplen;
  reduce_word = rws_reduce;
  rwsptr->hadlongoverlap = FALSE;

  for (i = 1; i <= rwsptr->num_eqns; i++) {
    wa = rwsptr->eqns[i].lhs;
    la = genstrlen(rwsptr->eqns[i].lhs);
    la2 = genstrlen(rwsptr->eqns[i].rhs);
    w = wa;
    we = w + la;
    pl = 0;
    if (rwsptr->cosets) {
      /* not interested in inter-subgroup overlaps */
      if (!Ggen(*(we - 1)))
        continue;
      while (w < we) {
        if (*w == rwsptr->separator) {
          pl = w - wa + 1;
          break;
        }
        w++;
      }
      w = wa;
    }
    st = 1;
    while (++w < we)
      st = dense_target(table, *w, st);
    beta[0] = st;
    r = 0;
    bt = FALSE;
    while (r >= 0 && !bt) {
      if (mol > 0 && r - pl + la > mol) {
        /* Any further overlap would exceed the permitted length */
        rwsptr->hadlongoverlap = TRUE;
        bt = TRUE;
      }
      betar = beta[r];
      bt = (bt || (betar < 0 && genstrlen(rwsptr->eqns[-betar].lhs) <= r) ||
            (betar >= 0 && preflen[betar] <= r));
      if (betar < 0 && !bt) {
        genstrcpy(testword1, rwsptr->eqns[i].rhs);
        wx = testword1 + la2;
        wb = rwsptr->eqns[-betar].lhs;
        lb = genstrlen(wb);
        w = wb + lb - r;
        we = wb + lb;
        while (w < we)
          *(wx++) = *(w++);
        *(wx) = 0;
        genstrcpy(testword2, rwsptr->eqns[i].lhs);
        wx = testword2 + la - lb + r;
        genstrcpy(wx, rwsptr->eqns[-betar].rhs);
        if (reduce_word(testword1, &rs_rws) == -1) {
          rwsptr->exit_status = 1;
          return -1;
        }
        if (reduce_word(testword2, &rs_rws) == -1) {
          rwsptr->exit_status = 1;
          return -1;
        }
        if (genstrlen(testword1) > rwsptr->maxreducelen / 2 ||
            genstrlen(testword2) > rwsptr->maxreducelen / 2)
          iv = -1;
        else if ((iv = insert(&(rwsptr->eqns[rwsptr->num_eqns + 1].lhs),
                              &(rwsptr->eqns[rwsptr->num_eqns + 1].rhs),
                              rwsptr)) > 0) {
          if (rwsptr->print_eqns) {
            printf("    #New equation number %d, from fast conf_check on eqn. "
                   "%d:\n",
                   rwsptr->num_eqns + 1, i);
            *kbm_buffer = '\0';
            add_to_buffer(6, "#");
            n = add_word_to_buffer(stdout,
                                   rwsptr->eqns[rwsptr->num_eqns + 1].lhs,
                                   rwsptr->gen_name);
            sprintf(kbm_buffer + strlen(kbm_buffer), "->");
            if (n > 0 || strlen(kbm_buffer) > 40) {
              printbuffer(stdout);
              add_to_buffer(8, "");
            }
            add_word_to_buffer(stdout, rwsptr->eqns[rwsptr->num_eqns + 1].rhs,
                               rwsptr->gen_name);
            printbuffer(stdout);
          }
          rwsptr->eqns[++rwsptr->num_eqns].done = FALSE;
          num_neweqns++;
          if (num_neweqns >= rwsptr->tidyint ||
              rwsptr->num_eqns == rwsptr->maxeqns) {
            if (kbm_print_level >= 2)
              printf("  #System is not confluent.\n");
            rwsptr->tidyon = TRUE;
            if (rwsptr->num_eqns == rwsptr->maxeqns) {
              if (kbm_print_level > 0)
                printf("#Maximum number of equations exceeded.\n");
              rwsptr->hadmaxeqns = TRUE;
              rwsptr->hadct++;
              rwsptr->tidyon_now = TRUE;
              if (!rwsptr->worddiffs || rwsptr->hadct > rwsptr->maxhad) {
                rwsptr->halting = TRUE;
                rwsptr->exit_status = 2;
              }
            }
            if (!rwsptr->halting) {
              build_quicktable(rwsptr);
              reduce_word = slow_rws_reduce;
            }
            return 0;
          }
        }
        if (iv == -1)
          /* We have discarded the equation because it is too long.
           * So we must remember that the system is not confluent.
           */
          discarded = TRUE;
        bt = TRUE;
      }
      if (!bt) {
        beta[r + 1] = dense_target(table, 1, betar);
        y[r + 1] = 2;
        r++;
      }
      else {
        while (bt && r > 0) {
          if (y[r] <= rwsptr->num_gens) {
            beta[r] = dense_target(table, y[r], beta[r - 1]);
            y[r]++;
            bt = FALSE;
          }
          else
            r--;
        }
      }
    }
  }
  if (num_neweqns > 0) {
    if (kbm_print_level >= 2)
      printf("  #System is not confluent (finished conf_check).\n");
    build_quicktable(rwsptr);
    reduce_word = slow_rws_reduce;
    return 0;
  }

  rwsptr->halting = TRUE;
  if (discarded) {
    /* We will mark all equations as not done, since we may want to resume with
     * higher limits on equation length.
     */
    for (i = 1; i <= rwsptr->num_eqns; i++)
      rwsptr->eqns[i].done = FALSE;
    rwsptr->exit_status = 2;
    return -1;
  }

  rwsptr->exit_status = 0;
  return 1;
}

/* The equations are re-ordered into order of increasing LHS.
 * Only equations up to length n are output.
 */
void sort_eqns(int n, rewriting_system *rwsptr)
{
  int i, l, ct, maxl;

  gen **newlhs, **newrhs;
  boolean *newdone;

  maxl = 0;
  for (i = 1; i <= rwsptr->num_eqns; i++)
    if ((l = genstrlen(rwsptr->eqns[i].lhs)) > maxl)
      maxl = l;
  if (n > 0 && maxl > n && kbm_print_level > 0) {
    printf("#Warning - not all equations will be output.\n");
    if (rwsptr->confluent) {
      printf("#The output system will not be confluent.\n");
      rwsptr->confluent = FALSE;
    }
  }
  if (n == 0 || n > maxl)
    n = maxl;
  tmalloc(newlhs, gen *, rwsptr->num_eqns + 1)
      tmalloc(newrhs, gen *, rwsptr->num_eqns + 1)
          tmalloc(newdone, boolean, rwsptr->num_eqns + 1) ct = 0;
  for (l = 1; l <= n; l++)
    /* Find equations of which LHS has length i */
    for (i = 1; i <= rwsptr->num_eqns; i++)
      if (genstrlen(rwsptr->eqns[i].lhs) == l) {
        newlhs[++ct] = rwsptr->eqns[i].lhs;
        newrhs[ct] = rwsptr->eqns[i].rhs;
        newdone[ct] = rwsptr->eqns[i].done;
      }
  /* and free the rest */
  for (i = 1; i <= rwsptr->num_eqns; i++)
    if (genstrlen(rwsptr->eqns[i].lhs) > n) {
      tfree(rwsptr->eqns[i].lhs);
      tfree(rwsptr->eqns[i].rhs);
    }

  for (i = 1; i <= rwsptr->num_eqns; i++) {
    rwsptr->eqns[i].lhs = newlhs[i];
    rwsptr->eqns[i].rhs = newrhs[i];
    rwsptr->eqns[i].done = newdone[i];
  }
  tfree(newlhs);
  tfree(newrhs);
  tfree(newdone);
  rwsptr->num_eqns = ct;
  build_quicktable(rwsptr);
  build_fulltable(rwsptr);
  if (kbm_print_level > 0)
    printf("#Output: %d eqns; table has %d states.\n", rwsptr->num_eqns,
           rwsptr->num_states);
}

/* Used only in cosets case.
 * The equations not already done are re-ordered so that coset eqns come
 * first, then those involving only G generators, and finally those involving
 * only H generators.
 */
int type_sort_eqns(int x, rewriting_system *rwsptr)
{
  int i, ct, ret;
  gen **newlhs, **newrhs;
  boolean *newdone;
  int ne = rwsptr->num_eqns;
  reduction_equation *eqn = rwsptr->eqns;
  reduction_equation eqni;
  int sep = rwsptr->separator;

  tmalloc(newlhs, gen *, ne + 1) tmalloc(newrhs, gen *, ne + 1)
      tmalloc(newdone, boolean, ne + 1) ct = 0;
  ret = 0;
  /* First find equations already done */
  for (i = 1; i <= ne; i++) {
    eqni = eqn[i];
    if (eqni.done) {
      newlhs[++ct] = eqni.lhs;
      newrhs[ct] = eqni.rhs;
      newdone[ct] = eqni.done;
    }
  }
  ret = ct;
  /* Now those with lhs starting with '_H' */
  for (i = 1; i <= ne; i++) {
    eqni = eqn[i];
    if (!eqni.done && *(eqni.lhs) == sep) {
      newlhs[++ct] = eqni.lhs;
      newrhs[ct] = eqni.rhs;
      newdone[ct] = eqni.done;
    }
  }
  /* Next the G-generator equations */
  for (i = 1; i <= ne; i++) {
    eqni = eqn[i];
    if (!eqni.done && Ggen(*(eqni.lhs))) {
      newlhs[++ct] = eqni.lhs;
      newrhs[ct] = eqni.rhs;
      newdone[ct] = eqni.done;
    }
  }
  /* And finally the H-generator equations */
  for (i = 1; i <= ne; i++) {
    eqni = eqn[i];
    if (!eqni.done && Hgen(*(eqni.lhs))) {
      newlhs[++ct] = eqni.lhs;
      newrhs[ct] = eqni.rhs;
      newdone[ct] = eqni.done;
    }
  }

  for (i = 1; i <= ne; i++) {
    eqn[i].lhs = newlhs[i];
    eqn[i].rhs = newrhs[i];
    eqn[i].done = newdone[i];
  }
  tfree(newlhs);
  tfree(newrhs);
  tfree(newdone);
  build_quicktable(rwsptr);
  return ret;
}

/* Used only in cosets case.
 * As for type_sort_eqns, but done at the end, so we do not worry about
 * what is already done.
 * This is to sort out the different categories of equations for
 * the cosets enumeration.
 */
void type_sort_eqns_final(rewriting_system *rwsptr)
{
  int i, ct;

  gen **newlhs, **newrhs;
  boolean *newdone;
  int ne = rwsptr->num_eqns;
  reduction_equation *eqn = rwsptr->eqns;
  reduction_equation eqni;
  int sep = rwsptr->separator;

  tmalloc(newlhs, gen *, ne + 1) tmalloc(newrhs, gen *, ne + 1)
      tmalloc(newdone, boolean, ne + 1) ct = 0;
  /* First find equations with lhs starting with '_H' */
  for (i = 1; i <= ne; i++) {
    eqni = eqn[i];
    if (*(eqni.lhs) == sep) {
      newlhs[++ct] = eqni.lhs;
      newrhs[ct] = eqni.rhs;
      newdone[ct] = eqni.done;
    }
  }

  /* Now the G-generator equations */
  for (i = 1; i <= ne; i++) {
    eqni = eqn[i];
    if (Ggen(*(eqni.lhs))) {
      newlhs[++ct] = eqni.lhs;
      newrhs[ct] = eqni.rhs;
      newdone[ct] = eqni.done;
    }
  }
  /* And finally the H-generator equations */
  for (i = 1; i <= ne; i++) {
    eqni = eqn[i];
    if (Hgen(*(eqni.lhs))) {
      newlhs[++ct] = eqni.lhs;
      newrhs[ct] = eqni.rhs;
      newdone[ct] = eqni.done;
    }
  }

  for (i = 1; i <= ne; i++) {
    eqn[i].lhs = newlhs[i];
    eqn[i].rhs = newrhs[i];
    eqn[i].done = newdone[i];
  }
  tfree(newlhs);
  tfree(newrhs);
  tfree(newdone);
  rwsptr->num_eqns = ct;
  build_quicktable(rwsptr);
  build_fulltable(rwsptr);
  if (kbm_print_level > 0)
    printf("#Output: %d eqns; table has %d states.\n", rwsptr->num_eqns,
           rwsptr->num_states);
}

/* Used only in cosets case.
 * This is called in place of type_sort_eqns_final, when we wish to output
 * in order of increasing length. We still output in the order of the
 * three categories of equations, but order by length of LHS within them.
 * Only equations up to length n (excluding separator) are output.
 */
void typelength_sort_eqns(int n, rewriting_system *rwsptr)
{
  int i, l, ct, maxl;
  gen *lhs, **newlhs, **newrhs;
  boolean *newdone;
  int ne = rwsptr->num_eqns;
  reduction_equation *eqn = rwsptr->eqns;
  reduction_equation eqni = {0,0,0,0,0};
  int sep = rwsptr->separator;

  maxl = 0;
  for (i = 1; i <= ne; i++) {
    lhs = eqn[i].lhs;
    l = *lhs == sep ? genstrlen(lhs + 1) : genstrlen(lhs);
    if (l > maxl)
      maxl = l;
  }
  if (n > 0 && maxl > n && kbm_print_level > 0) {
    printf("#Warning - not all equations will be output.\n");
    if (rwsptr->confluent) {
      printf("#The output system will not be confluent.\n");
      rwsptr->confluent = FALSE;
    }
  }
  if (n == 0 || n > maxl)
    n = maxl;
  tmalloc(newlhs, gen *, ne + 1) tmalloc(newrhs, gen *, ne + 1)
      tmalloc(newdone, boolean, ne + 1) ct = 0;
  /* First the coset equations */
  for (l = 1; l <= n; l++)
    /* Find equations of which LHS has length i */
    for (i = 1; i <= ne; i++) {
      eqni = eqn[i];
      lhs = eqni.lhs;
      if (*lhs == sep && genstrlen(lhs + 1) == l) {
        newlhs[++ct] = lhs;
        newrhs[ct] = eqni.rhs;
        newdone[ct] = eqni.done;
      }
    }
  /* Now the G-generator equations */
  for (l = 1; l <= n; l++)
    /* Find equations of which LHS has length i */
    for (i = 1; i <= ne; i++) {
      eqni = eqn[i];
      lhs = eqni.lhs;
      if (Ggen(*lhs) && genstrlen(lhs) == l) {
        newlhs[++ct] = eqni.lhs;
        newrhs[ct] = eqni.rhs;
        newdone[ct] = eqni.done;
      }
    }
  /* And finally the H-generator equations */
  for (l = 1; l <= n; l++)
    /* Find equations of which LHS has length i */
    for (i = 1; i <= ne; i++) {
      lhs = eqni.lhs;
      if (Hgen(*lhs) && genstrlen(lhs) == l) {
        newlhs[++ct] = lhs;
        newlhs[++ct] = eqni.lhs;
        newrhs[ct] = eqni.rhs;
        newdone[ct] = eqni.done;
      }
    }

  /* Free the rest (those that are too long) */
  for (i = 1; i <= ne; i++) {
    lhs = eqni.lhs;
    l = *lhs == sep ? genstrlen(lhs + 1) : genstrlen(lhs);
    if (l > n) {
      tfree(rwsptr->eqns[i].lhs);
      tfree(rwsptr->eqns[i].rhs);
    }
  }

  for (i = 1; i <= rwsptr->num_eqns; i++) {
    eqn[i].lhs = newlhs[i];
    eqn[i].rhs = newrhs[i];
    eqn[i].done = newdone[i];
  }
  tfree(newlhs);
  tfree(newrhs);
  tfree(newdone);
  rwsptr->num_eqns = ct;
  build_quicktable(rwsptr);
  build_fulltable(rwsptr);
  if (kbm_print_level > 0)
    printf("#Output: %d eqns; table has %d states.\n", rwsptr->num_eqns,
           rwsptr->num_states);
}

/* The equations are re-ordered so that those that resulted in new entries
 * in the word-difference table come first.
 * Those are recorded in the boolean array new_wd.
 * x is the current equation number in the KB.
 */
int wd_sort_eqns(int x, rewriting_system *rwsptr)
{
  int i, j, ct, ret, newmaxeqns = 0;
  int ne = rwsptr->num_eqns;
  reduction_equation *eqn = rwsptr->eqns;
  reduction_equation eqni;
  int sep = rwsptr->separator;
  boolean *nwd = rwsptr->new_wd;

  gen **newlhs, **newrhs;
  boolean *newdone;
  double r;

  if (rwsptr->hadmaxeqns) {
    /* In this case we will not keep all equations, to allow room for more */
    r = (double)x / rwsptr->num_eqns;
    if (r > 0.75) {
      if (kbm_print_level >= 2)
        printf(" #Halting - r=%f, rwsptr->hadct=%d.\n", r, rwsptr->hadct);
      rwsptr->halting = TRUE;
      rwsptr->exit_status = 2;
      rwsptr->hadmaxeqns = FALSE;
    }
    else
      newmaxeqns = ne * (1 + r) / 2;
  }
  tmalloc(newlhs, gen *, ne + 1) tmalloc(newrhs, gen *, ne + 1)
      tmalloc(newdone, boolean, ne + 1) ct = 0;
  /* Find equations that are already done */
  for (i = 1; i <= ne; i++) {
    eqni = eqn[i];
    if (eqni.done) {
      newlhs[++ct] = eqni.lhs;
      newrhs[ct] = eqni.rhs;
      newdone[ct] = eqni.done;
    }
  }
  ret = ct;
  /* Next those that gave new word-diffs */
  for (i = 1; i <= ne; i++) {
    eqni = eqn[i];
    if (!eqni.done && nwd[i]) {
      newlhs[++ct] = eqni.lhs;
      newrhs[ct] = eqni.rhs;
      newdone[ct] = eqni.done;
    }
  }
  /* Now take the rest. */
  if (rwsptr->cosets) {
    for (i = 1; i <= ne; i++) {
      eqni = eqn[i];
      if (*(eqni.lhs) == sep && !eqni.done && !nwd[i]) {
        newlhs[++ct] = eqni.lhs;
        newrhs[ct] = eqni.rhs;
        newdone[ct] = eqni.done;
      }
    }
    for (i = 1; i <= ne; i++) {
      eqni = eqn[i];
      if (Ggen(*(eqni.lhs)) && !eqni.done && !nwd[i]) {
        newlhs[++ct] = eqni.lhs;
        newrhs[ct] = eqni.rhs;
        newdone[ct] = eqni.done;
      }
    }
    for (i = 1; i <= ne; i++) {
      eqni = eqn[i];
      if (Hgen(*(eqni.lhs)) && !eqni.done && !nwd[i]) {
        newlhs[++ct] = eqni.lhs;
        newrhs[ct] = eqni.rhs;
        newdone[ct] = eqni.done;
      }
    }
  }
  else
    for (i = 1; i <= ne; i++) {
      eqni = eqn[i];
      if (!eqni.done && !rwsptr->new_wd[i]) {
        newlhs[++ct] = eqni.lhs;
        newrhs[ct] = eqni.rhs;
        newdone[ct] = eqni.done;
        if (rwsptr->hadmaxeqns && ct >= newmaxeqns) {
          if (kbm_print_level > 0)
            printf("Keeping only %d equations.\n", ct);
          /* free the rest */
          for (j = i + 1; j <= ne; j++)
            if (!eqn[j].done && !nwd[j]) {
              tfree(rwsptr->eqns[j].lhs);
              tfree(rwsptr->eqns[j].rhs);
            }
          rwsptr->num_eqns = ct;
          rwsptr->hadmaxeqns = FALSE;
          break;
        }
      }
    }
  for (i = 1; i <= ne; i++) {
    eqn[i].lhs = newlhs[i];
    eqn[i].rhs = newrhs[i];
    eqn[i].done = newdone[i];
  }
  tfree(newlhs);
  tfree(newrhs);
  tfree(newdone);
  build_quicktable(rwsptr);
  return ret;
}

/* Try to decide whether we should halt, using number of word-differences. */
void should_we_halt(rewriting_system *rwsptr)
{
  int i, ndiff, t;
  struct rusage tmp;
  getrusage(RUSAGE_SELF, &tmp);
  t = tmp.ru_utime.tv_sec;
  rwsptr->num_cycles++;
  if (rwsptr->num_cycles >= MAXCYCLES) {
    rwsptr->halting = TRUE;
    rwsptr->exit_status = 2;
  }
  rwsptr->wd_record[rwsptr->num_cycles].num_eqns = rwsptr->tot_eqns;
  rwsptr->wd_record[rwsptr->num_cycles].num_states = rwsptr->num_states;
  ndiff = rwsptr->wd_record[rwsptr->num_cycles].num_diff =
      rwsptr->wd_fsa->states->size;
  for (i = rwsptr->num_cycles - 1; i >= 1; i--)
    if (rwsptr->wd_record[i].num_diff < ndiff)
      break;
  i++;
  rwsptr->eqn_factor =
      rwsptr->wd_record[i].num_eqns == 0
          ? 0
          : 100 * rwsptr->tot_eqns / rwsptr->wd_record[i].num_eqns - 100;
  rwsptr->states_factor =
      rwsptr->hadct > 0
          ? 0
          : 100 * rwsptr->num_states / rwsptr->wd_record[i].num_states - 100;
  if (rwsptr->halting_factor > 0 &&
      ((t > rwsptr->min_time && rwsptr->eqn_factor >= rwsptr->halting_factor &&
        (rwsptr->states_factor == 0 ||
         rwsptr->states_factor >= rwsptr->halting_factor)) ||
       (rwsptr->eqn_factor >= 2 * rwsptr->halting_factor &&
        rwsptr->states_factor >= 2 * rwsptr->halting_factor))) {
    if (kbm_print_level > 1)
      printf("  #eqn_factor=%d, states_factor=%d - halting.\n",
             rwsptr->eqn_factor, rwsptr->states_factor);
    rwsptr->halting = TRUE;
    rwsptr->exit_status = 0;
  }
}

/* Used only in cosets case.
 * We finish by adjusting the reduction fsa to ensure that it only accepts
 * words in G-Generators alone, words in H-generators alone, or words of
 * form H-word*separator*G-word.
 */
void make_fsa_nice(rewriting_system *rwsptr)
{
  int first_Hstate, i, j, ng, im;
  int **table = rwsptr->reduction_fsa->table->table_data_ptr;

  if (dense_target(table, rwsptr->separator, 1) != 2) {
    fprintf(stderr, "Error: Why is image of 1 under separator not 2?\n");
    return;
  }
  ng = rwsptr->num_gens;
  first_Hstate = rwsptr->num_states + 1;
  for (i = rwsptr->separator + 1; i <= ng; i++) {
    im = dense_target(table, i, 1);
    if (im > 0 && im < first_Hstate)
      first_Hstate = im;
  }
  /* A G-generator cannot directly follow an H-generator */
  for (i = 1; i < rwsptr->separator; i++)
    for (j = first_Hstate; j <= rwsptr->num_states; j++)
      set_dense_target(table, i, j, 0);
  /* And _H or an H-generator cannot follow _H or a  G-generator */
  for (i = rwsptr->separator; i <= ng; i++)
    for (j = 2; j < first_Hstate; j++)
      set_dense_target(table, i, j, 0);
}

/* This is based on fsa_enumerate. It checks whether
 * the coset language accepted might be finite - by enumerating it up
 * to length max. If the enumeration completes and no word has length equal to
 * max, then it must be.
 * If finite, the size of the language is returned - otherwise 0.
 */
int check_finite(rewriting_system *rwsptr, int max)
{
  int i, ne, **table, ct, *cword, firste, clength, cstate, im, *statelist;
  boolean done, backtrack;
  fsa *fsaptr = rwsptr->reduction_fsa;

  if (fsaptr->num_initial == 0)
    return FALSE;

  ne = fsaptr->alphabet->size;
  table = fsaptr->table->table_data_ptr;

  tmalloc(cword, int,
          max + 1); /* to hold the current word in the enumeration */

  *kbm_buffer = '\0';
  tmalloc(statelist, int, max + 1);
  /* this is used to store the state history on scanning the current word. */
  for (i = 0; i <= max; i++)
    cword[i] = 0;
  clength = 0;
  statelist[0] = dense_target(table, rwsptr->separator, fsaptr->initial[1]);

  /* Backtrack search can now begin */
  done = FALSE;
  ct = 0;
  rwsptr->maxcosetlen = 0;
  while (!done) {
    ct++;
    /* Now proceed to next word in the search */
    firste = 1;
    backtrack = TRUE;
    while (backtrack && !done) {
      if (clength < max) {
        cstate = statelist[clength];
        i = firste - 1;
        while (backtrack && ++i <= ne)
          if (Ggen(i) && (im = dense_target(table, i, cstate)) > 0) {
            /* found next node */
            cword[clength++] = i;
            statelist[clength] = im;
            backtrack = FALSE;
            if (clength == max)
              return 0;
            if (clength > rwsptr->maxcosetlen)
              rwsptr->maxcosetlen = clength;
          }
      }
      if (backtrack) {
        if (clength == 0)
          done = TRUE;
        else {
          firste = cword[--clength] + 1;
          cword[clength] = '\0';
        }
      }
    }
  }
  tfree(cword);
  tfree(statelist);

  return ct;
}
