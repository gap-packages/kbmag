/* file worddiff.c 6/10/94
 * 6/2/98 - large scale re-organisation.
 * 13/1/98 changes for the `gen' type replacing char for generators.
 * Routines for adding equations to become acceptable by a word-difference
 * fsa.  These will be used both by kbprog, and later programs (mult and
 * newdiff) that correct the word-difference machines, but the word-reduction
 * algorithm will be different in both cases - in this file it is called
 * reduce_word.
 */

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "externals.h"
#define TESTWORDLEN 4096

extern int (*reduce_word)(gen *w, reduction_struct *rs_rws);

/* Functions defined in this file: */
int add_wd_fsa(fsa *wd_fsaptr, reduction_equation *eqn, int *inv,
               boolean reverse, reduction_struct *rsptr);

/* Initialise a word-difference automaton, using  *alphptr as base-alphabet.
 * First state is empty word, which is initial and only accepting state.
 */
int initialise_wd_fsa(fsa *wd_fsaptr, srec *alphptr, int maxwdiffs)
{
  int i, **table;

  fsa_init(wd_fsaptr);

  wd_fsaptr->states->type = WORDS;
  tmalloc(wd_fsaptr->states->words, gen *, maxwdiffs + 1);
  wd_fsaptr->states->alphabet_size = alphptr->size;
  for (i = 1; i <= alphptr->size; i++) {
    tmalloc(wd_fsaptr->states->alphabet[i], char,
            stringlen(alphptr->names[i]) + 1);
    strcpy(wd_fsaptr->states->alphabet[i], alphptr->names[i]);
  }
  wd_fsaptr->states->size = 1;
  /* Set up first state, which is the empty word. */
  tmalloc(wd_fsaptr->states->words[1], gen, 1);
  wd_fsaptr->states->words[1][0] = 0;

  wd_fsaptr->alphabet->type = PRODUCT;
  wd_fsaptr->alphabet->size = (alphptr->size + 1) * (alphptr->size + 1) - 1;
  wd_fsaptr->alphabet->arity = 2;
  wd_fsaptr->alphabet->padding = '_';
  tmalloc(wd_fsaptr->alphabet->base, srec, 1);
  srec_copy(wd_fsaptr->alphabet->base, alphptr);

  wd_fsaptr->num_initial = 1;
  tmalloc(wd_fsaptr->initial, int, 2);
  wd_fsaptr->initial[1] = 1;
  wd_fsaptr->num_accepting = 1;
  tmalloc(wd_fsaptr->accepting, int, 2);
  wd_fsaptr->accepting[1] = 1; /* Only the initial state is accepting */

  wd_fsaptr->flags[DFA] = TRUE;
  wd_fsaptr->flags[TRIM] = TRUE;

  fsa_table_init(wd_fsaptr->table, maxwdiffs, wd_fsaptr->alphabet->size);
  table = wd_fsaptr->table->table_data_ptr;
  for (i = 1; i <= wd_fsaptr->alphabet->size; i++)
    set_dense_target(table, i, 1, 0);
  wd_fsaptr->table->printing_format = SPARSE;
  if (fsa_table_dptr_init(wd_fsaptr) == -1)
    return -1;
  ;
  return 0;
}

/* Make the word-difference machine from the rewriting system rws */
int build_wd_fsa(fsa *wd_fsaptr, boolean *new_wd, reduction_struct *rsptr)
{
  int i, **table;
  int new;
  boolean printwd = kbm_print_level > 2 && kbm_print_level % 7 == 0;
  rewriting_system *rwsptr = rsptr->rws;
  wd_fsaptr->states->size = 1;
  table = wd_fsaptr->table->table_data_ptr;
  for (i = 1; i <= wd_fsaptr->alphabet->size; i++)
    set_dense_target(table, i, 1, 0);

  if (new_wd) /* new_wd nonzero means that we wish to note which equations
               * give rise to changes in the table.
               */
    for (i = 1; i <= rwsptr->num_eqns; i++)
      new_wd[i] = FALSE;

  /* Now add each equation to the fsa. */
  if (printwd)
    printf("New word  differences from equations:\n");
  for (i = 1; i <= rwsptr->num_eqns; i++) {
    new = add_wd_fsa(wd_fsaptr, rwsptr->eqns + i, rwsptr->inv_of, FALSE, rsptr);
    if (new == -1)
      return -1;
    if (new_wd && new)
      new_wd[i] = TRUE;
  }
  if (kbm_print_level >= 2)
    printf("	#There are %d word-differences.\n", wd_fsaptr->states->size);
  return 0;
}

/* Alter the word-difference machine to make it accept the equation *eqn
 * If reverse is true, then for all transitions added, the inverse transition
 * is also added.
 * It returns 1 or 0, according to whether new word-differences are added.
 */
int add_wd_fsa(fsa *wd_fsaptr, reduction_equation *eqn, int *inv,
               boolean reverse, reduction_struct *rsptr)
{
  char **names = 0;
  gen *wd1, *wd2, *stw, g1, g2;
  int i, j, l, l1, l2, maxl, state, image, size_pba, **table, ***wd_table;
  int ans = 0;
  boolean printwd = kbm_print_level > 2 && kbm_print_level % 7 == 0;
  gen testword[TESTWORDLEN];
  size_pba = 1 + wd_fsaptr->alphabet->base->size;
  wd1 = eqn->lhs;
  wd2 = eqn->rhs;
  l1 = genstrlen(wd1);
  l2 = genstrlen(wd2);
  maxl = l1 > l2 ? l1 : l2;
  if (printwd) {
    names = wd_fsaptr->alphabet->base->names;
    strcpy(kbm_buffer, "  ");
    add_word_to_buffer(stdout, wd1, names);
    strcat(kbm_buffer, " -> ");
    add_word_to_buffer(stdout, wd2, names);
    printf("%s\n", kbm_buffer);
  }

  table = wd_fsaptr->table->table_data_ptr;
  wd_table = wd_fsaptr->table->table_data_dptr;
  state = wd_fsaptr->initial[1];
  for (i = 0; i < maxl; i++) {
    g1 = i >= l1 ? size_pba : wd1[i];
    g2 = i >= l2 ? size_pba : wd2[i];
    image = dense_dtarget(wd_table, g1, g2, state);
    if (image == 0) {
      stw = wd_fsaptr->states->words[state];
      l = genstrlen(stw);
      if (g1 == size_pba) {
        genstrcpy(testword, stw);
        testword[l] = g2;
        testword[l + 1] = 0;
      }
      else if (g2 == size_pba) {
        testword[0] = inv[g1];
        genstrcpy(testword + 1, stw);
        testword[l + 1] = 0;
      }
      else {
        testword[0] = inv[g1];
        genstrcpy(testword + 1, stw);
        testword[l + 1] = g2;
        testword[l + 2] = 0;
      }
      if ((*reduce_word)(testword, rsptr) == -1)
        return -1;
      image = diff_no(wd_fsaptr, testword);
      if (image == 0) { /* new state */
        if (printwd) {
          strcpy(kbm_buffer, "    ");
          add_word_to_buffer(stdout, testword, names);
          printf("%s\n", kbm_buffer);
        }
        image = (++wd_fsaptr->states->size);
        if (image > wd_fsaptr->table->maxstates) {
          fprintf(stderr, "Maximum number of word-differences exceeded. Cannot "
                          "continue.\n");
          return -1;
        }
        tmalloc(wd_fsaptr->states->words[image], gen, genstrlen(testword) + 1);
        genstrcpy(wd_fsaptr->states->words[image], testword);
        for (j = 1; j <= wd_fsaptr->alphabet->size; j++)
          set_dense_target(table, j, image, 0);
      }
      set_dense_dtarget(wd_table, g1, g2, state, image);
      ans = 1;
    }
    if (reverse)
      set_dense_dtarget(wd_table, inv[g1], inv[g2], image, state);
    state = image;
  }
  return ans;
}

/* Close the set of word-differences under inversion, and add all possible
 * transitions, starting at state number start_no.
 */
int make_full_wd_fsa(fsa *wd_fsaptr, int *inv, int start_no,
                     reduction_struct *rsptr)
{
  int i, j, l, ns, n, g1, g2, size_pba, **table, ***wd_table;
  gen **wdn, *stw, *ptr, *ptre, *ptri;
  static boolean hadwarning = FALSE;
  gen testword[TESTWORDLEN];

  if (kbm_print_level > 2 && kbm_print_level % 3 == 0)
    printf("    #Calling make_full_wd_fsa.\n");
  size_pba = 1 + wd_fsaptr->alphabet->base->size;
  ns = wd_fsaptr->states->size;
  wdn = wd_fsaptr->states->words;
  table = wd_fsaptr->table->table_data_ptr;
  wd_table = wd_fsaptr->table->table_data_dptr;

  for (i = 1; i <= ns; i++) {
    ptr = wdn[i];
    ptre = ptr + genstrlen(ptr);
    /* invert this word-difference and put into testword. */
    ptri = testword;
    while (--ptre >= ptr)
      *(ptri++) = inv[*ptre];
    *ptri = 0;
    if ((*reduce_word)(testword, rsptr) == -1)
      return -1;
    if (i > 1 && genstrlen(testword) == 0 && kbm_print_level > 0 &&
        !hadwarning) {
      printf("#Warning: the inverse of a non-trivial word-difference is "
             "trivial.\n");
      printf("#Try running kbprog for longer.\n");
      hadwarning = TRUE;
    }

    if (diff_no(wd_fsaptr, testword) == 0) { /* new state */
      n = (++wd_fsaptr->states->size);
      if (n > wd_fsaptr->table->maxstates) {
        fprintf(stderr, "Too many word-differences. Increase maxwdiffs.\n");
        return -1;
      }
      tmalloc(wd_fsaptr->states->words[n], gen, genstrlen(testword) + 1);
      genstrcpy(wd_fsaptr->states->words[n], testword);
      for (j = 1; j <= wd_fsaptr->alphabet->size; j++)
        set_dense_target(table, j, n, 0);
    }
  }

  /* Now fill out table */
  ns = wd_fsaptr->states->size;
  if (start_no < 1)
    start_no = 1;
  for (i = start_no; i <= ns; i++) {
    for (g1 = 1; g1 <= size_pba; g1++)
      for (g2 = 1; g2 <= size_pba; g2++) {
        if (g1 == size_pba && g2 == size_pba)
          continue; /* Don't want padding-symbol on both sides. */
        if (dense_dtarget(wd_table, g1, g2, i) == 0) {
          stw = wd_fsaptr->states->words[i];
          l = genstrlen(stw);
          if (g1 == size_pba) {
            genstrcpy(testword, stw);
            testword[l] = g2;
            testword[l + 1] = 0;
          }
          else if (g2 == size_pba) {
            testword[0] = inv[g1];
            genstrcpy(testword + 1, stw);
            testword[l + 1] = 0;
          }
          else {
            testword[0] = inv[g1];
            genstrcpy(testword + 1, stw);
            testword[l + 1] = g2;
            testword[l + 2] = 0;
          }
          if ((*reduce_word)(testword, rsptr) == -1)
            return -1;
          if ((n = diff_no(wd_fsaptr, testword)))
            set_dense_dtarget(wd_table, g1, g2, i, n);
          if (n > 0 && n < start_no)
            set_dense_dtarget(wd_table, inv[g1], inv[g2], n, i);
        }
      }
  }
  return 0;
}


/* Clear the state-names for all states except the first. */
void clear_wd_fsa(fsa *wd_fsaptr)
{
  int i, ns;
  gen **wdn;
  ns = wd_fsaptr->states->size;
  wdn = wd_fsaptr->states->words;

  for (i = 2; i <= ns; i++)
    tfree(wdn[i]);
}


/* See if w is in the list of word-differences (state-names of wd_diff).
 * If so, return the number of the state.
 * If not, return 0.
 * This is done by a simple search. If it turns out to be too slow, we can use
 * hashing later.
 */
int diff_no(fsa *wd_fsaptr, gen *w)
{
  int i, ns;
  gen **wdn;
  ns = wd_fsaptr->states->size;
  wdn = wd_fsaptr->states->words;

  for (i = 1; i <= ns; i++)
    if (genstrcmp(w, wdn[i]) == 0)
      return i;

  return 0;
}

/* Use reduction in the word-difference machine to calculate
 * inverses of ngens.
 */
int calculate_inverses(int **invptr, int ngens, reduction_struct *rsptr)
{
  int i, j;
  gen testword[TESTWORDLEN];
  tmalloc(*invptr, int, ngens + 2);
  for (i = 1; i <= ngens; i++)
    for (j = 1; j <= ngens; j++) {
      testword[0] = i;
      testword[1] = j;
      testword[2] = 0;
      if ((*reduce_word)(testword, rsptr) == -1)
        return -1;
      if (genstrlen(testword) == 0) {
        (*invptr)[i] = j;
        break;
      }
    }
  (*invptr)[ngens + 1] = ngens + 1; /* to handle the padding symbol */
  return 0;
}
