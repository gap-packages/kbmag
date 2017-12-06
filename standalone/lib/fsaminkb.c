/* file fsaminkb.c  16. 12. 94.
 * 13/1/98 changes for introduction of `gen' type in place of char for
 * generators.
 * This file contains the routines necessary to calculate a 2-variable fsa
 * accepting precisely the minimal KB-rules of a short-lex automatic group.
 *
 * The first routine fsa_minred uses the word-acceptor to construct the
 * minimal reducible words - i.e. those for which all subwords are
 * accepted by the word-acceptor - clearly it is enough for the two words
 * obtained by omitting the first and last letters to be acceptable, so
 * it is essentially an application of fsa_and.
 *
 * The second routine fsa_minkb is a 2-variable machine accepting precisely the
 * minimal KB-reduction equations - i.e it accepts a pair (w1,w2) if w1 and w2
 * are equal in G, w1 is accepted by the fsa constructed by fsa_minred, and
 * w2 is accepted by the word-acceptor. Its construction is as in fsa_triples.
 *
 * The third routine, fsa_diff calculates the word-difference machine
 * associated with an fsa that accepts a collection of equations.
 * So, for example, it can be used with input the KB-reduction machine,
 * mentioned in the last paragraph, to calculate the correct diff1 machine,
 * or with the generalised multiplier to construct the correct diff2 machine.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "hash.h"
#include "externals.h"

/* Functions defined in this file: */

extern int (*reduce_word)(gen *w, reduction_struct *rs_rws);
static gen testword[4096]; /* Used for reducing words */

fsa *fsa_minred(fsa *waptr, storage_type op_table_type, boolean destroy,
                char *tempfilename)
{
  int **table, ne, nsi, nsi1, ns, dr, *fsarow, nt, cstate, csa, csb, im, i, g,
      len = 0, ct, *ht_ptr;
  boolean dense_ip, dense_op;
  fsa *minred;
  hash_table ht;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_minred.\n");
  if (!waptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_minred only applies to DFA's.\n");
    return 0;
  }

  tmalloc(minred, fsa, 1);
  fsa_init(minred);
  srec_copy(minred->alphabet, waptr->alphabet);
  minred->flags[DFA] = TRUE;
  minred->flags[ACCESSIBLE] = TRUE;
  minred->flags[BFS] = TRUE;

  ne = waptr->alphabet->size;
  nsi = waptr->states->size;
  nsi1 = nsi + 1;

  table = waptr->table->table_data_ptr;

  dense_ip = waptr->table->table_type == DENSE;
  dr = waptr->table->denserows;
  dense_op = op_table_type == DENSE;

  minred->states->type = SIMPLE;
  minred->num_initial = 1;
  tmalloc(minred->initial, int, 2);
  minred->initial[1] = 1;
  minred->table->table_type = op_table_type;
  minred->table->denserows = 0;
  minred->table->printing_format = op_table_type;

  hash_init(&ht, TRUE, 2, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = waptr->initial[1];
  ht_ptr[1] = waptr->initial[1];
  im = hash_locate(&ht, 2);
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_minred.\n");
    return 0;
  }
  if ((tempfile = fopen(tempfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow, int, ne) else tmalloc(fsarow, int, 2 * ne + 1)

        cstate = 0;
  if (dense_op)
    len = ne; /* The length of the fsarow output. */
  nt = 0;     /* Number of transitions in minred */

  /* A state of *minred will be essentially a pair of states of *waptr,
   * with the transitions coming from those of *waptr.
   * The differences are that the left hand side will accept words  w
   * which are not accepted by *waptr but whose maximal prefix is,
   * whereas the right hand side will accept words  w which are not accepted
   * by *waptr but whose maximal suffix is.
   * Thus, on the lhs, transitions to 0 in *waptr will go to a new accept-
   * state nsi1 instead (with no transitions from nsi1) whereas on the rhs
   * the first transition will be back to the intiial state.
   * The initial state itself is non-accept.
   */
  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    ht_ptr = hash_rec(&ht, cstate);
    csa = ht_ptr[0];
    csb = ht_ptr[1];
    if (!dense_op)
      len = 0;
    for (g = 1; g <= ne; g++) {
      /* Calculate action of generator g on state cstate */
      ht_ptr = ht.current_ptr;
      if (csa == 0 || csa == nsi1)
        ht_ptr[0] = 0;
      else {
        ht_ptr[0] = target(dense_ip, table, g, csa, dr);
        if (ht_ptr[0] == 0)
          ht_ptr[0] = nsi1;
      }
      if (cstate == 1)
        ht_ptr[1] = csb;
      else
        ht_ptr[1] = csb ? target(dense_ip, table, g, csb, dr) : 0;
      if (ht_ptr[0] == 0 || ht_ptr[1] == 0)
        im = 0;
      else
        im = hash_locate(&ht, 2);
      if (dense_op)
        fsarow[g - 1] = im;
      else if (im > 0) {
        fsarow[++len] = g;
        fsarow[++len] = im;
      }
      if (im > 0)
        nt++;
    }
    if (!dense_op)
      fsarow[0] = len++;
    fwrite((void *)fsarow, sizeof(int), (size_t)len, tempfile);
  }
  fclose(tempfile);

  ns = minred->states->size = ht.num_recs;
  minred->table->numTransitions = nt;
  /* Locate the accept states: first count them and then record them. */
  ct = 0;
  for (i = 1; i <= ns; i++) {
    ht_ptr = hash_rec(&ht, i);
    if (ht_ptr[0] == nsi1)
      ct++;
  }
  minred->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(minred->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++) {
      ht_ptr = hash_rec(&ht, i);
      if (ht_ptr[0] == nsi1)
        minred->accepting[++ct] = i;
    }
  }
  hash_clear(&ht);
  tfree(fsarow);
  tfree(waptr->is_accepting);

  if (destroy)
    fsa_clear(waptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(minred, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return minred;
}

/* *waptr is assumed to be the word-acceptor of an automatic group.
 * and *minredptr the fsa which accepts minimal reducible words
 * (computed using fsa_minred above).
 * In particular, all states of *waptr should be accepting.
 * *diffptr is assumed to be a word-difference machine of the same automatic
 *  group. Both are assumed to be stored in dense-format.
 * This routine constructs the fsa of which the states are triples (s1,s2,d),
 * with s1 and s2 states of *minredptr and *waptr and d a state of *diffptr.
 * (More precisely, if *waptr has n states, then s2 may also be equal
 * to n+1, meaning that the end of string symbol has been read on  rhs.
 * Since lhs is never shorter than rhs in an accpeted pair, the end of
 * string symbol on the lhs always leads to failure.)
 * The alphabet is 2-variable with base the alphabet of *waptr
 * (i.e. the same alphabet as *diffptr).
 * The alphabet member (g1,g2) maps (s1,s2,d) to (s1^g1,s2^g2,d^(g1,g2))
 * if all three components are nonzero, and to zero otherwise.
 * The transition-table of the resulting fsa is output in the usual way to
 * file tempfilename with table-type specified by op_table_type, before
 * minimisation.
 * A state is accept is s1, s2 and d all are (but s2 always is).
 * Short hash-tables will be used, so this routine won't work if *waptr
 * or *diffptr has more than 65535 states.
 *
 */
fsa *fsa_minkb(fsa *minredptr, fsa *waptr, fsa *diffptr,
               storage_type op_table_type, boolean destroy, char *tempfilename)
{
  int **minredtable, **watable, ***difftable, identity, ngens, ngens1, nswa1,
      ne, ns, *fsarow, nt, cstate, cswa1, cswa2, csdiff, im, i, e, len = 0, ct;
  unsigned short *ht_ptr;
  boolean dense_op;
  fsa *minkbptr;
  short_hash_table ht;
  FILE *tempfile;
  gen g1, g2;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_minkbptr.\n");

  if (!minredptr->flags[DFA] || !waptr->flags[DFA] || !diffptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_minkbptr only applies to DFA's.\n");
    return 0;
  }
  if (minredptr->alphabet->type != IDENTIFIERS ||
      waptr->alphabet->type != IDENTIFIERS) {
    fprintf(stderr, "Error in fsa_minkbptr: an fsa has wrong type.\n");
    return 0;
  }
  if (waptr->num_accepting != waptr->states->size) {
    fprintf(stderr,
            "Error in fsa_minkbptr: second fsa should be a word-acceptor.\n");
    return 0;
  }
  if (diffptr->alphabet->type != PRODUCT || diffptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_minkbptr: third fsa must be 2-variable.\n");
    return 0;
  }
  if (diffptr->states->type != WORDS) {
    fprintf(stderr,
            "Error in fsa_minkbptr: third fsa must be word-difference type.\n");
    return 0;
  }
  if (!srec_equal(diffptr->alphabet->base, waptr->alphabet)) {
    fprintf(stderr, "Error in fsa_minkbptr: fsa's alphabet's don't match.\n");
    return 0;
  }
  if (minredptr->states->size >= MAXUSHORT ||
      waptr->states->size >= MAXUSHORT || diffptr->states->size >= MAXUSHORT) {
    fprintf(stderr,
            "Error in fsa_minkbptr: one of the fsa's has too many states.\n");
    return 0;
  }

  if (fsa_table_dptr_init(diffptr) == -1)
    return 0;

  tmalloc(minkbptr, fsa, 1);
  fsa_init(minkbptr);
  srec_copy(minkbptr->alphabet, diffptr->alphabet);
  minkbptr->flags[DFA] = TRUE;
  minkbptr->flags[ACCESSIBLE] = TRUE;
  minkbptr->flags[BFS] = TRUE;

  ngens = waptr->alphabet->size;
  ngens1 = ngens + 1;
  ne = diffptr->alphabet->size;
  nswa1 = waptr->states->size + 1;

  if (ne != ngens1 * ngens1 - 1) {
    fprintf(
        stderr,
        "Error: in a 2-variable fsa, alphabet size should = ngens^2 - 1.\n");
    return 0;
  }

  minredtable = minredptr->table->table_data_ptr;
  watable = waptr->table->table_data_ptr;
  difftable = diffptr->table->table_data_dptr;

  dense_op = op_table_type == DENSE;

  minkbptr->states->type = SIMPLE;

  minkbptr->num_initial = 1;
  tmalloc(minkbptr->initial, int, 2);
  minkbptr->initial[1] = 1;
  minkbptr->table->table_type = op_table_type;
  minkbptr->table->denserows = 0;
  minkbptr->table->printing_format = op_table_type;

  short_hash_init(&ht, TRUE, 3, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = minredptr->initial[1];
  ht_ptr[1] = waptr->initial[1];
  ht_ptr[2] = identity = diffptr->initial[1];
  im = short_hash_locate(&ht, 3);
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_minkbptr.\n");
    return 0;
  }
  if ((tempfile = fopen(tempfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow, int, ne) else tmalloc(fsarow, int, 2 * ne + 1)

        cstate = 0;
  if (dense_op)
    len = ne; /* The length of the fsarow output. */
  nt = 0;     /* Number of transitions in minkbptr */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    ht_ptr = short_hash_rec(&ht, cstate);
    cswa1 = ht_ptr[0];
    cswa2 = ht_ptr[1];
    csdiff = ht_ptr[2];
    if (dense_op)
      for (i = 0; i < ne; i++)
        fsarow[i] = 0;
    else
      len = 0;
    e = 0; /* e is the number of the edge corresponding to the pair (g1,g2) */
    for (g1 = 1; g1 <= ngens; g1++)
      for (g2 = 1; g2 <= ngens1; g2++) {
        e++;
        /* Calculate action of generator-pair (g1,g2) on state cstate - since
         * the padding symbol cannot occur on the lhs, g1 only goes up to ngens.
         */
        ht_ptr = ht.current_ptr;
        ht_ptr[2] = dense_dtarget(difftable, g1, g2, csdiff);
        if (ht_ptr[2] == 0)
          im = 0;
        else {
          ht_ptr[0] = dense_target(minredtable, g1, cswa1);
          if (ht_ptr[0] == 0)
            im = 0;
          else {
            ht_ptr[1] =
                g2 == ngens1
                    ? nswa1
                    : cswa2 == nswa1 ? 0 : dense_target(watable, g2, cswa2);
            if (ht_ptr[1] == 0)
              im = 0;
            else
              im = short_hash_locate(&ht, 3);
          }
        }

        if (dense_op)
          fsarow[e - 1] = im;
        else if (im > 0) {
          fsarow[++len] = e;
          fsarow[++len] = im;
        }
        if (im > 0)
          nt++;
      } /* for (g1=1;g1<=ngens1; ... */
    if (!dense_op)
      fsarow[0] = len++;
    fwrite((void *)fsarow, sizeof(int), (size_t)len, tempfile);
  } /*while (++cstate <= ht.num_recs) */
  fclose(tempfile);

  ns = minkbptr->states->size = ht.num_recs;
  minkbptr->table->numTransitions = nt;

  if (kbm_print_level >= 3)
    printf("    #Calculated transitions - %d states, %d transitions.\n", ns,
           nt);

  /* Now locate the accept states */

  fsa_set_is_accepting(minredptr);
  ct = 0;
  for (i = 1; i <= ns; i++) {
    ht_ptr = short_hash_rec(&ht, i);
    if (minredptr->is_accepting[ht_ptr[0]] && ht_ptr[2] == identity)
      ct++;
  }
  minkbptr->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(minkbptr->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++) {
      ht_ptr = short_hash_rec(&ht, i);
      if (minredptr->is_accepting[ht_ptr[0]] && ht_ptr[2] == identity)
        minkbptr->accepting[++ct] = i;
    }
  }

  short_hash_clear(&ht);
  tfree(minredptr->is_accepting);
  tfree(fsarow);
  if (destroy) {
    fsa_clear(minredptr);
    fsa_clear(waptr);
    fsa_clear(diffptr);
  }
  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(minkbptr, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return minkbptr;
}

/* *fsaptr should be a two-variable automaton that accepts pairs of equations
 * It must be stored in dense format.
 * The corresponding word-difference machine is computed and returned.
 * For example, if fsaptr is minkb as returned by fsa_minkb (above),
 * then the correct diff1 machine for the shortlex automatic group is computed.
 */
fsa *fsa_diff(fsa *fsaptr, reduction_struct *rs_wd, storage_type op_table_type)
{
  int i, l, n, ngens, ngens1, ne, ns, g1, g2, fsaptr_state, diff_state,
      *state_diff, ***fsaptr_table, ***wd_table, **table, fsaptr_im, diff_im,
      *inv;
  fsa *diffptr;
  gen *stw;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_diff.\n");
  if (!fsaptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_diff only applies to DFA's.\n");
    return 0;
  }

  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_diff: fsa must be 2-variable.\n");
    return 0;
  }

  ne = fsaptr->alphabet->size;
  ngens = fsaptr->alphabet->base->size;
  ngens1 = ngens + 1;
  ns = fsaptr->states->size;
  if (fsa_table_dptr_init(fsaptr) == -1)
    return 0;
  fsaptr_table = fsaptr->table->table_data_dptr;

  if (ne != ngens1 * ngens1 - 1) {
    fprintf(
        stderr,
        "Error: in a 2-variable fsa, alphabet size should = ngens^2 - 1.\n");
    return 0;
  }

  tmalloc(diffptr, fsa, 1);
  fsa_init(diffptr);
  srec_copy(diffptr->alphabet, fsaptr->alphabet);

  /* Maximum possible number of states of diff is of course ns */
  diffptr->states->type = WORDS;
  tmalloc(diffptr->states->words, gen *, ns + 1);
  diffptr->states->alphabet_size = fsaptr->alphabet->base->size;
  for (i = 1; i <= fsaptr->alphabet->base->size; i++) {
    tmalloc(diffptr->states->alphabet[i], char,
            stringlen(fsaptr->alphabet->base->names[i]) + 1);
    strcpy(diffptr->states->alphabet[i], fsaptr->alphabet->base->names[i]);
  }
  diffptr->states->size = 1;
  /* Set up first state, which is the empty word. */
  tmalloc(diffptr->states->words[1], gen, 1);
  diffptr->states->words[1][0] = 0;

  diffptr->num_initial = 1;
  tmalloc(diffptr->initial, int, 2);
  diffptr->initial[1] = 1;
  diffptr->num_accepting = 1;
  tmalloc(diffptr->accepting, int, 2);
  diffptr->accepting[1] = 1; /* Only the initial state is accepting */

  diffptr->flags[DFA] = TRUE;
  diffptr->flags[TRIM] = TRUE;

  fsa_table_init(diffptr->table, ns, diffptr->alphabet->size);
  diffptr->table->printing_format = op_table_type;
  if (fsa_table_dptr_init(diffptr) == -1)
    return 0;
  wd_table = diffptr->table->table_data_dptr;
  table = diffptr->table->table_data_ptr;
  for (i = 1; i <= ne; i++)
    table[i][1] = 0;

  reduce_word = diff_reduce;
  if (calculate_inverses(&inv, ngens, rs_wd) == -1)
    return 0;

  /* Now build the transition-table of diffptr, using that of fsaptr.
   * Each state of fsaptr maps onto one of *diffptr, with the mapping
   * stored in the list state_diff.
   */
  tmalloc(state_diff, int, ns + 1);
  for (i = 1; i <= ns; i++)
    state_diff[i] = 0;
  state_diff[1] = 1;
  for (fsaptr_state = 1; fsaptr_state <= ns; fsaptr_state++) {
    diff_state = state_diff[fsaptr_state];
    for (g1 = 1; g1 <= ngens1; g1++)
      for (g2 = 1; g2 <= ngens1; g2++) {
        if (g1 == ngens1 && g2 == ngens1)
          continue;
        fsaptr_im = dense_dtarget(fsaptr_table, g1, g2, fsaptr_state);
        if (fsaptr_im == 0)
          continue;
        diff_im = state_diff[fsaptr_im];
        if (diff_im == 0) {
          /* We have to work out what word-difference the state maps onto */
          stw = diffptr->states->words[diff_state];
          l = genstrlen(stw);
          if (g1 == ngens1) {
            genstrcpy(testword, stw);
            testword[l] = g2;
            testword[l + 1] = 0;
          }
          else if (g2 == ngens1) {
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
          if ((*reduce_word)(testword, rs_wd) == -1)
            return 0;
          n = diff_no(diffptr, testword);
          if (n == 0) {
            n = ++diffptr->states->size;
            tmalloc(diffptr->states->words[n], gen, genstrlen(testword) + 1);
            genstrcpy(diffptr->states->words[n], testword);
            for (i = 1; i <= ne; i++)
              table[i][n] = 0;
          }
          state_diff[fsaptr_im] = diff_im = n;
        }
        set_dense_dtarget(wd_table, g1, g2, diff_state, diff_im);
      }
  }

  tfree(inv);
  tfree(state_diff);
  return diffptr;
}
