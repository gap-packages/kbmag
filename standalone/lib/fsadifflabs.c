/* file fsadifflabs.c  18/1/98
 *
 * This file contains the routine fsa_difflabs.
 * Given a two-variable fsa that reads pairs of words, it forms a new fsa
 * which accepts the same language but with states labeled by the associated
 * word-differences.
 * Code is similar to fsa_triples
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "rws.h"
#include "externals.h"

extern int (*reduce_word)(gen *w, reduction_struct *rs_rws);

/* Functions defined in this file: */
static fsa *fsa_difflabs_short(fsa *fsaptr, reduction_struct *rs_wdptr,
                               storage_type op_table_type, boolean destroy,
                               char *tempfilename, boolean readback);
static fsa *fsa_difflabs_int(fsa *fsaptr, reduction_struct *rs_wdptr,
                             storage_type op_table_type, boolean destroy,
                             char *tempfilename, boolean readback);

/* *fsaptr is assumed to be a two-variable fsa that reads pairs of
 * words, stored in dense format.
 * This routine constructs the fsa of which the states are difflabs (s,d),
 * with s a state of *fsaptr and d a word in the base alphabet of *fsaptr.
 * The alphabet is 2-variable with base the same as *fsaptr
 * The alphabet member (g1,g2) maps (s,d) to (s^(g1,g2),g1^-1*d*g2)
 * if s^(g1,g2) is nonzero, and to zero otherwise.
 * The word g1^-1*d*g2 is reduced using reduce_word and the structure rs_wdptr.
 * (This will normally be using diff_reduce on an automatic group.)
 * A state is accepting if and only if s is, and states are labeled
 * by the second component, the word-differnece d.
 * The transition-table of the resulting fsa is output in the usual way to
 * file tempfilename with table-type specified by op_table_type.
 *
 * If during the construction, a nontrivial equation between two words is
 * discovered as a result of encountering the identity word-difference,
 * then the word-acceptor *waptr must be accepting both of these words
 * which represent the same group-element, and must therefore be wrong.
 * The procedure therefore aborts without returning an fsa.
 * If the maxeqns is greater than zero, then a maximum of maxeqns such
 * equations are returned as eqnptr[i] - in order to do this, it is necessary
 * to store the defining transitions of the states as we proceed.
 */
fsa *fsa_difflabs(fsa *fsaptr, reduction_struct *rs_wdptr,
                  storage_type op_table_type, boolean destroy,
                  char *tempfilename, boolean readback)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_difflabs.\n");
  if (fsaptr->states->size >= MAXUSHORT)
    return fsa_difflabs_int(fsaptr, rs_wdptr, op_table_type, destroy,
                            tempfilename, readback);
  else
    return fsa_difflabs_short(fsaptr, rs_wdptr, op_table_type, destroy,
                              tempfilename, readback);
}

static fsa *fsa_difflabs_short(fsa *fsaptr, reduction_struct *rs_wdptr,
                               storage_type op_table_type, boolean destroy,
                               char *tempfilename, boolean readback)
{
  int ***fsatable, ngens, ngens1, ne, ns, *fsarow, nt, ndiffs, cstate, cswa,
      csdiff, im, i, l, e, len = 0, ct, *inv;
  unsigned short *ht_ptr;
  gen *ght_ptr, *wdiff;
  boolean dense_op;
  fsa *difflabs;
  srec *labels;
  short_hash_table ht;
  gen_hash_table ght;
  FILE *tempfile;
  gen g1, g2;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_difflabs_short.\n");

  if (!fsaptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_difflabs only applies to DFA's.\n");
    return 0;
  }
  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_difflabs: input fsa must be 2-variable.\n");
    return 0;
  }
  if (fsaptr->alphabet->base->type != IDENTIFIERS) {
    fprintf(stderr,
            "Error in fsa_difflabs: input fsa has wrong alphabet type.\n");
    return 0;
  }

  if (fsa_table_dptr_init(fsaptr) == -1)
    return 0;
  ;

  tmalloc(difflabs, fsa, 1);
  fsa_init(difflabs);
  srec_copy(difflabs->alphabet, fsaptr->alphabet);
  difflabs->flags[DFA] = TRUE;
  difflabs->flags[ACCESSIBLE] = TRUE;
  difflabs->flags[BFS] = TRUE;

  ngens = fsaptr->alphabet->base->size;
  ngens1 = ngens + 1;
  ne = fsaptr->alphabet->size;

  if (ne != ngens1 * ngens1 - 1) {
    fprintf(
        stderr,
        "Error: in a 2-variable fsa, alphabet size should = ngens^2 - 1.\n");
    return 0;
  }

  fsatable = fsaptr->table->table_data_dptr;

  dense_op = op_table_type == DENSE;

  difflabs->num_initial = 1;
  tmalloc(difflabs->initial, int, 2);
  difflabs->initial[1] = 1;
  difflabs->table->table_type = op_table_type;
  difflabs->table->denserows = 0;
  difflabs->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(difflabs->table->filename, char, stringlen(tempfilename) + 1);
    strcpy(difflabs->table->filename, tempfilename);
  }

  reduce_word = diff_reduce;
  if (calculate_inverses(&inv, ngens, rs_wdptr) == -1)
    return 0;

  /* We use two hash-tables - the first, ght, containing the word-differences,
   * and the second, ht, containing the pairs (s,d) representing the states
   * of *difflabs, where d is the number of the word-difference.
   */
  gen_hash_init(&ght, FALSE, 0, 0, 0);
  ght_ptr = ght.current_ptr;
  ght_ptr[0] = 0;
  im = gen_hash_locate(&ght, 1);
  if (im == -1)
    return 0;
  if (im != 1) {
    fprintf(stderr, "Gen. hash-initialisation problem in fsa_difflabs.\n");
    return 0;
  }

  short_hash_init(&ht, TRUE, 2, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = fsaptr->initial[1];
  ht_ptr[1] = 1;
  im = short_hash_locate(&ht, 2);
  if (im == -1)
    return 0;
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_difflabs.\n");
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
  nt = 0;     /* Number of transitions in difflabs */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    ht_ptr = short_hash_rec(&ht, cstate);
    cswa = ht_ptr[0];
    csdiff = ht_ptr[1];
    if (!dense_op)
      len = 0;
    e = 0; /* e is the number of the edge corresponding to the pair (g1,g2) */
    for (g1 = 1; g1 <= ngens1; g1++)
      for (g2 = 1; g2 <= ngens1; g2++) {
        e++;
        /* Calculate action of generator-pair (g1,g2) on state cstate */
        if (g1 == ngens1 && g2 == ngens1)
          continue;
        ht_ptr = ht.current_ptr;
        ht_ptr[0] = dense_dtarget(fsatable, g1, g2, cswa);
        if (ht_ptr[0] == 0)
          im = 0;
        else {
          /* Now we calculate the word-difference of the target state */
          wdiff = gen_hash_rec(&ght, csdiff);
          l = gen_hash_rec_len(&ght, csdiff) -
              1; /* length of word-difference */
          ght_ptr = ght.current_ptr;
          if (g1 == ngens1) {
            genstrcpy(ght_ptr, wdiff);
            ght_ptr[l] = g2;
            ght_ptr[l + 1] = 0;
          }
          else if (g2 == ngens1) {
            ght_ptr[0] = inv[g1];
            genstrcpy(ght_ptr + 1, wdiff);
            ght_ptr[l + 1] = 0;
          }
          else {
            ght_ptr[0] = inv[g1];
            genstrcpy(ght_ptr + 1, wdiff);
            ght_ptr[l + 1] = g2;
            ght_ptr[l + 2] = 0;
          }
          if ((*reduce_word)(ght_ptr, rs_wdptr) == -1)
            return 0;

          ht_ptr[1] = gen_hash_locate(&ght, genstrlen(ght_ptr) + 1);
          im = short_hash_locate(&ht, 2);
          if (im == -1)
            return 0;
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

  difflabs->states->type = LABELED;
  ns = difflabs->states->size = ht.num_recs;
  difflabs->table->numTransitions = nt;

  tmalloc(difflabs->states->labels, srec, 1);
  labels = difflabs->states->labels;
  labels->type = WORDS;
  for (i = 1; i <= ngens; i++) {
    tmalloc(labels->alphabet[i], char,
            stringlen(fsaptr->alphabet->base->names[i]) + 1);
    strcpy(labels->alphabet[i], fsaptr->alphabet->base->names[i]);
  }
  labels->alphabet_size = ngens;
  ndiffs = ght.num_recs;
  labels->size = ndiffs;
  tmalloc(labels->words, gen *, ndiffs + 1);
  for (i = 1; i <= ndiffs; i++) {
    tmalloc(labels->words[i], gen, gen_hash_rec_len(&ght, i) + 1);
    genstrcpy(labels->words[i], gen_hash_rec(&ght, i));
  }

  if (kbm_print_level >= 3) {
    printf("    #Calculated transitions - %d states, %d transitions.\n", ns,
           nt);
    printf("    #%d state labels (word-differneces).\n", ndiffs);
  }
  tmalloc(difflabs->states->setToLabels, setToLabelsType, ns + 1);
  difflabs->states->setToLabels[0] = 0;

  fsa_set_is_accepting(fsaptr);
  tmalloc(difflabs->is_accepting, boolean, ns + 1);
  difflabs->num_accepting = 0;
  for (i = 1; i <= ns; i++) {
    ht_ptr = short_hash_rec(&ht, i);
    difflabs->is_accepting[i] = fsaptr->is_accepting[ht_ptr[0]];
    if (difflabs->is_accepting[i])
      difflabs->num_accepting++;
    difflabs->states->setToLabels[i] = ht_ptr[1];
  }
  tfree(fsaptr->is_accepting);

  short_hash_clear(&ht);
  gen_hash_clear(&ght);
  tfree(fsarow);
  /* Now read the transition table back in */
  if (readback) {
    tempfile = fopen(tempfilename, "r");
    compressed_transitions_read(difflabs, tempfile);
    fclose(tempfile);
    unlink(tempfilename);
  }
  tmalloc(difflabs->accepting, int, difflabs->num_accepting + 1);
  ct = 0;
  for (i = 1; i <= ns; i++)
    if (difflabs->is_accepting[i])
      difflabs->accepting[++ct] = i;
  tfree(difflabs->is_accepting);
  if (destroy)
    fsa_clear(fsaptr);

  return difflabs;
}

static fsa *fsa_difflabs_int(fsa *fsaptr, reduction_struct *rs_wdptr,
                             storage_type op_table_type, boolean destroy,
                             char *tempfilename, boolean readback)
{
  exit(2);
}
