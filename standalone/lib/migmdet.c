/* file migmdet.c  23.10.95.
 * 6/8/98 large scale reorganisation to omit globals, etc.
 * 13/1/98 changes for the `gen' type replacing char for generators.
 *
 * This file contains the function migm_determinize, which makes the
 * multiple initial state generalised multiplier associated with
 * a coset automatic group deterministic.
 * That is, it computes the ordinary deterministic generalised multiplier.
 */

#define LABHTSIZE 8192

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "externals.h"

static fsa *migm_determinize_short(fsa *migmptr, storage_type op_table_type,
                                   boolean destroy, char *tempfilename);
static fsa *migm_determinize_int(fsa *migmptr, storage_type op_table_type,
                                 boolean destroy, char *tempfilename);

/* The fsa *migmptr must be a migm.
 * The returned fsa accepts a accepts the same language but is deterministic.
 */
fsa *migm_determinize(fsa *migmptr, storage_type op_table_type, boolean destroy,
                      char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling migm_determinize.\n");
  if (migmptr->states->size < MAXUSHORT)
    return migm_determinize_short(migmptr, op_table_type, destroy,
                                  tempfilename);
  else
    return migm_determinize_int(migmptr, op_table_type, destroy, tempfilename);
}

static fsa *migm_determinize_short(fsa *migmptr, storage_type op_table_type,
                                   boolean destroy, char *tempfilename)
{
  int **table, ne, ngens, nssi, ns, dr, *fsarow, nt, cstate, csi, im, i, j, k,
      g1, len = 0, nlab, ct;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  gen **w;
  boolean geninlab[MAXGEN + 1];
  boolean dense_ip, dense_op;
  short_hash_table ht, labelht;
  setToLabelsType *newlabel;
  fsa *det;
  srec *labelset;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling migm_determinize_short.\n");
  if (!migmptr->flags[MIDFA]) {
    fprintf(stderr, "Error: migm_determinize only applies to MIDFA's.\n");
    return 0;
  }
  if (migmptr->alphabet->type != PRODUCT || migmptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in migm_determinize: fsa must be 2-variable.\n");
    return 0;
  }
  if (migmptr->states->type != LABELED ||
      migmptr->states->labels->type != LISTOFWORDS) {
    fprintf(stderr, "Error in migm_determinize: states of fsa must be labels "
                    "to lists of words.\n");
    return 0;
  }

  ne = migmptr->alphabet->size;
  ngens = migmptr->alphabet->base->size;

  tmalloc(det, fsa, 1);
  fsa_init(det);
  srec_copy(det->alphabet, migmptr->alphabet);
  det->flags[DFA] = TRUE;
  det->flags[ACCESSIBLE] = TRUE;
  det->flags[BFS] = TRUE;

  det->table->table_type = op_table_type;
  det->table->denserows = 0;
  det->table->printing_format = op_table_type;

  dense_ip = migmptr->table->table_type == DENSE;
  dr = migmptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table = migmptr->table->table_data_ptr;

  det->num_initial = 1;
  tmalloc(det->initial, int, 2);
  det->initial[1] = 1;

  short_hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  nssi = migmptr->num_initial;
  for (i = 0; i < nssi; i++)
    ht_ptr[i] = migmptr->initial[i + 1];
  im = short_hash_locate(&ht, nssi);
  /* Each state in 'det' will be represented as a subset of the set of states
   * of *migmptr. The initial state contains the initial states
   * of *migmptr.
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in migm_determinize.\n");
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
  nt = 0;     /* Number of transitions in det */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = short_hash_rec(&ht, cstate) + short_hash_rec_len(&ht, cstate) - 1;
    if (!dense_op)
      len = 0;

    for (g1 = 1; g1 <= ne; g1++) {
      /* Calculate action of generator g1 on state cstate  - to get the image,
       * we simply apply it to each state in the subset of states representing
       * cstate.
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      while (++ptr <= cs_ptre) {
        csi = target(dense_ip, table, g1, *ptr, dr);
        if (csi == 0)
          continue;
        if (ht_ptrb > ht_ptre || csi > *ht_ptre) {
          /* We have a new state for the image subset to be added to the end */
          *(++ht_ptre) = csi;
        }
        else {
          ht_chptr = ht_ptrb;
          while (*ht_chptr < csi)
            ht_chptr++;
          if (csi < *ht_chptr) {
            /* we have a new state for the image subset to be added in the
             * middle */
            ht_ptr = ++ht_ptre;
            while (ht_ptr > ht_chptr) {
              *ht_ptr = *(ht_ptr - 1);
              ht_ptr--;
            }
            *ht_ptr = csi;
          }
        }
      }
      im = short_hash_locate(&ht, ht_ptre - ht_ptrb + 1);
      if (im == -1)
        return 0;
      if (dense_op)
        fsarow[g1 - 1] = im;
      else if (im > 0) {
        fsarow[++len] = g1;
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

  ns = det->states->size = ht.num_recs;
  det->table->numTransitions = nt;

  /* Now we need to work out the labels of the states. These are lists of words
   * of length <= 1, arising from the lists in the states of *migmptr that
   * make up the relevant subset of states that is a state of *det.
   * We need another hash-table for this.
   */
  det->states->type = LABELED;
  tmalloc(det->states->labels, srec, 1);
  labelset = det->states->labels;
  labelset->type = LISTOFWORDS;
  labelset->alphabet_size = migmptr->alphabet->base->size;
  for (i = 1; i <= ngens; i++) {
    tmalloc(labelset->alphabet[i], char,
            stringlen(migmptr->alphabet->base->names[i]) + 1);
    strcpy(labelset->alphabet[i], migmptr->alphabet->base->names[i]);
  }
  tmalloc(det->states->setToLabels, setToLabelsType, ns + 1);
  newlabel = det->states->setToLabels;

  short_hash_init(&labelht, FALSE, 0, LABHTSIZE, 2 * LABHTSIZE);

  tmalloc(det->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    det->is_accepting[i] = FALSE;
  for (cstate = 1; cstate <= ns; cstate++) {
    ht_ptrb = labelht.current_ptr;
    ht_ptre = ht_ptrb - 1;

    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = short_hash_rec(&ht, cstate) + short_hash_rec_len(&ht, cstate) - 1;
    for (i = 0; i <= ngens; i++)
      geninlab[i] = FALSE; /* geninlab records which generators occur in label*/
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre) {
      j = migmptr->states->setToLabels[*ptr];
      if (j) {
        w = migmptr->states->labels->wordslist[j];
        i = 0;
        while (w[i] != 0) {
          if (genstrlen(w[i]) <= 1) {
            det->is_accepting[cstate] = TRUE;
            geninlab[w[i][0]] = TRUE;
          }
          i++;
        }
      }
    }
    for (k = 0; k <= ngens; k++)
      if (geninlab[k])
        *(++ht_ptre) = k == 0 ? ngens + 1 : k;
    /* that completes calculation of label for cstate */
    newlabel[cstate] = short_hash_locate(&labelht, ht_ptre - ht_ptrb + 1);
    if (newlabel[cstate] == -1)
      return 0;
  }

  short_hash_clear(&ht);
  tfree(fsarow);

  /* Finally copy the records from the label hash-table into the set of labels
   */
  nlab = labelset->size = labelht.num_recs;
  if (kbm_print_level >= 3)
    printf("    #There are %d distinct labels.\n", nlab);
  tmalloc(labelset->wordslist, gen **, nlab + 1);
  for (i = 1; i <= nlab; i++) {
    len = short_hash_rec_len(&labelht, i);
    tmalloc(labelset->wordslist[i], gen *, len + 1);
    ht_ptr = short_hash_rec(&labelht, i);
    for (j = 0; j < len; j++) {
      if (ht_ptr[j] == ngens + 1) {
        tmalloc(labelset->wordslist[i][j], gen, 1);
        labelset->wordslist[i][j][0] = 0;
      }
      else {
        tmalloc(labelset->wordslist[i][j], gen, 2);
        labelset->wordslist[i][j][0] = ht_ptr[j];
        labelset->wordslist[i][j][1] = 0;
      }
    }
    labelset->wordslist[i][len] = 0;
  }

  short_hash_clear(&labelht);
  ct = 0;
  for (i = 1; i <= ns; i++)
    if (det->is_accepting[i])
      ct++;
  det->num_accepting = ct;
  tmalloc(det->accepting, int, ct + 1);
  ct = 0;
  for (i = 1; i <= ns; i++)
    if (det->is_accepting[i])
      det->accepting[++ct] = i;
  tfree(det->is_accepting);

  if (destroy)
    fsa_clear(migmptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(det, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return det;
}

static fsa *migm_determinize_int(fsa *migmptr, storage_type op_table_type,
                                 boolean destroy, char *tempfilename)
{
  fprintf(stderr,
          "Sorry - migm_determinize is not yet implemented for machines.\n");
  fprintf(stderr, "with more than 65536 states.\n");
  return 0;
}
