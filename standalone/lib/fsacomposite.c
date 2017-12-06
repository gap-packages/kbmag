/* file fsacomposite.c  24. 11. 94.
 * 29/9/98 large-scale re-organisation.
 * 3/8/98 - put in code for integer hash tables.
 * 13/1/98 - changes for `gen' type of generator replacing char.
 *
 * This file contains the routines necessary for axiom checking in an
 * automatic group.
 *
 * 13/9/95 - make the length 2 generalised multiplier have state set of
 * type setToLabels, where the labels are lists of words (of length 2),
 * rather than words.
 */

#define LABHTSIZE 8192

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "externals.h"

/* Functions defined in this file: */
static fsa *fsa_genmult2_short(fsa *genmultptr, storage_type op_table_type,
                               boolean destroy, char *genmult2filename,
                               boolean readback);
static fsa *fsa_genmult2_int(fsa *genmultptr, storage_type op_table_type,
                             boolean destroy, char *genmult2filename,
                             boolean readback);
static fsa *fsa_composite_short(fsa *mult1ptr, fsa *mult2ptr,
                                storage_type op_table_type, boolean destroy,
                                char *compfilename, boolean readback);
static fsa *fsa_composite_int(fsa *mult1ptr, fsa *mult2ptr,
                              storage_type op_table_type, boolean destroy,
                              char *compfilename, boolean readback);

/* *genmultptr should be the general multiplier fsa of an automatic group.
 * This function calculates the transition table of the general multiplier for
 * products of two generators. This is output (in unformatted form) to the
 * file with name genmult2filename, followed by a list of states, which
 * specifies which states are accept-states for which length-two words.
 * It can then be minimised for any such word as required.
 * If readback is false, then
 * the fsa returned does not have its transition table stored internally
 * (since these are in the file genmult2filename) - instead, its table
 * component table->filename contains the name of this file.
 * Otherwise, the transition table is read back in as usual.
 * If genmult2filename is the empty string, then the transition table is
 * not stored at all.
 * (This can be done when all relators of the group have length at most 4.)
 */
fsa *fsa_genmult2(fsa *genmultptr, storage_type op_table_type, boolean destroy,
                  char *genmult2filename, boolean readback)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_genmult2.\n");
  if (genmultptr->states->size < MAXUSHORT)
    return fsa_genmult2_short(genmultptr, op_table_type, destroy,
                              genmult2filename, readback);
  else
    return fsa_genmult2_int(genmultptr, op_table_type, destroy,
                            genmult2filename, readback);
}

static fsa *fsa_genmult2_short(fsa *genmultptr, storage_type op_table_type,
                               boolean destroy, char *genmult2filename,
                               boolean readback)
{
  int **table, ne, ngens, ngens1, ns, *fsarow, e, e1, e2, es1, ef1, dr, nt,
      cstate, im, csa, csb, csima, csimb, i, j, j1, j2, g1, g2, g3, len = 0, reclen,
      nlab, ct;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  boolean dense_ip, dense_op, got, leftpad, rightpad, keeptable;
  setToLabelsType *label, l1, l2, *newlabel;
  gen **labellist1, **labellist2;
  short_hash_table ht, labelht;
  fsa *genmult2ptr;
  srec *labelset;
  FILE *tablefile = 0;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_genmult2_short.\n");
  if (!genmultptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_genmult2 only applies to DFA's.\n");
    return 0;
  }

  if (genmultptr->alphabet->type != PRODUCT ||
      genmultptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_genmult2: fsa must be 2-variable.\n");
    return 0;
  }

  if (genmultptr->states->type != LABELED) {
    fprintf(stderr, "Error in fsa_genmult2: states of fsa must be labeled.\n");
    return 0;
  }

  keeptable = stringlen(genmult2filename) > 0;
  if (readback && !keeptable) {
    fprintf(stderr,
            "Error in fsa_genmult2: readback true but empty filename.\n");
    return 0;
  }

  tmalloc(genmult2ptr, fsa, 1);
  fsa_init(genmult2ptr);
  srec_copy(genmult2ptr->alphabet, genmultptr->alphabet);
  genmult2ptr->num_initial = 1;
  tmalloc(genmult2ptr->initial, int, 2);
  genmult2ptr->initial[1] = 1;
  genmult2ptr->flags[DFA] = TRUE;
  genmult2ptr->flags[ACCESSIBLE] = TRUE;
  genmult2ptr->flags[BFS] = TRUE;

  genmult2ptr->table->table_type = op_table_type;
  genmult2ptr->table->denserows = 0;
  genmult2ptr->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(genmult2ptr->table->filename, char,
            stringlen(genmult2filename) + 1);
    strcpy(genmult2ptr->table->filename, genmult2filename);
  }

  ne = genmultptr->alphabet->size;
  ngens = genmultptr->alphabet->base->size;
  ngens1 = ngens + 1;

  if (ne != ngens1 * ngens1 - 1) {
    fprintf(stderr, "Error: in a 2-variable fsa, alphabet size should = "
                    "(ngens+1)^2 - 1.\n");
    return 0;
  }

  fsa_set_is_accepting(genmultptr);

  dense_ip = genmultptr->table->table_type == DENSE;
  dr = genmultptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table = genmultptr->table->table_data_ptr;

  short_hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = genmultptr->initial[1];
  ht_ptr[1] = genmultptr->initial[1];
  im = short_hash_locate(&ht, 2);
  /* Each state in the composite transition table will be represented as a
   * subset of the set of ordered pairs of states of *genmultptr. The initial
   * state contains just one such pair, of which both components are the initial
   * state of *genmultptr. The subsets will be stored as variable-length records
   * in the hash-table, as a list of pairs in increasing order. If a state is
   * reached from a transition ($,x) or (x,$) (with $ the padding symbol), then
   * it needs to be marked as such, since we do not allow a $ to be followed by
   * any other generator. We do this by adding a 1 or a 2 to the end of the
   * statelist - this is recognisable by the fact that the length of the
   * statelist then becomes odd.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_genmult2.\n");
    return 0;
  }
  if (keeptable)
    if ((tablefile = fopen(genmult2filename, "w")) == 0) {
      fprintf(stderr, "Error: cannot open file %s\n", genmult2filename);
      return 0;
    }
  if (dense_op)
    tmalloc(fsarow, int, ne) else tmalloc(fsarow, int, 2 * ne + 1)

        label = genmultptr->states->setToLabels;
  cstate = 0;
  if (dense_op)
    len = ne; /* The length of the fsarow output. */
  nt = 0;     /* Number of transitions in genmult2ptr */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    reclen = short_hash_rec_len(&ht, cstate);
    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = short_hash_rec(&ht, cstate) + reclen - 1;
    if (reclen % 2 == 1) {
      if (*cs_ptre == 1) {
        leftpad = TRUE;
        rightpad = FALSE;
      }
      else {
        leftpad = FALSE;
        rightpad = TRUE;
      }
      cs_ptre--;
    }
    else {
      leftpad = FALSE;
      rightpad = FALSE;
    }

    if (dense_op)
      for (i = 0; i < ne; i++)
        fsarow[i] = 0;
    else
      len = 0;

    e = 0; /* e is the edge number of generator pair (g1,g3) */
    for (g1 = 1; g1 <= ngens1; g1++)
      for (g3 = 1; g3 <= ngens1; g3++) {
        /* Calculate action of pair (g1,g3) on state cstate  - to get the image,
         * we have to apply ( (g1,g2), (g2,g3) ) to each ordered pair in the
         * subset corresponding to cstate, * and this for each generator g2 of
         * the base-alphabet (including the padding symbol).
         */

        e++;
        if (g1 == ngens1 && g3 == ngens1)
          continue;

        if ((leftpad && g1 <= ngens) || (rightpad && g3 <= ngens))
          continue;
        ht_ptrb = ht.current_ptr;
        ht_ptre = ht_ptrb - 1;

        es1 = (g1 - 1) * ngens1 + 1;
        ef1 = g1 * ngens1;
        /* As g2 ranges from 1 to ngens+1 in the pair (g1,g2), for fixed g1, the
         * corresponding edge number in the fsa ranges from es1 to ef1.
         *
         * As g2 ranges from 1 to ngens+1 in the pair (g2,g3), for fixed g3, the
         * corresponding edge number in the fsa ranges from g3 upwards, with
         * increments of size ngens+1.
         */

        ptr = cs_ptr;
        while (ptr <= cs_ptre) {
          csa = *(ptr++);
          csb = *(ptr++);
          for (g2 = 1, e1 = es1, e2 = g3; e1 <= ef1; g2++, e1++, e2 += ngens1) {
            csima = g1 == ngens1 && g2 == ngens1
                        ? (genmultptr->is_accepting[csa] ? csa : 0)
                        : target(dense_ip, table, e1, csa, dr);
            if (csima == 0)
              continue;

            csimb = g2 == ngens1 && g3 == ngens1
                        ? (genmultptr->is_accepting[csb] ? csb : 0)
                        : target(dense_ip, table, e2, csb, dr);
            if (csimb == 0)
              continue;
            if (ht_ptrb > ht_ptre || csima > *(ht_ptre - 1) ||
                (csima == *(ht_ptre - 1) && csimb > *ht_ptre)) {
              /* We have a new state for the image subset to be added to the end
               */
              *(++ht_ptre) = csima;
              *(++ht_ptre) = csimb;
            }
            else {
              ht_chptr = ht_ptrb;
              while (*ht_chptr < csima)
                ht_chptr += 2;
              while (*ht_chptr == csima && *(ht_chptr + 1) < csimb)
                ht_chptr += 2;
              if (csima < *ht_chptr || csimb < *(ht_chptr + 1)) {
                /* we have a new state for the image subset to be added in the
                 * middle */
                ht_ptr = ht_ptre;
                ht_ptre += 2;
                while (ht_ptr >= ht_chptr) {
                  *(ht_ptr + 2) = *ht_ptr;
                  ht_ptr--;
                }
                *ht_chptr = csima;
                *(ht_chptr + 1) = csimb;
              }
            }
          }
        }
        if (ht_ptre > ht_ptrb) {
          if (g1 == ngens1)
            *(++ht_ptre) = 1;
          else if (g3 == ngens1)
            *(++ht_ptre) = 2;
        }
        im = short_hash_locate(&ht, ht_ptre - ht_ptrb + 1);
        if (im > 0) {
          if (dense_op)
            fsarow[e - 1] = im;
          else {
            fsarow[++len] = e;
            fsarow[++len] = im;
          }
          nt++;
        }
      }
    if (!dense_op)
      fsarow[0] = len++;
    if (keeptable)
      fwrite((void *)fsarow, sizeof(int), (size_t)len, tablefile);
  }

  if (keeptable)
    fclose(tablefile);
  tfree(fsarow);

  ns = genmult2ptr->states->size = ht.num_recs;
  genmult2ptr->table->numTransitions = nt;

  if (kbm_print_level >= 3) {
    printf("    #Calculated transitions - %d states, %d transitions.\n", ns,
           nt);
    printf("    #Now calculating state labels.\n");
  }

  /* Locate the accept states for  Mult_(a*b)  each generator pair (a,b).
   * This is slightly cumbersome, since a state S
   * is an accept state if either the  subset representing S contains a
   * pair (s1,s2), where s1 is accept state for Mult_a and s2 for Mult_b,
   * or we can get from to such a state by applying ( ($,g), (g,$) ) to one
   * of the pairs in S, for some generator g.
   * It is most convenient to work out this information taking the states
   * S in reverse order.
   * The information on the accept-states will be stored as labels, which
   * (13/9/95 - change labels from words to lists of words)
   * will be lists of words in the generators. Each such list will have the form
   * [a1*b1,a2*b2,...,ar*br], where the (ai,bi) are the generator pairs for
   * which that particular state is an accept state. The labels will be
   * collected initially in a new hash-table.
   * The identity generator will be numbered ngens+1 and given name '_'
   * rather than represented by the empty word. This is so that we can
   * distinguish between multipliers for "_*a" and "a*_" if necessary.
   */

  genmult2ptr->states->type = LABELED;
  tmalloc(genmult2ptr->states->labels, srec, 1);
  labelset = genmult2ptr->states->labels;
  labelset->type = LISTOFWORDS;
  labelset->alphabet_size = ngens1;
  for (i = 1; i <= ngens; i++) {
    tmalloc(labelset->alphabet[i], char,
            stringlen(genmultptr->states->labels->alphabet[i]) + 1);
    strcpy(labelset->alphabet[i], genmultptr->states->labels->alphabet[i]);
  }
  tmalloc(labelset->alphabet[ngens1], char, 2);
  labelset->alphabet[ngens1][0] = '_';
  labelset->alphabet[ngens1][1] = 0;
  tmalloc(genmult2ptr->states->setToLabels, setToLabelsType, ns + 1);
  newlabel = genmult2ptr->states->setToLabels;
  tmalloc(genmult2ptr->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    genmult2ptr->is_accepting[i] = FALSE;
  short_hash_init(&labelht, FALSE, 0, LABHTSIZE, 2 * LABHTSIZE);

  es1 = ngens * ngens1 + 1;
  ef1 = ngens1 * ngens1 - 1;
  for (cstate = ns; cstate >= 1; cstate--) {
    /* We work backwards through the states, since we wish to add on additional
     * elements at the end of the list in the hash-table - this destroys
     * later entries, but that doesn't matter, since we have already dealt
     * with them.
     */
    cs_ptr = short_hash_rec(&ht, cstate);
    reclen = short_hash_rec_len(&ht, cstate);
    if (reclen % 2 == 1)
      reclen--;
    /* The last entry only marks the fact that this is a "padded state"*/
    cs_ptre = short_hash_rec(&ht, cstate) + reclen - 1;
    /* Apply generators ( ($,g2), (g2,$) ) and see if we get anything new.
     * We won't bother about having them in increasing order this time.
     */
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++);
      csb = *(ptr++);
      for (e1 = es1, e2 = ngens1; e1 <= ef1; e1++, e2 += ngens1) {
        csima = target(dense_ip, table, e1, csa, dr);
        if (csima == 0)
          continue;
        csimb = target(dense_ip, table, e2, csb, dr);
        if (csimb == 0)
          continue;
        /* see if (csima,csimb) is new */
        ht_chptr = cs_ptr;
        got = FALSE;
        while (ht_chptr < cs_ptre) {
          if (csima == ht_chptr[0] && csimb == ht_chptr[1]) {
            got = TRUE;
            break;
          }
          ht_chptr += 2;
        }
        if (!got) {
          /* add (csima,csimb) to the end */
          *(++cs_ptre) = csima;
          *(++cs_ptre) = csimb;
        }
      }
    }
    /* Now we see which pairs in the subset are of form (s,t), where s is
     * an accept state for a generator a, and t for a generator b.
     * The list of all such pairs (a,b) will form the label of the state, which
     * will be the list of words [a1*b1,a2*b2,..,ar*br], with the (ai,bi) coming
     * in lex-order.
     */

    ht_ptrb = labelht.current_ptr;
    ht_ptre = ht_ptrb - 1;
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++);
      csb = *(ptr++);
      if (((l1 = label[csa]) != 0) && ((l2 = label[csb]) != 0)) {
        labellist1 = genmultptr->states->labels->wordslist[l1];
        labellist2 = genmultptr->states->labels->wordslist[l2];
        j1 = 0;
        while (labellist1[j1]) {
          g1 = labellist1[j1][0];
          if (g1 == 0)
            g1 = ngens1;
          j2 = 0;
          while (labellist2[j2]) {
            genmult2ptr->is_accepting[cstate] = TRUE;
            g2 = labellist2[j2][0];
            if (g2 == 0)
              g2 = ngens1;
            if (ht_ptrb > ht_ptre || g1 > *(ht_ptre - 1) ||
                (g1 == *(ht_ptre - 1) && g2 > *ht_ptre)) {
              /* We have a new generator pair to be added to the end */
              *(++ht_ptre) = g1;
              *(++ht_ptre) = g2;
            }
            else {
              ht_chptr = ht_ptrb;
              while (*ht_chptr < g1)
                ht_chptr += 2;
              while (*ht_chptr == g1 && *(ht_chptr + 1) < g2)
                ht_chptr += 2;
              if (g1 < *ht_chptr || g2 < *(ht_chptr + 1)) {
                /* we have a new generator pair to be added in the middle */
                ht_ptr = ht_ptre;
                ht_ptre += 2;
                while (ht_ptr >= ht_chptr) {
                  *(ht_ptr + 2) = *ht_ptr;
                  ht_ptr--;
                }
                *ht_chptr = g1;
                *(ht_chptr + 1) = g2;
              }
            }
            j2++;
          }
          j1++;
        }
      }
    }
    /* That completes the calculation of the label for cstate */
    newlabel[cstate] = short_hash_locate(&labelht, ht_ptre - ht_ptrb + 1);
  }
  short_hash_clear(&ht);

  ct = 0;
  for (i = 1; i <= ns; i++)
    if (genmult2ptr->is_accepting[i])
      ct++;
  genmult2ptr->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(genmult2ptr->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (genmult2ptr->is_accepting[i])
        genmult2ptr->accepting[++ct] = i;
  }
  tfree(genmult2ptr->is_accepting);
  tfree(genmultptr->is_accepting);

  /* Finally copy the records from the label hash-table into the set of labels
   */
  nlab = labelset->size = labelht.num_recs;
  if (kbm_print_level >= 3)
    printf("    #There are %d distinct labels.\n", nlab);
  tmalloc(labelset->wordslist, gen **, nlab + 1);
  for (i = 1; i <= nlab; i++) {
    len = short_hash_rec_len(&labelht, i) / 2;
    tmalloc(labelset->wordslist[i], gen *, len + 1);
    ht_ptr = short_hash_rec(&labelht, i);
    for (j = 0; j < len; j++) {
      tmalloc(labelset->wordslist[i][j], gen, 3);
      labelset->wordslist[i][j][0] = ht_ptr[2 * j];
      labelset->wordslist[i][j][1] = ht_ptr[2 * j + 1];
      labelset->wordslist[i][j][2] = 0;
    }
    labelset->wordslist[i][len] = 0;
  }

  short_hash_clear(&labelht);
  if (destroy)
    fsa_clear(genmultptr);

  if (readback) {
    tablefile = fopen(genmult2filename, "r");
    compressed_transitions_read(genmult2ptr, tablefile);
    fclose(tablefile);
    unlink(genmult2filename);
  }

  return genmult2ptr;
}

static fsa *fsa_genmult2_int(fsa *genmultptr, storage_type op_table_type,
                             boolean destroy, char *genmult2filename,
                             boolean readback)
{
  int **table, ne, ngens, ngens1, ns, *fsarow, e, e1, e2, es1, ef1, dr, nt,
      cstate, im, csa, csb, csima, csimb, i, j, j1, j2, g1, g2, g3, len = 0, reclen,
      nlab, ct;
  int *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre, *ptr;
  boolean dense_ip, dense_op, got, leftpad, rightpad, keeptable;
  setToLabelsType *label, l1, l2, *newlabel;
  gen **labellist1, **labellist2;
  hash_table ht, labelht;
  fsa *genmult2ptr;
  srec *labelset;
  FILE *tablefile = 0;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_genmult2_int.\n");
  if (!genmultptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_genmult2 only applies to DFA's.\n");
    return 0;
  }

  if (genmultptr->alphabet->type != PRODUCT ||
      genmultptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_genmult2: fsa must be 2-variable.\n");
    return 0;
  }

  if (genmultptr->states->type != LABELED) {
    fprintf(stderr, "Error in fsa_genmult2: states of fsa must be labeled.\n");
    return 0;
  }

  keeptable = stringlen(genmult2filename) > 0;
  if (readback && !keeptable) {
    fprintf(stderr,
            "Error in fsa_genmult2: readback true but empty filename.\n");
    return 0;
  }

  tmalloc(genmult2ptr, fsa, 1);
  fsa_init(genmult2ptr);
  srec_copy(genmult2ptr->alphabet, genmultptr->alphabet);
  genmult2ptr->num_initial = 1;
  tmalloc(genmult2ptr->initial, int, 2);
  genmult2ptr->initial[1] = 1;
  genmult2ptr->flags[DFA] = TRUE;
  genmult2ptr->flags[ACCESSIBLE] = TRUE;
  genmult2ptr->flags[BFS] = TRUE;

  genmult2ptr->table->table_type = op_table_type;
  genmult2ptr->table->denserows = 0;
  genmult2ptr->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(genmult2ptr->table->filename, char,
            stringlen(genmult2filename) + 1);
    strcpy(genmult2ptr->table->filename, genmult2filename);
  }

  ne = genmultptr->alphabet->size;
  ngens = genmultptr->alphabet->base->size;
  ngens1 = ngens + 1;

  if (ne != ngens1 * ngens1 - 1) {
    fprintf(stderr, "Error: in a 2-variable fsa, alphabet size should = "
                    "(ngens+1)^2 - 1.\n");
    return 0;
  }

  fsa_set_is_accepting(genmultptr);

  dense_ip = genmultptr->table->table_type == DENSE;
  dr = genmultptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table = genmultptr->table->table_data_ptr;

  hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = genmultptr->initial[1];
  ht_ptr[1] = genmultptr->initial[1];
  im = hash_locate(&ht, 2);
  /* Each state in the composite transition table will be represented as a
   * subset of the set of ordered pairs of states of *genmultptr. The initial
   * state contains just one such pair, of which both components are the initial
   * state of *genmultptr. The subsets will be stored as variable-length records
   * in the hash-table, as a list of pairs in increasing order. If a state is
   * reached from a transition ($,x) or (x,$) (with $ the padding symbol), then
   * it needs to be marked as such, since we do not allow a $ to be followed by
   * any other generator. We do this by adding a 1 or a 2 to the end of the
   * statelist - this is recognisable by the fact that the length of the
   * statelist then becomes odd.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_genmult2.\n");
    return 0;
  }
  if (keeptable)
    if ((tablefile = fopen(genmult2filename, "w")) == 0) {
      fprintf(stderr, "Error: cannot open file %s\n", genmult2filename);
      return 0;
    }
  if (dense_op)
    tmalloc(fsarow, int, ne) else tmalloc(fsarow, int, 2 * ne + 1)

        label = genmultptr->states->setToLabels;
  cstate = 0;
  if (dense_op)
    len = ne; /* The length of the fsarow output. */
  nt = 0;     /* Number of transitions in genmult2ptr */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    reclen = hash_rec_len(&ht, cstate);
    cs_ptr = hash_rec(&ht, cstate);
    cs_ptre = hash_rec(&ht, cstate) + reclen - 1;
    if (reclen % 2 == 1) {
      if (*cs_ptre == 1) {
        leftpad = TRUE;
        rightpad = FALSE;
      }
      else {
        leftpad = FALSE;
        rightpad = TRUE;
      }
      cs_ptre--;
    }
    else {
      leftpad = FALSE;
      rightpad = FALSE;
    }

    if (dense_op)
      for (i = 0; i < ne; i++)
        fsarow[i] = 0;
    else
      len = 0;

    e = 0; /* e is the edge number of generator pair (g1,g3) */
    for (g1 = 1; g1 <= ngens1; g1++)
      for (g3 = 1; g3 <= ngens1; g3++) {
        /* Calculate action of pair (g1,g3) on state cstate  - to get the image,
         * we have to apply ( (g1,g2), (g2,g3) ) to each ordered pair in the
         * subset corresponding to cstate, * and this for each generator g2 of
         * the base-alphabet (including the padding symbol).
         */

        e++;
        if (g1 == ngens1 && g3 == ngens1)
          continue;

        if ((leftpad && g1 <= ngens) || (rightpad && g3 <= ngens))
          continue;
        ht_ptrb = ht.current_ptr;
        ht_ptre = ht_ptrb - 1;

        es1 = (g1 - 1) * ngens1 + 1;
        ef1 = g1 * ngens1;
        /* As g2 ranges from 1 to ngens+1 in the pair (g1,g2), for fixed g1, the
         * corresponding edge number in the fsa ranges from es1 to ef1.
         *
         * As g2 ranges from 1 to ngens+1 in the pair (g2,g3), for fixed g3, the
         * corresponding edge number in the fsa ranges from g3 upwards, with
         * increments of size ngens+1.
         */

        ptr = cs_ptr;
        while (ptr <= cs_ptre) {
          csa = *(ptr++);
          csb = *(ptr++);
          for (g2 = 1, e1 = es1, e2 = g3; e1 <= ef1; g2++, e1++, e2 += ngens1) {
            csima = g1 == ngens1 && g2 == ngens1
                        ? (genmultptr->is_accepting[csa] ? csa : 0)
                        : target(dense_ip, table, e1, csa, dr);
            if (csima == 0)
              continue;

            csimb = g2 == ngens1 && g3 == ngens1
                        ? (genmultptr->is_accepting[csb] ? csb : 0)
                        : target(dense_ip, table, e2, csb, dr);
            if (csimb == 0)
              continue;
            if (ht_ptrb > ht_ptre || csima > *(ht_ptre - 1) ||
                (csima == *(ht_ptre - 1) && csimb > *ht_ptre)) {
              /* We have a new state for the image subset to be added to the end
               */
              *(++ht_ptre) = csima;
              *(++ht_ptre) = csimb;
            }
            else {
              ht_chptr = ht_ptrb;
              while (*ht_chptr < csima)
                ht_chptr += 2;
              while (*ht_chptr == csima && *(ht_chptr + 1) < csimb)
                ht_chptr += 2;
              if (csima < *ht_chptr || csimb < *(ht_chptr + 1)) {
                /* we have a new state for the image subset to be added in the
                 * middle */
                ht_ptr = ht_ptre;
                ht_ptre += 2;
                while (ht_ptr >= ht_chptr) {
                  *(ht_ptr + 2) = *ht_ptr;
                  ht_ptr--;
                }
                *ht_chptr = csima;
                *(ht_chptr + 1) = csimb;
              }
            }
          }
        }
        if (ht_ptre > ht_ptrb) {
          if (g1 == ngens1)
            *(++ht_ptre) = 1;
          else if (g3 == ngens1)
            *(++ht_ptre) = 2;
        }
        im = hash_locate(&ht, ht_ptre - ht_ptrb + 1);
        if (im > 0) {
          if (dense_op)
            fsarow[e - 1] = im;
          else {
            fsarow[++len] = e;
            fsarow[++len] = im;
          }
          nt++;
        }
      }
    if (!dense_op)
      fsarow[0] = len++;
    if (keeptable)
      fwrite((void *)fsarow, sizeof(int), (size_t)len, tablefile);
  }

  if (keeptable)
    fclose(tablefile);
  tfree(fsarow);

  ns = genmult2ptr->states->size = ht.num_recs;
  genmult2ptr->table->numTransitions = nt;

  if (kbm_print_level >= 3) {
    printf("    #Calculated transitions - %d states, %d transitions.\n", ns,
           nt);
    printf("    #Now calculating state labels.\n");
  }

  /* Locate the accept states for  Mult_(a*b)  each generator pair (a,b).
   * This is slightly cumbersome, since a state S
   * is an accept state if either the  subset representing S contains a
   * pair (s1,s2), where s1 is accept state for Mult_a and s2 for Mult_b,
   * or we can get from to such a state by applying ( ($,g), (g,$) ) to one
   * of the pairs in S, for some generator g.
   * It is most convenient to work out this information taking the states
   * S in reverse order.
   * The information on the accept-states will be stored as labels, which
   * (13/9/95 - change labels from words to lists of words)
   * will be lists of words in the generators. Each such list will have the form
   * [a1*b1,a2*b2,...,ar*br], where the (ai,bi) are the generator pairs for
   * which that particular state is an accept state. The labels will be
   * collected initially in a new hash-table.
   * The identity generator will be numbered ngens+1 and given name '_'
   * rather than represented by the empty word. This is so that we can
   * distinguish between multipliers for "_*a" and "a*_" if necessary.
   */

  genmult2ptr->states->type = LABELED;
  tmalloc(genmult2ptr->states->labels, srec, 1);
  labelset = genmult2ptr->states->labels;
  labelset->type = LISTOFWORDS;
  labelset->alphabet_size = ngens1;
  for (i = 1; i <= ngens; i++) {
    tmalloc(labelset->alphabet[i], char,
            stringlen(genmultptr->states->labels->alphabet[i]) + 1);
    strcpy(labelset->alphabet[i], genmultptr->states->labels->alphabet[i]);
  }
  tmalloc(labelset->alphabet[ngens1], char, 2);
  labelset->alphabet[ngens1][0] = '_';
  labelset->alphabet[ngens1][1] = 0;
  tmalloc(genmult2ptr->states->setToLabels, setToLabelsType, ns + 1);
  newlabel = genmult2ptr->states->setToLabels;
  tmalloc(genmult2ptr->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    genmult2ptr->is_accepting[i] = FALSE;
  hash_init(&labelht, FALSE, 0, LABHTSIZE, 2 * LABHTSIZE);

  es1 = ngens * ngens1 + 1;
  ef1 = ngens1 * ngens1 - 1;
  for (cstate = ns; cstate >= 1; cstate--) {
    /* We work backwards through the states, since we wish to add on additional
     * elements at the end of the list in the hash-table - this destroys
     * later entries, but that doesn't matter, since we have already dealt
     * with them.
     */
    cs_ptr = hash_rec(&ht, cstate);
    reclen = hash_rec_len(&ht, cstate);
    if (reclen % 2 == 1)
      reclen--;
    /* The last entry only marks the fact that this is a "padded state"*/
    cs_ptre = hash_rec(&ht, cstate) + reclen - 1;
    /* Apply generators ( ($,g2), (g2,$) ) and see if we get anything new.
     * We won't bother about having them in increasing order this time.
     */
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++);
      csb = *(ptr++);
      for (e1 = es1, e2 = ngens1; e1 <= ef1; e1++, e2 += ngens1) {
        csima = target(dense_ip, table, e1, csa, dr);
        if (csima == 0)
          continue;
        csimb = target(dense_ip, table, e2, csb, dr);
        if (csimb == 0)
          continue;
        /* see if (csima,csimb) is new */
        ht_chptr = cs_ptr;
        got = FALSE;
        while (ht_chptr < cs_ptre) {
          if (csima == ht_chptr[0] && csimb == ht_chptr[1]) {
            got = TRUE;
            break;
          }
          ht_chptr += 2;
        }
        if (!got) {
          /* add (csima,csimb) to the end */
          *(++cs_ptre) = csima;
          *(++cs_ptre) = csimb;
        }
      }
    }
    /* Now we see which pairs in the subset are of form (s,t), where s is
     * an accept state for a generator a, and t for a generator b.
     * The list of all such pairs (a,b) will form the label of the state, which
     * will be the list of words [a1*b1,a2*b2,..,ar*br], with the (ai,bi) coming
     * in lex-order.
     */

    ht_ptrb = labelht.current_ptr;
    ht_ptre = ht_ptrb - 1;
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++);
      csb = *(ptr++);
      if (((l1 = label[csa]) != 0) && ((l2 = label[csb]) != 0)) {
        labellist1 = genmultptr->states->labels->wordslist[l1];
        labellist2 = genmultptr->states->labels->wordslist[l2];
        j1 = 0;
        while (labellist1[j1]) {
          g1 = labellist1[j1][0];
          if (g1 == 0)
            g1 = ngens1;
          j2 = 0;
          while (labellist2[j2]) {
            genmult2ptr->is_accepting[cstate] = TRUE;
            g2 = labellist2[j2][0];
            if (g2 == 0)
              g2 = ngens1;
            if (ht_ptrb > ht_ptre || g1 > *(ht_ptre - 1) ||
                (g1 == *(ht_ptre - 1) && g2 > *ht_ptre)) {
              /* We have a new generator pair to be added to the end */
              *(++ht_ptre) = g1;
              *(++ht_ptre) = g2;
            }
            else {
              ht_chptr = ht_ptrb;
              while (*ht_chptr < g1)
                ht_chptr += 2;
              while (*ht_chptr == g1 && *(ht_chptr + 1) < g2)
                ht_chptr += 2;
              if (g1 < *ht_chptr || g2 < *(ht_chptr + 1)) {
                /* we have a new generator pair to be added in the middle */
                ht_ptr = ht_ptre;
                ht_ptre += 2;
                while (ht_ptr >= ht_chptr) {
                  *(ht_ptr + 2) = *ht_ptr;
                  ht_ptr--;
                }
                *ht_chptr = g1;
                *(ht_chptr + 1) = g2;
              }
            }
            j2++;
          }
          j1++;
        }
      }
    }
    /* That completes the calculation of the label for cstate */
    newlabel[cstate] = hash_locate(&labelht, ht_ptre - ht_ptrb + 1);
  }
  hash_clear(&ht);

  ct = 0;
  for (i = 1; i <= ns; i++)
    if (genmult2ptr->is_accepting[i])
      ct++;
  genmult2ptr->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(genmult2ptr->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (genmult2ptr->is_accepting[i])
        genmult2ptr->accepting[++ct] = i;
  }
  tfree(genmult2ptr->is_accepting);
  tfree(genmultptr->is_accepting);

  /* Finally copy the records from the label hash-table into the set of labels
   */
  nlab = labelset->size = labelht.num_recs;
  if (kbm_print_level >= 3)
    printf("    #There are %d distinct labels.\n", nlab);
  tmalloc(labelset->wordslist, gen **, nlab + 1);
  for (i = 1; i <= nlab; i++) {
    len = hash_rec_len(&labelht, i) / 2;
    tmalloc(labelset->wordslist[i], gen *, len + 1);
    ht_ptr = hash_rec(&labelht, i);
    for (j = 0; j < len; j++) {
      tmalloc(labelset->wordslist[i][j], gen, 3);
      labelset->wordslist[i][j][0] = ht_ptr[2 * j];
      labelset->wordslist[i][j][1] = ht_ptr[2 * j + 1];
      labelset->wordslist[i][j][2] = 0;
    }
    labelset->wordslist[i][len] = 0;
  }

  hash_clear(&labelht);
  if (destroy)
    fsa_clear(genmultptr);

  if (readback) {
    tablefile = fopen(genmult2filename, "r");
    compressed_transitions_read(genmult2ptr, tablefile);
    fclose(tablefile);
    unlink(genmult2filename);
  }

  return genmult2ptr;
}

/* This procedure takes the fsa *genmultptr produced by fsa_triples,
 * and builds a particular  multiplier Mult_g1.
 * This merely involves setting the accept states of *genmultptr
 * in accordance with the labels of its states.
 * g can be 0, for the identity generator, which (in shortlex case) inevitably
 * produces the diagonal of the word-acceptor.
 * This procedure alters its arguments and does not return anything.
 */
int fsa_makemult(fsa *genmultptr, int g)
{
  int ngens, ns, i, j, ct;
  gen **labellist;
  setToLabelsType *label;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_makemult with generator number %d.\n", g);
  if (!genmultptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_makemult only applies to DFA's.\n");
    return -1;
  }

  if (genmultptr->alphabet->type != PRODUCT ||
      genmultptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_makemult: fsa must be 2-variable.\n");
    return -1;
  }

  if (genmultptr->states->type != LABELED) {
    fprintf(stderr, "Error in fsa_makemult: states of fsa must be labeled.\n");
    return -1;
  }

  ns = genmultptr->states->size;
  ngens = genmultptr->alphabet->base->size;
  if (g < 0 || g > ngens + 1) {
    fprintf(stderr, "#Error in fsa_makemult: Generator is out of range.\n");
    return -1;
  }

  tfree(genmultptr->accepting);
  tfree(genmultptr->is_accepting);
  label = genmultptr->states->setToLabels;
  ct = 0;
  for (i = 1; i <= ns; i++)
    if (label[i] > 0) {
      labellist = genmultptr->states->labels->wordslist[label[i]];
      j = 0;
      while (labellist[j]) {
        if (labellist[j][0] == g)
          ct++;
        j++;
      }
    }
  genmultptr->num_accepting = ct;
  if (ct < ns || ns == 1) {
    tfree(genmultptr->accepting);
    tmalloc(genmultptr->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (label[i] > 0) {
        labellist = genmultptr->states->labels->wordslist[label[i]];
        j = 0;
        while (labellist[j]) {
          if (labellist[j][0] == g)
            genmultptr->accepting[++ct] = i;
          j++;
        }
      }
  }
  /* The state labelling is no longer relevant, so we clear it */
  genmultptr->states->type = SIMPLE;
  srec_clear(genmultptr->states->labels);
  tfree(genmultptr->states->labels);
  tfree(genmultptr->states->setToLabels);
  return 0;
}

/* This procedure takes the fsa *genmult2ptr produced by fsa_genmult2,
 * and builds a particular length-2 multiplier Mult_g1g2.
 * This merely involves locating the accept states.
 * This procedure alters its arguments and does not return anything.
 */
int fsa_makemult2(fsa *genmult2ptr, int g1, int g2)
{
  int ngens, ns, nlabs, i, j, ct;
  gen ***labellist;
  boolean *accept;
  setToLabelsType *labelnumber;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_makemult2 with generators %d and %d.\n", g1, g2);
  if (!genmult2ptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_makemult2 only applies to DFA's.\n");
    return -1;
  }

  if (genmult2ptr->alphabet->type != PRODUCT ||
      genmult2ptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_makemult2: fsa must be 2-variable.\n");
    return -1;
  }

  if (genmult2ptr->states->type != LABELED) {
    fprintf(stderr, "Error in fsa_makemult2: states of fsa must be labeled.\n");
    return -1;
  }

  if (genmult2ptr->states->labels->type != LISTOFWORDS) {
    fprintf(stderr, "Error in fsa_makemult2: labels must be lists of words.\n");
    return -1;
  }

  ns = genmult2ptr->states->size;
  nlabs = genmult2ptr->states->labels->size;
  ngens = genmult2ptr->states->labels->alphabet_size;
  if (g1 <= 0 || g1 > ngens || g2 <= 0 || g2 > ngens) {
    fprintf(stderr, "#Error in fsa_makemult2: A generator is out of range.\n");
    return -1;
  }

  tmalloc(accept, boolean, nlabs + 1);
  labellist = genmult2ptr->states->labels->wordslist;
  /* Now we see which labels are accept-labels for the pair (g1,g2) - the
   * label is an accept-label if the list of words which is its name
   * contains g1*g2.
   */
  accept[0] = FALSE;
  for (i = 1; i <= nlabs; i++) {
    accept[i] = FALSE;
    j = 0;
    while (labellist[i][j]) {
      if (labellist[i][j][0] == g1 && labellist[i][j][1] == g2) {
        accept[i] = TRUE;
        break;
      }
      j++;
    }
  }

  /* Now we can see which states are accept-states. A state is an accept-state
   * iff its label is an accept-label.
   * First we count the number.
   */
  ct = 0;
  labelnumber = genmult2ptr->states->setToLabels;
  for (i = 1; i <= ns; i++)
    if (accept[labelnumber[i]])
      ct++;

  genmult2ptr->num_accepting = ct;
  if (ct < ns || ns == 1) {
    tfree(genmult2ptr->accepting);
    tmalloc(genmult2ptr->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (accept[labelnumber[i]])
        genmult2ptr->accepting[++ct] = i;
  }

  tfree(accept);

  /* The state labelling is no longer relevant, so we clear it */
  genmult2ptr->states->type = SIMPLE;
  srec_clear(genmult2ptr->states->labels);
  tfree(genmult2ptr->states->labels);
  tfree(genmult2ptr->states->setToLabels);
  return 0;
}

/* *mult1ptr and *mult2ptr should be multiplier fsa's of an automatic group.
 * This function calculates the composite of these two multipliers.
 * So if *mult1ptr is the mutiplier for the word w1 and *mult2ptr for w2,
 * then the returned fsa is the multiplier for w1*w2.
 * In fact, *mult1ptr and *mult2ptr can be any 2-variable automata over the
 * same alphabet, and the composite is returned.
 */
fsa *fsa_composite(fsa *mult1ptr, fsa *mult2ptr, storage_type op_table_type,
                   boolean destroy, char *compfilename, boolean readback)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_composite.\n");
  if (mult1ptr->states->size < MAXUSHORT && mult2ptr->states->size < MAXUSHORT)
    return fsa_composite_short(mult1ptr, mult2ptr, op_table_type, destroy,
                               compfilename, readback);
  else
    return fsa_composite_int(mult1ptr, mult2ptr, op_table_type, destroy,
                             compfilename, readback);
}

static fsa *fsa_composite_short(fsa *mult1ptr, fsa *mult2ptr,
                                storage_type op_table_type, boolean destroy,
                                char *compfilename, boolean readback)
{
  int **table1, **table2, ne, ngens, ngens1, ns, *fsarow, e, e1, e2, es1, ef1,
      dr1, dr2, nt, cstate, im, csa, csb, csima, csimb, i, ct, g1, g2, g3, len = 0,
      reclen;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  boolean dense_ip1, dense_ip2, dense_op, got, leftpad, rightpad;
  short_hash_table ht;
  fsa *compositeptr;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_composite_short.\n");
  if (!mult1ptr->flags[DFA] || !mult2ptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_composite only applies to DFA's.\n");
    return 0;
  }

  if (mult1ptr->alphabet->type != PRODUCT || mult1ptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_composite: fsa must be 2-variable.\n");
    return 0;
  }
  if (mult2ptr->alphabet->type != PRODUCT || mult2ptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_composite: fsa must be 2-variable.\n");
    return 0;
  }

  if (!srec_equal(mult1ptr->alphabet, mult2ptr->alphabet)) {
    fprintf(stderr, "Error in fsa_composite: fsa's must have same alphabet.\n");
    return 0;
  }

  tmalloc(compositeptr, fsa, 1);
  fsa_init(compositeptr);
  srec_copy(compositeptr->alphabet, mult1ptr->alphabet);
  compositeptr->states->type = SIMPLE;
  compositeptr->num_initial = 1;
  tmalloc(compositeptr->initial, int, 2);
  compositeptr->initial[1] = 1;
  compositeptr->flags[DFA] = TRUE;
  compositeptr->flags[ACCESSIBLE] = TRUE;
  compositeptr->flags[BFS] = TRUE;

  compositeptr->table->table_type = op_table_type;
  compositeptr->table->denserows = 0;
  compositeptr->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(compositeptr->table->filename, char, stringlen(compfilename) + 1);
    strcpy(compositeptr->table->filename, compfilename);
  }

  ne = mult1ptr->alphabet->size;
  ngens = mult1ptr->alphabet->base->size;
  ngens1 = ngens + 1;

  if (ne != ngens1 * ngens1 - 1) {
    fprintf(stderr, "Error: in a 2-variable fsa, alphabet size should = "
                    "(ngens+1)^2 - 1.\n");
    return 0;
  }

  fsa_set_is_accepting(mult1ptr);
  fsa_set_is_accepting(mult2ptr);

  dense_ip1 = mult1ptr->table->table_type == DENSE;
  dr1 = mult1ptr->table->denserows;
  dense_ip2 = mult2ptr->table->table_type == DENSE;
  dr2 = mult2ptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table1 = mult1ptr->table->table_data_ptr;
  table2 = mult2ptr->table->table_data_ptr;

  short_hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = mult1ptr->initial[1];
  ht_ptr[1] = mult2ptr->initial[1];
  im = short_hash_locate(&ht, 2);
  /* Each state in the composite transition table will be represented as a
   * subset of the set of ordered pairs in which the first component is a state
   * in *multptr1 and the second a state in *multptr2. The initial state
   * contains just one such pair, of which the components are the initial states
   * of *mult1ptr and *multptr2. The subsets will be stored as variable-length
   * records in the hash-table, as a list of pairs in increasing order. If a
   * state is reached from a transition ($,x) or (x,$) (with $ the padding
   * symbol), then it needs to be marked as such, since we do not allow a $
   * to be followed by any other generator.
   * We do this by adding a 1 or a 2 to the end of the statelist - this is
   * recognisable by the fact that the length of the statelist then becomes odd.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_composite.\n");
    return 0;
  }
  if ((tempfile = fopen(compfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", compfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow, int, ne) else tmalloc(fsarow, int, 2 * ne + 1)

        cstate = 0;
  if (dense_op)
    len = ne; /* The length of the fsarow output. */
  nt = 0;     /* Number of transitions in compositeptr */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    reclen = short_hash_rec_len(&ht, cstate);
    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = short_hash_rec(&ht, cstate) + reclen - 1;
    /* for (i=0;i<reclen;i++) printf(" %d",cs_ptr[i]); printf("\n"); */
    if (reclen % 2 == 1) {
      if (*cs_ptre == 1) {
        leftpad = TRUE;
        rightpad = FALSE;
      }
      else {
        leftpad = FALSE;
        rightpad = TRUE;
      }
      cs_ptre--;
    }
    else {
      leftpad = FALSE;
      rightpad = FALSE;
    }

    if (dense_op)
      for (i = 0; i < ne; i++)
        fsarow[i] = 0;
    else
      len = 0;

    e = 0; /* e is the edge number of generator pair (g1,g3) */
    for (g1 = 1; g1 <= ngens1; g1++)
      for (g3 = 1; g3 <= ngens1; g3++) {
        /* Calculate action of pair (g1,g3) on state cstate  - to get the image,
         * we have to apply ( (g1,g2), (g2,g3) ) to each ordered pair in the
         * subset corresponding to cstate, and this for each generator g2 of the
         * base-alphabet (including the padding symbol).
         */
        e++;
        if (g1 == ngens1 && g3 == ngens1)
          continue;
        if ((leftpad && g1 <= ngens) || (rightpad && g3 <= ngens))
          continue;
        ht_ptrb = ht.current_ptr;
        ht_ptre = ht_ptrb - 1;
        es1 = (g1 - 1) * ngens1 + 1;
        ef1 = g1 * ngens1;
        /* As g2 ranges from 1 to ngens+1 in the pair (g1,g2), for fixed g1, the
         * corresponding edge number in the fsa ranges from es1 to ef1.
         *
         * As g2 ranges from 1 to ngens+1 in the pair (g2,g3), for fixed g3, the
         * corresponding edge number in the fsa ranges from g3 upwards, with
         * increments of size ngens+1.
         */

        ptr = cs_ptr;
        while (ptr <= cs_ptre) {
          csa = *(ptr++);
          csb = *(ptr++);
          for (g2 = 1, e1 = es1, e2 = g3; e1 <= ef1; g2++, e1++, e2 += ngens1) {
            csima = g1 == ngens1 && g2 == ngens1
                        ? (mult1ptr->is_accepting[csa] > 0 ? csa : 0)
                        : target(dense_ip1, table1, e1, csa, dr1);
            if (csima == 0)
              continue;

            csimb = g2 == ngens1 && g3 == ngens1
                        ? (mult2ptr->is_accepting[csb] > 0 ? csb : 0)
                        : target(dense_ip2, table2, e2, csb, dr2);
            if (csimb == 0)
              continue;

            if (ht_ptrb > ht_ptre || csima > *(ht_ptre - 1) ||
                (csima == *(ht_ptre - 1) && csimb > *ht_ptre)) {
              /* We have a new state for the image subset to be added to the end
               */
              *(++ht_ptre) = csima;
              *(++ht_ptre) = csimb;
            }
            else {
              ht_chptr = ht_ptrb;
              while (*ht_chptr < csima)
                ht_chptr += 2;
              while (*ht_chptr == csima && *(ht_chptr + 1) < csimb)
                ht_chptr += 2;
              if (csima < *ht_chptr || csimb < *(ht_chptr + 1)) {
                /* we have a new state for the image subset to be added in the
                 * middle */
                ht_ptr = ht_ptre;
                ht_ptre += 2;
                while (ht_ptr >= ht_chptr) {
                  *(ht_ptr + 2) = *ht_ptr;
                  ht_ptr--;
                }
                *ht_chptr = csima;
                *(ht_chptr + 1) = csimb;
              }
            }
          }
        }
        if (ht_ptre > ht_ptrb) {
          if (g1 == ngens1)
            *(++ht_ptre) = 1;
          else if (g3 == ngens1)
            *(++ht_ptre) = 2;
        }
        im = short_hash_locate(&ht, ht_ptre - ht_ptrb + 1);
        if (im > 0) {
          if (dense_op)
            fsarow[e - 1] = im;
          else {
            fsarow[++len] = e;
            fsarow[++len] = im;
          }
          nt++;
        }
      }
    if (!dense_op)
      fsarow[0] = len++;
    fwrite((void *)fsarow, sizeof(int), (size_t)len, tempfile);
  }
  fclose(tempfile);

  ns = compositeptr->states->size = ht.num_recs;
  compositeptr->table->numTransitions = nt;

  if (kbm_print_level >= 3)
    printf("    #Calculated transitions - %d states, %d transitions.\n", ns,
           nt);

  /* Locate the accept states. This is slightly cumbersome, since a state
   * is an accept state if either the corresponding subset contains a
   * a pair (s1,s2), where s1 is and accept state of *mult1ptr and s2 an
   * accept state of *mult2ptr, or we can get from some such state to an
   * accept state by applying elements ( ($,x), (x,$ ).
   * We will need to use the array compositeptr->is_accepting.
   */

  tmalloc(compositeptr->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    compositeptr->is_accepting[i] = FALSE;
  ct = 0;
  es1 = ngens * ngens1 + 1;
  ef1 = ngens1 * ngens1 - 1;
  for (cstate = ns; cstate >= 1; cstate--) {
    /* We work backwards through the states, since we wish to add on additional
     * elements at the end of the list in the hash-table - this destroys
     * later entries, but that doesn't matter, since we have already dealt
     * with them.
     */
    cs_ptr = short_hash_rec(&ht, cstate);
    reclen = short_hash_rec_len(&ht, cstate);
    if (reclen % 2 == 1)
      reclen--; /* The last entry marks the fact that this is a "padded state"*/
    cs_ptre = short_hash_rec(&ht, cstate) + reclen - 1;
    /* First see if the set itself contains an accept-state */
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++);
      csb = *(ptr++);
      if (mult1ptr->is_accepting[csa] && mult2ptr->is_accepting[csb]) {
        compositeptr->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    }
    if (compositeptr->is_accepting[cstate])
      continue;
    /* Next apply generators ( ($,g2), (g2,$) ) and see if we get anything new.
     * We won't bother about having them in increasing order this time.
     */
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++);
      csb = *(ptr++);
      for (e1 = es1, e2 = ngens1; e1 <= ef1; e1++, e2 += ngens1) {
        csima = target(dense_ip1, table1, e1, csa, dr1);
        if (csima == 0)
          continue;
        csimb = target(dense_ip2, table2, e2, csb, dr2);
        if (csimb == 0)
          continue;

        /* see if (csima,csimb) is accepting */
        if (mult1ptr->is_accepting[csima] && mult2ptr->is_accepting[csimb]) {
          compositeptr->is_accepting[cstate] = TRUE;
          ct++;
          break;
        }
        /* now see if it is new */
        ht_chptr = cs_ptr;
        got = FALSE;
        while (ht_chptr < cs_ptre) {
          if (csima == ht_chptr[0] && csimb == ht_chptr[1]) {
            got = TRUE;
            break;
          }
          ht_chptr += 2;
        }
        if (!got) {
          /* add (csima,csimb) to the end */
          *(++cs_ptre) = csima;
          *(++cs_ptre) = csimb;
        }
      }
      if (compositeptr->is_accepting[cstate])
        continue;
    }
  }

  compositeptr->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(compositeptr->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (compositeptr->is_accepting[i])
        compositeptr->accepting[++ct] = i;
  }
  tfree(compositeptr->is_accepting);
  tfree(mult1ptr->is_accepting);
  tfree(mult2ptr->is_accepting);
  short_hash_clear(&ht);
  tfree(fsarow);
  if (destroy) {
    fsa_clear(mult1ptr);
    fsa_clear(mult2ptr);
  }

  if (readback) {
    tempfile = fopen(compfilename, "r");
    compressed_transitions_read(compositeptr, tempfile);
    fclose(tempfile);
    unlink(compfilename);
  }

  return compositeptr;
}

static fsa *fsa_composite_int(fsa *mult1ptr, fsa *mult2ptr,
                              storage_type op_table_type, boolean destroy,
                              char *compfilename, boolean readback)
{
  int **table1, **table2, ne, ngens, ngens1, ns, *fsarow, e, e1, e2, es1, ef1,
      dr1, dr2, nt, cstate, im, csa, csb, csima, csimb, i, ct, g1, g2, g3, len = 0,
      reclen;
  int *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre, *ptr;
  boolean dense_ip1, dense_ip2, dense_op, got, leftpad, rightpad;
  hash_table ht;
  fsa *compositeptr;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_composite_int.\n");
  if (!mult1ptr->flags[DFA] || !mult2ptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_composite only applies to DFA's.\n");
    return 0;
  }

  if (mult1ptr->alphabet->type != PRODUCT || mult1ptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_composite: fsa must be 2-variable.\n");
    return 0;
  }
  if (mult2ptr->alphabet->type != PRODUCT || mult2ptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_composite: fsa must be 2-variable.\n");
    return 0;
  }

  if (!srec_equal(mult1ptr->alphabet, mult2ptr->alphabet)) {
    fprintf(stderr, "Error in fsa_composite: fsa's must have same alphabet.\n");
    return 0;
  }

  tmalloc(compositeptr, fsa, 1);
  fsa_init(compositeptr);
  srec_copy(compositeptr->alphabet, mult1ptr->alphabet);
  compositeptr->states->type = SIMPLE;
  compositeptr->num_initial = 1;
  tmalloc(compositeptr->initial, int, 2);
  compositeptr->initial[1] = 1;
  compositeptr->flags[DFA] = TRUE;
  compositeptr->flags[ACCESSIBLE] = TRUE;
  compositeptr->flags[BFS] = TRUE;

  compositeptr->table->table_type = op_table_type;
  compositeptr->table->denserows = 0;
  compositeptr->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(compositeptr->table->filename, char, stringlen(compfilename) + 1);
    strcpy(compositeptr->table->filename, compfilename);
  }

  ne = mult1ptr->alphabet->size;
  ngens = mult1ptr->alphabet->base->size;
  ngens1 = ngens + 1;

  if (ne != ngens1 * ngens1 - 1) {
    fprintf(stderr, "Error: in a 2-variable fsa, alphabet size should = "
                    "(ngens+1)^2 - 1.\n");
    return 0;
  }

  fsa_set_is_accepting(mult1ptr);
  fsa_set_is_accepting(mult2ptr);

  dense_ip1 = mult1ptr->table->table_type == DENSE;
  dr1 = mult1ptr->table->denserows;
  dense_ip2 = mult2ptr->table->table_type == DENSE;
  dr2 = mult2ptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table1 = mult1ptr->table->table_data_ptr;
  table2 = mult2ptr->table->table_data_ptr;

  hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = mult1ptr->initial[1];
  ht_ptr[1] = mult2ptr->initial[1];
  im = hash_locate(&ht, 2);
  /* Each state in the composite transition table will be represented as a
   * subset of the set of ordered pairs in which the first component is a state
   * in *multptr1 and the second a state in *multptr2. The initial state
   * contains just one such pair, of which the components are the initial states
   * of *mult1ptr and *multptr2. The subsets will be stored as variable-length
   * records in the hash-table, as a list of pairs in increasing order. If a
   * state is reached from a transition ($,x) or (x,$) (with $ the padding
   * symbol), then it needs to be marked as such, since we do not allow a $
   * to be followed by any other generator.
   * We do this by adding a 1 or a 2 to the end of the statelist - this is
   * recognisable by the fact that the length of the statelist then becomes odd.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_composite.\n");
    return 0;
  }
  if ((tempfile = fopen(compfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", compfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow, int, ne) else tmalloc(fsarow, int, 2 * ne + 1)

        cstate = 0;
  if (dense_op)
    len = ne; /* The length of the fsarow output. */
  nt = 0;     /* Number of transitions in compositeptr */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    reclen = hash_rec_len(&ht, cstate);
    cs_ptr = hash_rec(&ht, cstate);
    cs_ptre = hash_rec(&ht, cstate) + reclen - 1;
    /* for (i=0;i<reclen;i++) printf(" %d",cs_ptr[i]); printf("\n"); */
    if (reclen % 2 == 1) {
      if (*cs_ptre == 1) {
        leftpad = TRUE;
        rightpad = FALSE;
      }
      else {
        leftpad = FALSE;
        rightpad = TRUE;
      }
      cs_ptre--;
    }
    else {
      leftpad = FALSE;
      rightpad = FALSE;
    }

    if (dense_op)
      for (i = 0; i < ne; i++)
        fsarow[i] = 0;
    else
      len = 0;

    e = 0; /* e is the edge number of generator pair (g1,g3) */
    for (g1 = 1; g1 <= ngens1; g1++)
      for (g3 = 1; g3 <= ngens1; g3++) {
        /* Calculate action of pair (g1,g3) on state cstate  - to get the image,
         * we have to apply ( (g1,g2), (g2,g3) ) to each ordered pair in the
         * subset corresponding to cstate, and this for each generator g2 of the
         * base-alphabet (including the padding symbol).
         */
        e++;
        if (g1 == ngens1 && g3 == ngens1)
          continue;
        if ((leftpad && g1 <= ngens) || (rightpad && g3 <= ngens))
          continue;
        ht_ptrb = ht.current_ptr;
        ht_ptre = ht_ptrb - 1;
        es1 = (g1 - 1) * ngens1 + 1;
        ef1 = g1 * ngens1;
        /* As g2 ranges from 1 to ngens+1 in the pair (g1,g2), for fixed g1, the
         * corresponding edge number in the fsa ranges from es1 to ef1.
         *
         * As g2 ranges from 1 to ngens+1 in the pair (g2,g3), for fixed g3, the
         * corresponding edge number in the fsa ranges from g3 upwards, with
         * increments of size ngens+1.
         */

        ptr = cs_ptr;
        while (ptr <= cs_ptre) {
          csa = *(ptr++);
          csb = *(ptr++);
          for (g2 = 1, e1 = es1, e2 = g3; e1 <= ef1; g2++, e1++, e2 += ngens1) {
            csima = g1 == ngens1 && g2 == ngens1
                        ? (mult1ptr->is_accepting[csa] > 0 ? csa : 0)
                        : target(dense_ip1, table1, e1, csa, dr1);
            if (csima == 0)
              continue;

            csimb = g2 == ngens1 && g3 == ngens1
                        ? (mult2ptr->is_accepting[csb] > 0 ? csb : 0)
                        : target(dense_ip2, table2, e2, csb, dr2);
            if (csimb == 0)
              continue;

            if (ht_ptrb > ht_ptre || csima > *(ht_ptre - 1) ||
                (csima == *(ht_ptre - 1) && csimb > *ht_ptre)) {
              /* We have a new state for the image subset to be added to the end
               */
              *(++ht_ptre) = csima;
              *(++ht_ptre) = csimb;
            }
            else {
              ht_chptr = ht_ptrb;
              while (*ht_chptr < csima)
                ht_chptr += 2;
              while (*ht_chptr == csima && *(ht_chptr + 1) < csimb)
                ht_chptr += 2;
              if (csima < *ht_chptr || csimb < *(ht_chptr + 1)) {
                /* we have a new state for the image subset to be added in the
                 * middle */
                ht_ptr = ht_ptre;
                ht_ptre += 2;
                while (ht_ptr >= ht_chptr) {
                  *(ht_ptr + 2) = *ht_ptr;
                  ht_ptr--;
                }
                *ht_chptr = csima;
                *(ht_chptr + 1) = csimb;
              }
            }
          }
        }
        if (ht_ptre > ht_ptrb) {
          if (g1 == ngens1)
            *(++ht_ptre) = 1;
          else if (g3 == ngens1)
            *(++ht_ptre) = 2;
        }
        im = hash_locate(&ht, ht_ptre - ht_ptrb + 1);
        if (im > 0) {
          if (dense_op)
            fsarow[e - 1] = im;
          else {
            fsarow[++len] = e;
            fsarow[++len] = im;
          }
          nt++;
        }
      }
    if (!dense_op)
      fsarow[0] = len++;
    fwrite((void *)fsarow, sizeof(int), (size_t)len, tempfile);
  }
  fclose(tempfile);

  ns = compositeptr->states->size = ht.num_recs;
  compositeptr->table->numTransitions = nt;

  if (kbm_print_level >= 3)
    printf("    #Calculated transitions - %d states, %d transitions.\n", ns,
           nt);

  /* Locate the accept states. This is slightly cumbersome, since a state
   * is an accept state if either the corresponding subset contains a
   * a pair (s1,s2), where s1 is and accept state of *mult1ptr and s2 an
   * accept state of *mult2ptr, or we can get from some such state to an
   * accept state by applying elements ( ($,x), (x,$ ).
   * We will need to use the array compositeptr->is_accepting.
   */

  tmalloc(compositeptr->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    compositeptr->is_accepting[i] = FALSE;
  ct = 0;
  es1 = ngens * ngens1 + 1;
  ef1 = ngens1 * ngens1 - 1;
  for (cstate = ns; cstate >= 1; cstate--) {
    /* We work backwards through the states, since we wish to add on additional
     * elements at the end of the list in the hash-table - this destroys
     * later entries, but that doesn't matter, since we have already dealt
     * with them.
     */
    cs_ptr = hash_rec(&ht, cstate);
    reclen = hash_rec_len(&ht, cstate);
    if (reclen % 2 == 1)
      reclen--; /* The last entry marks the fact that this is a "padded state"*/
    cs_ptre = hash_rec(&ht, cstate) + reclen - 1;
    /* First see if the set itself contains an accept-state */
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++);
      csb = *(ptr++);
      if (mult1ptr->is_accepting[csa] && mult2ptr->is_accepting[csb]) {
        compositeptr->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    }
    if (compositeptr->is_accepting[cstate])
      continue;
    /* Next apply generators ( ($,g2), (g2,$) ) and see if we get anything new.
     * We won't bother about having them in increasing order this time.
     */
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++);
      csb = *(ptr++);
      for (e1 = es1, e2 = ngens1; e1 <= ef1; e1++, e2 += ngens1) {
        csima = target(dense_ip1, table1, e1, csa, dr1);
        if (csima == 0)
          continue;
        csimb = target(dense_ip2, table2, e2, csb, dr2);
        if (csimb == 0)
          continue;

        /* see if (csima,csimb) is accepting */
        if (mult1ptr->is_accepting[csima] && mult2ptr->is_accepting[csimb]) {
          compositeptr->is_accepting[cstate] = TRUE;
          ct++;
          break;
        }
        /* now see if it is new */
        ht_chptr = cs_ptr;
        got = FALSE;
        while (ht_chptr < cs_ptre) {
          if (csima == ht_chptr[0] && csimb == ht_chptr[1]) {
            got = TRUE;
            break;
          }
          ht_chptr += 2;
        }
        if (!got) {
          /* add (csima,csimb) to the end */
          *(++cs_ptre) = csima;
          *(++cs_ptre) = csimb;
        }
      }
      if (compositeptr->is_accepting[cstate])
        continue;
    }
  }

  compositeptr->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(compositeptr->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (compositeptr->is_accepting[i])
        compositeptr->accepting[++ct] = i;
  }
  tfree(compositeptr->is_accepting);
  tfree(mult1ptr->is_accepting);
  tfree(mult2ptr->is_accepting);
  hash_clear(&ht);
  tfree(fsarow);
  if (destroy) {
    fsa_clear(mult1ptr);
    fsa_clear(mult2ptr);
  }

  if (readback) {
    tempfile = fopen(compfilename, "r");
    compressed_transitions_read(compositeptr, tempfile);
    fclose(tempfile);
    unlink(compfilename);
  }

  return compositeptr;
}
