/* file fsarevmid.c  18. 4. 96.
 *
 * 16.7.98. added fsa_miexists1, fsa_miexists2 to existentialise over
 * the two variables of a 2-variable midfa machine.
 *
 * 11.9.97. wrote a different version of fsa_reverse
 * called fsa_mireverse which * returns a labeled MIDFA with the
 * singleton accept states of the input fsa as initial states.
 *
 * This file contains the routine fsa_reverse.
 * It  takes a determinstic fsa F as input.
 * fsa_reverse returns an fsa that accepts a word a_1a_2...a_n  if and only
 * if F accepts a_n...a_2a_1.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "externals.h"


/* Functions defined in this file: */
static fsa *fsa_reverse_short(fsa *fsaptr, storage_type op_table_type,
                              boolean destroy, boolean subsets,
                              char *tempfilename);
static fsa *fsa_reverse_int(fsa *fsaptr, storage_type op_table_type,
                            boolean destroy, boolean subsets,
                            char *tempfilename);
static fsa *fsa_mireverse_short(fsa *fsaptr, storage_type op_table_type,
                                boolean destroy, char *tempfilename);
static fsa *fsa_mireverse_int(fsa *fsaptr, storage_type op_table_type,
                              boolean destroy, char *tempfilename);
static fsa *fsa_miexists1_short(fsa *fsaptr, storage_type op_table_type,
                                boolean destroy, char *tempfilename);
static fsa *fsa_miexists1_int(fsa *fsaptr, storage_type op_table_type,
                              boolean destroy, char *tempfilename);
static fsa *fsa_miexists2_short(fsa *fsaptr, storage_type op_table_type,
                                boolean destroy, char *tempfilename);
static fsa *fsa_miexists2_int(fsa *fsaptr, storage_type op_table_type,
                              boolean destroy, char *tempfilename);


/* *fsaptr must be a deterministic fsa.
 * The returned *fsa accepts words accepted by *fsaptr but read
 * backwards.
 * If subsets is true, then the returned fsa will have state-set of type
 * "list of integers", where the list represents the subset of the state-set
 * of *fsaptr that correponds to the state of the returned fsa.
 */
fsa *fsa_reverse(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                 boolean subsets, char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_reverse.\n");
  if (fsaptr->states->size < MAXUSHORT)
    return fsa_reverse_short(fsaptr, op_table_type, destroy, subsets,
                             tempfilename);
  else
    return fsa_reverse_int(fsaptr, op_table_type, destroy, subsets,
                           tempfilename);
}

static fsa *fsa_reverse_short(fsa *fsaptr, storage_type op_table_type,
                              boolean destroy, boolean subsets,
                              char *tempfilename)
{
  int **table, ne, nsi, ns, is, dr, *fsarow, nt, cstate, cs, csi, im, i, g, n,
      len = 0, ct;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  boolean dense_ip, dense_op;
  short_hash_table ht;
  fsa *reverse;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_reverse_short.\n");
  if (!fsaptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_reverse only applies to DFA's.\n");
    return 0;
  }

  tmalloc(reverse, fsa, 1);
  fsa_init(reverse);
  srec_copy(reverse->alphabet, fsaptr->alphabet);
  reverse->flags[DFA] = TRUE;
  reverse->flags[ACCESSIBLE] = TRUE;
  reverse->flags[BFS] = TRUE;

  reverse->states->type = subsets ? LISTOFINTS : SIMPLE;

  reverse->table->table_type = op_table_type;
  reverse->table->denserows = 0;
  reverse->table->printing_format = op_table_type;

  if (fsaptr->num_initial == 0 || fsaptr->num_accepting == 0) {
    reverse->num_initial = 0;
    reverse->num_accepting = 0;
    reverse->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return reverse;
  }
  ne = fsaptr->alphabet->size;
  nsi = fsaptr->states->size;

  dense_ip = fsaptr->table->table_type == DENSE;
  dr = fsaptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  reverse->num_initial = 1;
  tmalloc(reverse->initial, int, 2);
  reverse->initial[1] = 1;

  /* The states of *reverse will be subsets of the state-set of *fsaptr.
   * The initial state consists of all accept states of *fsaptr.
   */
  short_hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptrb = ht.current_ptr;
  ht_ptre = ht_ptrb - 1;
  fsa_set_is_accepting(fsaptr);
  for (i = 1; i <= nsi; i++)
    if (fsaptr->is_accepting[i])
      *(++ht_ptre) = i;
  tfree(fsaptr->is_accepting);
  im = short_hash_locate(&ht, ht_ptre - ht_ptrb + 1);
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_reverse.\n");
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
  nt = 0;     /* Number of transitions in reverse */

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

    for (g = 1; g <= ne; g++) {
      /* Calculate action of label g on state cstate  - to get the image, we
       * have to look for all inverse images under g of all states cs in the
       * subset cstate. The subset formed will be the image.
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      while (++ptr <= cs_ptre) {
        cs = *ptr;
        for (csi = 1; csi <= nsi; csi++)
          if (target(dense_ip, table, g, csi, dr) == cs) {
            /* csi has to be added to the subset of states that forms the image
             * of cstate under g - we want to keep this subset in ascending
             * order.
             */
            if (ht_ptrb > ht_ptre || csi > *ht_ptre) {
              *(++ht_ptre) = csi;
            }
            else {
              ht_chptr = ht_ptrb;
              while (*ht_chptr < csi)
                ht_chptr++;
              if (csi < *ht_chptr) {
                ht_ptr = ++ht_ptre;
                while (ht_ptr > ht_chptr) {
                  *ht_ptr = *(ht_ptr - 1);
                  ht_ptr--;
                }
                *ht_ptr = csi;
              }
            }
          }
      }
      im = short_hash_locate(&ht, ht_ptre - ht_ptrb + 1);
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

  ns = reverse->states->size = ht.num_recs;
  reverse->table->numTransitions = nt;

  /* Locate the accept states. These are those that contain the initial
   * state of *fsaptr.
   * Also, if subsets is true, record the states in the intlist field
   * of reverse->states.
   */
  is = fsaptr->initial[1];
  tmalloc(reverse->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    reverse->is_accepting[i] = FALSE;
  if (subsets)
    tmalloc(reverse->states->intlist, int *, ns + 1);
  ct = 0;
  for (cstate = 1; cstate <= ns; cstate++) {
    len = short_hash_rec_len(&ht, cstate);
    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = cs_ptr + len - 1;
    /* See if the set contains the initial state */
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre)
      if (*ptr == is) {
        reverse->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    if (subsets) {
      tmalloc(reverse->states->intlist[cstate], int, len + 1);
      reverse->states->intlist[cstate][0] = len;
      n = 0;
      ptr = cs_ptr - 1;
      while (++ptr <= cs_ptre)
        reverse->states->intlist[cstate][++n] = *ptr;
    }
  }

  reverse->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(reverse->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (reverse->is_accepting[i])
        reverse->accepting[++ct] = i;
  }
  tfree(reverse->is_accepting);
  short_hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(reverse, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return reverse;
}

fsa *fsa_reverse_int(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                     boolean subsets, char *tempfilename)
{
  fprintf(stderr, "Sorry - fsa_reverse is not yet implemented for machines.\n");
  fprintf(stderr, "with more than 65536 states.\n");
  return 0;
}

/* *fsaptr must be a deterministic fsa.
 * The returned *fsa accepts words accepted by *fsaptr read backwards,
 * and is a labeled MIDFA, with initial states the singleton accept states of
 * *fsaptr.
 */
fsa *fsa_mireverse(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                   char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_mireverse.\n");
  if (fsaptr->states->size < MAXUSHORT)
    return fsa_mireverse_short(fsaptr, op_table_type, destroy, tempfilename);
  else
    return fsa_mireverse_int(fsaptr, op_table_type, destroy, tempfilename);
}

static fsa *fsa_mireverse_short(fsa *fsaptr, storage_type op_table_type,
                                boolean destroy, char *tempfilename)
{
  int **table, ne, nsi, ns, nai, is, dr, *fsarow, nt, cstate, cs, csi, im, i, g,
      len = 0, ct;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  boolean dense_ip, dense_op;
  short_hash_table ht;
  fsa *reverse;
  srec *labs;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_mireverse_short.\n");
  if (!fsaptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_mireverse only applies to DFA's.\n");
    return 0;
  }

  tmalloc(reverse, fsa, 1);
  fsa_init(reverse);
  srec_copy(reverse->alphabet, fsaptr->alphabet);
  reverse->flags[MIDFA] = TRUE;
  reverse->flags[ACCESSIBLE] = TRUE;

  ne = fsaptr->alphabet->size;
  nsi = fsaptr->states->size;

  /* set up the labels for the states of reverse */
  reverse->states->type = LABELED;
  tmalloc(reverse->states->labels, srec, 1);
  labs = reverse->states->labels;
  nai = fsaptr->num_accepting;
  labs->size = nai + 2;
  labs->type = LISTOFINTS;
  /* The labels will be [i] for all initial states i of fsa,
   * [0] for other accepting states of reverse, and [] for other states.
   */
  tmalloc(labs->intlist, int *, nai + 3);
  for (i = 1; i <= nai; i++) {
    tmalloc(labs->intlist[i], int, 2);
    labs->intlist[i][0] = 1;
    labs->intlist[i][1] = nsi == nai ? i : fsaptr->accepting[i];
  }
  tmalloc(labs->intlist[nai + 1], int, 2);
  labs->intlist[nai + 1][0] = 1;
  labs->intlist[nai + 1][1] = 0;
  tmalloc(labs->intlist[nai + 2], int, 1);
  labs->intlist[nai + 2][0] = 0;

  reverse->table->table_type = op_table_type;
  reverse->table->denserows = 0;
  reverse->table->printing_format = op_table_type;

  if (fsaptr->num_initial == 0 || fsaptr->num_accepting == 0) {
    reverse->num_initial = 0;
    reverse->num_accepting = 0;
    reverse->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return reverse;
  }

  dense_ip = fsaptr->table->table_type == DENSE;
  dr = fsaptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  reverse->num_initial = nai;
  tmalloc(reverse->initial, int, nai + 1);
  for (i = 1; i <= nai; i++)
    reverse->initial[i] = i;

  /* The states of *reverse will be subsets of the state-set of *fsaptr.
   * The initial states consists of all singleton accept states of *fsaptr.
   */
  short_hash_init(&ht, FALSE, 0, 0, 0);
  for (i = 1; i <= nai; i++) {
    ht_ptrb = ht.current_ptr;
    *ht_ptrb = nsi == nai ? i : fsaptr->accepting[i];
    im = short_hash_locate(&ht, 1);
    if (im != i) {
      fprintf(stderr, "Hash-initialisation problem in fsa_reverse.\n");
      return 0;
    }
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
  nt = 0;     /* Number of transitions in reverse */

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

    for (g = 1; g <= ne; g++) {
      /* Calculate action of label g on state cstate  - to get the image, we
       * have to look for all inverse images under g of all states cs in the
       * subset cstate. The subset formed will be the image.
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      while (++ptr <= cs_ptre) {
        cs = *ptr;
        for (csi = 1; csi <= nsi; csi++)
          if (target(dense_ip, table, g, csi, dr) == cs) {
            /* csi has to be added to the subset of states that forms the image
             * of cstate under g - we want to keep this subset in ascending
             * order.
             */
            if (ht_ptrb > ht_ptre || csi > *ht_ptre) {
              *(++ht_ptre) = csi;
            }
            else {
              ht_chptr = ht_ptrb;
              while (*ht_chptr < csi)
                ht_chptr++;
              if (csi < *ht_chptr) {
                ht_ptr = ++ht_ptre;
                while (ht_ptr > ht_chptr) {
                  *ht_ptr = *(ht_ptr - 1);
                  ht_ptr--;
                }
                *ht_ptr = csi;
              }
            }
          }
      }
      im = short_hash_locate(&ht, ht_ptre - ht_ptrb + 1);
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

  ns = reverse->states->size = ht.num_recs;
  reverse->table->numTransitions = nt;

  /* Initialize the state setToLabels ptr.
   * Then locate the accept states. These are those that contain the initial
   * state of *fsaptr.
   */
  tmalloc(reverse->states->setToLabels, setToLabelsType, ns + 1);
  for (i = 1; i <= nai; i++)
    reverse->states->setToLabels[i] = i;

  is = fsaptr->initial[1];
  tmalloc(reverse->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    reverse->is_accepting[i] = FALSE;
  ct = 0;
  for (cstate = 1; cstate <= ns; cstate++) {
    len = short_hash_rec_len(&ht, cstate);
    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = cs_ptr + len - 1;
    /* See if the set contains the initial state */
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre)
      if (*ptr == is) {
        reverse->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    if (cstate > nai)
      reverse->states->setToLabels[cstate] =
          reverse->is_accepting[cstate] ? nai + 1 : nai + 2;
  }

  reverse->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(reverse->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (reverse->is_accepting[i])
        reverse->accepting[++ct] = i;
  }
  tfree(reverse->is_accepting);
  short_hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(reverse, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return reverse;
}

static fsa *fsa_mireverse_int(fsa *fsaptr, storage_type op_table_type,
                              boolean destroy, char *tempfilename)
{
  fprintf(stderr,
          "Sorry - fsa_mireverse is not yet implemented for machines.\n");
  fprintf(stderr, "with more than 65536 states.\n");
  return 0;
}

/* *fsaptr must be a 2-variable MIDFA fsa.
 * The returned midfa accepts a word w_1 iff (w_1,w_2) is accepted by *fsaptr,
 * for some word w_2 - but here the padding symbol is part of the
 * alphabet of the output midfa.
 * In fact, fsa_miexists1 calls fsa_miexists1_int or (more usually)
 * fsa_miexists1_short, the latter using the short hash table functions.
 */
fsa *fsa_miexists1(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                   char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_miexists1.\n");
  if (fsaptr->states->size < MAXUSHORT)
    return fsa_miexists1_short(fsaptr, op_table_type, destroy, tempfilename);
  else
    return fsa_miexists1_int(fsaptr, op_table_type, destroy, tempfilename);
}

static fsa *fsa_miexists1_short(fsa *fsaptr, storage_type op_table_type,
                                boolean destroy, char *tempfilename)
{
  int **table, ne, ngens, ns, nsi, dr, *fsarow, e, es, ef, nt, cstate, cs, csi,
      im, i, g1, len = 0, ct, ni;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  boolean dense_ip, dense_op;
  short_hash_table ht;
  fsa *miexists1;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_miexists1_short.\n");
  if (!fsaptr->flags[MIDFA]) {
    fprintf(stderr, "Error: fsa_miexists1 only applies to MIDFA's.\n");
    exit(1);
  }

  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_miexists1: fsa must be 2-variable.\n");
    exit(1);
  }

  tmalloc(miexists1, fsa, 1);
  fsa_init(miexists1);
  nsi = fsaptr->states->size;
  ne = fsaptr->alphabet->size;
  ngens = fsaptr->alphabet->base->size;

  if (ne != (ngens + 1) * (ngens + 1) - 1) {
    fprintf(stderr, "Error: in a 2-variable fsa, alphabet size should = "
                    "(ngens+1)^2 - 1.\n");
    exit(1);
  }
  /* alphabet will include padding symbol */
  miexists1->alphabet->type = IDENTIFIERS;
  miexists1->alphabet->size = ngens + 1;
  tmalloc(miexists1->alphabet->names, char *, ngens + 2);
  for (i = 1; i <= ngens; i++) {
    tmalloc(miexists1->alphabet->names[i], char,
            stringlen(fsaptr->alphabet->base->names[i]) + 1);
    strcpy(miexists1->alphabet->names[i], fsaptr->alphabet->base->names[i]);
  }
  tmalloc(miexists1->alphabet->names[ngens + 1], char, 2);
  miexists1->alphabet->names[ngens + 1][0] = fsaptr->alphabet->padding;
  miexists1->alphabet->names[ngens + 1][1] = '\0';
  miexists1->flags[MIDFA] = TRUE;
  miexists1->flags[ACCESSIBLE] = TRUE;

  miexists1->states->type = LABELED;
  tmalloc(miexists1->states->labels, srec, 1);
  srec_copy(miexists1->states->labels, fsaptr->states->labels);

  miexists1->table->table_type = op_table_type;
  miexists1->table->denserows = 0;
  miexists1->table->printing_format = op_table_type;

  if (fsaptr->num_initial == 0 || fsaptr->num_accepting == 0) {
    miexists1->num_initial = 0;
    miexists1->num_accepting = 0;
    miexists1->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return miexists1;
  }

  fsa_set_is_accepting(fsaptr);

  dense_ip = fsaptr->table->table_type == DENSE;
  dr = fsaptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  ni = fsaptr->num_initial;
  miexists1->num_initial = ni;
  tmalloc(miexists1->initial, int, ni + 1);
  for (i = 1; i <= ni; i++)
    miexists1->initial[i] = i;

  short_hash_init(&ht, FALSE, 0, 0, 0);
  for (i = 1; i <= ni; i++) {
    ht_ptrb = ht.current_ptr;
    *ht_ptrb = nsi == ni ? i : fsaptr->initial[i];
    im = short_hash_locate(&ht, 1);
    if (im != i) {
      fprintf(stderr, "Hash-initialisation problem in fsa_miexists.\n");
      exit(1);
    }
  }
  /* Each state in 'miexists1' will be represented as a subset of the states
   * of *fsaptr. The initial states are  one-element set containing the initial
   * states of *fsaptr. A subset is an accept-state if it contains an accept
   * state of *fsaptr.
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if ((tempfile = fopen(tempfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", tempfilename);
    exit(1);
  }
  if (dense_op)
    tmalloc(fsarow, int, ngens) else tmalloc(fsarow, int, 2 * ngens + 1)

        cstate = 0;
  if (dense_op)
    len = ngens + 1; /* The length of the fsarow output. */
  nt = 0;            /* Number of transitions in miexists1 */

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

    for (g1 = 1; g1 <= ngens + 1; g1++) {
      /* Calculate action of generator g1 on state cstate  - to get the image,
       * we have to apply (g1,g2) to each element in the subset corresponding to
       * cstate, and this for each generator g2 of the base-alphabet (including
       * the padding symbol).
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      es = (g1 - 1) * (ngens + 1) + 1;
      ef = g1 == ngens + 1 ? g1 * (ngens + 1) - 1 : g1 * (ngens + 1);
      /* As g2 ranges from 1 to ngens+1 in the pair (g1,g2), for fixed g1, the
       * corresponding edge number in the fsa ranges from es to ef.
       */
      while (++ptr <= cs_ptre) {
        cs = *ptr;
        for (e = es; e <= ef; e++) {
          csi = target(dense_ip, table, e, cs, dr);
          if (csi == 0)
            continue;
          if (ht_ptrb > ht_ptre || csi > *ht_ptre) {
            /* We have a new state for the image subset to be added to the end
             */
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
      }
      im = short_hash_locate(&ht, ht_ptre - ht_ptrb + 1);
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

  ns = miexists1->states->size = ht.num_recs;
  miexists1->table->numTransitions = nt;

  /* Locate the initial and accept states, and assign labels.
   * A state is an accept state if the
   * corresponding subset contains an accept state of *fsaptr.
   * We will need to use the array miexists1->is_accepting.
   */
  tmalloc(miexists1->states->setToLabels, setToLabelsType, ns + 1);
  for (i = 1; i <= ni; i++)
    miexists1->states->setToLabels[i] =
        fsaptr->states->setToLabels[fsaptr->initial[i]];
  tmalloc(miexists1->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    miexists1->is_accepting[i] = FALSE;
  ct = 0;
  for (cstate = ns; cstate >= 1; cstate--) {
    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = short_hash_rec(&ht, cstate) + short_hash_rec_len(&ht, cstate) - 1;
    /* See if the set an accept-state */
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre)
      if (fsaptr->is_accepting[*ptr]) {
        miexists1->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    if (cstate > ni)
      miexists1->states->setToLabels[cstate] =
          miexists1->is_accepting[cstate] ? ni + 1 : ni + 2;
  }

  miexists1->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(miexists1->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (miexists1->is_accepting[i])
        miexists1->accepting[++ct] = i;
  }
  tfree(fsaptr->is_accepting);
  tfree(miexists1->is_accepting);
  short_hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(miexists1, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return miexists1;
}

static fsa *fsa_miexists1_int(fsa *fsaptr, storage_type op_table_type,
                              boolean destroy, char *tempfilename)
{
  fprintf(stderr,
          "Sorry - fsa_miexists1 is not yet implemented for machines.\n");
  fprintf(stderr, "with more than 65536 states.\n");
  exit(1);
}

/* *fsaptr must be a 2-variable MIDFA fsa.
 * The returned midfa accepts a word w_1 iff (w_1,w_2) is accepted by *fsaptr,
 * for some word w_2 - but here the padding symbol is part of the
 * alphabet of the output midfa.
 * In fact, fsa_miexists2 calls fsa_miexists2_int or (more usually)
 * fsa_miexists2_short, the latter using the short hash table functions.
 */
fsa *fsa_miexists2(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                   char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_miexists2.\n");
  if (fsaptr->states->size < MAXUSHORT)
    return fsa_miexists2_short(fsaptr, op_table_type, destroy, tempfilename);
  else
    return fsa_miexists2_int(fsaptr, op_table_type, destroy, tempfilename);
}

static fsa *fsa_miexists2_short(fsa *fsaptr, storage_type op_table_type,
                                boolean destroy, char *tempfilename)
{
  int **table, ne, ngens, ngens1, ns, nsi, dr, *fsarow, e, es, ef, nt, cstate,
      cs, csi, im, i, g2, len = 0, ct, ni;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  boolean dense_ip, dense_op;
  short_hash_table ht;
  fsa *miexists2;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_miexists2_short.\n");
  if (!fsaptr->flags[MIDFA]) {
    fprintf(stderr, "Error: fsa_miexists2 only applies to MIDFA's.\n");
    exit(1);
  }

  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_miexists2: fsa must be 2-variable.\n");
    exit(1);
  }

  tmalloc(miexists2, fsa, 1);
  fsa_init(miexists2);
  nsi = fsaptr->states->size;
  ne = fsaptr->alphabet->size;
  ngens = fsaptr->alphabet->base->size;
  ngens1 = ngens + 1;

  if (ne != ngens1 * ngens1 - 1) {
    fprintf(stderr, "Error: in a 2-variable fsa, alphabet size should = "
                    "(ngens+1)^2 - 1.\n");
    exit(1);
  }
  /* alphabet will include padding symbol */
  miexists2->alphabet->type = IDENTIFIERS;
  miexists2->alphabet->size = ngens1;
  tmalloc(miexists2->alphabet->names, char *, ngens + 2);
  for (i = 1; i <= ngens; i++) {
    tmalloc(miexists2->alphabet->names[i], char,
            stringlen(fsaptr->alphabet->base->names[i]) + 1);
    strcpy(miexists2->alphabet->names[i], fsaptr->alphabet->base->names[i]);
  }
  tmalloc(miexists2->alphabet->names[ngens1], char, 2);
  miexists2->alphabet->names[ngens1][0] = fsaptr->alphabet->padding;
  miexists2->alphabet->names[ngens1][1] = '\0';
  miexists2->flags[MIDFA] = TRUE;
  miexists2->flags[ACCESSIBLE] = TRUE;

  miexists2->states->type = LABELED;
  tmalloc(miexists2->states->labels, srec, 1);
  srec_copy(miexists2->states->labels, fsaptr->states->labels);

  miexists2->table->table_type = op_table_type;
  miexists2->table->denserows = 0;
  miexists2->table->printing_format = op_table_type;

  if (fsaptr->num_initial == 0 || fsaptr->num_accepting == 0) {
    miexists2->num_initial = 0;
    miexists2->num_accepting = 0;
    miexists2->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return miexists2;
  }

  fsa_set_is_accepting(fsaptr);

  dense_ip = fsaptr->table->table_type == DENSE;
  dr = fsaptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  ni = fsaptr->num_initial;
  miexists2->num_initial = ni;
  tmalloc(miexists2->initial, int, ni + 1);
  for (i = 1; i <= ni; i++)
    miexists2->initial[i] = i;

  short_hash_init(&ht, FALSE, 0, 0, 0);
  for (i = 1; i <= ni; i++) {
    ht_ptrb = ht.current_ptr;
    *ht_ptrb = nsi == ni ? i : fsaptr->initial[i];
    im = short_hash_locate(&ht, 1);
    if (im != i) {
      fprintf(stderr, "Hash-initialisation problem in fsa_miexists.\n");
      exit(1);
    }
  }
  /* Each state in 'miexists2' will be represented as a subset of the states
   * of *fsaptr. The initial states are  one-element set containing the initial
   * states of *fsaptr. A subset is an accept-state if it contains an accept
   * state of *fsaptr.
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if ((tempfile = fopen(tempfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", tempfilename);
    exit(1);
  }
  if (dense_op)
    tmalloc(fsarow, int, ngens) else tmalloc(fsarow, int, 2 * ngens1)

        cstate = 0;
  if (dense_op)
    len = ngens1; /* The length of the fsarow output. */
  nt = 0;         /* Number of transitions in miexists2 */

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

    for (g2 = 1; g2 <= ngens1; g2++) {
      /* Calculate action of generator g2 on state cstate  - to get the image,
       * we have to apply (g1,g2) to each element in the subset corresponding to
       * cstate, and this for each generator g1 of the base-alphabet (including
       * the padding symbol).
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      es = g2;
      ef = g2 == ngens1 ? ngens * ngens + g2 : ngens * ngens1 + g2;
      /* As g2 ranges from 1 to ngens+1 in the pair (g2,g2), for fixed g2, the
       * corresponding edge number in the fsa ranges from es to ef.
       */
      while (++ptr <= cs_ptre) {
        cs = *ptr;
        for (e = es; e <= ef; e += ngens1) {
          csi = target(dense_ip, table, e, cs, dr);
          if (csi == 0)
            continue;
          if (ht_ptrb > ht_ptre || csi > *ht_ptre) {
            /* We have a new state for the image subset to be added to the end
             */
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
      }
      im = short_hash_locate(&ht, ht_ptre - ht_ptrb + 1);
      if (dense_op)
        fsarow[g2 - 1] = im;
      else if (im > 0) {
        fsarow[++len] = g2;
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

  ns = miexists2->states->size = ht.num_recs;
  miexists2->table->numTransitions = nt;

  /* Locate the initial and accept states, and assign labels.
   * A state is an accept state if the
   * corresponding subset contains an accept state of *fsaptr.
   * We will need to use the array miexists2->is_accepting.
   */
  tmalloc(miexists2->states->setToLabels, setToLabelsType, ns + 1);
  for (i = 1; i <= ni; i++)
    miexists2->states->setToLabels[i] =
        fsaptr->states->setToLabels[fsaptr->initial[i]];
  tmalloc(miexists2->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    miexists2->is_accepting[i] = FALSE;
  ct = 0;
  for (cstate = ns; cstate >= 1; cstate--) {
    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = short_hash_rec(&ht, cstate) + short_hash_rec_len(&ht, cstate) - 1;
    /* See if the set an accept-state */
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre)
      if (fsaptr->is_accepting[*ptr]) {
        miexists2->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    if (cstate > ni)
      miexists2->states->setToLabels[cstate] =
          miexists2->is_accepting[cstate] ? ni + 1 : ni + 2;
  }

  miexists2->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(miexists2->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (miexists2->is_accepting[i])
        miexists2->accepting[++ct] = i;
  }
  tfree(fsaptr->is_accepting);
  tfree(miexists2->is_accepting);
  short_hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(miexists2, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return miexists2;
}

static fsa *fsa_miexists2_int(fsa *fsaptr, storage_type op_table_type,
                              boolean destroy, char *tempfilename)
{
  fprintf(stderr,
          "Sorry - fsa_miexists2 is not yet implemented for machines.\n");
  fprintf(stderr, "with more than 65536 states.\n");
  exit(1);
}
