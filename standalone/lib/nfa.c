/* file nfa.c  8.9.97.
 *
 * 25/9/98 added parameter subsets to nfa_determinize.
 * 2/10/97 - added version of nfa_determinize for compactly stored
 * transition tables.
 * This file contains routines for processing nfa's i.e. non-deterministic
 * finite state automata.
 * Currently, the only routine available is nfa_determinize, which returns
 * an equivalent deterministic automaton, whose states are subsets of the
 * input fsa.
 * Currently, the only input format accepted is sparse, where epsilon
 * transitions are from generator 0.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "externals.h"
/* the following three definitions are for use in extracting edge-label
 * and state in compactly stored pairs.
 */
#define SHIFT 24
#define MASKR (unsigned)0xffffff
#define MASKL (unsigned)0xff000000

/* Functions defined in this file: */
static fsa *nfa_determinize_short(fsa *fsaptr, storage_type op_table_type,
                                  boolean eps_trans, boolean destroy,
                                  boolean subsets, char *tempfilename);
static fsa *nfa_determinize_int(fsa *fsaptr, storage_type op_table_type,
                                boolean eps_trans, boolean destroy,
                                boolean subsets, char *tempfilename);
static fsa *nfa_cdeterminize_short(fsa *fsaptr, storage_type op_table_type,
                                   boolean destroy, char *tempfilename);
static fsa *nfa_cdeterminize_int(fsa *fsaptr, storage_type op_table_type,
                                 boolean destroy, char *tempfilename);
static fsa *nfa_exists_short(fsa *fsaptr, storage_type op_table_type,
                             boolean destroy, char *tempfilename);
static fsa *nfa_exists_int(fsa *fsaptr, storage_type op_table_type,
                           boolean destroy, char *tempfilename);


/* The fsa *fsaptr must be an fsa with sparse table.
 * The returned fsa accepts the same language but is deterministic.
 * If eps_trans is false, it is assumed that *fsaptr has no epsilon
 * transitions.
 * If subsets is true, then the returned fsa will have state-set of type
 * "list of integers", where the list represents the subset of the state-set
 * of *fsaptr that correponds to the state of the returned fsa.
 */
fsa *nfa_determinize(fsa *fsaptr, storage_type op_table_type, boolean eps_trans,
                     boolean destroy, boolean subsets, char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling nfa_determinize.\n");
  if (fsaptr->states->size < MAXUSHORT)
    return nfa_determinize_short(fsaptr, op_table_type, eps_trans, destroy,
                                 subsets, tempfilename);
  else
    return nfa_determinize_int(fsaptr, op_table_type, eps_trans, destroy,
                               subsets, tempfilename);
}

static fsa *nfa_determinize_short(fsa *fsaptr, storage_type op_table_type,
                                  boolean eps_trans, boolean destroy,
                                  boolean subsets, char *tempfilename)
{
  int **table, *tableptr, *tableptre, ngens, nssi, ns, *fsarow, nt, cstate, csi,
      im, i, g1, len = 0, ct, n;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  boolean dense_op;
  short_hash_table ht;
  fsa *det;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling nfa_determinize_short.\n");

  tmalloc(det, fsa, 1);
  fsa_init(det);
  srec_copy(det->alphabet, fsaptr->alphabet);
  det->flags[DFA] = TRUE;
  det->flags[ACCESSIBLE] = TRUE;
  det->flags[BFS] = TRUE;

  det->states->type = subsets ? LISTOFINTS : SIMPLE;

  det->table->table_type = op_table_type;
  det->table->denserows = 0;
  det->table->printing_format = op_table_type;

  if (fsaptr->num_initial == 0) {
    det->num_initial = 0;
    det->num_accepting = 0;
    det->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return det;
  }
  ngens = det->alphabet->size;

  fsa_set_is_accepting(fsaptr);

  dense_op = op_table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  det->num_initial = 1;
  tmalloc(det->initial, int, 2);
  det->initial[1] = 1;

  short_hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptrb = ht.current_ptr;
  ht_ptre = ht_ptrb - 1;
  nssi = fsaptr->num_initial;
  for (i = 0; i < nssi; i++)
    *(++ht_ptre) = fsaptr->initial[i + 1];
  /* now perform epsilon closure of initial subset */
  ptr = ht_ptrb - 1;
  if (eps_trans)
    while (++ptr <= ht_ptre) {
      tableptr = table[*ptr];
      tableptre = table[*ptr + 1];
      while (tableptr < tableptre) {
        if (*tableptr == 0) {
          csi = *(tableptr + 1);
          if (csi == 0) {
            tableptr += 2;
            continue;
          }
          if (csi > *ht_ptre) {
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
              if (ptr > ht_ptr)
                ptr = ht_ptr - 1;
            }
          }
        }
        tableptr += 2;
      }
    }
  im = short_hash_locate(&ht, ht_ptre - ht_ptrb + 1);
  /* Each state in 'det' will be represented as a subset of the set of states
   * of *fsaptr. The initial state contains the initial states
   * of *fsaptr.
   * A subset is an accept-state if it contains an accept state of *fsaptr
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in nfa_determinize.\n");
    return 0;
  }
  if ((tempfile = fopen(tempfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow, int, ngens) else tmalloc(fsarow, int, 2 * ngens + 1)

        cstate = 0;
  if (dense_op)
    len = ngens; /* The length of the fsarow output. */
  nt = 0;        /* Number of transitions in det */

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

    for (g1 = 1; g1 <= ngens; g1++) {
      /* Calculate action of generator g1 on state cstate  - to get the image,
       * we simply apply it to each state in the subset of states representing
       * cstate.
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      while (++ptr <= cs_ptre) {
        tableptr = table[*ptr];
        tableptre = table[*ptr + 1];
        while (tableptr < tableptre) {
          if (*tableptr == g1) {
            csi = *(tableptr + 1);
            if (csi == 0) {
              tableptr += 2;
              continue;
            }
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
          tableptr += 2;
        }
      }
      /* now perform epsilon closure of image subset */
      ptr = ht_ptrb - 1;
      if (eps_trans)
        while (++ptr <= ht_ptre) {
          tableptr = table[*ptr];
          tableptre = table[*ptr + 1];
          while (tableptr < tableptre) {
            if (*tableptr == 0) {
              csi = *(tableptr + 1);
              if (csi == 0) {
                tableptr += 2;
                continue;
              }
              if (csi > *ht_ptre) {
                /* We have a new state for the image subset to be added to the
                 * end */
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
                  if (ptr > ht_ptr)
                    ptr = ht_ptr - 1;
                }
              }
            }
            tableptr += 2;
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

  ns = det->states->size = ht.num_recs;
  det->table->numTransitions = nt;

  /* Locate the accept states. A state is an accept state if and only if
   * the subset representing it contains an accept state of *fsaptr.
   * Also, if subsets is true, record the states in the intlist field
   * of det->states.
   */
  tmalloc(det->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    det->is_accepting[i] = FALSE;
  if (subsets)
    tmalloc(det->states->intlist, int *, ns + 1);
  ct = 0;
  for (cstate = 1; cstate <= ns; cstate++) {
    len = short_hash_rec_len(&ht, cstate);
    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = short_hash_rec(&ht, cstate) + len - 1;
    /* See if the set contains an accept-state */
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre)
      if (fsaptr->is_accepting[*ptr]) {
        det->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    if (subsets) {
      tmalloc(det->states->intlist[cstate], int, len + 1);
      det->states->intlist[cstate][0] = len;
      n = 0;
      ptr = cs_ptr - 1;
      while (++ptr <= cs_ptre)
        det->states->intlist[cstate][++n] = *ptr;
    }
  }

  det->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(det->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (det->is_accepting[i])
        det->accepting[++ct] = i;
  }
  tfree(fsaptr->is_accepting);
  tfree(det->is_accepting);
  short_hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(det, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return det;
}

static fsa *nfa_determinize_int(fsa *fsaptr, storage_type op_table_type,
                                boolean eps_trans, boolean destroy,
                                boolean subsets, char *tempfilename)
{
  int **table, *tableptr, *tableptre, ngens, nssi, ns, *fsarow, nt, cstate, csi,
      im, i, g1, len = 0, ct, n;
  int *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre, *ptr;
  boolean dense_op;
  hash_table ht;
  fsa *det;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling nfa_determinize_int.\n");

  tmalloc(det, fsa, 1);
  fsa_init(det);
  srec_copy(det->alphabet, fsaptr->alphabet);
  det->flags[DFA] = TRUE;
  det->flags[ACCESSIBLE] = TRUE;
  det->flags[BFS] = TRUE;

  det->states->type = subsets ? LISTOFINTS : SIMPLE;

  det->table->table_type = op_table_type;
  det->table->denserows = 0;
  det->table->printing_format = op_table_type;

  if (fsaptr->num_initial == 0) {
    det->num_initial = 0;
    det->num_accepting = 0;
    det->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return det;
  }
  ngens = det->alphabet->size;

  fsa_set_is_accepting(fsaptr);

  dense_op = op_table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  det->num_initial = 1;
  tmalloc(det->initial, int, 2);
  det->initial[1] = 1;

  hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptrb = ht.current_ptr;
  ht_ptre = ht_ptrb - 1;
  nssi = fsaptr->num_initial;
  for (i = 0; i < nssi; i++)
    *(++ht_ptre) = fsaptr->initial[i + 1];
  /* now perform epsilon closure of initial subset */
  ptr = ht_ptrb - 1;
  if (eps_trans)
    while (++ptr <= ht_ptre) {
      tableptr = table[*ptr];
      tableptre = table[*ptr + 1];
      while (tableptr < tableptre) {
        if (*tableptr == 0) {
          csi = *(tableptr + 1);
          if (csi == 0) {
            tableptr += 2;
            continue;
          }
          if (csi > *ht_ptre) {
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
              if (ptr > ht_ptr)
                ptr = ht_ptr - 1;
            }
          }
        }
        tableptr += 2;
      }
    }
  im = hash_locate(&ht, ht_ptre - ht_ptrb + 1);
  /* Each state in 'det' will be represented as a subset of the set of states
   * of *fsaptr. The initial state contains the initial states
   * of *fsaptr.
   * A subset is an accept-state if it contains an accept state of *fsaptr
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in nfa_determinize.\n");
    return 0;
  }
  if ((tempfile = fopen(tempfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow, int, ngens) else tmalloc(fsarow, int, 2 * ngens + 1)

        cstate = 0;
  if (dense_op)
    len = ngens; /* The length of the fsarow output. */
  nt = 0;        /* Number of transitions in det */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    cs_ptr = hash_rec(&ht, cstate);
    cs_ptre = hash_rec(&ht, cstate) + hash_rec_len(&ht, cstate) - 1;
    if (!dense_op)
      len = 0;

    for (g1 = 1; g1 <= ngens; g1++) {
      /* Calculate action of generator g1 on state cstate  - to get the image,
       * we simply apply it to each state in the subset of states representing
       * cstate.
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      while (++ptr <= cs_ptre) {
        tableptr = table[*ptr];
        tableptre = table[*ptr + 1];
        while (tableptr < tableptre) {
          if (*tableptr == g1) {
            csi = *(tableptr + 1);
            if (csi == 0) {
              tableptr += 2;
              continue;
            }
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
          tableptr += 2;
        }
      }
      /* now perform epsilon closure of image subset */
      ptr = ht_ptrb - 1;
      if (eps_trans)
        while (++ptr <= ht_ptre) {
          tableptr = table[*ptr];
          tableptre = table[*ptr + 1];
          while (tableptr < tableptre) {
            if (*tableptr == 0) {
              csi = *(tableptr + 1);
              if (csi == 0) {
                tableptr += 2;
                continue;
              }
              if (csi > *ht_ptre) {
                /* We have a new state for the image subset to be added to the
                 * end */
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
                  if (ptr > ht_ptr)
                    ptr = ht_ptr - 1;
                }
              }
            }
            tableptr += 2;
          }
        }
      im = hash_locate(&ht, ht_ptre - ht_ptrb + 1);
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

  /* Locate the accept states. A state is an accept state if and only if
   * the subset representing it contains an accept state of *fsaptr.
   * Also, if subsets is true, record the states in the intlist field
   * of det->states.
   */
  tmalloc(det->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    det->is_accepting[i] = FALSE;
  if (subsets)
    tmalloc(det->states->intlist, int *, ns + 1);
  ct = 0;
  for (cstate = 1; cstate <= ns; cstate++) {
    len = hash_rec_len(&ht, cstate);
    cs_ptr = hash_rec(&ht, cstate);
    cs_ptre = hash_rec(&ht, cstate) + len - 1;
    /* See if the set contains an accept-state */
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre)
      if (fsaptr->is_accepting[*ptr]) {
        det->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    if (subsets) {
      tmalloc(det->states->intlist[cstate], int, len + 1);
      det->states->intlist[cstate][0] = len;
      n = 0;
      ptr = cs_ptr - 1;
      while (++ptr <= cs_ptre)
        det->states->intlist[cstate][++n] = *ptr;
    }
  }

  det->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(det->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (det->is_accepting[i])
        det->accepting[++ct] = i;
  }
  tfree(fsaptr->is_accepting);
  tfree(det->is_accepting);
  hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(det, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return det;
}

/* Version of nfa_determinize for transtition tables stored compactly.
 * FOR THE MOMENT WE ASSUME NO EPSILON TRANSITIONS
 * The fsa *fsaptr must be an fsa with compact table.
 * The returned fsa accepts the same language but is deterministic.
 */
fsa *nfa_cdeterminize(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                      char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling nfa_determinize.\n");
  if (fsaptr->states->size < MAXUSHORT)
    return nfa_cdeterminize_short(fsaptr, op_table_type, destroy, tempfilename);
  else
    return nfa_cdeterminize_int(fsaptr, op_table_type, destroy, tempfilename);
}

static fsa *nfa_cdeterminize_short(fsa *fsaptr, storage_type op_table_type,
                                   boolean destroy, char *tempfilename)
{
  int ngens, nssi, ns, *fsarow, nt, cstate, csi, im, i, g1, len = 0, ct;
  unsigned int **table, *tableptr, *tableptre, g1shift;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  boolean dense_op;
  short_hash_table ht;
  fsa *det;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling nfa_determinize_short.\n");

  tmalloc(det, fsa, 1);
  fsa_init(det);
  srec_copy(det->alphabet, fsaptr->alphabet);
  det->flags[DFA] = TRUE;
  det->flags[ACCESSIBLE] = TRUE;
  det->flags[BFS] = TRUE;

  det->states->type = SIMPLE;

  det->table->table_type = op_table_type;
  det->table->denserows = 0;
  det->table->printing_format = op_table_type;

  if (fsaptr->num_initial == 0) {
    det->num_initial = 0;
    det->num_accepting = 0;
    det->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return det;
  }
  ngens = det->alphabet->size;

  fsa_set_is_accepting(fsaptr);

  dense_op = op_table_type == DENSE;
  table = fsaptr->table->ctable_data_ptr;

  det->num_initial = 1;
  tmalloc(det->initial, int, 2);
  det->initial[1] = 1;

  short_hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptrb = ht.current_ptr;
  ht_ptre = ht_ptrb - 1;
  nssi = fsaptr->num_initial;
  for (i = 0; i < nssi; i++)
    *(++ht_ptre) = fsaptr->initial[i + 1];
  im = short_hash_locate(&ht, ht_ptre - ht_ptrb + 1);
  /* Each state in 'det' will be represented as a subset of the set of states
   * of *fsaptr. The initial state contains the initial states
   * of *fsaptr.
   * A subset is an accept-state if it contains an accept state of *fsaptr
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in nfa_determinize.\n");
    return 0;
  }
  if ((tempfile = fopen(tempfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow, int, ngens) else tmalloc(fsarow, int, 2 * ngens + 1)

        cstate = 0;
  if (dense_op)
    len = ngens; /* The length of the fsarow output. */
  nt = 0;        /* Number of transitions in det */

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

    for (g1 = 1; g1 <= ngens; g1++) {
      /* Calculate action of generator g1 on state cstate  - to get the image,
       * we simply apply it to each state in the subset of states representing
       * cstate.
       */
      g1shift = ((unsigned)g1) << SHIFT;
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      while (++ptr <= cs_ptre) {
        tableptr = table[*ptr];
        tableptre = table[*ptr + 1];
        while (tableptr < tableptre) {
          if ((*tableptr & MASKL) == g1shift) {
            csi = *tableptr & MASKR;
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
          tableptr++;
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

  ns = det->states->size = ht.num_recs;
  det->table->numTransitions = nt;

  /* Locate the accept states. A state is an accept state if and only if
   * the subset representing it contains an accept state of *fsaptr.
   */
  tmalloc(det->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    det->is_accepting[i] = FALSE;
  ct = 0;
  for (cstate = 1; cstate <= ns; cstate++) {
    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = short_hash_rec(&ht, cstate) + short_hash_rec_len(&ht, cstate) - 1;
    /* See if the set contains an accept-state */
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre)
      if (fsaptr->is_accepting[*ptr]) {
        det->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
  }

  det->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(det->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (det->is_accepting[i])
        det->accepting[++ct] = i;
  }
  tfree(fsaptr->is_accepting);
  tfree(det->is_accepting);
  short_hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(det, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return det;
}

static fsa *nfa_cdeterminize_int(fsa *fsaptr, storage_type op_table_type,
                                 boolean destroy, char *tempfilename)
{
  int ngens, nssi, ns, *fsarow, nt, cstate, csi, im, i, g1, len = 0, ct;
  unsigned int **table, *tableptr, *tableptre, g1shift;
  int *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre, *ptr;
  boolean dense_op;
  hash_table ht;
  fsa *det;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling nfa_determinize_short.\n");

  tmalloc(det, fsa, 1);
  fsa_init(det);
  srec_copy(det->alphabet, fsaptr->alphabet);
  det->flags[DFA] = TRUE;
  det->flags[ACCESSIBLE] = TRUE;
  det->flags[BFS] = TRUE;

  det->states->type = SIMPLE;

  det->table->table_type = op_table_type;
  det->table->denserows = 0;
  det->table->printing_format = op_table_type;

  if (fsaptr->num_initial == 0) {
    det->num_initial = 0;
    det->num_accepting = 0;
    det->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return det;
  }
  ngens = det->alphabet->size;

  fsa_set_is_accepting(fsaptr);

  dense_op = op_table_type == DENSE;
  table = fsaptr->table->ctable_data_ptr;

  det->num_initial = 1;
  tmalloc(det->initial, int, 2);
  det->initial[1] = 1;

  hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptrb = ht.current_ptr;
  ht_ptre = ht_ptrb - 1;
  nssi = fsaptr->num_initial;
  for (i = 0; i < nssi; i++)
    *(++ht_ptre) = fsaptr->initial[i + 1];
  im = hash_locate(&ht, ht_ptre - ht_ptrb + 1);
  /* Each state in 'det' will be represented as a subset of the set of states
   * of *fsaptr. The initial state contains the initial states
   * of *fsaptr.
   * A subset is an accept-state if it contains an accept state of *fsaptr
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in nfa_determinize.\n");
    return 0;
  }
  if ((tempfile = fopen(tempfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow, int, ngens) else tmalloc(fsarow, int, 2 * ngens + 1)

        cstate = 0;
  if (dense_op)
    len = ngens; /* The length of the fsarow output. */
  nt = 0;        /* Number of transitions in det */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    cs_ptr = hash_rec(&ht, cstate);
    cs_ptre = hash_rec(&ht, cstate) + hash_rec_len(&ht, cstate) - 1;
    if (!dense_op)
      len = 0;

    for (g1 = 1; g1 <= ngens; g1++) {
      /* Calculate action of generator g1 on state cstate  - to get the image,
       * we simply apply it to each state in the subset of states representing
       * cstate.
       */
      g1shift = ((unsigned)g1) << SHIFT;
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      while (++ptr <= cs_ptre) {
        tableptr = table[*ptr];
        tableptre = table[*ptr + 1];
        while (tableptr < tableptre) {
          if ((*tableptr & MASKL) == g1shift) {
            csi = *tableptr & MASKR;
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
          tableptr++;
        }
      }
      im = hash_locate(&ht, ht_ptre - ht_ptrb + 1);
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

  /* Locate the accept states. A state is an accept state if and only if
   * the subset representing it contains an accept state of *fsaptr.
   */
  tmalloc(det->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    det->is_accepting[i] = FALSE;
  ct = 0;
  for (cstate = 1; cstate <= ns; cstate++) {
    cs_ptr = hash_rec(&ht, cstate);
    cs_ptre = hash_rec(&ht, cstate) + hash_rec_len(&ht, cstate) - 1;
    /* See if the set contains an accept-state */
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre)
      if (fsaptr->is_accepting[*ptr]) {
        det->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
  }

  det->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(det->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (det->is_accepting[i])
        det->accepting[++ct] = i;
  }
  tfree(fsaptr->is_accepting);
  tfree(det->is_accepting);
  hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(det, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return det;
}

/* *fsaptr must be a 2-variable (non-deterministic) fsa.
 * For the moment we assume it has no epsilon transitions.
 * The returned fsa is deterministic and accepts a word w_1 iff (w_1,w_2) is
 * accepted by *fsaptr, for some w_2 (with the usual padding conventions).
 * In fact, nfa_exists calls nfa_exists_int or nfa_exists_short,
 * the latter using the short hash table functions.
 */
fsa *nfa_exists(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling nfa_exists.\n");
  if (fsaptr->states->size < MAXUSHORT)
    return nfa_exists_short(fsaptr, op_table_type, destroy, tempfilename);
  else
    return nfa_exists_int(fsaptr, op_table_type, destroy, tempfilename);
}

fsa *nfa_exists_short(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                      char *tempfilename)
{
  int **table, ne, *tableptr, *tableptre, ngens, ns, *fsarow, es, ef, nt,
      cstate, csi, im, i, k, g1, len = 0, ct;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  boolean dense_op, got;
  short_hash_table ht;
  fsa *exists;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling nfa_exists_short.\n");

  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in nfa_exists: fsa must be 2-variable.\n");
    return 0;
  }

  tmalloc(exists, fsa, 1);
  fsa_init(exists);
  srec_copy(exists->alphabet, fsaptr->alphabet->base);
  exists->flags[DFA] = TRUE;
  exists->flags[ACCESSIBLE] = TRUE;
  exists->flags[BFS] = TRUE;

  exists->states->type = SIMPLE;

  exists->table->table_type = op_table_type;
  exists->table->denserows = 0;
  exists->table->printing_format = op_table_type;

  if (fsaptr->num_initial == 0) {
    exists->num_initial = 0;
    exists->num_accepting = 0;
    exists->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return exists;
  }
  ne = fsaptr->alphabet->size;
  ngens = exists->alphabet->size;

  if (ne != (ngens + 1) * (ngens + 1) - 1) {
    fprintf(stderr, "Error: in a 2-variable fsa, alphabet size should = "
                    "(ngens+1)^2 - 1.\n");
    return 0;
  }

  fsa_set_is_accepting(fsaptr);

  dense_op = op_table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  exists->num_initial = 1;
  tmalloc(exists->initial, int, 2);
  exists->initial[1] = 1;

  short_hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  k = fsaptr->num_initial;
  for (i = 1; i <= k; i++)
    ht_ptr[i - 1] = fsaptr->initial[i];
  im = short_hash_locate(&ht, k);
  /* Each state in 'exists' will be represented as a subset of the set of states
   * of *fsaptr. The initial state consists of the initial states
   * of *fsaptr. A subset is an accept-state if it contains an accept state of
   * *fsaptr, or if one can get to an accept-state by applying elements
   * ($,x) where $ is the padding symbol.
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in nfa_exists.\n");
    return 0;
  }
  if ((tempfile = fopen(tempfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow, int, ngens) else tmalloc(fsarow, int, 2 * ngens + 1)

        cstate = 0;
  if (dense_op)
    len = ngens; /* The length of the fsarow output. */
  nt = 0;        /* Number of transitions in exists */

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

    for (g1 = 1; g1 <= ngens; g1++) {
      /* Calculate action of generator g1 on state cstate  - to get the image,
       * we have to apply (g1,g2) to each element in the subset corresponding to
       * cstate, and this for each generator g2 of the base-alphabet (including
       * the padding symbol).
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      es = (g1 - 1) * (ngens + 1) + 1;
      ef = g1 * (ngens + 1);
      /* As g2 ranges from 1 to ngens+1 in the pair (g1,g2), for fixed g1, the
       * corresponding edge number in the fsa ranges from es to ef.
       */
      while (++ptr <= cs_ptre) {
        tableptr = table[*ptr];
        tableptre = table[*ptr + 1];
        while (tableptr < tableptre) {
          if (*tableptr >= es && *tableptr <= ef) {
            csi = *(tableptr + 1);
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
          tableptr += 2;
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

  ns = exists->states->size = ht.num_recs;
  exists->table->numTransitions = nt;

  /* Locate the accept states. This is slightly cumbersome, since a state
   * is an accept state if either the corresponding subset contains an
   * accept state of *fsaptr, or we can get from some such state to an
   * accept state by applying elements ($,x).
   * We will need to use the array exists->is_accepting.
   */
  tmalloc(exists->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    exists->is_accepting[i] = FALSE;
  ct = 0;
  for (cstate = ns; cstate >= 1; cstate--) {
    /* We work backwards through the states, since we wish to add on additional
     * elements at the end of the list in the hash-table - this destroys
     * later entries, but that doesn't matter, since we have already dealt
     * with them.
     */
    cs_ptr = short_hash_rec(&ht, cstate);
    cs_ptre = short_hash_rec(&ht, cstate) + short_hash_rec_len(&ht, cstate) - 1;
    /* First see if the set itself contains an accept-state */
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre)
      if (fsaptr->is_accepting[*ptr]) {
        exists->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    if (exists->is_accepting[cstate])
      continue;
    /* Next apply generators ($,x) and see if we get anything new, and
     * if it is an accept state.
     * Anything new is added to the end of the list - we don't need to
     * bother about having them in increasing order this time.
     */
    es = ngens * (ngens + 1) + 1;
    ef = (ngens + 1) * (ngens + 1) - 1;
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre) {
      tableptr = table[*ptr];
      tableptre = table[*ptr + 1];
      while (tableptr < tableptre) {
        if (*tableptr >= es && *tableptr <= ef) {
          csi = *(tableptr + 1);
          if (csi == 0)
            continue;
          if (fsaptr->is_accepting[csi]) {
            exists->is_accepting[cstate] = TRUE;
            ct++;
            break;
          }
          /* see if csi is new */
          ht_chptr = cs_ptr - 1;
          got = FALSE;
          while (++ht_chptr <= cs_ptre)
            if (csi == *ht_chptr) {
              got = TRUE;
              break;
            }
          if (!got)
            /* add csi to the end */
            *(++cs_ptre) = csi;
        }
        tableptr += 2;
      }
      if (exists->is_accepting[cstate])
        break;
    }
  }

  exists->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(exists->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (exists->is_accepting[i])
        exists->accepting[++ct] = i;
  }
  tfree(fsaptr->is_accepting);
  tfree(exists->is_accepting);
  short_hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(exists, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return exists;
}

fsa *nfa_exists_int(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                    char *tempfilename)
{
  int **table, ne, *tableptr, *tableptre, ngens, ns, *fsarow, es, ef, nt,
      cstate, csi, im, i, k, g1, len = 0, ct;
  int *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre, *ptr;
  boolean dense_op, got;
  hash_table ht;
  fsa *exists;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling nfa_exists_int.\n");

  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in nfa_exists: fsa must be 2-variable.\n");
    return 0;
  }

  tmalloc(exists, fsa, 1);
  fsa_init(exists);
  srec_copy(exists->alphabet, fsaptr->alphabet->base);
  exists->flags[DFA] = TRUE;
  exists->flags[ACCESSIBLE] = TRUE;
  exists->flags[BFS] = TRUE;

  exists->states->type = SIMPLE;

  exists->table->table_type = op_table_type;
  exists->table->denserows = 0;
  exists->table->printing_format = op_table_type;

  if (fsaptr->num_initial == 0) {
    exists->num_initial = 0;
    exists->num_accepting = 0;
    exists->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return exists;
  }
  ne = fsaptr->alphabet->size;
  ngens = exists->alphabet->size;

  if (ne != (ngens + 1) * (ngens + 1) - 1) {
    fprintf(stderr, "Error: in a 2-variable fsa, alphabet size should = "
                    "(ngens+1)^2 - 1.\n");
    return 0;
  }

  fsa_set_is_accepting(fsaptr);

  dense_op = op_table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  exists->num_initial = 1;
  tmalloc(exists->initial, int, 2);
  exists->initial[1] = 1;

  hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  k = fsaptr->num_initial;
  for (i = 1; i <= k; i++)
    ht_ptr[i - 1] = fsaptr->initial[i];
  im = hash_locate(&ht, k);
  /* Each state in 'exists' will be represented as a subset of the set of states
   * of *fsaptr. The initial state consists of the initial states
   * of *fsaptr. A subset is an accept-state if it contains an accept state of
   * *fsaptr, or if one can get to an accept-state by applying elements
   * ($,x) where $ is the padding symbol.
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in nfa_exists.\n");
    return 0;
  }
  if ((tempfile = fopen(tempfilename, "w")) == 0) {
    fprintf(stderr, "Error: cannot open file %s\n", tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow, int, ngens) else tmalloc(fsarow, int, 2 * ngens + 1)

        cstate = 0;
  if (dense_op)
    len = ngens; /* The length of the fsarow output. */
  nt = 0;        /* Number of transitions in exists */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level >= 3) {
      if ((cstate <= 1000 && cstate % 100 == 0) ||
          (cstate <= 10000 && cstate % 1000 == 0) ||
          (cstate <= 100000 && cstate % 5000 == 0) || cstate % 50000 == 0)
        printf("    #cstate = %d;  number of states = %d.\n", cstate,
               ht.num_recs);
    }
    cs_ptr = hash_rec(&ht, cstate);
    cs_ptre = hash_rec(&ht, cstate) + hash_rec_len(&ht, cstate) - 1;
    if (!dense_op)
      len = 0;

    for (g1 = 1; g1 <= ngens; g1++) {
      /* Calculate action of generator g1 on state cstate  - to get the image,
       * we have to apply (g1,g2) to each element in the subset corresponding to
       * cstate, and this for each generator g2 of the base-alphabet (including
       * the padding symbol).
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      es = (g1 - 1) * (ngens + 1) + 1;
      ef = g1 * (ngens + 1);
      /* As g2 ranges from 1 to ngens+1 in the pair (g1,g2), for fixed g1, the
       * corresponding edge number in the fsa ranges from es to ef.
       */
      while (++ptr <= cs_ptre) {
        tableptr = table[*ptr];
        tableptre = table[*ptr + 1];
        while (tableptr < tableptre) {
          if (*tableptr >= es && *tableptr <= ef) {
            csi = *(tableptr + 1);
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
          tableptr += 2;
        }
      }
      im = hash_locate(&ht, ht_ptre - ht_ptrb + 1);
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

  ns = exists->states->size = ht.num_recs;
  exists->table->numTransitions = nt;

  /* Locate the accept states. This is slightly cumbersome, since a state
   * is an accept state if either the corresponding subset contains an
   * accept state of *fsaptr, or we can get from some such state to an
   * accept state by applying elements ($,x).
   * We will need to use the array exists->is_accepting.
   */
  tmalloc(exists->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    exists->is_accepting[i] = FALSE;
  ct = 0;
  for (cstate = ns; cstate >= 1; cstate--) {
    /* We work backwards through the states, since we wish to add on additional
     * elements at the end of the list in the hash-table - this destroys
     * later entries, but that doesn't matter, since we have already dealt
     * with them.
     */
    cs_ptr = hash_rec(&ht, cstate);
    cs_ptre = hash_rec(&ht, cstate) + hash_rec_len(&ht, cstate) - 1;
    /* First see if the set itself contains an accept-state */
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre)
      if (fsaptr->is_accepting[*ptr]) {
        exists->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    if (exists->is_accepting[cstate])
      continue;
    /* Next apply generators ($,x) and see if we get anything new, and
     * if it is an accept state.
     * Anything new is added to the end of the list - we don't need to
     * bother about having them in increasing order this time.
     */
    es = ngens * (ngens + 1) + 1;
    ef = (ngens + 1) * (ngens + 1) - 1;
    ptr = cs_ptr - 1;
    while (++ptr <= cs_ptre) {
      tableptr = table[*ptr];
      tableptre = table[*ptr + 1];
      while (tableptr < tableptre) {
        if (*tableptr >= es && *tableptr <= ef) {
          csi = *(tableptr + 1);
          if (csi == 0)
            continue;
          if (fsaptr->is_accepting[csi]) {
            exists->is_accepting[cstate] = TRUE;
            ct++;
            break;
          }
          /* see if csi is new */
          ht_chptr = cs_ptr - 1;
          got = FALSE;
          while (++ht_chptr <= cs_ptre)
            if (csi == *ht_chptr) {
              got = TRUE;
              break;
            }
          if (!got)
            /* add csi to the end */
            *(++cs_ptre) = csi;
        }
        tableptr += 2;
      }
      if (exists->is_accepting[cstate])
        break;
    }
  }

  exists->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(exists->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (exists->is_accepting[i])
        exists->accepting[++ct] = i;
  }
  tfree(fsaptr->is_accepting);
  tfree(exists->is_accepting);
  hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(exists, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return exists;
}
