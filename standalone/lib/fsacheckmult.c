/* file fsacheckmult.c  21. 11. 94.
 * 6/8/98 large scale reorganisation to omit globals, etc.
 * 30/7/98 - put in code for fsa_checkmult_int
 * 13/1/98 - changes for `gen' type of generator replacing char.
 * 16.10.96. Put in code to check which generators actually occur as labels
 * of success states in the generalised multiplier, and to ignore any that
 * do not, when checking correctness. (The test is certain to fail for any that
 * do not occur.)
 * This is unnecessary in the normal shortlex case, where they all occur
 * in any case.
 *
 * 22.9.95. Added code for coset automatic groups case.
 * The code is now fairly uniform for the two cases.
 *
 * This file contains the routine fsa_checkmult, which is used by the program
 * gpcheckmult.
 * (See also comments in file ../src/gpcheckmult.c.)
 * Its input automaton *multptr is the general multiplier of an automatic group.
 * It goes through the transition table generation process of fsa_exists
 * on this automaton (but does not write the table, since it will not be
 * needed). It does remember definitions of states (as in fsa_triples).
 * These are needed to reconstruct the failing word  w (see below).
 * Each state is a subset of the states of *multptr. Each such subset
 * should contain an accept state of each individual multiplier. If the
 * generation process completes, and this always holds, then the checking
 * process succeeds, and the procedure returns 0.
 * If some state is constructed which does not contain an accept state of
 * mult_g, for some generator g of the group, and w is a word with target
 * this state, then there can be no word x so that (w,x) is accepted by
 * mult_g, and so the checking process fails,
 * and the word w and generator x are remembered.
 * The number of such words found by the end of the process is returned.
 * The word w must be accepted by the word-acceptor (for otherwise (w,y)
 * would map to 0 for all words y, and w would never be considered),
 * so we do not need to use the word-acceptor explicitly.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "hash.h"
#include "externals.h"

static int fsa_checkmult_short(fsa *multptr, reduction_equation *eqnptr,
                               int maxeqns, boolean cosets, int separator);
static int fsa_checkmult_int(fsa *multptr, reduction_equation *eqnptr,
                             int maxeqns, boolean cosets, int separator);

/* If the checking fails, the failing words will be returned in the lhs of
 * eqnptr[i], and the associated generator in the rhs, for i=0,1,...
 * If more than maxeqns such words are found, we abort.
 * The function returns the number of equations found.
 */
int fsa_checkmult(fsa *multptr, reduction_equation *eqnptr, int maxeqns,
                  boolean cosets, int separator)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_checkmult.\n");
  if (multptr->states->size < MAXUSHORT)
    return fsa_checkmult_short(multptr, eqnptr, maxeqns, cosets, separator);
  else
    return fsa_checkmult_int(multptr, eqnptr, maxeqns, cosets, separator);
}

/* If the checking fails, the failing word will be returned in the lhs of
 * *eqnptr, and the associated generator in the rhs.
 */
static int fsa_checkmult_short(fsa *multptr, reduction_equation *eqnptr,
                               int maxeqns, boolean cosets, int separator)
{
  int **table, dr, ne, ngens, ngens1, ns, nsnew, bstate, numeqns, e, es, ef,
      espad, efpad, cstate, cs, csi, i, j, g1, bg1, im, len;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  gen **genlist, *genptr;
  boolean dense_ip, *occurs, *includes, got;
  setToLabelsType *state_label;
  short_hash_table ht;
  int maxv = 65536;
  struct vertexd {
    gen g;
    int state;
  } * definition, *newdef;
  /* This is used to store the defining transition for the states of the new
   * fsa. If definition[i] = v, then state i is defined by the transition from
   * state v.state, with generator v.g.
   * State 1 does not have a definition.
   */

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_checkmult_short.\n");
  if (!multptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_checkmult only applies to DFA's.\n");
    return -1;
  }

  if (multptr->alphabet->type != PRODUCT || multptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_checkmult: fsa must be 2-variable.\n");
    return -1;
  }
  if (multptr->states->type != LABELED) {
    fprintf(stderr,
            "Error in fsa_checkmult: states of fsa must be of labeled type.\n");
    return -1;
  }

  /* We are not actually going to costruct a new fsa - we just go through the
   * motions of constructing the hash-table that represents its states.
   */
  ne = multptr->alphabet->size;
  ngens = multptr->alphabet->base->size;
  ngens1 = ngens + 1;
  state_label = multptr->states->setToLabels;
  ns = multptr->states->size;

  if (ne != ngens1 * ngens1 - 1) {
    fprintf(stderr, "Error: in a 2-variable fsa, alphabet size should = "
                    "(ngens+1)^2 - 1.\n");
    return -1;
  }

  tmalloc(occurs, boolean, ngens + 1);
  for (i = 0; i <= ngens; i++)
    occurs[i] = FALSE;
  for (i = 1; i <= ns; i++)
    if ((j = state_label[i])) {
      genlist = multptr->states->labels->wordslist[j];
      /* the list of words that is the label for state number *ptr */
      while ((genptr = *(genlist++)))
        occurs[genptr[0]] = TRUE;
    }

  dense_ip = multptr->table->table_type == DENSE;
  dr = multptr->table->denserows;
  table = multptr->table->table_data_ptr;

  short_hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = multptr->initial[1];
  im = short_hash_locate(&ht, 1);
  /* Each state in the new fsa will be represented as a subset of the set of
   * states * of *multptr. The initial state is one-element set containing
   * the initial state of *multptr.
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_checkmult.\n");
    return -1;
  }

  /* Set up the array of structures to remember state-definitions. */
  tmalloc(definition, struct vertexd, maxv);
  nsnew = 1;

  tmalloc(includes, boolean, ngens + 2);
  /* this will be used for checking validity of new states -
   * includes[ngens+1] is not used, but may be referenced accidentally
   */
  cstate = 0;
  numeqns = 0;

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
    for (g1 = 1; g1 <= ngens; g1++) {
      /* Calculate action of generator g1 on state cstate  - to get the image,
       * we have to apply (g1,g2) to each element in the subset corresponding to
       * cstate, and this for each generator g2 of the base-alphabet (including
       * the padding symbol).
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      es = (g1 - 1) * ngens1 + 1;
      ef = g1 * ngens1;
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
      if (im == -1)
        return -1;
      if (im > nsnew) {
        /* We have a new state. We must check to see if it is valid - i.e.
         * contains an accept-state of each multiplier. But first we have to
         * close it under the action of ($,g) for generators g. (We can put
         * extra states found at the end - this will not disturb the
         *  hash-table.)
         */
        espad = ngens * ngens1 + 1;
        efpad = ngens1 * ngens1 - 1;
        ptr = ht_ptrb - 1;
        while (++ptr <= ht_ptre) {
          cs = *ptr;
          for (e = espad; e <= efpad; e++) {
            csi = target(dense_ip, table, e, cs, dr);
            if (csi == 0)
              continue;
            /* see if csi is new */
            ht_chptr = ht_ptrb - 1;
            got = FALSE;
            while (++ht_chptr < ht_ptre)
              if (csi == *ht_chptr) {
                got = TRUE;
                break;
              }
            if (!got)
              /* add csi to the end */
              *(++ht_ptre) = csi;
          }
        }
        /* State is now closed under ($,g) - so check validity */
        for (i = 0; i <= ngens; i++)
          includes[i] = FALSE;
        ptr = ht_ptrb - 1;
        while (++ptr <= ht_ptre)
          if ((j = state_label[*ptr])) {
            genlist = multptr->states->labels->wordslist[j];
            /* the list of words that is the label for state number *ptr */
            while ((genptr = *(genlist++)))
              includes[genptr[0]] = TRUE;
          }

        for (i = 0; i <= ngens; i++)
          if (occurs[i] && !includes[i]) {
            /* The state is invalid for generator number i.
             * We reconstruct the offending word w, using the state-definitions,
             * and then abort.
             */
            if (numeqns == 0 && kbm_print_level > 0)
              printf("#Multiplier incorrect with generator number %d.\n", i);
            /* First see how long the word is */
            len = 1;
            bg1 = g1;
            bstate = cstate;
            while (bstate != 1) {
              len++;
              bg1 = definition[bstate].g;
              bstate = definition[bstate].state;
            }
            /* Now allocate space for it - allow an extra place for multiplying
             * by a generator.
             * In the cosets case, also an extra place for the separator
             * that we insert at the beginning of the word.
             */
            if (cosets)
              len++;
            tmalloc(eqnptr[numeqns].lhs, gen, len + 2);
            eqnptr[numeqns].lhs[len] = 0;
            bg1 = g1;
            bstate = cstate;
            while (1) {
              eqnptr[numeqns].lhs[--len] = bg1;
              if (bstate == 1)
                break;
              bg1 = definition[bstate].g;
              bstate = definition[bstate].state;
            }
            if (cosets)
              eqnptr[numeqns].lhs[--len] = separator;
            /* Put the offending generator in the rhs of *eqnptr */
            if (i == 0) {
              tmalloc(eqnptr[numeqns].rhs, gen, 1);
              eqnptr[numeqns].rhs[0] = 0;
            }
            else {
              tmalloc(eqnptr[numeqns].rhs, gen, 2);
              eqnptr[numeqns].rhs[0] = i;
              eqnptr[numeqns].rhs[1] = 0;
            }
            numeqns++;
            if (kbm_print_level >= 3)
              printf("    #Found offending word number %d.\n", numeqns);

            if (numeqns >= maxeqns) {
              tfree(definition);
              tfree(occurs);
              tfree(includes);
              short_hash_clear(&ht);
              if (kbm_print_level >= 2)
                printf("  #Found %d new equations. Aborting.\n", maxeqns);
              return numeqns;
            }
          }
        /* We have now checked that the new state is valid  -
         * so remember its definition
         */
        nsnew++;
        if (nsnew == maxv) { /* need room for more definitions */
          if (kbm_print_level >= 3)
            printf("    #Allocating more space for vertex definitions.\n");
          tmalloc(newdef, struct vertexd, 2 * maxv);
          for (i = 1; i < maxv; i++)
            newdef[i] = definition[i];
          tfree(definition);
          definition = newdef;
          maxv *= 2;
        }
        definition[nsnew].g = g1;
        definition[nsnew].state = cstate;
      }
    }
  }

  /* If we get to the end of the loop safely, then we have completed the
   * multiplier correctness checking test.
   */
  tfree(definition);
  tfree(occurs);
  tfree(includes);
  short_hash_clear(&ht);

  return numeqns;
}

/* If the checking fails, the failing word will be returned in the lhs of
 * *eqnptr, and the associated generator in the rhs.
 */
static int fsa_checkmult_int(fsa *multptr, reduction_equation *eqnptr,
                             int maxeqns, boolean cosets, int separator)
{
  int **table, dr, ne, ngens, ngens1, ns, nsnew, bstate, numeqns, e, es, ef,
      espad, efpad, cstate, cs, csi, i, j, g1, bg1, im, len;
  int *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre, *ptr;
  gen **genlist, *genptr;
  boolean dense_ip, *occurs, *includes, got;
  setToLabelsType *state_label;
  hash_table ht;
  int maxv = 65536;
  struct vertexd {
    gen g;
    int state;
  } * definition, *newdef;
  /* This is used to store the defining transition for the states of the new
   * fsa. If definition[i] = v, then state i is defined by the transition from
   * state v.state, with generator v.g.
   * State 1 does not have a definition.
   */

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_checkmult_short.\n");
  if (!multptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_checkmult only applies to DFA's.\n");
    return -1;
  }

  if (multptr->alphabet->type != PRODUCT || multptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_checkmult: fsa must be 2-variable.\n");
    return -1;
  }
  if (multptr->states->type != LABELED) {
    fprintf(stderr,
            "Error in fsa_checkmult: states of fsa must be of labeled type.\n");
    return -1;
  }

  /* We are not actually going to costruct a new fsa - we just go through the
   * motions of constructing the hash-table that represents its states.
   */
  ne = multptr->alphabet->size;
  ngens = multptr->alphabet->base->size;
  ngens1 = ngens + 1;
  state_label = multptr->states->setToLabels;
  ns = multptr->states->size;

  if (ne != ngens1 * ngens1 - 1) {
    fprintf(stderr, "Error: in a 2-variable fsa, alphabet size should = "
                    "(ngens+1)^2 - 1.\n");
    return -1;
  }

  tmalloc(occurs, boolean, ngens + 1);
  for (i = 0; i <= ngens; i++)
    occurs[i] = FALSE;
  for (i = 1; i <= ns; i++)
    if ((j = state_label[i])) {
      genlist = multptr->states->labels->wordslist[j];
      /* the list of words that is the label for state number *ptr */
      while ((genptr = *(genlist++)))
        occurs[genptr[0]] = TRUE;
    }

  dense_ip = multptr->table->table_type == DENSE;
  dr = multptr->table->denserows;
  table = multptr->table->table_data_ptr;

  hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = multptr->initial[1];
  im = hash_locate(&ht, 1);
  /* Each state in the new fsa will be represented as a subset of the set of
   * states * of *multptr. The initial state is one-element set containing
   * the initial state of *multptr.
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_checkmult.\n");
    return -1;
  }

  /* Set up the array of structures to remember state-definitions. */
  tmalloc(definition, struct vertexd, maxv);
  nsnew = 1;

  tmalloc(includes, boolean, ngens + 2);
  /* this will be used for checking validity of new states -
   * includes[ngens+1] is not used, but may be referenced accidentally
   */
  cstate = 0;
  numeqns = 0;

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
    for (g1 = 1; g1 <= ngens; g1++) {
      /* Calculate action of generator g1 on state cstate  - to get the image,
       * we have to apply (g1,g2) to each element in the subset corresponding to
       * cstate, and this for each generator g2 of the base-alphabet (including
       * the padding symbol).
       */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb - 1;
      ptr = cs_ptr - 1;
      es = (g1 - 1) * ngens1 + 1;
      ef = g1 * ngens1;
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
      im = hash_locate(&ht, ht_ptre - ht_ptrb + 1);
      if (im == -1)
        return -1;
      if (im > nsnew) {
        /* We have a new state. We must check to see if it is valid - i.e.
         * contains an accept-state of each multiplier. But first we have to
         * close it under the action of ($,g) for generators g. (We can put
         * extra states found at the end - this will not disturb the
         *  hash-table.)
         */
        espad = ngens * ngens1 + 1;
        efpad = ngens1 * ngens1 - 1;
        ptr = ht_ptrb - 1;
        while (++ptr <= ht_ptre) {
          cs = *ptr;
          for (e = espad; e <= efpad; e++) {
            csi = target(dense_ip, table, e, cs, dr);
            if (csi == 0)
              continue;
            /* see if csi is new */
            ht_chptr = ht_ptrb - 1;
            got = FALSE;
            while (++ht_chptr < ht_ptre)
              if (csi == *ht_chptr) {
                got = TRUE;
                break;
              }
            if (!got)
              /* add csi to the end */
              *(++ht_ptre) = csi;
          }
        }
        /* State is now closed under ($,g) - so check validity */
        for (i = 0; i <= ngens; i++)
          includes[i] = FALSE;
        ptr = ht_ptrb - 1;
        while (++ptr <= ht_ptre)
          if ((j = state_label[*ptr])) {
            genlist = multptr->states->labels->wordslist[j];
            /* the list of words that is the label for state number *ptr */
            while ((genptr = *(genlist++)))
              includes[genptr[0]] = TRUE;
          }

        for (i = 0; i <= ngens; i++)
          if (occurs[i] && !includes[i]) {
            /* The state is invalid for generator number i.
             * We reconstruct the offending word w, using the state-definitions,
             * and then abort.
             */
            if (numeqns == 0 && kbm_print_level > 0)
              printf("#Multiplier incorrect with generator number %d.\n", i);
            /* First see how long the word is */
            len = 1;
            bg1 = g1;
            bstate = cstate;
            while (bstate != 1) {
              len++;
              bg1 = definition[bstate].g;
              bstate = definition[bstate].state;
            }
            /* Now allocate space for it - allow an extra place for multiplying
             * by a generator.
             * In the cosets case, also an extra place for the separator
             * that we insert at the beginning of the word.
             */
            if (cosets)
              len++;
            tmalloc(eqnptr[numeqns].lhs, gen, len + 2);
            eqnptr[numeqns].lhs[len] = 0;
            bg1 = g1;
            bstate = cstate;
            while (1) {
              eqnptr[numeqns].lhs[--len] = bg1;
              if (bstate == 1)
                break;
              bg1 = definition[bstate].g;
              bstate = definition[bstate].state;
            }
            if (cosets)
              eqnptr[numeqns].lhs[--len] = separator;
            /* Put the offending generator in the rhs of *eqnptr */
            if (i == 0) {
              tmalloc(eqnptr[numeqns].rhs, gen, 1);
              eqnptr[numeqns].rhs[0] = 0;
            }
            else {
              tmalloc(eqnptr[numeqns].rhs, gen, 2);
              eqnptr[numeqns].rhs[0] = i;
              eqnptr[numeqns].rhs[1] = 0;
            }
            numeqns++;
            if (kbm_print_level >= 3)
              printf("    #Found offending word number %d.\n", numeqns);

            if (numeqns >= maxeqns) {
              tfree(definition);
              tfree(occurs);
              tfree(includes);
              hash_clear(&ht);
              if (kbm_print_level >= 2)
                printf("  #Found %d new equations. Aborting.\n", maxeqns);
              return numeqns;
            }
          }
        /* We have now checked that the new state is valid  -
         * so remember its definition
         */
        nsnew++;
        if (nsnew == maxv) { /* need room for more definitions */
          if (kbm_print_level >= 3)
            printf("    #Allocating more space for vertex definitions.\n");
          tmalloc(newdef, struct vertexd, 2 * maxv);
          for (i = 1; i < maxv; i++)
            newdef[i] = definition[i];
          tfree(definition);
          definition = newdef;
          maxv *= 2;
        }
        definition[nsnew].g = g1;
        definition[nsnew].state = cstate;
      }
    }
  }

  /* If we get to the end of the loop safely, then we have completed the
   * multiplier correctness checking test.
   */
  tfree(definition);
  tfree(occurs);
  tfree(includes);
  hash_clear(&ht);

  return numeqns;
}
