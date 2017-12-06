/* file fsamitriples.c  10/10/94
 * 6/8/98 large scale reorganisation to omit globals, etc.
 * 13/1/98 changes for the `gen' type replacing char for generators.
 * This file contains the routine fsa_mitriples, which is used to construct the
 * general product fsa with multiple (labeled) initial-states in a
 * coset automatic group.
 * It is a variation of fsa_triples, allowing multiple initial states.
 * For general methodology, see comment at top of file fsalogic.c.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "rws.h"
#include "externals.h"

/* Functions defined in this file: */
static fsa *fsa_mitriples_short(fsa *waptr, fsa *diffptr,
                                storage_type op_table_type, boolean destroy,
                                char *tempfilename, reduction_equation *eqnptr,
                                int maxeqns, boolean eqnstop,
                                boolean *foundeqns, boolean readback);
static fsa *fsa_mitriples_int(fsa *waptr, fsa *diffptr,
                              storage_type op_table_type, boolean destroy,
                              char *tempfilename, reduction_equation *eqnptr,
                              int maxeqns, boolean eqnstop, boolean *foundeqns,
                              boolean readback);

/* readback must be true for the time being */
/* *waptr is assumed to be the word-acceptor of a coset automatic group.
 * (In particular, all states should be accepting.)
 * *diffptr is assumed to be a word-difference machine of the same automatic
 *  group, with multiple initial states.
 * Both are assumed to be stored in dense-format.
 * This routine constructs the fsa of which the states are triples (s1,s2,d),
 * with s1 and s2 states of *waptr and d a state of *diffptr.
 * (More precisely, if *waptr has n states, then s1 and s2 may also be equal
 * to n+1, meaning that the end of string symbol has been read on lhs or rhs.)
 * The initial states are (1,1,i), where 1 is the initial state of *waptr,
 * and i an initial state of *diffptr.
 * The alphabet is 2-variable with base the alphabet of *waptr
 * (i.e. the same alphabet as *diffptr).
 * The alphabet member (g1,g2) maps (s1,s2,d) to (s1^g1,s2^g2,d^(g1,g2))
 * if all three components are nonzero, and to zero otherwise.
 * The transition-table of the resulting fsa is output in the usual way to
 * file tempfilename with table-type specified by op_table_type, before
 * minimisation.
 * Short hash-tables will be used, so this routine won't work if *waptr
 * or *diffptr has more than MAXUSHORT states.
 * There are several categories of accept-states - one for each distinct
 * group element of word-length 0 or 1, and these are specified by
 * the labels of the states, which are lists of words (all words of length 1
 * for the appropriate group element).
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
fsa *fsa_mitriples(fsa *waptr, fsa *diffptr, storage_type op_table_type,
                   boolean destroy, char *tempfilename,
                   reduction_equation *eqnptr, int maxeqns, boolean eqnstop,
                   boolean *foundeqns, boolean readback)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_triples.\n");
  if (waptr->states->size >= MAXUSHORT || diffptr->states->size >= MAXUSHORT)
    return fsa_mitriples_int(waptr, diffptr, op_table_type, destroy,
                             tempfilename, eqnptr, maxeqns, eqnstop, foundeqns,
                             readback);
  else
    return fsa_mitriples_short(waptr, diffptr, op_table_type, destroy,
                               tempfilename, eqnptr, maxeqns, eqnstop,
                               foundeqns, readback);
}

/* readback must be true for the time being */
static fsa *fsa_mitriples_short(fsa *waptr, fsa *diffptr,
                                storage_type op_table_type, boolean destroy,
                                char *tempfilename, reduction_equation *eqnptr,
                                int maxeqns, boolean eqnstop,
                                boolean *foundeqns, boolean readback)
{
  int **watable, ***difftable, identity, ngens, ngens1, nswa1, ne, ns = 0, *fsarow,
      nt, cstate, cswa1, cswa2, csdiff, im, i, j, k, e, len = 0, rlen, ct, bstate,
      bigger, numeqns, num_init;
  gen *subwd, reduced_genno[MAXGEN + 1], reduced_gen[2];
  /* for calculating and storing reductions of generators in case some
   * generators happen to be equal to others.
   */
  int labno[MAXGEN + 1], nlab;
  unsigned short *ht_ptr;
  boolean dense_op;
  fsa *mitriples;
  srec *labels;
  short_hash_table ht;
  FILE *tempfile;
  gen g1, g2, bg1, bg2;
  int maxv = 65536;
  reduction_struct rs_wd;
  int separator;
  struct vertexd {
    gen g1;
    gen g2;
    int state;
  } * definition = 0, *newdef;
  /* This is used to store the defining transition for the states of *mitriples.
   * If definition[i] = v, then state i is defined by the transition from
   * state v.state, with generator (v.g1,v.g2).
   * State 1 does not have a definition.
   */

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_mitriples_short.\n");

  if (!waptr->flags[DFA] || !diffptr->flags[MIDFA]) {
    fprintf(stderr, "Error: fsa__mitriples only applies to (MI)DFA's.\n");
    return 0;
  }
  if (waptr->alphabet->type != IDENTIFIERS) {
    fprintf(stderr, "Error in fsa_mitriples: first fsa has wrong type.\n");
    return 0;
  }
  if (waptr->num_accepting != waptr->states->size) {
    fprintf(stderr,
            "Error in fsa_mitriples: first fsa should be a word-acceptor.\n");
    return 0;
  }
  if (diffptr->alphabet->type != PRODUCT || diffptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_mitriples: second fsa must be 2-variable.\n");
    return 0;
  }
  if (diffptr->states->type != WORDS) {
    fprintf(
        stderr,
        "Error in fsa_mitriples: second fsa must be word-difference type.\n");
    return 0;
  }
  if (!srec_equal(diffptr->alphabet->base, waptr->alphabet)) {
    fprintf(stderr, "Error in fsa_mitriples: fsa's alphabet's don't match.\n");
    return 0;
  }
  if (waptr->states->size >= MAXUSHORT || diffptr->states->size >= MAXUSHORT) {
    fprintf(stderr,
            "Error in fsa_mitriples: one of the fsa's has too many states.\n");
    return 0;
  }

  if (fsa_table_dptr_init(diffptr) == -1)
    return 0;
  separator = diffptr->alphabet->base->size + 1;

  tmalloc(mitriples, fsa, 1);
  fsa_init(mitriples);
  srec_copy(mitriples->alphabet, diffptr->alphabet);
  mitriples->flags[MIDFA] = TRUE;
  mitriples->flags[ACCESSIBLE] = TRUE;
  mitriples->num_accepting = 0;
  /* In fact there will be lots of different categories of accept-states -
   * one for each generator - they will be recorded as labels of the states.
   */

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

  watable = waptr->table->table_data_ptr;
  difftable = diffptr->table->table_data_dptr;

  dense_op = op_table_type == DENSE;

  num_init = diffptr->num_initial;
  mitriples->num_initial = num_init;
  tmalloc(mitriples->initial, int, num_init + 1);
  for (i = 1; i <= num_init; i++)
    mitriples->initial[i] = i;
  mitriples->table->table_type = op_table_type;
  mitriples->table->denserows = 0;
  mitriples->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(mitriples->table->filename, char, stringlen(tempfilename) + 1);
    strcpy(mitriples->table->filename, tempfilename);
  }

  if (maxeqns > 0) {
    /* We need to remember vertex definitions */
    tmalloc(definition, struct vertexd, maxv);
    ns = num_init;
  }
  *foundeqns = FALSE;

  short_hash_init(&ht, TRUE, 3, 0, 0);
  identity = diffptr->initial[1];
  for (i = 1; i <= num_init; i++) {
    ht_ptr = ht.current_ptr;
    ht_ptr[0] = waptr->initial[1];
    ht_ptr[1] = waptr->initial[1];
    ht_ptr[2] = diffptr->initial[i];
    im = short_hash_locate(&ht, 3);
    if (im != i) {
      fprintf(stderr, "Hash-initialisation problem in fsa_mitriples.\n");
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
  nt = 0;     /* Number of transitions in mitriples */

  numeqns = 0; /* this becomes nonzero when we have started collecting
                * equations of equal words both accepted by word-acceptor.
                */
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
    if (!dense_op)
      len = 0;
    e = 0; /* e is the num,ber of the edge corresponding to the pair (g1,g2) */
    for (g1 = 1; g1 <= ngens1; g1++)
      for (g2 = 1; g2 <= ngens1; g2++) {
        e++;
        /* Calculate action of generator-pair (g1,g2) on state cstate */
        if (g1 == ngens1 && g2 == ngens1)
          continue;
        ht_ptr = ht.current_ptr;
        ht_ptr[2] = dense_dtarget(difftable, g1, g2, csdiff);
        if (ht_ptr[2] == 0)
          im = 0;
        else {
          ht_ptr[0] =
              g1 > ngens
                  ? nswa1
                  : cswa1 == nswa1 ? 0 : dense_target(watable, g1, cswa1);
          if (ht_ptr[0] == 0)
            im = 0;
          else {
            ht_ptr[1] =
                g2 > ngens
                    ? nswa1
                    : cswa2 == nswa1 ? 0 : dense_target(watable, g2, cswa2);
            if (ht_ptr[1] == 0)
              im = 0;
            else {
              if (eqnstop && ht_ptr[2] == identity && g1 != g2) {
                /* This means that we have found a new equation between two
                 * distinct words accepted by the word-acceptor *gpwa, and so
                 * *gpwa must have been wrong.
                 */
                *foundeqns = TRUE;
                if (kbm_print_level > 0 && numeqns == 0)
                  printf("#Equation found between two words accepted by "
                         "word-acceptor.\n");
                if (maxeqns > 0) { /* We reconstruct the equation explicitly */
                  /* First we calculate the length of the equation */
                  if (kbm_print_level >= 3)
                    printf("    #Calculating equation number %d.\n",
                           numeqns + 1);
                  len = 1;
                  bg1 = g1;
                  bg2 = g2;
                  bstate = cstate;
                  bigger = g2 > ngens ? 1 : g1 > ngens ? 2 : 0;
                  /* bigger=1 or 2 means resp. lhs/rhs larger in shortlex order
                   */
                  while (bstate > num_init) {
                    len++;
                    bg1 = definition[bstate].g1;
                    bg2 = definition[bstate].g2;
                    bstate = definition[bstate].state;
                  }
                  if (bigger == 0)
                    bigger = bg1 > bg2 ? 1 : 2;

                  /* Now we allocate space for it and store it -
                   * we insert the separator at the beginning
                   */
                  len++;
                  /* The right hand side will be preceded by the word in the
                   * subgroup involved in the equation - this is the label of
                   * the state bstate of *diffptr
                   */
                  subwd = diffptr->states->words[bstate];
                  rlen = len + genstrlen(subwd);
                  tmalloc(eqnptr[numeqns].lhs, gen, len + 1);
                  tmalloc(eqnptr[numeqns].rhs, gen, rlen + 1);
                  genstrcpy(eqnptr[numeqns].rhs, subwd);
                  eqnptr[numeqns].lhs[len] = eqnptr[numeqns].rhs[rlen] = 0;
                  bg1 = g1;
                  bg2 = g2;
                  bstate = cstate;
                  while (1) {
                    len--;
                    rlen--;
                    if (bigger == 1) {
                      eqnptr[numeqns].lhs[len] = bg1 > ngens ? 0 : bg1;
                      eqnptr[numeqns].rhs[rlen] = bg2 > ngens ? 0 : bg2;
                    }
                    else {
                      eqnptr[numeqns].rhs[rlen] = bg1 > ngens ? 0 : bg1;
                      eqnptr[numeqns].lhs[len] = bg2 > ngens ? 0 : bg2;
                    }
                    if (bstate <= num_init)
                      break;
                    bg1 = definition[bstate].g1;
                    bg2 = definition[bstate].g2;
                    bstate = definition[bstate].state;
                  }
                  eqnptr[numeqns].lhs[--len] = separator;
                  eqnptr[numeqns].rhs[--rlen] = separator;
                }

                if (numeqns == 0) {
                  /* We are no longer constructing the fsa, so we no longer need
                   * the file. */
                  fclose(tempfile);
                  unlink(tempfilename);
                }
                numeqns++;
                if (numeqns >= maxeqns) { /* exit */
                  if (kbm_print_level >= 2 && maxeqns > 0)
                    printf("  #Found %d new equations - aborting.\n", maxeqns);
                  short_hash_clear(&ht);
                  tfree(fsarow);
                  fsa_clear(mitriples);
                  tfree(mitriples);
                  if (maxeqns > 0)
                    tfree(definition);
                  if (destroy)
                    fsa_clear(waptr);
                  return 0;
                }
                else
                  eqnptr[numeqns].lhs = 0; /* to mark how many we have later */
              }
              im = short_hash_locate(&ht, 3);
              if (im == -1)
                return 0;
              if (maxeqns > 0 && im > ns) {
                ns++;
                if (ns == maxv) { /* need room for more definitions */
                  if (kbm_print_level >= 3)
                    printf(
                        "    #Allocating more space for vertex definitions.\n");
                  tmalloc(newdef, struct vertexd, 2 * maxv);
                  for (i = 1; i < maxv; i++)
                    newdef[i] = definition[i];
                  tfree(definition);
                  definition = newdef;
                  maxv *= 2;
                }
                definition[ns].g1 = g1;
                definition[ns].g2 = g2;
                definition[ns].state = cstate;
              }
            }
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
    if (numeqns == 0)
      fwrite((void *)fsarow, sizeof(int), (size_t)len, tempfile);
  } /*while (++cstate <= ht.num_recs) */

  if (numeqns > 0) {
    short_hash_clear(&ht);
    tfree(fsarow);
    fsa_clear(mitriples);
    tfree(mitriples);
    tfree(definition);
    if (destroy)
      fsa_clear(waptr);
    if (kbm_print_level >= 2)
      printf("  #Found %d new equations - aborting with algorithm complete.\n",
             numeqns);
    return 0;
  }

  fclose(tempfile);

  mitriples->states->type = LABELED;
  tmalloc(mitriples->states->labels, srec, 1);
  ns = mitriples->states->size = ht.num_recs;
  mitriples->table->numTransitions = nt;

  if (kbm_print_level >= 3) {
    printf("    #Calculated transitions - %d states, %d transitions.\n", ns,
           nt);
    printf("    #Now calculating state labels.\n");
  }
  tmalloc(mitriples->states->setToLabels, setToLabelsType, ns + 1);
  mitriples->states->setToLabels[0] = 0;
  /* First we calculate the array reduced_genno, to record if any generators
   * are equal to a lower one.
   */
  reduced_genno[0] = 0;
  rs_wd.wd_fsa = diffptr;
  for (i = 1; i <= ngens; i++) {
    reduced_gen[0] = i;
    reduced_gen[1] = 0;
    diff_reduce(reduced_gen, &rs_wd);
    reduced_genno[i] = reduced_gen[0]; /* also OK if equal to null-string */
  }
  for (i = 0; i <= ngens; i++)
    labno[i] = 0;
  labels = mitriples->states->labels;
  labels->type = LISTOFWORDS;
  for (i = 1; i <= ngens; i++) {
    tmalloc(labels->alphabet[i], char,
            stringlen(waptr->alphabet->names[i]) + 1);
    strcpy(labels->alphabet[i], waptr->alphabet->names[i]);
  }
  labels->alphabet_size = ngens;
  tmalloc(labels->wordslist, gen **, ngens + num_init + 1);
  /* All states whose label has length <=1 will be classed as accept states,
   * since they are accept-states for some generator.
   * We need to mark them specifically in the "mi" case, since the information
   * is needed by the minimisation function midfa_labeled_minimize".
   */
  tmalloc(mitriples->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    mitriples->is_accepting[i] = FALSE;
  mitriples->num_accepting = 0;
  nlab = 0;
  for (i = 1; i <= ns; i++) {
    ht_ptr = short_hash_rec(&ht, i);
    csdiff = ht_ptr[2];
    len = genstrlen(diffptr->states->words[csdiff]);
    if (len <= 1) {
      mitriples->is_accepting[i] = TRUE;
      mitriples->num_accepting++;
      j = (len == 0) ? 0 : diffptr->states->words[csdiff][0];
      if (labno[j] > 0)
        mitriples->states->setToLabels[i] = labno[j];
      else {
        /* new label - first see how many generators reduce to this */
        nlab++;
        ct = 0;
        for (k = 0; k <= ngens; k++)
          if (reduced_genno[k] == reduced_genno[j]) {
            ct++;
            labno[k] = nlab;
          }
        tmalloc(labels->wordslist[nlab], gen *, ct + 1);
        ct = 0;
        for (k = 0; k <= ngens; k++)
          if (reduced_genno[k] == reduced_genno[j]) {
            if (k == 0) {
              tmalloc(labels->wordslist[nlab][ct], gen, 1);
              labels->wordslist[nlab][ct][0] = 0;
            }
            else {
              tmalloc(labels->wordslist[nlab][ct], gen, 2);
              labels->wordslist[nlab][ct][0] = k;
              labels->wordslist[nlab][ct][1] = 0;
            }
            ct++;
          }
        labels->wordslist[nlab][ct] = 0;
        mitriples->states->setToLabels[i] = nlab;
      }
    }
    else if (i <= num_init) {
      nlab++;
      tmalloc(labels->wordslist[nlab], gen *, 2);
      tmalloc(labels->wordslist[nlab][0], gen,
              genstrlen(diffptr->states->words[csdiff]) + 1);
      genstrcpy(labels->wordslist[nlab][0], diffptr->states->words[csdiff]);
      labels->wordslist[nlab][1] = 0;
      mitriples->states->setToLabels[i] = nlab;
    }
    else
      mitriples->states->setToLabels[i] = 0;
  }
  labels->size = nlab;

  short_hash_clear(&ht);
  tfree(fsarow);
  if (maxeqns > 0)
    tfree(definition);
  /* Now read the transition table back in */
  if (readback) {
    tempfile = fopen(tempfilename, "r");
    compressed_transitions_read(mitriples, tempfile);
    fclose(tempfile);
    unlink(tempfilename);
  }
  tmalloc(mitriples->accepting, int, mitriples->num_accepting + 1);
  ct = 0;
  for (i = 1; i <= ns; i++)
    if (mitriples->is_accepting[i])
      mitriples->accepting[++ct] = i;
  tfree(mitriples->is_accepting);
  if (destroy) {
    fsa_clear(waptr);
    fsa_clear(diffptr);
  }

  return mitriples;
}

/* readback must be true for the time being */
static fsa *fsa_mitriples_int(fsa *waptr, fsa *diffptr,
                              storage_type op_table_type, boolean destroy,
                              char *tempfilename, reduction_equation *eqnptr,
                              int maxeqns, boolean eqnstop, boolean *foundeqns,
                              boolean readback)
{
  int **watable, ***difftable, identity, ngens, ngens1, nswa1, ne, ns = 0, *fsarow,
      nt, cstate, cswa1, cswa2, csdiff, im, i, j, k, e, len = 0, rlen, ct, bstate,
      bigger, numeqns, num_init;
  gen *subwd, reduced_genno[MAXGEN + 1], reduced_gen[2];
  /* for calculating and storing reductions of generators in case some
   * generators happen to be equal to others.
   */
  int labno[MAXGEN + 1], nlab;
  int *ht_ptr;
  boolean dense_op;
  fsa *mitriples;
  srec *labels;
  hash_table ht;
  FILE *tempfile;
  gen g1, g2, bg1, bg2;
  int maxv = 65536;
  reduction_struct rs_wd;
  int separator;
  struct vertexd {
    gen g1;
    gen g2;
    int state;
  } * definition = 0, *newdef;
  /* This is used to store the defining transition for the states of *mitriples.
   * If definition[i] = v, then state i is defined by the transition from
   * state v.state, with generator (v.g1,v.g2).
   * State 1 does not have a definition.
   */

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_mitriples_int.\n");

  if (!waptr->flags[DFA] || !diffptr->flags[MIDFA]) {
    fprintf(stderr, "Error: fsa__mitriples only applies to (MI)DFA's.\n");
    return 0;
  }
  if (waptr->alphabet->type != IDENTIFIERS) {
    fprintf(stderr, "Error in fsa_mitriples: first fsa has wrong type.\n");
    return 0;
  }
  if (waptr->num_accepting != waptr->states->size) {
    fprintf(stderr,
            "Error in fsa_mitriples: first fsa should be a word-acceptor.\n");
    return 0;
  }
  if (diffptr->alphabet->type != PRODUCT || diffptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_mitriples: second fsa must be 2-variable.\n");
    return 0;
  }
  if (diffptr->states->type != WORDS) {
    fprintf(
        stderr,
        "Error in fsa_mitriples: second fsa must be word-difference type.\n");
    return 0;
  }
  if (!srec_equal(diffptr->alphabet->base, waptr->alphabet)) {
    fprintf(stderr, "Error in fsa_mitriples: fsa's alphabet's don't match.\n");
    return 0;
  }
  if (waptr->states->size >= MAXUSHORT || diffptr->states->size >= MAXUSHORT) {
    fprintf(stderr,
            "Error in fsa_mitriples: one of the fsa's has too many states.\n");
    return 0;
  }

  if (fsa_table_dptr_init(diffptr) == -1)
    return 0;
  separator = diffptr->alphabet->base->size + 1;

  tmalloc(mitriples, fsa, 1);
  fsa_init(mitriples);
  srec_copy(mitriples->alphabet, diffptr->alphabet);
  mitriples->flags[MIDFA] = TRUE;
  mitriples->flags[ACCESSIBLE] = TRUE;
  mitriples->num_accepting = 0;
  /* In fact there will be lots of different categories of accept-states -
   * one for each generator - they will be recorded as labels of the states.
   */

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

  watable = waptr->table->table_data_ptr;
  difftable = diffptr->table->table_data_dptr;

  dense_op = op_table_type == DENSE;

  num_init = diffptr->num_initial;
  mitriples->num_initial = num_init;
  tmalloc(mitriples->initial, int, num_init + 1);
  for (i = 1; i <= num_init; i++)
    mitriples->initial[i] = i;
  mitriples->table->table_type = op_table_type;
  mitriples->table->denserows = 0;
  mitriples->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(mitriples->table->filename, char, stringlen(tempfilename) + 1);
    strcpy(mitriples->table->filename, tempfilename);
  }

  if (maxeqns > 0) {
    /* We need to remember vertex definitions */
    tmalloc(definition, struct vertexd, maxv);
    ns = num_init;
  }
  *foundeqns = FALSE;

  hash_init(&ht, TRUE, 3, 0, 0);
  identity = diffptr->initial[1];
  for (i = 1; i <= num_init; i++) {
    ht_ptr = ht.current_ptr;
    ht_ptr[0] = waptr->initial[1];
    ht_ptr[1] = waptr->initial[1];
    ht_ptr[2] = diffptr->initial[i];
    im = hash_locate(&ht, 3);
    if (im != i) {
      fprintf(stderr, "Hash-initialisation problem in fsa_mitriples.\n");
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
  nt = 0;     /* Number of transitions in mitriples */

  numeqns = 0; /* this becomes nonzero when we have started collecting
                * equations of equal words both accepted by word-acceptor.
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
    cswa1 = ht_ptr[0];
    cswa2 = ht_ptr[1];
    csdiff = ht_ptr[2];
    if (!dense_op)
      len = 0;
    e = 0; /* e is the num,ber of the edge corresponding to the pair (g1,g2) */
    for (g1 = 1; g1 <= ngens1; g1++)
      for (g2 = 1; g2 <= ngens1; g2++) {
        e++;
        /* Calculate action of generator-pair (g1,g2) on state cstate */
        if (g1 == ngens1 && g2 == ngens1)
          continue;
        ht_ptr = ht.current_ptr;
        ht_ptr[2] = dense_dtarget(difftable, g1, g2, csdiff);
        if (ht_ptr[2] == 0)
          im = 0;
        else {
          ht_ptr[0] =
              g1 > ngens
                  ? nswa1
                  : cswa1 == nswa1 ? 0 : dense_target(watable, g1, cswa1);
          if (ht_ptr[0] == 0)
            im = 0;
          else {
            ht_ptr[1] =
                g2 > ngens
                    ? nswa1
                    : cswa2 == nswa1 ? 0 : dense_target(watable, g2, cswa2);
            if (ht_ptr[1] == 0)
              im = 0;
            else {
              if (eqnstop && ht_ptr[2] == identity && g1 != g2) {
                /* This means that we have found a new equation between two
                 * distinct words accepted by the word-acceptor *gpwa, and so
                 * *gpwa must have been wrong.
                 */
                *foundeqns = TRUE;
                if (kbm_print_level > 0 && numeqns == 0)
                  printf("#Equation found between two words accepted by "
                         "word-acceptor.\n");
                if (maxeqns > 0) { /* We reconstruct the equation explicitly */
                  /* First we calculate the length of the equation */
                  if (kbm_print_level >= 3)
                    printf("    #Calculating equation number %d.\n",
                           numeqns + 1);
                  len = 1;
                  bg1 = g1;
                  bg2 = g2;
                  bstate = cstate;
                  bigger = g2 > ngens ? 1 : g1 > ngens ? 2 : 0;
                  /* bigger=1 or 2 means resp. lhs/rhs larger in shortlex order
                   */
                  while (bstate > num_init) {
                    len++;
                    bg1 = definition[bstate].g1;
                    bg2 = definition[bstate].g2;
                    bstate = definition[bstate].state;
                  }
                  if (bigger == 0)
                    bigger = bg1 > bg2 ? 1 : 2;

                  /* Now we allocate space for it and store it -
                   * we insert the separator at the beginning
                   */
                  len++;
                  /* The right hand side will be preceded by the word in the
                   * subgroup involved in the equation - this is the label of
                   * the state bstate of *diffptr
                   */
                  subwd = diffptr->states->words[bstate];
                  rlen = len + genstrlen(subwd);
                  tmalloc(eqnptr[numeqns].lhs, gen, len + 1);
                  tmalloc(eqnptr[numeqns].rhs, gen, rlen + 1);
                  genstrcpy(eqnptr[numeqns].rhs, subwd);
                  eqnptr[numeqns].lhs[len] = eqnptr[numeqns].rhs[rlen] = 0;
                  bg1 = g1;
                  bg2 = g2;
                  bstate = cstate;
                  while (1) {
                    len--;
                    rlen--;
                    if (bigger == 1) {
                      eqnptr[numeqns].lhs[len] = bg1 > ngens ? 0 : bg1;
                      eqnptr[numeqns].rhs[rlen] = bg2 > ngens ? 0 : bg2;
                    }
                    else {
                      eqnptr[numeqns].rhs[rlen] = bg1 > ngens ? 0 : bg1;
                      eqnptr[numeqns].lhs[len] = bg2 > ngens ? 0 : bg2;
                    }
                    if (bstate <= num_init)
                      break;
                    bg1 = definition[bstate].g1;
                    bg2 = definition[bstate].g2;
                    bstate = definition[bstate].state;
                  }
                  eqnptr[numeqns].lhs[--len] = separator;
                  eqnptr[numeqns].rhs[--rlen] = separator;
                }

                if (numeqns == 0) {
                  /* We are no longer constructing the fsa, so we no longer need
                   * the file. */
                  fclose(tempfile);
                  unlink(tempfilename);
                }
                numeqns++;
                if (numeqns >= maxeqns) { /* exit */
                  if (kbm_print_level >= 2 && maxeqns > 0)
                    printf("  #Found %d new equations - aborting.\n", maxeqns);
                  hash_clear(&ht);
                  tfree(fsarow);
                  fsa_clear(mitriples);
                  tfree(mitriples);
                  if (maxeqns > 0)
                    tfree(definition);
                  if (destroy)
                    fsa_clear(waptr);
                  return 0;
                }
                else
                  eqnptr[numeqns].lhs = 0; /* to mark how many we have later */
              }
              im = hash_locate(&ht, 3);
              if (im == -1)
                return 0;
              if (maxeqns > 0 && im > ns) {
                ns++;
                if (ns == maxv) { /* need room for more definitions */
                  if (kbm_print_level >= 3)
                    printf(
                        "    #Allocating more space for vertex definitions.\n");
                  tmalloc(newdef, struct vertexd, 2 * maxv);
                  for (i = 1; i < maxv; i++)
                    newdef[i] = definition[i];
                  tfree(definition);
                  definition = newdef;
                  maxv *= 2;
                }
                definition[ns].g1 = g1;
                definition[ns].g2 = g2;
                definition[ns].state = cstate;
              }
            }
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
    if (numeqns == 0)
      fwrite((void *)fsarow, sizeof(int), (size_t)len, tempfile);
  } /*while (++cstate <= ht.num_recs) */

  if (numeqns > 0) {
    hash_clear(&ht);
    tfree(fsarow);
    fsa_clear(mitriples);
    tfree(mitriples);
    tfree(definition);
    if (destroy)
      fsa_clear(waptr);
    if (kbm_print_level >= 2)
      printf("  #Found %d new equations - aborting with algorithm complete.\n",
             numeqns);
    return 0;
  }

  fclose(tempfile);

  mitriples->states->type = LABELED;
  tmalloc(mitriples->states->labels, srec, 1);
  ns = mitriples->states->size = ht.num_recs;
  mitriples->table->numTransitions = nt;

  if (kbm_print_level >= 3) {
    printf("    #Calculated transitions - %d states, %d transitions.\n", ns,
           nt);
    printf("    #Now calculating state labels.\n");
  }
  tmalloc(mitriples->states->setToLabels, setToLabelsType, ns + 1);
  mitriples->states->setToLabels[0] = 0;
  /* First we calculate the array reduced_genno, to record if any generators
   * are equal to a lower one.
   */
  reduced_genno[0] = 0;
  rs_wd.wd_fsa = diffptr;
  for (i = 1; i <= ngens; i++) {
    reduced_gen[0] = i;
    reduced_gen[1] = 0;
    diff_reduce(reduced_gen, &rs_wd);
    reduced_genno[i] = reduced_gen[0]; /* also OK if equal to null-string */
  }
  for (i = 0; i <= ngens; i++)
    labno[i] = 0;
  labels = mitriples->states->labels;
  labels->type = LISTOFWORDS;
  for (i = 1; i <= ngens; i++) {
    tmalloc(labels->alphabet[i], char,
            stringlen(waptr->alphabet->names[i]) + 1);
    strcpy(labels->alphabet[i], waptr->alphabet->names[i]);
  }
  labels->alphabet_size = ngens;
  tmalloc(labels->wordslist, gen **, ngens + num_init + 1);
  /* All states whose label has length <=1 will be classed as accept states,
   * since they are accept-states for some generator.
   * We need to mark them specifically in the "mi" case, since the information
   * is needed by the minimsation function midfa_labeled_minimize".
   */
  tmalloc(mitriples->is_accepting, boolean, ns + 1);
  for (i = 1; i <= ns; i++)
    mitriples->is_accepting[i] = FALSE;
  mitriples->num_accepting = 0;
  nlab = 0;
  for (i = 1; i <= ns; i++) {
    ht_ptr = hash_rec(&ht, i);
    csdiff = ht_ptr[2];
    len = genstrlen(diffptr->states->words[csdiff]);
    if (len <= 1) {
      mitriples->is_accepting[i] = TRUE;
      mitriples->num_accepting++;
      j = (len == 0) ? 0 : diffptr->states->words[csdiff][0];
      if (labno[j] > 0)
        mitriples->states->setToLabels[i] = labno[j];
      else {
        /* new label - first see how many generators reduce to this */
        nlab++;
        ct = 0;
        for (k = 0; k <= ngens; k++)
          if (reduced_genno[k] == reduced_genno[j]) {
            ct++;
            labno[k] = nlab;
          }
        tmalloc(labels->wordslist[nlab], gen *, ct + 1);
        ct = 0;
        for (k = 0; k <= ngens; k++)
          if (reduced_genno[k] == reduced_genno[j]) {
            if (k == 0) {
              tmalloc(labels->wordslist[nlab][ct], gen, 1);
              labels->wordslist[nlab][ct][0] = 0;
            }
            else {
              tmalloc(labels->wordslist[nlab][ct], gen, 2);
              labels->wordslist[nlab][ct][0] = k;
              labels->wordslist[nlab][ct][1] = 0;
            }
            ct++;
          }
        labels->wordslist[nlab][ct] = 0;
        mitriples->states->setToLabels[i] = nlab;
      }
    }
    else if (i <= num_init) {
      nlab++;
      tmalloc(labels->wordslist[nlab], gen *, 2);
      tmalloc(labels->wordslist[nlab][0], gen,
              genstrlen(diffptr->states->words[csdiff]) + 1);
      genstrcpy(labels->wordslist[nlab][0], diffptr->states->words[csdiff]);
      labels->wordslist[nlab][1] = 0;
      mitriples->states->setToLabels[i] = nlab;
    }
    else
      mitriples->states->setToLabels[i] = 0;
  }
  labels->size = nlab;

  hash_clear(&ht);
  tfree(fsarow);
  if (maxeqns > 0)
    tfree(definition);
  /* Now read the transition table back in */
  if (readback) {
    tempfile = fopen(tempfilename, "r");
    compressed_transitions_read(mitriples, tempfile);
    fclose(tempfile);
    unlink(tempfilename);
  }
  tmalloc(mitriples->accepting, int, mitriples->num_accepting + 1);
  ct = 0;
  for (i = 1; i <= ns; i++)
    if (mitriples->is_accepting[i])
      mitriples->accepting[++ct] = i;
  tfree(mitriples->is_accepting);
  if (destroy) {
    fsa_clear(waptr);
    fsa_clear(diffptr);
  }

  return mitriples;
}
