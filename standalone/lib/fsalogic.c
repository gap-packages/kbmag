/* file fsalogic.c  2. 11. 94.
 * 9/2/98  - introduced function fsa_concat to concatenate the languages of
 * two fsa's and fsa_star for starred language.
 * 31/12/98 - adapt fsa_binop to deal with case in which first
 * argument has type labeled. The output fsa acquires the same labels.
 * Introduced new function fsa_laband to access this.
 * 13/1/98 - changes for `gen' type of generator replacing char.
 * 18.11.94. - added fsa_and_not
 * This file contains routines for performing logical operations on
 * finite state automata.
 * The functions in this file currently only deal with deterministic fsa's
 *
 * The general methodology of some functions in this file, such as
 * fsa_and, fsa_or and fsa_exists, and of several functions in different files
 * is as follows.
 * These functions construct a particular finite state automaton, of which
 * the states are some kind of sets of states of the input automata,
 * and the transition table is generated in order.
 * The states are stored as records in a hash-table, so that they can be
 * located easily.
 * The initial state is constructed by hand and numbered 1, and then the
 * transitions from each state are generated in order. If a new state is
 * generated as target of a transition, then it is added to the end of the
 * list of states. Eventually the process will terminate when the table closes,
 * and all transitions have been generated from each state.
 * The transitions from a particular state will not be needed again until
 * the generation process is complete, and so they are output(in unformatted
 * form) to a file (with name tempfilename).
 * When the table is complete, the hash-table data can normally be discarded
 * (once it has been used to identify accept-states in the constructed fsa),
 * and then the transition table can be read back in.
 * There is also an option to clear the space taken by the input automata
 * before re-reading.
 * This results in saving of core memory, because the transition table of
 * the fsa being constructed and the data in the hash-table are never held
 * in main memory at the same time.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "externals.h"

typedef enum { AND, OR, AND_NOT } kbm_binop;

static fsa *fsa_binop(fsa *fsaptr1, fsa *fsaptr2, storage_type op_table_type,
                      boolean destroy, char *tempfilename, kbm_binop op,
                      boolean labels);

static fsa *fsa_exists_short(fsa *fsaptr, storage_type op_table_type,
                             boolean destroy, char *tempfilename);

static fsa *fsa_exists_int(fsa *fsaptr, storage_type op_table_type,
                           boolean destroy, char *tempfilename);


/* Test equality of set records *srptr1 and *srptr2 */
boolean srec_equal(srec *srptr1, srec *srptr2)
{
  int i, j, l, *il1, *il2;
  if (srptr1->type != srptr2->type)
    return FALSE;
  if (srptr1->size != srptr2->size)
    return FALSE;
  if (srptr1->type == IDENTIFIERS || srptr1->type == STRINGS) {
    for (i = 1; i <= srptr1->size; i++)
      if (strcmp(srptr1->names[i], srptr2->names[i]))
        return FALSE;
  }
  else if (srptr1->type == WORDS) {
    for (i = 1; i <= srptr1->size; i++)
      if (genstrcmp(srptr1->words[i], srptr2->words[i]))
        return FALSE;
  }
  else if (srptr1->type == LISTOFWORDS) {
    for (i = 1; i <= srptr1->size; i++) {
      j = 0;
      while (srptr1->wordslist[i][j]) {
        if (!srptr2->wordslist[i][j])
          return FALSE;
        if (genstrcmp(srptr1->wordslist[i][j], srptr2->wordslist[i][j]))
          return FALSE;
        j++;
      }
      if (srptr2->wordslist[i][j])
        return FALSE;
    }
  }
  else if (srptr1->type == LISTOFINTS) {
    for (i = 1; i <= srptr1->size; i++) {
      il1 = srptr1->intlist[i];
      il2 = srptr2->intlist[i];
      l = il1[0];
      for (j = 0; j <= l; j++)
        if (il1[j] != il2[j])
          return FALSE;
    }
  }
  if (srptr1->type == WORDS || srptr1->type == LISTOFWORDS) {
    for (i = 1; i <= srptr1->alphabet_size; i++)
      if (strcmp(srptr1->alphabet[i], srptr2->alphabet[i]))
        return FALSE;
  }
  if (srptr1->type == PRODUCT) {
    if (!srec_equal(srptr1->base, srptr2->base))
      return FALSE;
    if (srptr1->arity != srptr2->arity)
      return FALSE;
    if (srptr1->padding != srptr2->padding)
      return FALSE;
  }

  return TRUE;
}

/* Test equality of the transition tables *tableptr1 and *tableptr2.
 * The storage-types don't need to be equal.
 */
boolean table_equal(table_struc *tableptr1, table_struc *tableptr2, int ne,
                    int ns)
{
  int **table1, **table2, i, j, dr1, dr2;
  boolean dense1, dense2;

  dense1 = tableptr1->table_type == DENSE;
  dense2 = tableptr2->table_type == DENSE;
  table1 = tableptr1->table_data_ptr;
  table2 = tableptr2->table_data_ptr;
  dr1 = tableptr1->denserows;
  dr2 = tableptr2->denserows;

  for (j = 1; j <= ne; j++)
    for (i = 1; i <= ns; i++)
      if (target(dense1, table1, j, i, dr1) !=
          target(dense2, table2, j, i, dr2))
        return FALSE;

  return TRUE;
}

/* Test equality of the fsa's fsaptr1 and fsaptr2 */
boolean fsa_equal(fsa *fsaptr1, fsa *fsaptr2)
{
  int ns, ne, ni, na, i;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_equal.\n");
  if (!srec_equal(fsaptr1->alphabet, fsaptr2->alphabet))
    return FALSE;

  if (!srec_equal(fsaptr1->states, fsaptr2->states))
    return FALSE;

  ns = fsaptr1->states->size;
  ne = fsaptr1->alphabet->size;

  if (fsaptr1->num_initial != fsaptr2->num_initial)
    return FALSE;
  ni = fsaptr1->num_initial;
  if (ni > 0 && ni < ns) {
    fsa_set_is_initial(fsaptr1);
    fsa_set_is_initial(fsaptr2);
    for (i = 1; i <= ns; i++)
      if (fsaptr1->is_initial[i] != fsaptr2->is_initial[i])
        return FALSE;
    tfree(fsaptr1->is_initial);
    tfree(fsaptr2->is_initial);
  }

  if (fsaptr1->num_accepting != fsaptr2->num_accepting)
    return FALSE;
  na = fsaptr1->num_accepting;
  if (na > 0 && na < ns) {
    fsa_set_is_accepting(fsaptr1);
    fsa_set_is_accepting(fsaptr2);
    for (i = 1; i <= ns; i++)
      if (fsaptr1->is_accepting[i] != fsaptr2->is_accepting[i])
        return FALSE;
    tfree(fsaptr1->is_accepting);
    tfree(fsaptr2->is_accepting);
  }

  /* The flag strings are additional information, and needn't correspond */

  if (!table_equal(fsaptr1->table, fsaptr2->table, ne, ns))
    return FALSE;

  return TRUE;
}

/* The code for the next 4 functions is so similar, that we combine them
 * into a single function fsa_binop.
 * (The negatives of these would be more difficult, because (0,0) would
 *  be an accept state - so use fsa_not for these.)
 */

fsa *fsa_and(fsa *fsaptr1, fsa *fsaptr2, storage_type op_table_type,
             boolean destroy, char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_and.\n");
  return fsa_binop(fsaptr1, fsaptr2, op_table_type, destroy, tempfilename, AND,
                   FALSE);
}

fsa *fsa_laband(fsa *fsaptr1, fsa *fsaptr2, storage_type op_table_type,
                boolean destroy, char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_laband.\n");
  return fsa_binop(fsaptr1, fsaptr2, op_table_type, destroy, tempfilename, AND,
                   TRUE);
}

fsa *fsa_or(fsa *fsaptr1, fsa *fsaptr2, storage_type op_table_type,
            boolean destroy, char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_or.\n");
  return fsa_binop(fsaptr1, fsaptr2, op_table_type, destroy, tempfilename, OR,
                   FALSE);
}

fsa *fsa_and_not(fsa *fsaptr1, fsa *fsaptr2, storage_type op_table_type,
                 boolean destroy, char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_and_not.\n");
  return fsa_binop(fsaptr1, fsaptr2, op_table_type, destroy, tempfilename,
                   AND_NOT, FALSE);
}

static fsa *fsa_binop(fsa *fsaptr1, fsa *fsaptr2, storage_type op_table_type,
                      boolean destroy, char *tempfilename, kbm_binop op,
                      const boolean labels)
{
  int **table1, **table2, ne, ns, dr1, dr2, *fsarow, nt, cstate, csa, csb, im,
      i, g, len = 0, ct, *ht_ptr;
  boolean dense_ip1, dense_ip2, dense_op, accept;
  fsa *and_or_not;
  hash_table ht;
  setToLabelsType *lab = 0;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_binop.\n");
  if (!fsaptr1->flags[DFA] || !fsaptr2->flags[DFA]) {
    fprintf(stderr, "Error: fsa_binop only applies to DFA's.\n");
    return 0;
  }

  if (!srec_equal(fsaptr1->alphabet, fsaptr2->alphabet)) {
    fprintf(stderr, "Error in fsa_binop: fsa's have different alphabets.\n");
    return 0;
  }

  if (fsaptr1->flags[RWS])
    fsa_clear_rws(fsaptr1);

  if (fsaptr2->flags[RWS])
    fsa_clear_rws(fsaptr2);

  tmalloc(and_or_not, fsa, 1);
  if (fsaptr2->num_initial == 0 && (op == AND_NOT || op == OR)) {
    fsa_copy(and_or_not, fsaptr1);
    and_or_not->table->printing_format = op_table_type;
    if (destroy) {
      fsa_clear(fsaptr1);
      fsa_clear(fsaptr2);
    }
    return and_or_not;
  }
  if (fsaptr1->num_initial == 0 && op == OR) {
    fsa_copy(and_or_not, fsaptr2);
    and_or_not->table->printing_format = op_table_type;
    if (fsaptr1->states->type == LABELED) {
      srec_clear(and_or_not->states);
      srec_copy(and_or_not->states, fsaptr1->states);
      tfree(and_or_not->states->setToLabels);
      ns = fsaptr2->states->size;
      tmalloc(and_or_not->states->setToLabels, setToLabelsType, ns + 1);
      for (i = 0; i <= ns; i++)
        and_or_not->states->setToLabels[i] = 0;
    }
    if (destroy) {
      fsa_clear(fsaptr1);
      fsa_clear(fsaptr2);
    }
    return and_or_not;
  }

  fsa_init(and_or_not);
  srec_copy(and_or_not->alphabet, fsaptr1->alphabet);
  and_or_not->flags[DFA] = TRUE;
  and_or_not->flags[ACCESSIBLE] = TRUE;
  and_or_not->flags[BFS] = TRUE;

  if (labels) {
    if (fsaptr1->states->type != LABELED) {
      fprintf(stderr,
              "Error in fsa_binop: first fsa should have labeled states.\n");
      return 0;
    }
    srec_copy(and_or_not->states, fsaptr1->states);
    tfree(and_or_not->states->setToLabels);
    lab = fsaptr1->states->setToLabels;
  }
  else
    and_or_not->states->type = SIMPLE;

  and_or_not->table->table_type = op_table_type;
  and_or_not->table->denserows = 0;
  and_or_not->table->printing_format = op_table_type;

  if (fsaptr1->num_initial == 0 || fsaptr2->num_initial == 0) {
    and_or_not->num_initial = 0;
    and_or_not->num_accepting = 0;
    and_or_not->states->size = 0;
    if (destroy) {
      fsa_clear(fsaptr1);
      fsa_clear(fsaptr2);
    }
    return and_or_not;
  }

  ne = fsaptr1->alphabet->size;

  fsa_set_is_accepting(fsaptr1);
  fsa_set_is_accepting(fsaptr2);
  table1 = fsaptr1->table->table_data_ptr;
  table2 = fsaptr2->table->table_data_ptr;

  dense_ip1 = fsaptr1->table->table_type == DENSE;
  dense_ip2 = fsaptr2->table->table_type == DENSE;
  dr1 = fsaptr1->table->denserows;
  dr2 = fsaptr2->table->denserows;
  dense_op = op_table_type == DENSE;

  and_or_not->num_initial = 1;
  tmalloc(and_or_not->initial, int, 2);
  and_or_not->initial[1] = 1;

  hash_init(&ht, TRUE, 2, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = fsaptr1->initial[1];
  ht_ptr[1] = fsaptr2->initial[1];
  im = hash_locate(&ht, 2);
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_binop.\n");
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
  nt = 0;     /* Number of transitions in and_or_not */

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
      ht_ptr[0] = csa ? target(dense_ip1, table1, g, csa, dr1) : 0;
      ht_ptr[1] = csb ? target(dense_ip2, table2, g, csb, dr2) : 0;
      if ((op == AND && (ht_ptr[0] == 0 || ht_ptr[1] == 0)) ||
          (op == AND_NOT && ht_ptr[0] == 0))
        im = 0;
      else
        im = hash_locate(&ht, 2);
      if (im == -1)
        return 0;
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

  ns = and_or_not->states->size = ht.num_recs;
  and_or_not->table->numTransitions = nt;
  if (labels)
    tmalloc(and_or_not->states->setToLabels, setToLabelsType, ns + 1);
  /* Locate the accept states: first count them and then record them. */
  ct = 0;
  for (i = 1; i <= ns; i++) {
    ht_ptr = hash_rec(&ht, i);
    csa = ht_ptr[0];
    csb = ht_ptr[1];
    accept = op == AND
                 ? fsaptr1->is_accepting[csa] && fsaptr2->is_accepting[csb]
                 : op == OR ? fsaptr1->is_accepting[csa] ||
                                  fsaptr2->is_accepting[csb]
                            : op == AND_NOT ? fsaptr1->is_accepting[csa] &&
                                                  !fsaptr2->is_accepting[csb]
                                            : FALSE; /* default cannot occur */
    if (accept)
      ct++;
    if (labels)
      and_or_not->states->setToLabels[i] = csa == 0 ? 0 : lab[csa];
  }
  and_or_not->num_accepting = ct;
  if (ct == 1 || ct != ns) {
    tmalloc(and_or_not->accepting, int, ct + 1);
    ct = 0;
    for (i = 1; i <= ns; i++) {
      ht_ptr = hash_rec(&ht, i);
      csa = ht_ptr[0];
      csb = ht_ptr[1];
      accept =
          op == AND
              ? fsaptr1->is_accepting[csa] && fsaptr2->is_accepting[csb]
              : op == OR
                    ? fsaptr1->is_accepting[csa] || fsaptr2->is_accepting[csb]
                    : op == AND_NOT ? fsaptr1->is_accepting[csa] &&
                                          !fsaptr2->is_accepting[csb]
                                    : FALSE; /* default cannot occur */
      if (accept)
        and_or_not->accepting[++ct] = i;
    }
  }
  hash_clear(&ht);
  tfree(fsarow);
  tfree(fsaptr1->is_accepting);
  tfree(fsaptr2->is_accepting);

  if (destroy) {
    fsa_clear(fsaptr1);
    fsa_clear(fsaptr2);
  }
  /* Now read the transition table back in */
  tempfile = fopen(tempfilename, "r");
  compressed_transitions_read(and_or_not, tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return and_or_not;
}

/* This function ought to be easy - just interchange accept and non-accept
 * states. In fact it is complicated slightly by the fact that we are
 * working with partial fsa's, so the 0 state has to become a new state,
 * and a former state may become 0.
 * The storage-type of the computed fsa *not will always be dense.
 */
fsa *fsa_not(fsa *fsaptr, storage_type op_table_type)
{
  int i, j, k, ns, ne, **oldtable, **newtable, newzero, dr;
  fsa * not;
  boolean dense, zero;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_not.\n");

  if (!fsaptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_not only applies to DFA's.\n");
    return 0;
  }

  if (fsaptr->flags[RWS])
    fsa_clear_rws(fsaptr);

  tmalloc(not, fsa, 1);
  fsa_init(not);
  /* Most of the information is simply copied from *fsaptr to *not-
   * but we allow room for an extra accept state of *not, to replace 0
   */
  ne = fsaptr->alphabet->size;
  ns = fsaptr->states->size;

  srec_copy(not->alphabet, fsaptr->alphabet);
  not->states->type = SIMPLE;
  not->states->size = ns;
  not->num_initial = 1;
  tmalloc(not->initial, int, 2);
  not->initial[1] = fsaptr->num_initial == 0 ? 1 : fsaptr->initial[1];

  fsa_table_init(not->table, ns + 1, ne);
  oldtable = fsaptr->table->table_data_ptr;
  newtable = not->table->table_data_ptr;
  dense = fsaptr->table->table_type == DENSE;
  dr = fsaptr->table->denserows;
  not->table->printing_format = op_table_type;
  not->table->denserows = 0;

  zero = ns == 0;
  for (j = 1; j <= ne; j++)
    for (i = 1; i <= ns; i++) {
      k = target(dense, oldtable, j, i, dr);
      set_dense_target(newtable, j, i, k);
      if (!zero && k == 0)
        zero = TRUE;
    }

  tmalloc(not->is_accepting, boolean, ns + 2);
  if (fsaptr->num_accepting == ns) {
    for (i = 1; i <= ns; i++)
      not->is_accepting[i] = FALSE;
    not->is_accepting[ns + 1] = TRUE;
  }
  else {
    for (i = 1; i <= ns + 1; i++)
      not->is_accepting[i] = TRUE;
    for (i = 1; i <= fsaptr->num_accepting; i++)
      not->is_accepting[fsaptr->accepting[i]] = FALSE;
  }

  /* See if there is a new zero-state */
  newzero = 0;
  for (i = 1; i <= ns; i++)
    if (!not->is_accepting[i]) {
      newzero = i;
      for (j = 1; j <= ne; j++)
        if (dense_target(newtable, j, i) != i) {
          newzero = 0;
          break;
        }
      if (newzero)
        break;
    }

  if (newzero == 0 && zero)
    not->states->size = ++ns;

  not->num_accepting = 0;
  for (i = 1; i <= ns; i++)
    if (not->is_accepting[i])
      not->num_accepting++;
  if (ns == 1 || not->num_accepting != ns) {
    k = 0;
    tmalloc(not->accepting, int, not->num_accepting + 1);
    for (i = 1; i <= ns; i++)
      if (not->is_accepting[i])
        not->accepting[++k] = i;
  }
  tfree(not->is_accepting);

  if (zero && newzero) {
    /* swap zero with the new zero-state */
    for (j = 1; j <= ne; j++)
      for (i = 1; i <= ns; i++) {
        if (i == newzero)
          continue;
        if (dense_target(newtable, j, i) == 0)
          newtable[j][i] = newzero;
        else if (dense_target(newtable, j, i) == newzero)
          set_dense_target(newtable, j, i, 0);
      }
  }
  else if (newzero)
    fsa_delete_state(not, newzero);
  else if (zero) {
    for (j = 1; j <= ne; j++)
      set_dense_target(newtable, j, ns, ns);
    for (j = 1; j <= ne; j++)
      for (i = 1; i < ns; i++)
        if (dense_target(newtable, j, i) == 0)
          set_dense_target(newtable, j, i, ns);
  }

  for (i = 0; i < num_kbm_flag_strings; i++)
    not->flags[i] = fsaptr->flags[i];
  not->flags[BFS] = FALSE;
  /* BFS property would be ruined by 0 state of *fsaptr */

  return not;
}

/* *fsaptr should be a deterministic fsa.
 * A (usually) non-deterministic fsa accepting the star L* of
 * the language L of *fsaptr is returned.
 * The method is simply to insert epsilon-transitions from the accept states
 * of *fsaptr to its initial state.
 */
fsa *fsa_star(fsa *fsaptr, boolean destroy)
{
  int **itable, **table, ne, ns, nt1, dr, nt, *sparseptr, iin, ina, im, i, ct,
      g;
  boolean dense_ip;
  fsa *star;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_star.\n");
  if (!fsaptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_star only applies to DFA's.\n");
    return 0;
  }

  if (fsaptr->flags[RWS])
    fsa_clear_rws(fsaptr);

  tmalloc(star, fsa, 1);
  if (fsaptr->num_initial == 0) {
    fsa_copy(star, fsaptr);
    if (destroy)
      fsa_clear(fsaptr);
    star->table->printing_format = SPARSE;
    return star;
  }

  fsa_init(star);
  srec_copy(star->alphabet, fsaptr->alphabet);
  star->flags[NFA] = TRUE;
  fsa_set_is_accepting(fsaptr);
  ne = fsaptr->alphabet->size;
  ns = fsaptr->states->size;
  star->states->size = ns;

  iin = fsaptr->initial[1];
  tmalloc(star->initial, int, 2);
  star->initial[1] = iin;
  star->num_initial = 1;
  ina = fsaptr->num_accepting;
  if (!fsaptr->is_accepting[iin]) {
    ina++;
    fsaptr->is_accepting[iin] = TRUE;
  }
  star->num_accepting = ina;
  if (ns == 1 || ina < ns) {
    tmalloc(star->accepting, int, ina + 1);
    ct = 0;
    for (i = 1; i <= ns; i++)
      if (fsaptr->is_accepting[i])
        star->accepting[++ct] = i;
  }

  itable = fsaptr->table->table_data_ptr;
  dense_ip = fsaptr->table->table_type == DENSE;
  dr = fsaptr->table->denserows;
  /* We won't rely on fsaptr->table->numTransitions being stored */
  nt1 = 0;
  for (g = 1; g <= ne; g++)
    for (i = 1; i <= ns; i++)
      if (target(dense_ip, itable, g, i, dr) != 0)
        nt1++;

  nt = nt1 + ina;
  star->table->numTransitions = nt;
  star->table->table_type = SPARSE;
  star->table->denserows = 0;
  star->table->printing_format = SPARSE;
  tmalloc(star->table->table_data_ptr, int *, ns + 2);
  table = star->table->table_data_ptr;
  tmalloc(table[0], int, 2 * nt + 1);
  sparseptr = table[0];

  for (i = 1; i <= ns; i++) {
    table[i] = sparseptr;
    if (fsaptr->is_accepting[i]) {
      *(sparseptr++) = 0;
      *(sparseptr++) = iin;
    }
    for (g = 1; g <= ne; g++) {
      im = target(dense_ip, itable, g, i, dr);
      if (im) {
        *(sparseptr++) = g;
        *(sparseptr++) = im;
      }
    }
  }
  table[ns + 1] = sparseptr; /* to show end of data */

  tfree(fsaptr->is_accepting);
  if (destroy)
    fsa_clear(fsaptr);
  return star;
}

/* *fsaptr1 and *fsaptr2 should be two deterministic fsa's.
 * A (usually) non-deterministic fsa accepting the concatenation of
 * the languages of *fsaptr1 and *fsaptr2 is returned.
 * The method is simply to take the union of the two fsa's, and
 * insert epsilon-transitions from the accept states of *fsaptr1 to the
 * initial states of *fsaptr2.
 */
fsa *fsa_concat(fsa *fsaptr1, fsa *fsaptr2, boolean destroy)
{
  int **table1, **table2, **table, ne, ns1, ns2, nt1, nt2, dr1, dr2, nt,
      *sparseptr, in2, na2, im, i, g;
  boolean dense_ip1, dense_ip2;
  fsa *concat;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_concat.\n");
  if (!fsaptr1->flags[DFA] || !fsaptr2->flags[DFA]) {
    fprintf(stderr, "Error: fsa_concat only applies to DFA's.\n");
    return 0;
  }

  if (!srec_equal(fsaptr1->alphabet, fsaptr2->alphabet)) {
    fprintf(stderr, "Error in fsa_concat: fsa's have different alphabets.\n");
    return 0;
  }

  if (fsaptr1->flags[RWS])
    fsa_clear_rws(fsaptr1);
  if (fsaptr2->flags[RWS])
    fsa_clear_rws(fsaptr2);

  tmalloc(concat, fsa, 1);
  if (fsaptr1->num_initial == 0) {
    fsa_copy(concat, fsaptr1);
    if (destroy) {
      fsa_clear(fsaptr1);
      fsa_clear(fsaptr2);
    }
    concat->table->printing_format = SPARSE;
    return concat;
  }
  if (fsaptr2->num_initial == 0) {
    fsa_copy(concat, fsaptr2);
    if (destroy) {
      fsa_clear(fsaptr1);
      fsa_clear(fsaptr2);
    }
    concat->table->printing_format = SPARSE;
    return concat;
  }

  fsa_init(concat);
  srec_copy(concat->alphabet, fsaptr1->alphabet);
  concat->flags[NFA] = TRUE;
  fsa_set_is_accepting(fsaptr1);
  ne = fsaptr1->alphabet->size;
  ns1 = fsaptr1->states->size;
  ns2 = fsaptr2->states->size;
  concat->states->size = ns1 + ns2;

  tmalloc(concat->initial, int, 2);
  concat->initial[1] = fsaptr1->initial[1];
  concat->num_initial = 1;
  na2 = fsaptr2->num_accepting;
  concat->num_accepting = na2;
  tmalloc(concat->accepting, int, na2 + 1);
  if (na2 == ns2) {
    for (i = 1; i <= na2; i++)
      concat->accepting[i] = i + ns1;
  }
  else
    for (i = 1; i <= na2; i++)
      concat->accepting[i] = fsaptr2->accepting[i] + ns1;
  in2 = fsaptr2->initial[1] + ns1;

  table1 = fsaptr1->table->table_data_ptr;
  table2 = fsaptr2->table->table_data_ptr;
  dense_ip1 = fsaptr1->table->table_type == DENSE;
  dense_ip2 = fsaptr2->table->table_type == DENSE;
  dr1 = fsaptr1->table->denserows;
  dr2 = fsaptr2->table->denserows;
  /* We won't rely on fsaptr1/2->table->numTransitions being stored */
  nt1 = 0;
  for (g = 1; g <= ne; g++)
    for (i = 1; i <= ns1; i++)
      if (target(dense_ip1, table1, g, i, dr1) != 0)
        nt1++;
  nt2 = 0;
  for (g = 1; g <= ne; g++)
    for (i = 1; i <= ns2; i++)
      if (target(dense_ip2, table2, g, i, dr2) != 0)
        nt2++;

  nt = nt1 + nt2 + fsaptr1->num_accepting;
  concat->table->numTransitions = nt;
  concat->table->table_type = SPARSE;
  concat->table->denserows = 0;
  concat->table->printing_format = SPARSE;
  tmalloc(concat->table->table_data_ptr, int *, ns1 + ns2 + 2);
  table = concat->table->table_data_ptr;
  tmalloc(table[0], int, 2 * nt + 1);
  sparseptr = table[0];

  for (i = 1; i <= ns1; i++) {
    table[i] = sparseptr;
    if (fsaptr1->is_accepting[i]) {
      *(sparseptr++) = 0;
      *(sparseptr++) = in2;
    }
    for (g = 1; g <= ne; g++) {
      im = target(dense_ip1, table1, g, i, dr1);
      if (im) {
        *(sparseptr++) = g;
        *(sparseptr++) = im;
      }
    }
  }
  for (i = 1; i <= ns2; i++) {
    table[i + ns1] = sparseptr;
    for (g = 1; g <= ne; g++) {
      im = target(dense_ip2, table2, g, i, dr2);
      if (im) {
        *(sparseptr++) = g;
        *(sparseptr++) = im + ns1;
      }
    }
  }
  table[ns1 + ns2 + 1] = sparseptr; /* to show end of data */

  tfree(fsaptr1->is_accepting);
  if (destroy) {
    fsa_clear(fsaptr1);
    fsa_clear(fsaptr2);
  }
  return concat;
}

/* *fsaptr must be a 2-variable fsa.
 * The returned fsa accepts a word w_1 iff (w_1,w_2) is accepted by *fsaptr,
 * for some word w_2 (with the usual padding conventions).
 * In fact, fsa_exists calls fsa_exists_int or (more usually) fsa_exists_short,
 * the latter using the short hash table functions.
 */
fsa *fsa_exists(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                char *tempfilename)
{
  if (kbm_print_level >= 3)
    printf("    #Calling fsa_exists.\n");
  if (fsaptr->states->size < MAXUSHORT)
    return fsa_exists_short(fsaptr, op_table_type, destroy, tempfilename);
  else
    return fsa_exists_int(fsaptr, op_table_type, destroy, tempfilename);
}

static fsa *fsa_exists_short(fsa *fsaptr, storage_type op_table_type,
                             boolean destroy, char *tempfilename)
{
  int **table, ne, ngens, ns, dr, *fsarow, e, es, ef, nt, cstate, cs, csi, im,
      i, g1, len = 0, ct;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre,
      *ptr;
  boolean dense_ip, dense_op, got;
  short_hash_table ht;
  fsa *exists;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_exists_short.\n");
  if (!fsaptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_exists only applies to DFA's.\n");
    return 0;
  }

  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_exists: fsa must be 2-variable.\n");
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

  dense_ip = fsaptr->table->table_type == DENSE;
  dr = fsaptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  exists->num_initial = 1;
  tmalloc(exists->initial, int, 2);
  exists->initial[1] = 1;

  short_hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = fsaptr->initial[1];
  im = short_hash_locate(&ht, 1);
  if (im == -1)
    return 0;
  /* Each state in 'exists' will be represented as a subset of the set of states
   * of *fsaptr. The initial state is one-element set containing the initial
   * state of *fsaptr. A subset is an accept-state if it contains an accept
   * state of *fsaptr, or if one can get to an accept-state by applying elements
   * ($,x) where $ is the padding symbol.
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_exists.\n");
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
      cs = *ptr;
      for (e = es; e <= ef; e++) {
        csi = target(dense_ip, table, e, cs, dr);
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

fsa *fsa_exists_int(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                    char *tempfilename)
{
  int **table, ne, ngens, ns, dr, *fsarow, e, es, ef, nt, cstate, cs, csi, im,
      i, g1, len = 0, ct;
  int *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre, *ptr;
  boolean dense_ip, dense_op, got;
  hash_table ht;
  fsa *exists;
  FILE *tempfile;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_exists_short.\n");
  if (!fsaptr->flags[DFA]) {
    fprintf(stderr, "Error: fsa_exists only applies to DFA's.\n");
    return 0;
  }

  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr, "Error in fsa_exists: fsa must be 2-variable.\n");
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

  dense_ip = fsaptr->table->table_type == DENSE;
  dr = fsaptr->table->denserows;
  dense_op = op_table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  exists->num_initial = 1;
  tmalloc(exists->initial, int, 2);
  exists->initial[1] = 1;

  hash_init(&ht, FALSE, 0, 0, 0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = fsaptr->initial[1];
  im = hash_locate(&ht, 1);
  if (im == -1)
    return 0;
  /* Each state in 'exists' will be represented as a subset of the set of states
   * of *fsaptr. The initial state is one-element set containing the initial
   * state of *fsaptr. A subset is an accept-state if it contains an accept
   * state of *fsaptr, or if one can get to an accept-state by applying elements
   * ($,x) where $ is the padding symbol.
   * The subsets will be stored as variable-length records in the hash-table,
   * always in increasing order.
   */
  if (im != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_exists.\n");
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
      cs = *ptr;
      for (e = es; e <= ef; e++) {
        csi = target(dense_ip, table, e, cs, dr);
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

/* This constructs the two-variable fsa with base-alphabet *alphptr
 * that accepts (w_1,w_2) iff w_1 > w_2 in the shortlex ordering.
 * The shorter of the two words (if any) is padded with the padding-symbol.
 * Any occurrence of the padding symbol in mid-word leads to failure.
 * The table-type of the returned fsa will always be dense.
 */
fsa *fsa_greater_than(srec *alphptr)
{
  int ngens, ***dtable, i, j, p;
  fsa *greater_than;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_greater_than.\n");
  tmalloc(greater_than, fsa, 1);
  fsa_init(greater_than);

  ngens = alphptr->size;
  greater_than->alphabet->type = PRODUCT;
  greater_than->alphabet->size = (ngens + 1) * (ngens + 1) - 1;
  greater_than->alphabet->arity = 2;
  greater_than->alphabet->padding = '_';
  tmalloc(greater_than->alphabet->base, srec, 1);
  srec_copy(greater_than->alphabet->base, alphptr);

  greater_than->states->type = SIMPLE;
  greater_than->states->size = 4;
  /* state 1 = initial (fail state),
   * state 2 = words of equal length, lhs leading (accept state),
   * state 3 = words of equal length, rhs leading (fail state),
   * state 4 = eos on rhs (accept state),
   * state 0 = eos on lhs (dead state)
   */

  greater_than->num_initial = 1;
  tmalloc(greater_than->initial, int, 2);
  greater_than->initial[1] = 1;

  greater_than->num_accepting = 2;
  tmalloc(greater_than->accepting, int, 3);
  greater_than->accepting[1] = 2;
  greater_than->accepting[2] = 4;

  greater_than->flags[DFA] = TRUE;
  greater_than->flags[MINIMIZED] = TRUE;

  fsa_table_init(greater_than->table, 4, greater_than->alphabet->size);
  greater_than->table->printing_format = DENSE;
  greater_than->table->denserows = 0;
  if (fsa_table_dptr_init(greater_than) == -1)
    return 0;
  dtable = greater_than->table->table_data_dptr;
  p = ngens + 1;
  for (i = 1; i <= ngens; i++) {
    set_dense_dtarget(dtable, i, p, 1, 4);
    set_dense_dtarget(dtable, i, p, 2, 4);
    set_dense_dtarget(dtable, i, p, 3, 4);
    set_dense_dtarget(dtable, i, p, 4, 4);
    set_dense_dtarget(dtable, p, i, 1, 0);
    set_dense_dtarget(dtable, p, i, 2, 0);
    set_dense_dtarget(dtable, p, i, 3, 0);
    set_dense_dtarget(dtable, p, i, 4, 0);
    set_dense_dtarget(dtable, i, i, 1, 1);
    set_dense_dtarget(dtable, i, i, 2, 2);
    set_dense_dtarget(dtable, i, i, 3, 3);
    set_dense_dtarget(dtable, i, i, 4, 0);
  }
  for (i = 2; i <= ngens; i++)
    for (j = 1; j < i; j++) {
      set_dense_dtarget(dtable, i, j, 1, 2);
      set_dense_dtarget(dtable, j, i, 1, 3);
      set_dense_dtarget(dtable, i, j, 2, 2);
      set_dense_dtarget(dtable, j, i, 2, 2);
      set_dense_dtarget(dtable, i, j, 3, 3);
      set_dense_dtarget(dtable, j, i, 3, 3);
      set_dense_dtarget(dtable, i, j, 4, 0);
      set_dense_dtarget(dtable, j, i, 4, 0);
    }

  return greater_than;
}
