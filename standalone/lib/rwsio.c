/* file rwsio.c 12/12/94
 *
 * 9/1/98 change type of generators from char to `gen'
 * 14.3.95. introduced read_extra_kbinput.
 * 12. 12. 94. implemented format type c) (see below).
 *
 * This file contains input and output routines to read and write GAP syntax
 * files for the Knuth-Bendix program.
 * (from 18/1/95) other such routines are in the file rwsio2.c.
 * The basic functions, which are shared by the finite state automata programs,
 * are in the file miscio.c.
 * To help fast reading of large sets of words, two specials formats
 * for monoid generators are recognised:
 * a) single letter characters (usually 'A' will be inverse of 'a', etc.)
 * b) names of form <prefix><posint>, for a fixed prefix, where posint should
 *    be at most 255.
 * In all cases, rws.num_gens is the total number of monoid generators,
 * and the generator names are stored in the array rws.gen_name.
 * In case a), the variable kbm_algno is set equal to 0, and the array
 * kbm_gen_no is used to translate from rws.gen_name back to the gneerator
 * number.
 * In case b), kbm_algno is set equal to the length of <prefix> (which must be
 * strictly positive), and kbm_gen_no is defined on the <posint> suffixes to
 * get the generator number back from the rws.gen_name.
 * If neither case a) nor case b) applies then kbm_algno is set equal to -1,
 * and names are located in the list by a straightforward linear search - of
 * course this will be considerably slower for long lists of words.
 */

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "externals.h"

/* Functions defined in this file: */

/* We initialise the reduction automaton as an fsa type.
 * Some of its components like fsa.states->size are stored elsewhere
 * (as rws.num_states) and will only be updated at the end, before printing.
 */
void initialise_reduction_fsa(rewriting_system *rwsptr)
{
  int i;
  fsa_init(rwsptr->reduction_fsa);

  rwsptr->reduction_fsa->states->type = SIMPLE;
  rwsptr->reduction_fsa->states->size = 0;

  rwsptr->reduction_fsa->alphabet->type = IDENTIFIERS;
  rwsptr->reduction_fsa->alphabet->size = rwsptr->num_gens;
  tmalloc(rwsptr->reduction_fsa->alphabet->names, char *, rwsptr->num_gens + 1);
  for (i = 1; i <= rwsptr->num_gens; i++) {
    tmalloc(rwsptr->reduction_fsa->alphabet->names[i], char,
            stringlen(rwsptr->gen_name[i]) + 1);
    strcpy(rwsptr->reduction_fsa->alphabet->names[i], rwsptr->gen_name[i]);
  }

  rwsptr->reduction_fsa->num_initial = 1;
  tmalloc(rwsptr->reduction_fsa->initial, int, 2);
  rwsptr->reduction_fsa->initial[1] = 1;
  /* All states will be accepting, so rwsptr->reduction_fsa->num_accepting will
   * be equal to states.size.
   * This is manipulated as rws.num_states in the program, so we do not set it
   * until the end.
   */
  rwsptr->reduction_fsa->flags[DFA] = TRUE;
  rwsptr->reduction_fsa->flags[TRIM] = TRUE;
  rwsptr->reduction_fsa->flags[RWS] = TRUE;
  rwsptr->current_maxstates =
      rwsptr->maxstates == 0
          ? rwsptr->num_gens == 0 ? 1 : rwsptr->init_fsaspace / rwsptr->num_gens
          : rwsptr->maxstates;
  fsa_table_init(rwsptr->reduction_fsa->table, rwsptr->current_maxstates,
                 rwsptr->num_gens);
  rwsptr->reduction_fsa->table->printing_format = DENSE;
  tmalloc(rwsptr->preflen, int, rwsptr->current_maxstates + 1);
  tmalloc(rwsptr->prefno, int, rwsptr->current_maxstates + 1);
  build_quicktable(rwsptr);
}

/* This function is called after the generators and inverses have been read
 * in. We initialise the list of equations by making one equation
 * with lhs a*inv(a) and rhs identity for each generator a.
 * (These equations will probably be in the list that we read in as well,
 *  but that does not matter.)
 * We also initialise the finite state automaton that is used for reducing
 * words.
 */
void initialise_eqns(rewriting_system *rwsptr)
{
  int i;
  /* maxeqns, maxstates and maxreducelen should have been set by now */
  tmalloc(rwsptr->eqns, reduction_equation, rwsptr->maxeqns + 1);
  tmalloc(rwsptr->eqn_no, int, rwsptr->maxeqns + 1);
  tmalloc(rwsptr->testword1, gen, rwsptr->maxreducelen + 1);
  tmalloc(rwsptr->testword2, gen, rwsptr->maxreducelen + 1);
  rwsptr->num_eqns = 0;
  for (i = 1; i <= rwsptr->num_gens; i++)
    if (rwsptr->inv_of[i]) {
      rwsptr->num_eqns++;
      tmalloc(rwsptr->eqns[rwsptr->num_eqns].lhs, gen, 3);
      tmalloc(rwsptr->eqns[rwsptr->num_eqns].rhs, gen, 1);
      rwsptr->eqns[rwsptr->num_eqns].lhs[0] = i;
      rwsptr->eqns[rwsptr->num_eqns].lhs[1] = rwsptr->inv_of[i];
      rwsptr->eqns[rwsptr->num_eqns].lhs[2] = 0;
      rwsptr->eqns[rwsptr->num_eqns].rhs[0] = 0;
      rwsptr->eqns[rwsptr->num_eqns].done = TRUE;
    }
  rwsptr->num_inveqns = rwsptr->num_eqns;
  tmalloc(rwsptr->reduction_fsa, fsa, 1);
  initialise_reduction_fsa(rwsptr);
}

/* Read the initial reduction equations and install them. */
void read_eqns(FILE *rfile, boolean check, rewriting_system *rwsptr)
{
  int delim, i, ct, iv;
  gen *test1 = rwsptr->testword1, *test2 = rwsptr->testword2;
  check_next_char(rfile, '[');
  read_delim(rfile, &delim);
  if (delim == ']')
    return;
  if (delim != '[') {
    fprintf(stderr, "#Input error: '[' expected.\n");
    exit(1);
  }
  ct = 0;
  while (1) {
    ct++;
    read_word(rfile, test1, test1 + rwsptr->maxreducelen, &delim,
              rwsptr->gen_name, rwsptr->num_gens, check);
    if (delim != ',') {
      fprintf(stderr, "#Input error: ',' expected.\n");
      exit(1);
    }
    read_word(rfile, test2, test2 + rwsptr->maxreducelen, &delim,
              rwsptr->gen_name, rwsptr->num_gens, check);
    if (delim != ']') {
      fprintf(stderr, "#Input error: ']' expected.\n");
      exit(1);
    }
    if (genstrlen(test1) != 2 || genstrlen(test2) != 0 ||
        test1[1] != rwsptr->inv_of[test1[0]]) {
      /* this is  NOT an inverse equation, which we already know about. */
      if ((iv = insert(&(rwsptr->eqns[rwsptr->num_eqns + 1].lhs),
                       &(rwsptr->eqns[rwsptr->num_eqns + 1].rhs), rwsptr)) >
          0) {
        i = modify_table(rwsptr->num_eqns + 1, rwsptr);
        if (i == -1) {
          fprintf(stderr,
                  "#rwsptr->maxstates is too small. Cannot get started.\n");
          exit(1);
        }
        if (i == 1) {
          rwsptr->num_eqns++;
          if (rwsptr->num_eqns > rwsptr->maxeqns) {
            printf("#Too many equations - increase maxeqns to get started.\n");
            exit(1);
          }
          rwsptr->eqns[rwsptr->num_eqns].done = FALSE;
          rwsptr->eqn_no[ct] = rwsptr->num_eqns;
        }
      }
      else if (iv == -1) {
        fprintf(
            stderr,
            "#Error: input equation has lhs or rhs longer than limit set.\n");
        exit(1);
      }
    }

    read_delim(rfile, &delim);
    if (delim == ']')
      break;
    if (delim != ',') {
      fprintf(stderr, "#Input error: ',' expected.\n");
      exit(1);
    }
    check_next_char(rfile, '[');
  }
}

/* Read the list of equation numbers that have already been processed. */
void read_done(FILE *rfile, rewriting_system *rwsptr)
{
  int delim, i, j, n;
  check_next_char(rfile, '[');
  read_delim(rfile, &delim);
  if (delim == ']')
    return;
  if (delim != '[') {
    fprintf(stderr, "#Input error: '[' expected.\n");
    exit(1);
  }
  while (1) {
    read_int(rfile, &i, &delim);
    if (delim == '.') {
      check_next_char(rfile, '.');
      read_int(rfile, &j, &delim);
      for (n = i; n <= j; n++)
        if (n > 0 && n <= rwsptr->maxeqns && rwsptr->eqn_no[n] > 0)
          rwsptr->eqns[rwsptr->eqn_no[n]].done = TRUE;
    }
    else if (i > 0 && i <= rwsptr->maxeqns && rwsptr->eqn_no[i] > 0)
      rwsptr->eqns[rwsptr->eqn_no[i]].done = TRUE;

    read_delim(rfile, &delim);
    if (delim == ']')
      break;
    if (delim != ',') {
      fprintf(stderr, "#Input error: ',' expected.\n");
      exit(1);
    }
    check_next_char(rfile, '[');
  }
}

/* This function reads the full input for the Knuth-Bendix program
 * from the file rfile, which should already be open.
 * The rewriting system is read into the externally defined rwsptr->
 * If check is true, then the words in the equations are checked for
 * validity - this could make input slower if there are many equations
 */
void read_kbinput(FILE *rfile, boolean check, rewriting_system *rwsptr)
{
  int delim, n, m;
  boolean isRWS = FALSE, seengens = FALSE, seeneqns = FALSE;

  read_ident(rfile, rwsptr->name, &delim, FALSE);
  if (delim != ':') {
    fprintf(stderr, "#Input error: file must contain a record assignment\n");
    exit(1);
  }
  check_next_char(rfile, '=');
  read_ident(rfile, kbm_buffer, &delim, FALSE);
  if (delim != '(' || strcmp(kbm_buffer, "rec") != 0) {
    fprintf(stderr, "#Input error: file must contain a record assignment\n");
    exit(1);
  }

  /* main loop reading the fields of the record follows. */
  do {
    read_ident(rfile, kbm_buffer, &delim, FALSE);
    if (delim != ':') {
      fprintf(stderr, "#Input error: bad record field assignment\n");
      exit(1);
    }
    check_next_char(rfile, '=');
    if (strcmp(kbm_buffer, "isRWS") == 0) {
      isRWS = TRUE;
      read_ident(rfile, kbm_buffer, &delim, FALSE);
      if (strcmp(kbm_buffer, "true") != 0) {
        fprintf(stderr, "#Input error: isRWS field must equal \"true\"\n");
        exit(1);
      }
    }
    else if (strcmp(kbm_buffer, "isConfluent") == 0) {
      read_ident(rfile, kbm_buffer, &delim, FALSE);
      if (strcmp(kbm_buffer, "true") == 0 && !rwsptr->resume_with_orig) {
        fprintf(stderr, "#System is already confluent!\n");
        exit(0);
      }
    }
    else if (strcmp(kbm_buffer, "tidyint") == 0) {
      read_int(rfile, &n, &delim);
      /* Parameters on the command-line override those in the input file */
      if (!rwsptr->tidyintset && n > 0)
        rwsptr->tidyint = n;
    }
    else if (strcmp(kbm_buffer, "maxeqns") == 0) {
      read_int(rfile, &n, &delim);
      if (rwsptr->inv_of != 0) {
        fprintf(
            stderr,
            "#Input error: 'maxeqns' field must precede 'inverses' field\n");
        exit(1);
      }
      /* We will exclude ridiculously small values of limit parameters. */
      if (!rwsptr->maxeqnsset && !rwsptr->resume_with_orig && n > 16)
        rwsptr->maxeqns = n;
    }
    else if (strcmp(kbm_buffer, "maxstates") == 0) {
      read_int(rfile, &n, &delim);
      if (rwsptr->inv_of != 0) {
        fprintf(
            stderr,
            "#Input error: 'maxstates' field must precede 'inverses' field\n");
        exit(1);
      }
      if (!rwsptr->maxstatesset && n > 128)
        rwsptr->maxstates = n;
    }
    else if (strcmp(kbm_buffer, "confnum") == 0) {
      read_int(rfile, &n, &delim);
      if (!rwsptr->confnumset && n > 0)
        rwsptr->confnum = n;
    }
    else if (strcmp(kbm_buffer, "sorteqns") == 0) {
      read_ident(rfile, kbm_buffer, &delim, FALSE);
      if (strcmp(kbm_buffer, "true") == 0)
        rwsptr->sorteqns = TRUE;
    }
    else if (strcmp(kbm_buffer, "maxoplen") == 0) {
      read_int(rfile, &n, &delim);
      if (rwsptr->maxoplen == 0 && n >= 0) {
        rwsptr->sorteqns = TRUE;
        rwsptr->maxoplen = n;
      }
    }
    else if (strcmp(kbm_buffer, "maxstoredlen") == 0) {
      check_next_char(rfile, '[');
      read_int(rfile, &n, &delim);
      if (delim != ',') {
        fprintf(stderr, "#Input error:  format of maxstoredlen field wrong\n");
        exit(1);
      }
      read_int(rfile, &m, &delim);
      if (delim != ']') {
        fprintf(stderr, "#Input error:  format of maxstoredlen field wrong\n");
        exit(1);
      }
      if (n > 0 && m > 0 && rwsptr->maxlenleft == 0 &&
          rwsptr->maxlenright == 0) {
        rwsptr->maxlenleft = n;
        rwsptr->maxlenright = m;
      }
      read_delim(rfile, &delim);
    }
    else if (strcmp(kbm_buffer, "maxoverlaplen") == 0) {
      read_int(rfile, &n, &delim);
      if (n > 0)
        rwsptr->maxoverlaplen = n;
    }
    else if (strcmp(kbm_buffer, "maxwdiffs") == 0) {
      read_int(rfile, &n, &delim);
      if (!rwsptr->maxwdiffset && n > 16)
        rwsptr->maxwdiffs = n;
    }
    else if (strcmp(kbm_buffer, "maxreducelen") == 0) {
      read_int(rfile, &n, &delim);
      if (n > 4096 && !rwsptr->maxreducelenset)
        rwsptr->maxreducelen = n;
    }
    else if (strcmp(kbm_buffer, "silent") == 0) {
      read_ident(rfile, kbm_buffer, &delim, FALSE);
      if (!rwsptr->silentset && !rwsptr->verboseset &&
          strcmp(kbm_buffer, "true") == 0)
        kbm_print_level = 0;
    }
    else if (strcmp(kbm_buffer, "verbose") == 0) {
      read_ident(rfile, kbm_buffer, &delim, FALSE);
      if (!rwsptr->silentset && !rwsptr->verboseset &&
          strcmp(kbm_buffer, "true") == 0)
        kbm_print_level = 2;
    }
    else if (strcmp(kbm_buffer, "veryVerbose") == 0) {
      read_ident(rfile, kbm_buffer, &delim, FALSE);
      if (!rwsptr->silentset && !rwsptr->verboseset &&
          strcmp(kbm_buffer, "true") == 0)
        kbm_print_level = 3;
    }
    else if (strcmp(kbm_buffer, "RabinKarp") == 0) {
      check_next_char(rfile, '[');
      read_int(rfile, &n, &delim);
      if (delim != ',') {
        fprintf(stderr, "#Input error:  format of maxstoredlen field wrong\n");
        exit(1);
      }
      read_int(rfile, &m, &delim);
      if (delim != ']') {
        fprintf(stderr, "#Input error:  format of maxstoredlen field wrong\n");
        exit(1);
      }
      if (n > 0 && m > 0 && rwsptr->rkminlen == 0 && rwsptr->rkmineqns == 0) {
        rwsptr->rkminlen = n;
        rwsptr->rkmineqns = m;
      }
      read_delim(rfile, &delim);
    }
    else if (strcmp(kbm_buffer, "ordering") == 0) {
      read_string(rfile, kbm_buffer, &delim);
      if (!rwsptr->orderingset) {
        if (strcmp(kbm_buffer, "shortlex") == 0)
          rwsptr->ordering = SHORTLEX;
        else if (strcmp(kbm_buffer, "recursive") == 0)
          rwsptr->ordering = RECURSIVE;
        else if (strcmp(kbm_buffer, "rt_recursive") == 0)
          rwsptr->ordering = RT_RECURSIVE;
        else if (strcmp(kbm_buffer, "wtlex") == 0)
          rwsptr->ordering = WTLEX;
        else if (strcmp(kbm_buffer, "wreathprod") == 0)
          rwsptr->ordering = WREATHPROD;
        else if (strcmp(kbm_buffer, "none") == 0)
          rwsptr->ordering = NONE;
        else {
          fprintf(stderr, "#Input error: invalid string for ordering field\n");
          exit(1);
        }
      }
    }
    else if (strcmp(kbm_buffer, "generatorOrder") == 0) {
      read_gens(rfile, rwsptr);
      process_names(rwsptr->gen_name, rwsptr->num_gens);
      seengens = TRUE;
      read_delim(rfile, &delim);
    }
    else if (strcmp(kbm_buffer, "weight") == 0) {
      if (rwsptr->ordering != WTLEX)
        skip_gap_expression(rfile, &delim);
      else {
        if (!seengens) {
          fprintf(stderr,
                  "#Input error: generator field must precede weight field\n");
          exit(1);
        }
        tmalloc(rwsptr->weight, int, rwsptr->num_gens + 1);
        check_next_char(rfile, '[');
        for (n = 1; n <= rwsptr->num_gens; n++) {
          read_int(rfile, rwsptr->weight + n, &delim);
          if (rwsptr->weight[n] <= 0) {
            fprintf(stderr,
                    "#Input error: weights must be positive integers.\n");
            exit(1);
          }
          if ((n < rwsptr->num_gens && delim != ',') ||
              (n == rwsptr->num_gens && delim != ']')) {
            fprintf(stderr, "#Input error: ',' or ']' expected.\n");
            exit(1);
          }
        }
        read_delim(rfile, &delim);
      }
    }
    else if (strcmp(kbm_buffer, "level") == 0) {
      if (rwsptr->ordering != WREATHPROD)
        skip_gap_expression(rfile, &delim);
      else {
        if (!seengens) {
          fprintf(stderr,
                  "#Input error: generator field must precede level field\n");
          exit(1);
        }
        tmalloc(rwsptr->level, int, rwsptr->num_gens + 1);
        check_next_char(rfile, '[');
        for (n = 1; n <= rwsptr->num_gens; n++) {
          read_int(rfile, rwsptr->level + n, &delim);
          if (rwsptr->level[n] <= 0) {
            fprintf(stderr,
                    "#Input error: levels must be positive integers.\n");
            exit(1);
          }
          if ((n < rwsptr->num_gens && delim != ',') ||
              (n == rwsptr->num_gens && delim != ']')) {
            fprintf(stderr, "#Input error: ',' or ']' expected.\n");
            exit(1);
          }
        }
        read_delim(rfile, &delim);
      }
    }
    else if (strcmp(kbm_buffer, "inverses") == 0) {
      if (!seengens) {
        fprintf(stderr,
                "#Input error: generator field must precede inverses field\n");
        exit(1);
      }
      read_inverses(rfile, rwsptr);
      initialise_eqns(rwsptr);
      read_delim(rfile, &delim);
    }
    else if (strcmp(kbm_buffer, "equations") == 0) {
      if (rwsptr->ordering == WTLEX && rwsptr->weight == 0) {
        fprintf(stderr,
                "Input error: weight field missing (for this ordering).\n");
        exit(1);
      }
      if (rwsptr->ordering == WREATHPROD && rwsptr->level == 0) {
        fprintf(stderr,
                "Input error: level field missing (for this ordering).\n");
        exit(1);
      }
      if (rwsptr->num_gens != 0 && rwsptr->inv_of == 0) {
        fprintf(stderr, "#Input error: record must have 'inverses' field\n");
        exit(1);
      }
      /* Set separator in cosets case. */
      if (rwsptr->cosets)
        set_separator(rwsptr);
      read_eqns(rfile, check, rwsptr);
      read_delim(rfile, &delim);
      seeneqns = TRUE;
    }
    else if (strcmp(kbm_buffer, "done") == 0) {
      if (!seeneqns) {
        fprintf(stderr,
                "#Input error: 'equations' field must precede 'done' field\n");
        exit(1);
      }
      read_done(rfile, rwsptr);
      read_delim(rfile, &delim);
    }
    else {
      printf("#Warning: Unknown record field: %s\n", kbm_buffer);
      skip_gap_expression(rfile, &delim);
    }
    if (delim != ')' && delim != ',') {
      fprintf(
          stderr,
          "#Input error:  field %s assignment must end ',' or ')', not %c\n",
          kbm_buffer, delim);
      exit(1);
    }
  } while (delim != ')');

  check_next_char(rfile, ';');
  if (!isRWS) {
    fprintf(stderr, "#Input error: record must have 'isRWS' field\n");
    exit(1);
  }
  if (rwsptr->num_gens != 0 && rwsptr->inv_of == 0) {
    fprintf(stderr, "#Input error: record must have 'inverses' field\n");
    exit(1);
  }
  tfree(rwsptr->eqn_no);
}

/* This function reads the additional equations (from the original
 * input file), when these are to be re-adjoined to the output equations
 * (which is what happens under the -ro option of kbprog).
 * The file rfile should already be open.
 * If check is true, then the words in the equations are checked for
 * validity
 */
void read_extra_kbinput(FILE *rfile, boolean check, rewriting_system *rwsptr)
{
  int delim;

  read_ident(rfile, rwsptr->name, &delim, FALSE);
  if (delim != ':') {
    fprintf(stderr, "#Input error: file must contain a record assignment\n");
    exit(1);
  }
  check_next_char(rfile, '=');
  read_ident(rfile, kbm_buffer, &delim, FALSE);
  if (delim != '(' || strcmp(kbm_buffer, "rec") != 0) {
    fprintf(stderr, "#Input error: file must contain a record assignment\n");
    exit(1);
  }

  /* main loop reading the fields of the record follows. */
  do {
    read_ident(rfile, kbm_buffer, &delim, FALSE);
    if (delim != ':') {
      fprintf(stderr, "#Input error: bad record field assignment\n");
      exit(1);
    }
    check_next_char(rfile, '=');
    if (strcmp(kbm_buffer, "equations") == 0) {
      tmalloc(rwsptr->eqn_no, int, rwsptr->maxeqns + 1);
      read_eqns(rfile, check, rwsptr);
      read_delim(rfile, &delim);
    }
    else
      skip_gap_expression(rfile, &delim);
  } while (delim != ')');
  check_next_char(rfile, ';');
  tfree(rwsptr->eqn_no);
}


/* This function prints the output from the KB program to the file named
 * wfile, which should already be open for writing.
 * Note that the rewriting system rws and its reduction-fsa are
 * defined externally.
 * This starts with the rewriting system, in the same format as the
 * input, and is followed by a new field, the reduction automaton.
 * The fsa function fsa_print is used to print this.
 */
void print_kboutput(FILE *wfile, rewriting_system *rwsptr)
{
  int i, i1, n;
  boolean in, first;

  sprintf(kbm_buffer, "%s := rec(", rwsptr->name);
  printbuffer(wfile);
  add_to_buffer(16, "isRWS");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := true,");
  printbuffer(wfile);

  add_to_buffer(16, "isConfluent");
  if (rwsptr->confluent)
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := true,");
  else
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := false,");
  printbuffer(wfile);

  if (rwsptr->confluent) {
    /* Since the number of equations won't be increased again, we specify this
     * number here as the maxeqns component. This is useful for programs that
     * re-read the system later.
     */
    add_to_buffer(16, "maxeqns");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := %d,", rwsptr->num_eqns);
    printbuffer(wfile);
  }

  add_to_buffer(16, "generatorOrder");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
  for (i = 1; i <= rwsptr->num_gens; i++) {
    if (i == 1 ||
        stringlen(kbm_buffer) + stringlen(rwsptr->gen_name[i]) <= 76) {
      if (i > 1)
        add_to_buffer(0, ",");
      sprintf(kbm_buffer + stringlen(kbm_buffer), "%s", rwsptr->gen_name[i]);
    }
    else {
      add_to_buffer(0, ",");
      printbuffer(wfile);
      add_to_buffer(21, "");
      sprintf(kbm_buffer + stringlen(kbm_buffer), "%s", rwsptr->gen_name[i]);
    }
  }
  add_to_buffer(0, "],");
  printbuffer(wfile);

  add_to_buffer(16, "ordering");
  if (rwsptr->ordering == SHORTLEX)
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"shortlex\",");
  else if (rwsptr->ordering == RECURSIVE)
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"recursive\",");
  else if (rwsptr->ordering == RT_RECURSIVE)
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"rt_recursive\",");
  else if (rwsptr->ordering == WTLEX)
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"wtlex\",");
  else if (rwsptr->ordering == WREATHPROD)
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"wreathprod\",");
  else if (rwsptr->ordering == NONE)
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"none\",");
  printbuffer(wfile);

  if (rwsptr->ordering == WTLEX) {
    add_to_buffer(16, "weight");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
    for (i = 1; i <= rwsptr->num_gens; i++) {
      if (i > 1)
        add_to_buffer(0, ",");
      sprintf(kbm_buffer + stringlen(kbm_buffer), "%d", rwsptr->weight[i]);
    }
    add_to_buffer(0, "],");
    printbuffer(wfile);
  }

  if (rwsptr->ordering == WREATHPROD) {
    add_to_buffer(16, "level");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
    for (i = 1; i <= rwsptr->num_gens; i++) {
      if (i > 1)
        add_to_buffer(0, ",");
      sprintf(kbm_buffer + stringlen(kbm_buffer), "%d", rwsptr->level[i]);
    }
    add_to_buffer(0, "],");
    printbuffer(wfile);
  }

  add_to_buffer(16, "inverses");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
  for (i = 1; i <= rwsptr->num_gens; i++) {
    if (i > 1)
      add_to_buffer(0, ",");
    if (rwsptr->inv_of[i] != 0) {
      if (stringlen(kbm_buffer) +
              stringlen(rwsptr->gen_name[rwsptr->inv_of[i]]) >
          76) {
        printbuffer(wfile);
        add_to_buffer(21, "");
      }
      sprintf(kbm_buffer + stringlen(kbm_buffer), "%s",
              rwsptr->gen_name[rwsptr->inv_of[i]]);
    }
  }
  add_to_buffer(0, "],");
  printbuffer(wfile);

  add_to_buffer(16, "equations");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
  for (i = 1; i <= rwsptr->num_eqns; i++) {
    printbuffer(wfile);
    add_to_buffer(10, "[");
    n = add_word_to_buffer(wfile, rwsptr->eqns[i].lhs, rwsptr->gen_name);
    sprintf(kbm_buffer + stringlen(kbm_buffer), ",");
    if (n > 0 || stringlen(kbm_buffer) > 40) {
      printbuffer(wfile);
      add_to_buffer(12, "");
    }
    add_word_to_buffer(wfile, rwsptr->eqns[i].rhs, rwsptr->gen_name);
    if (i == rwsptr->num_eqns)
      sprintf(kbm_buffer + stringlen(kbm_buffer), "]");
    else
      sprintf(kbm_buffer + stringlen(kbm_buffer), "],");
  }
  printbuffer(wfile);
  if (rwsptr->confluent)
    add_to_buffer(8, "]");
  else
    add_to_buffer(9, "],");
  printbuffer(wfile);

  if (!rwsptr->confluent) {
    /* print the list of equations that have been processed, in case the run is
     * continued later.
     */
    add_to_buffer(16, "done");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
    first = TRUE;
    in = FALSE;
    for (i = 1; i <= rwsptr->num_eqns + 1; i++) {
      if (i <= rwsptr->num_eqns && !in && rwsptr->eqns[i].done) {
        in = TRUE;
        i1 = i;
      }
      else if (in && (i > rwsptr->num_eqns || !rwsptr->eqns[i].done)) {
        in = FALSE;
        if (!first)
          sprintf(kbm_buffer + stringlen(kbm_buffer), ",");
        printbuffer(wfile);
        first = FALSE;
        add_to_buffer(10, "[");
        if (i == i1 + 1)
          sprintf(kbm_buffer + stringlen(kbm_buffer), "%d]", i1);
        else
          sprintf(kbm_buffer + stringlen(kbm_buffer), "%d..%d]", i1, i - 1);
      }
    }
    printbuffer(wfile);
    add_to_buffer(8, "]");
    printbuffer(wfile);
  }

  sprintf(kbm_buffer, ");");
  printbuffer(wfile);
}

/* This function prints the word-difference from the KB program to the file
 * named wfile, which should already be open for writing.
 * The fsa function fsa_print is used to print this.
 */
void print_wdoutput(FILE *wfile, char *suffix, rewriting_system *rwsptr)
{
  char diffname[128];

  strcpy(diffname, rwsptr->name);
  strcat(diffname, suffix);
  fsa_print(wfile, rwsptr->wd_fsa, diffname);
}
