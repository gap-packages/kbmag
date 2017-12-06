/* file fsaio.c - 11. 10. 94.
 * 9/1/98. Change generator type from char to `gen'.
 * 1.5.96.  - adjusted kbm_type_names, srec_read and srec_print to deal with
 *            srec type "list of Integers".
 * This file contains io-routines for manipulating finite state automata
 * They can deal with both deterministic and non-deterministic automata,
 * but the functions in fsa.c currently only deal with dfa's.
 *
 * 13.9.95. - wrote in code to handle srec type "list of words"
 * 5.12.94. - changes for sparse storage type with some dense rows.
 * 17.11.94. Added parts to do with labeled srec type.
 */

#define MAXWORDLEN 65535

#include <stdlib.h>
#include "defs.h"
#include "fsa.h"
#include "externals.h"

char *kbm_type_names[] = {"simple",        "identifiers",      "words",
                          "list of words", "list of integers", "strings",
                          "labeled",       "product"};
char *kbm_flag_names[] = {"DFA", "NFA",        "MIDFA", "minimized",
                          "BFS", "accessible", "trim",  "RWS"};
static gen *wbuffer; /* used only for calls of read_word - this can
                      * be allocated temporarily.
                      */

/* Functions defined in this file: */


/* Print the set record *srptr. Follows corresponding GAP routine.
 * Currently, rather arbitrarily, identifiers and strings names are
 * printed in dense format, and words and lists of words in sparse format.
 */
void srec_print(FILE *wfile, srec *srptr, char *name, int offset,
                char *endstring)

{
  int ct, j, l;
  srec sr;
  boolean first;

  sr = *srptr;
  *kbm_buffer = '\0';
  if (stringlen(name) == 0)
    add_to_buffer(0, "rec(");
  else {
    add_to_buffer(12 + offset, name);
    add_to_buffer(0, " := rec(");
  }

  printbuffer(wfile);
  add_to_buffer(16 + offset, "type");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"%s\",",
          kbm_type_names[sr.type]);
  printbuffer(wfile);

  add_to_buffer(16 + offset, "size");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := %d", sr.size);
  if (sr.type != SIMPLE)
    add_to_buffer(0, ",");
  printbuffer(wfile);

  if (sr.type == PRODUCT) {
    add_to_buffer(16 + offset, "arity");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := %d,", sr.arity);
    printbuffer(wfile);

    add_to_buffer(16 + offset, "padding");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := %c,", sr.padding);
    printbuffer(wfile);

    srec_print(wfile, sr.base, "base", offset + 4, " ");
  }

  else if (sr.type == IDENTIFIERS) {
    add_to_buffer(16 + offset, "format");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"dense\",");
    printbuffer(wfile);

    add_to_buffer(16 + offset, "names");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
    ct = 1;
    while (ct <= sr.size) {
      if (ct == 1 || stringlen(kbm_buffer) + stringlen(sr.names[ct]) <= 76) {
        if (ct > 1)
          add_to_buffer(0, ",");
        sprintf(kbm_buffer + stringlen(kbm_buffer), "%s", sr.names[ct]);
      }
      else {
        add_to_buffer(0, ",");
        printbuffer(wfile);
        add_to_buffer(21 + offset, "");
        sprintf(kbm_buffer + stringlen(kbm_buffer), "%s", sr.names[ct]);
      }
      ct++;
    }
    add_to_buffer(0, "]");
    printbuffer(wfile);
  }

  else if (sr.type == STRINGS) {
    add_to_buffer(16 + offset, "format");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"dense\",");
    printbuffer(wfile);

    add_to_buffer(16 + offset, "names");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
    ct = 1;
    while (ct <= sr.size) {
      if (ct == 1 ||
          stringlen(kbm_buffer) + stringlen(sr.names[ct]) + 2 <= 76) {
        if (ct > 1)
          add_to_buffer(0, ",");
        sprintf(kbm_buffer + stringlen(kbm_buffer), "\"%s\"", sr.names[ct]);
      }
      else {
        add_to_buffer(0, ",");
        printbuffer(wfile);
        add_to_buffer(21 + offset, "");
        sprintf(kbm_buffer + stringlen(kbm_buffer), "\"%s\"", sr.names[ct]);
      }
      ct++;
    }
    add_to_buffer(0, "]");
    printbuffer(wfile);
  }

  else if (sr.type == WORDS || sr.type == LISTOFWORDS) {
    add_to_buffer(16 + offset, "alphabet");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
    ct = 1;
    while (ct <= sr.alphabet_size) {
      if (ct == 1 || stringlen(kbm_buffer) + stringlen(sr.alphabet[ct]) <= 76) {
        if (ct > 1)
          add_to_buffer(0, ",");
        sprintf(kbm_buffer + stringlen(kbm_buffer), "%s", sr.alphabet[ct]);
      }
      else {
        add_to_buffer(0, ",");
        printbuffer(wfile);
        add_to_buffer(21 + offset, "");
        sprintf(kbm_buffer + stringlen(kbm_buffer), "%s", sr.alphabet[ct]);
      }
      ct++;
    }
    add_to_buffer(0, "],");
    printbuffer(wfile);

    add_to_buffer(16 + offset, "format");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"sparse\",");
    printbuffer(wfile);

    add_to_buffer(16 + offset, "names");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
    printbuffer(wfile);
    for (ct = 1; ct <= sr.size; ct++) {
      /* If the set is large, we will format less nicely, to save space. */
      if (sr.size > 128)
        add_to_buffer(0, "\t");
      else
        add_to_buffer(12 + offset, "");
      sprintf(kbm_buffer + stringlen(kbm_buffer), "[%d,", ct);
      if (sr.type == WORDS)
        add_word_to_buffer(wfile, sr.words[ct], sr.alphabet);
      else {
        add_to_buffer(0, "[");
        j = 0;
        while (sr.wordslist[ct][j]) {
          if (j > 0)
            add_to_buffer(0, ",");
          if (stringlen(kbm_buffer) > 68) {
            printbuffer(wfile);
            if (sr.size > 128)
              add_to_buffer(0, "\t      ");
            else
              add_to_buffer(18 + offset, "");
          }
          add_word_to_buffer(wfile, sr.wordslist[ct][j], sr.alphabet);
          j++;
        }
        add_to_buffer(0, "]");
      }
      if (ct == sr.size)
        add_to_buffer(0, "]");
      else
        add_to_buffer(0, "],");
      printbuffer(wfile);
    }
    add_to_buffer(11 + offset, "]");
    printbuffer(wfile);
  }

  else if (sr.type == LISTOFINTS) {
    add_to_buffer(16 + offset, "format");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"sparse\",");
    printbuffer(wfile);

    add_to_buffer(16 + offset, "names");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
    printbuffer(wfile);
    for (ct = 1; ct <= sr.size; ct++) {
      /* If the set is large, we will format less nicely, to save space. */
      if (sr.size > 128)
        add_to_buffer(0, "\t");
      else
        add_to_buffer(12 + offset, "");
      sprintf(kbm_buffer + stringlen(kbm_buffer), "[%d,", ct);
      add_to_buffer(0, "[");
      l = sr.intlist[ct][0];
      for (j = 1; j <= l; j++) {
        if (j > 1)
          add_to_buffer(0, ",");
        if (stringlen(kbm_buffer) > 74) {
          printbuffer(wfile);
          if (sr.size > 128)
            add_to_buffer(0, "\t      ");
          else
            add_to_buffer(18 + offset, "");
        }
        sprintf(kbm_buffer + stringlen(kbm_buffer), "%d", sr.intlist[ct][j]);
      }
      add_to_buffer(0, "]");
      if (ct == sr.size)
        add_to_buffer(0, "]");
      else
        add_to_buffer(0, "],");
      printbuffer(wfile);
    }
    add_to_buffer(11 + offset, "]");
    printbuffer(wfile);
  }

  else if (sr.type == LABELED) {
    srec_print(wfile, sr.labels, "labels", offset + 4, ",");

    add_to_buffer(16 + offset, "format");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"sparse\",");
    printbuffer(wfile);

    add_to_buffer(16 + offset, "setToLabels");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
    printbuffer(wfile);
    first = TRUE;
    for (ct = 1; ct <= sr.size; ct++)
      if (sr.setToLabels[ct] != 0) {
        if (first)
          first = FALSE;
        else {
          strcat(kbm_buffer, ",");
          printbuffer(wfile);
        }
        if (sr.size <= 128)
          add_to_buffer(21 + offset, "");
        else
          add_to_buffer(0, "\t");
        sprintf(kbm_buffer + stringlen(kbm_buffer), "[%d,%d]", ct,
                sr.setToLabels[ct]);
      }
    printbuffer(wfile);
    add_to_buffer(21 + offset, "]");
    printbuffer(wfile);
  }

  if (stringlen(name) == 0)
    add_to_buffer(0, ")");
  else
    add_to_buffer(12 + offset, ")");
  add_to_buffer(0, endstring);
  printbuffer(wfile);
}

/* Print the table record *tableptr. */
void table_print(FILE *wfile, table_struc *tableptr, char *name, int offset,
                 char *endstring, int ns, int ne)

{
  int **table, ct, g, i, k, nl, dr, *ptr, *ptre;
  boolean dense, densepf, first, firstg;

  table = tableptr->table_data_ptr;
  dense = tableptr->table_type == DENSE;
  densepf = tableptr->printing_format == DENSE;
  dr = tableptr->denserows;

  *kbm_buffer = '\0';
  if (stringlen(name) == 0)
    add_to_buffer(0, "rec(");
  else {
    add_to_buffer(12 + offset, name);
    add_to_buffer(0, " := rec(");
  }

  printbuffer(wfile);

  /* Calculate number of nonzero transitions - this ought to be stored in
   * tableptr->numTransitions, but we won't rely on that (unless the table
   * is stored externally).
   */

  add_to_buffer(offset + 16, "format");
  if (densepf)
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"dense deterministic\",");
  else
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"sparse\",");
  printbuffer(wfile);

  if (tableptr->filename == 0) {
    if (dense) {
      ct = 0;
      for (g = 1; g <= ne; g++)
        for (i = 1; i <= ns; i++)
          if (target(dense, table, g, i, dr) != 0)
            ct++;
    }
    else {
      ct = 0;
      for (g = 1; g <= ne; g++)
        for (i = 1; i <= dr; i++)
          if (target(dense, table, g, i, dr) != 0)
            ct++;
      if (dr < ns)
        ct += (table[ns + 1] - table[dr + 1]) / 2;
    }
    tableptr->numTransitions = ct;
  }

  add_to_buffer(offset + 16, "numTransitions");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := %d,",
          tableptr->numTransitions);
  printbuffer(wfile);

  if (tableptr->filename) {
    add_to_buffer(offset + 16, "filename");
    sprintf(kbm_buffer + stringlen(kbm_buffer), " := \"%s\"",
            tableptr->filename);
    printbuffer(wfile);
    if (stringlen(name) == 0)
      add_to_buffer(0, ")");
    else
      add_to_buffer(12 + offset, ")");
    add_to_buffer(0, endstring);
    printbuffer(wfile);
    return;
  }

  add_to_buffer(offset + 16, "transitions");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
  if (ns == 0 || ns > 128)
    printbuffer(wfile);
  first = TRUE;
  for (i = 1; i <= ns; i++) {
    if (!first && ns <= 128)
      add_to_buffer(offset + 21, "");
    sprintf(kbm_buffer + stringlen(kbm_buffer), "[");
    first = FALSE;
    if (!dense && !densepf && i > dr) {
      /* In this case we can print directly */
      ptr = table[i];
      ptre = table[i + 1];
      firstg = TRUE;
      while (ptr < ptre) {
        if (!firstg)
          sprintf(kbm_buffer + stringlen(kbm_buffer), ",");
        firstg = FALSE;
        g = *(ptr++);
        k = *(ptr++);
        nl = int_len(k) + 3 + int_len((int)g);
        if (stringlen(kbm_buffer) + nl >= 76) {
          printbuffer(wfile);
          /* If the state-set is large, we format less nicely to save space. */
          if (ns <= 128)
            add_to_buffer(offset + 22, "");
          else
            add_to_buffer(0, " ");
        }
        sprintf(kbm_buffer + stringlen(kbm_buffer), "[%d,%d]", g, k);
      }
    }
    else {
      firstg = TRUE;
      for (g = 1; g <= ne; g++) {
        k = target(dense, table, g, i, dr);
        if (densepf || k != 0) {
          if (!firstg)
            sprintf(kbm_buffer + stringlen(kbm_buffer), ",");
          firstg = FALSE;
          nl = densepf ? int_len(k) : int_len(k) + 3 + int_len((int)g);
          if (stringlen(kbm_buffer) + nl >= 76) {
            printbuffer(wfile);
            if (ns <= 128)
              add_to_buffer(offset + 22, "");
            else
              add_to_buffer(0, " ");
          }
          if (densepf)
            sprintf(kbm_buffer + stringlen(kbm_buffer), "%d", k);
          else
            sprintf(kbm_buffer + stringlen(kbm_buffer), "[%d,%d]", g, k);
        }
      }
    }
    if (i < ns)
      sprintf(kbm_buffer + stringlen(kbm_buffer), "],");
    else
      sprintf(kbm_buffer + stringlen(kbm_buffer), "] ");
    if (tableptr->comment_state_numbers)
      sprintf(kbm_buffer + stringlen(kbm_buffer), "#%d", i);
    printbuffer(wfile);
  }
  add_to_buffer(offset + 20, "");
  sprintf(kbm_buffer + stringlen(kbm_buffer), "]");
  printbuffer(wfile);

  if (stringlen(name) == 0)
    add_to_buffer(0, ")");
  else
    add_to_buffer(12 + offset, ")");
  add_to_buffer(0, endstring);
  printbuffer(wfile);
}

void fsa_print(FILE *wfile, fsa *fsaptr, char *name)
{
  int i, ns, ne;
  boolean first;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_print.\n");
  ns = fsaptr->states->size;
  ne = fsaptr->alphabet->size;

  *kbm_buffer = '\0';
  if (stringlen(name) == 0)
    add_to_buffer(0, "rec(");
  else {
    sprintf(kbm_buffer, "%s := rec(", name);
  }
  printbuffer(wfile);

  add_to_buffer(16, "isFSA");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := true,");
  printbuffer(wfile);

  srec_print(wfile, fsaptr->alphabet, "alphabet", 4, ",");

  srec_print(wfile, fsaptr->states, "states", 4, ",");

  add_to_buffer(16, "flags");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
  first = TRUE;
  for (i = 0; i < num_kbm_flag_strings; i++)
    if (fsaptr->flags[i]) {
      if (!first)
        sprintf(kbm_buffer + stringlen(kbm_buffer), ",");
      first = FALSE;
      sprintf(kbm_buffer + stringlen(kbm_buffer), "\"%s\"", kbm_flag_names[i]);
    }
  sprintf(kbm_buffer + stringlen(kbm_buffer), "],");
  printbuffer(wfile);

  add_to_buffer(16, "initial");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
  if (ns > 1 && ns == fsaptr->num_initial)
    sprintf(kbm_buffer + stringlen(kbm_buffer), "1..%d", fsaptr->states->size);
  else {
    for (i = 1; i <= fsaptr->num_initial; i++) {
      if (i > 1)
        sprintf(kbm_buffer + stringlen(kbm_buffer), ",");
      if (stringlen(kbm_buffer) + int_len(fsaptr->initial[i]) > 76) {
        printbuffer(wfile);
        add_to_buffer(21, "");
      }
      sprintf(kbm_buffer + stringlen(kbm_buffer), "%d", fsaptr->initial[i]);
    }
  }
  sprintf(kbm_buffer + stringlen(kbm_buffer), "],");
  printbuffer(wfile);

  add_to_buffer(16, "accepting");
  sprintf(kbm_buffer + stringlen(kbm_buffer), " := [");
  if (ns > 1 && ns == fsaptr->num_accepting)
    sprintf(kbm_buffer + stringlen(kbm_buffer), "1..%d", fsaptr->states->size);
  else {
    for (i = 1; i <= fsaptr->num_accepting; i++) {
      if (i > 1)
        sprintf(kbm_buffer + stringlen(kbm_buffer), ",");
      if (stringlen(kbm_buffer) + int_len(fsaptr->accepting[i]) > 76) {
        printbuffer(wfile);
        add_to_buffer(21, "");
      }
      sprintf(kbm_buffer + stringlen(kbm_buffer), "%d", fsaptr->accepting[i]);
    }
  }
  sprintf(kbm_buffer + stringlen(kbm_buffer), "],");
  printbuffer(wfile);

  /* If the fsa is not known to be deterministic (or (25.7.95.) possibly
   * multiple start-state deterministic), we will print it sparsely
   */
  if (!fsaptr->flags[DFA] && !fsaptr->flags[MIDFA])
    fsaptr->table->printing_format = SPARSE;
  table_print(wfile, fsaptr->table, "table", 4, "", ns, ne);

  sprintf(kbm_buffer, ");");
  printbuffer(wfile);
}

/* Read the set record *srptr from rfile, assigning space as required.
 * If maxsize is larger than srptr->size, and space is allocated for
 * names or labels, then space is allocated for maxsize of these.
 * This allows for possible later expansion.
 */
void srec_read(FILE *rfile, srec *srptr, int maxsize)

{
  int delim, i, j, k, l, ct, n;
  boolean typeset, sizeset, baseset, arityset, paddingset, namesset, formatset,
      labelsset, alphabetset, setToLabelsset, nonempty;
  int *buf1, *buf2, *swapbuf, bufsize; /* for reading lists of integers */
  gen *wbp;
  storage_type st = DENSE;
  read_ident(rfile, kbm_buffer, &delim, FALSE);
  if (delim != '(' || strcmp(kbm_buffer, "rec") != 0) {
    fprintf(stderr, "#Input error: \"rec(\" expected\n");
    exit(1);
  }

  /* main loop reading the fields of the record follows. */
  typeset = FALSE;
  sizeset = FALSE;
  baseset = FALSE;
  arityset = FALSE;
  paddingset = FALSE;
  namesset = FALSE;
  formatset = FALSE;
  labelsset = FALSE;
  alphabetset = FALSE;
  setToLabelsset = FALSE;
  do {
    read_ident(rfile, kbm_buffer, &delim, FALSE);
    if (delim != ':') {
      fprintf(stderr, "#Input error: bad record field assignment\n");
      exit(1);
    }
    check_next_char(rfile, '=');
    if (strcmp(kbm_buffer, "type") == 0) {
      typeset = TRUE;
      read_string(rfile, kbm_buffer, &delim);
      if (strcmp(kbm_buffer, "simple") == 0)
        srptr->type = SIMPLE;
      else if (strcmp(kbm_buffer, "identifiers") == 0)
        srptr->type = IDENTIFIERS;
      else if (strcmp(kbm_buffer, "group generators") == 0) {
        /* put in for compatability with a variant (by Paul Sanders).
         * Here the "names" field becomes "generatorOrder", and the
         * format field is omitted, with dense format assumed.
         */
        formatset = TRUE;
        st = DENSE;
        srptr->type = IDENTIFIERS;
      }
      else if (strcmp(kbm_buffer, "words") == 0)
        srptr->type = WORDS;
      else if (strcmp(kbm_buffer, "list of words") == 0)
        srptr->type = LISTOFWORDS;
      else if (strcmp(kbm_buffer, "list of integers") == 0)
        srptr->type = LISTOFINTS;
      else if (strcmp(kbm_buffer, "strings") == 0)
        srptr->type = STRINGS;
      else if (strcmp(kbm_buffer, "product") == 0)
        srptr->type = PRODUCT;
      else if (strcmp(kbm_buffer, "labeled") == 0 ||
               strcmp(kbm_buffer, "labelled") == 0)
        srptr->type = LABELED;
      else {
        fprintf(stderr, "Error: unknown set-record type %s.\n", kbm_buffer);
        exit(1);
      }
    }
    else if (strcmp(kbm_buffer, "size") == 0) {
      sizeset = TRUE;
      read_int(rfile, &(srptr->size), &delim);
    }
    else if (strcmp(kbm_buffer, "arity") == 0) {
      arityset = TRUE;
      if (!typeset || srptr->type != PRODUCT) {
        fprintf(stderr, "Error: arity field only used for product type.\n");
        exit(1);
      }
      read_int(rfile, &(srptr->arity), &delim);
    }
    else if (strcmp(kbm_buffer, "padding") == 0) {
      paddingset = TRUE;
      if (!typeset || srptr->type != PRODUCT) {
        fprintf(stderr, "Error: padding field only used for product type.\n");
        exit(1);
      }
      read_ident(rfile, kbm_buffer, &delim, FALSE);
      srptr->padding = kbm_buffer[0];
    }
    else if (strcmp(kbm_buffer, "base") == 0) {
      baseset = TRUE;
      if (!typeset || srptr->type != PRODUCT) {
        fprintf(stderr, "Error: base field only used for product type.\n");
        exit(1);
      }
      tmalloc(srptr->base, srec, 1);
      srec_read(rfile, srptr->base, 0);
      read_delim(rfile, &delim);
    }
    else if (strcmp(kbm_buffer, "format") == 0) {
      formatset = TRUE;
      if (srptr->type != IDENTIFIERS && srptr->type != WORDS &&
          srptr->type != LISTOFWORDS && srptr->type != LISTOFINTS &&
          srptr->type != STRINGS && srptr->type != LABELED) {
        fprintf(stderr,
                "Error: set-record type doesn't require format field.\n");
        exit(1);
      }
      read_string(rfile, kbm_buffer, &delim);
      if (strcmp(kbm_buffer, "dense") == 0)
        st = DENSE;
      else if (strcmp(kbm_buffer, "sparse") == 0)
        st = SPARSE;
      else {
        fprintf(stderr, "Error: unknown storage type %s.\n", kbm_buffer);
        exit(1);
      }
    }
    else if (strcmp(kbm_buffer, "alphabet") == 0) {
      alphabetset = TRUE;
      if (srptr->type != WORDS && srptr->type != LISTOFWORDS) {
        fprintf(stderr,
                "Error: set-record type doesn't require alphabet field.\n");
        exit(1);
      }
      check_next_char(rfile, '[');
      i = 0;
      do {
        read_ident(rfile, kbm_buffer, &delim, TRUE);
        if (stringlen(kbm_buffer) > 0) {
          i++;
          if (i > MAXGEN) {
            fprintf(stderr, "Error: alphabet is too large.\n");
            exit(1);
          }
          tmalloc(srptr->alphabet[i], char, stringlen(kbm_buffer) + 1);
          strcpy(srptr->alphabet[i], kbm_buffer);
        }
      } while (delim != ']');
      srptr->alphabet_size = i;
      check_next_char(rfile, ',');
    }
    else if (strcmp(kbm_buffer, "names") == 0 ||
             strcmp(kbm_buffer, "generatorOrder") == 0) {
      if (!typeset || !sizeset || !formatset) {
        fprintf(stderr,
                "Error: type, size and format fields must precede names.\n");
        exit(1);
      }
      if (srptr->type != IDENTIFIERS && srptr->type != WORDS &&
          srptr->type != STRINGS && srptr->type != LISTOFWORDS &&
          srptr->type != LISTOFINTS) {
        fprintf(stderr,
                "Error: set-record type doesn't require names field.\n");
        exit(1);
      }
      namesset = TRUE;
      check_next_char(rfile, '[');
      if (maxsize < srptr->size)
        maxsize = srptr->size;
      maxsize++; /* hack  (can't remember why) */
      if (srptr->type == LISTOFWORDS)
        tmalloc(srptr->wordslist, gen **,
                maxsize + 1) else if (srptr->type == LISTOFINTS)
            tmalloc(srptr->intlist, int *,
                    maxsize + 1) else if (srptr->type == WORDS)
                tmalloc(srptr->words, gen *, maxsize + 1) else tmalloc(
                    srptr->names, char *, maxsize + 1);
      if (srptr->type == WORDS || srptr->type == LISTOFWORDS) {
        if (!alphabetset) {
          fprintf(stderr, "Error: alphabet field must precede names.\n");
          exit(1);
        }
        /* We now have to work out the algorithm for converting words to
         * generator numbers, based on the alphabet names - similar to that in
         * rwsio.c
         */
        process_names(srptr->alphabet, srptr->alphabet_size);
        /* Finally allocate some space temporarily to read the words into. */
        tmalloc(wbuffer, gen, MAXWORDLEN + 1);
      }
      if (st == DENSE) {
        if (srptr->size == 0)
          read_delim(rfile, &delim);
        for (i = 1; i <= srptr->size; i++) {
          if (srptr->type == IDENTIFIERS) {
            read_ident(rfile, kbm_buffer, &delim, TRUE);
            tmalloc(srptr->names[i], char, stringlen(kbm_buffer) + 1);
            strcpy(srptr->names[i], kbm_buffer);
          }
          else if (srptr->type == STRINGS) {
            read_string(rfile, kbm_buffer, &delim);
            tmalloc(srptr->names[i], char, stringlen(kbm_buffer) + 1);
            strcpy(srptr->names[i], kbm_buffer);
          }
          else if (srptr->type == WORDS) {
            read_word(rfile, wbuffer, wbuffer + MAXWORDLEN, &delim,
                      srptr->alphabet, srptr->alphabet_size, TRUE);
            tmalloc(srptr->words[i], gen, genstrlen(wbuffer) + 1);
            genstrcpy(srptr->words[i], wbuffer);
          }
          else if (srptr->type == LISTOFWORDS) {
            check_next_char(rfile, '[');
            l = 0;
            wbp = wbuffer;
            do {
              nonempty = read_word(rfile, wbp, wbuffer + MAXWORDLEN, &delim,
                                   srptr->alphabet, srptr->alphabet_size, TRUE);
              if (nonempty || l > 0 || delim != ']')
                l++;
              wbp += (genstrlen(wbp) + 1);
            } while (delim != ']');
            tmalloc(srptr->wordslist[i], gen *, l + 1);
            wbp = wbuffer;
            for (j = 0; j < l; j++) {
              tmalloc(srptr->wordslist[i][j], gen, genstrlen(wbp) + 1);
              genstrcpy(srptr->wordslist[i][j], wbp);
              wbp += (genstrlen(wbp) + 1);
            }
            srptr->wordslist[i][l] = 0;
            if (i < srptr->size)
              check_next_char(rfile, ',');
            else
              check_next_char(rfile, ']');
          }
          else if (srptr->type == LISTOFINTS) {
            check_next_char(rfile, '[');
            ct = 0;
            bufsize = 1024;
            tmalloc(buf1, int, bufsize);
            do {
              if (!read_int(rfile, &j, &delim))
                break; /* should only happen if list is empty */
              ct++;
              if (ct >= bufsize) {
                bufsize *= 2;
                tmalloc(buf2, int, bufsize);
                for (k = 1; k < ct; k++)
                  buf2[k] = buf1[k];
                tfree(buf1);
                swapbuf = buf1;
                buf1 = buf2;
                buf2 = swapbuf;
              }
              buf1[ct] = j;
            } while (delim != ']');
            tmalloc(srptr->intlist[i], int, ct + 1);
            for (j = 1; j <= ct; j++)
              srptr->intlist[i][j] = buf1[j];
            srptr->intlist[i][0] = ct;
            if (i < srptr->size)
              check_next_char(rfile, ',');
            else
              check_next_char(rfile, ']');
            tfree(buf1);
          }
        }
      }
      else {
        read_delim(rfile, &delim);
        while (delim != ']') {
          read_int(rfile, &i, &delim);
          if (i <= 0 || i > srptr->size) {
            fprintf(stderr, "Error: name-number out of range.\n");
            exit(1);
          }
          if (srptr->type == IDENTIFIERS) {
            read_ident(rfile, kbm_buffer, &delim, TRUE);
            tmalloc(srptr->names[i], char, stringlen(kbm_buffer) + 1);
            strcpy(srptr->names[i], kbm_buffer);
          }
          else if (srptr->type == STRINGS) {
            read_string(rfile, kbm_buffer, &delim);
            tmalloc(srptr->names[i], char, stringlen(kbm_buffer) + 1);
            strcpy(srptr->names[i], kbm_buffer);
          }
          else if (srptr->type == WORDS) {
            read_word(rfile, wbuffer, wbuffer + MAXWORDLEN, &delim,
                      srptr->alphabet, srptr->alphabet_size, TRUE);
            tmalloc(srptr->words[i], gen, genstrlen(wbuffer) + 1);
            genstrcpy(srptr->words[i], wbuffer);
          }
          else if (srptr->type == LISTOFWORDS) {
            check_next_char(rfile, '[');
            l = 0;
            wbp = wbuffer;
            do {
              nonempty = read_word(rfile, wbp, wbuffer + MAXWORDLEN, &delim,
                                   srptr->alphabet, srptr->alphabet_size, TRUE);
              if (nonempty || l > 0 || delim != ']')
                l++;
              wbp += (genstrlen(wbp) + 1);
            } while (delim != ']');
            tmalloc(srptr->wordslist[i], gen *, l + 1);
            wbp = wbuffer;
            for (j = 0; j < l; j++) {
              tmalloc(srptr->wordslist[i][j], gen, genstrlen(wbp) + 1);
              genstrcpy(srptr->wordslist[i][j], wbp);
              wbp += (genstrlen(wbp) + 1);
            }
            srptr->wordslist[i][l] = 0;
            check_next_char(rfile, ']');
          }
          else if (srptr->type == LISTOFINTS) {
            check_next_char(rfile, '[');
            ct = 0;
            bufsize = 1024;
            tmalloc(buf1, int, bufsize);
            do {
              if (!read_int(rfile, &j, &delim))
                break; /* should only happen if list is empty */
              ct++;
              if (ct >= bufsize) {
                bufsize *= 2;
                tmalloc(buf2, int, bufsize);
                for (k = 1; k < ct; k++)
                  buf2[k] = buf1[k];
                tfree(buf1);
                swapbuf = buf1;
                buf1 = buf2;
                buf2 = swapbuf;
              }
              buf1[ct] = j;
            } while (delim != ']');
            tmalloc(srptr->intlist[i], int, ct + 1);
            for (j = 1; j <= ct; j++)
              srptr->intlist[i][j] = buf1[j];
            srptr->intlist[i][0] = ct;
            check_next_char(rfile, ']');
            tfree(buf1);
          }
          read_delim(rfile, &delim);
          if (delim == ',')
            read_delim(rfile, &delim);
        }
      }
      read_delim(rfile, &delim);
      /* don't forget to de-allocate space for reading words if necessary */
      if (srptr->type == WORDS || srptr->type == LISTOFWORDS)
        tfree(wbuffer);
    }
    else if (strcmp(kbm_buffer, "labels") == 0) {
      labelsset = TRUE;
      if (!typeset || (srptr->type != LABELED)) {
        fprintf(stderr, "Error: labels field only used for labeled type.\n");
        exit(1);
      }
      tmalloc(srptr->labels, srec, 1);
      srec_read(rfile, srptr->labels, 0);
      read_delim(rfile, &delim);
      if (srptr->labels->size > MAXUSHORT) {
        fprintf(stderr, "Error: label-set can have size at most 65535.\n");
        exit(1);
      }
    }
    else if (strcmp(kbm_buffer, "setToLabels") == 0) {
      setToLabelsset = TRUE;
      if (!typeset || (srptr->type != LABELED)) {
        fprintf(stderr,
                "Error: setToLabels field only used for labeled type.\n");
        exit(1);
      }
      if (!labelsset) {
        fprintf(stderr, "Error: labels field must precede setToLabels.\n");
        exit(1);
      }
      if (!formatset) {
        fprintf(stderr, "Error: format field must precede setToLabels.\n");
        exit(1);
      }
      check_next_char(rfile, '[');
      if (maxsize < srptr->size)
        maxsize = srptr->size;
      tmalloc(srptr->setToLabels, setToLabelsType, maxsize + 1);
      for (i = 0; i <= srptr->size; i++)
        srptr->setToLabels[i] = 0;
      if (st == DENSE) {
        for (i = 1; i <= srptr->size; i++) {
          read_int(rfile, &n, &delim);
          if (n < 0 || n > srptr->labels->size) {
            fprintf(stderr, "Error: label out of range.\n");
            exit(1);
          }
          srptr->setToLabels[i] = n;
          if (delim == ']')
            break;
        }
      }
      else {
        read_delim(rfile, &delim);
        while (delim != ']') {
          read_int(rfile, &i, &delim);
          if (i <= 0 || i > srptr->size) {
            fprintf(stderr, "Error: label-number out of range.\n");
            exit(1);
          }
          read_int(rfile, &n, &delim);
          if (n < 0 || n > srptr->labels->size) {
            fprintf(stderr, "Error: label out of range.\n");
            exit(1);
          }
          srptr->setToLabels[i] = n;
          read_delim(rfile, &delim);
          if (delim == ',')
            read_delim(rfile, &delim);
        }
      }
      read_delim(rfile, &delim);
    }
    else {
      printf("#Warning: Unknown field name %s.\n", kbm_buffer);
      skip_gap_expression(rfile, &delim);
    }
  } while (delim != ')');

  if (!typeset || !sizeset) {
    fprintf(stderr, "Error: type and size fields must be set.\n");
    exit(1);
  }
  if (srptr->type == IDENTIFIERS || srptr->type == WORDS ||
      srptr->type == STRINGS || srptr->type == LISTOFWORDS ||
      srptr->type == LISTOFINTS) {
    if (!namesset) {
      fprintf(stderr, "Error: set-record type requires names field.\n");
      exit(1);
    }
  }
  if (srptr->type == PRODUCT) {
    if (!arityset || !paddingset || !baseset) {
      fprintf(
          stderr,
          "Error: set-record type require arity, padding and base fields.\n");
      exit(1);
    }
    /* The size of the set-record should be (n+1)^r or (n+1)^r-1, where
     * n is the size of the base set, and r the arity.
     */
    n = srptr->base->size + 1;
    for (i = 1; i < srptr->arity; i++)
      n *= (srptr->base->size + 1);
    if (srptr->size != n && srptr->size != n - 1) {
      fprintf(stderr, "Error: set-record size wrong for product type.\n");
      exit(1);
    }
  }
  if (srptr->type == LABELED) {
    if (!setToLabelsset) {
      fprintf(stderr, "Error: set-record type require setToLabels field.\n");
      exit(1);
    }
  }
}

/* Read the table_struc *tableptr from rfile, assigning space as required.
 * dr is the number of rows stored densely if storage_type=SPARSE.
 * ns and ne are the sizes of the state-set and alphabet-set.
 * maxstates is the maximum number of states that we allocate space for
 * in dense-storage mode.
 * nondet is true if fsa-table is not known to be deterministic.
 */
void table_read(FILE *rfile, table_struc *tableptr,
                storage_type table_storage_type, int dr, int ns, int maxstates,
                int ne, boolean nondet)
{
  int delim, i, j, k, ntleft = 0, dt = 0;
  boolean filenameset, numTransitionsset, transitionsset;
  int **table, *sparseptr = 0;

  numTransitionsset = FALSE;
  transitionsset = FALSE;
  filenameset = FALSE;

  read_ident(rfile, kbm_buffer, &delim, FALSE);
  if (delim != '(' || strcmp(kbm_buffer, "rec") != 0) {
    fprintf(stderr, "#Input error: \"rec(\" expected\n");
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
    if (strcmp(kbm_buffer, "filename") == 0) {
      /* In this case, the transition table (and possibly other info) is stored
       * externally in the file "filename"
       */
      if (transitionsset) {
        fprintf(stderr, "#Input error - filename and transitions fields are "
                        "both present.\n");
        exit(1);
      }
      filenameset = TRUE;
      read_string(rfile, kbm_buffer, &delim);
      tmalloc(tableptr->filename, char, stringlen(kbm_buffer) + 1);
      strcpy(tableptr->filename, kbm_buffer);
    }
    else if (strcmp(kbm_buffer, "format") == 0) {
      read_string(rfile, kbm_buffer, &delim);
      if (strcmp(kbm_buffer, "dense deterministic") == 0)
        tableptr->printing_format = DENSE;
      else if (strcmp(kbm_buffer, "sparse") == 0)
        tableptr->printing_format = SPARSE;
      else {
        fprintf(stderr, "Error: invalid format value %s\n", kbm_buffer);
        exit(1);
      }
    }
    else if (strcmp(kbm_buffer, "numTransitions") == 0) {
      numTransitionsset = TRUE;
      read_int(rfile, &(tableptr->numTransitions), &delim);
    }
    else if (strcmp(kbm_buffer, "defaultTarget") == 0) {
      read_int(rfile, &dt, &delim);
      if (dt != 0)
        /* Our code doesn't currently cope with this, so we will enforce
         * storage-type dense in this case.
         */
        table_storage_type = DENSE;
    }
    else if (strcmp(kbm_buffer, "transitions") == 0) {
      if (filenameset) {
        fprintf(stderr, "#Input error - filename and transitions fields are "
                        "both present.\n");
        exit(1);
      }
      transitionsset = TRUE;
      if (!numTransitionsset) {
        /* In this case, we have currently to use dense storage */
        if (nondet) {
          fprintf(stderr, "Error: In a non-deterministic trnasition table\n");
          fprintf(stderr, "you must include the 'numTransitions' field,\n");
          exit(1);
        }
        table_storage_type = DENSE;
      }
      tableptr->table_type = table_storage_type;
      if (table_storage_type == SPARSE) {
        if (dr > ns)
          dr = ns;
        tableptr->denserows = dr;
      }
      tableptr->maxstates = maxstates;
      /*  assign space according to storage type */
      if (table_storage_type == DENSE) {
        fsa_table_init(tableptr, maxstates, ne);
        table = tableptr->table_data_ptr;
      }
      else {
        tmalloc(tableptr->table_data_ptr, int *, ns + 2);
        table = tableptr->table_data_ptr;
        if (dr > 0) {
          /* Here we have to read in the data in two separate chunks. */
          tmalloc(table[0], int, dr *ne);
          for (i = 1; i <= dr; i++)
            table[i] = table[0] + (i - 1) * ne - 1;
          ntleft = tableptr->numTransitions;
        }
        else {
          tmalloc(table[0], int, 2 * tableptr->numTransitions + 1);
          sparseptr = table[0];
        }
      }
      /* Now read the transitions  */
      check_next_char(rfile, '[');
      for (i = 1; i <= ns; i++) {
        check_next_char(rfile, '[');
        if (table_storage_type == SPARSE) {
          if (dr > 0 && i == dr + 1) { /* allocate remaining storage */
            tmalloc(table[i], int, 2 * ntleft + 1);
            sparseptr = table[i];
          }
          else if (i > dr)
            table[i] = sparseptr;
        }
        if (tableptr->printing_format == DENSE) {
          if (ne == 0)
            read_delim(rfile, &delim);
          else
            for (j = 1; j <= ne; j++) {
              read_int(rfile, &k, &delim);
              if (table_storage_type == DENSE)
                table[j][i] = k;
              else if (i <= dr) {
                table[i][j] = k;
                if (k != 0)
                  ntleft--;
              }
              else if (k != 0) {
                *(sparseptr++) = j;
                *(sparseptr++) = k;
              }
              if (k > ns) {
                fprintf(stderr,
                        "Error: transition target out of range in table.\n");
                exit(1);
              }
            }
          if (delim != ']') {
            fprintf(stderr, "Error: format error in table.\n");
            exit(1);
          }
        }
        else {
          if (table_storage_type == DENSE)
            for (j = 1; j <= ne; j++)
              table[j][i] = dt; /* in case there is a default target */
          else if (i <= dr)
            for (j = 1; j <= ne; j++)
              table[i][j] = 0;
          read_delim(rfile, &delim);
          while (delim != ']') {
            read_int(rfile, &j, &delim);
            read_int(rfile, &k, &delim);
            if (table_storage_type == DENSE)
              table[j][i] = k;
            else if (i <= dr) {
              table[i][j] = k;
              if (k != 0)
                ntleft--;
            }
            else if (k != 0) {
              *(sparseptr++) = j;
              *(sparseptr++) = k;
            }
            if (k > ns) {
              fprintf(stderr,
                      "Error: transition target out of range in table.\n");
              exit(1);
            }
            read_delim(rfile, &delim);
            if (delim == ',')
              read_delim(rfile, &delim);
          }
        }
        read_delim(rfile, &delim);
      }
      if (ns == 0)
        read_delim(rfile, &delim);
      if (table_storage_type == SPARSE && (ns > dr || ns == 0))
        /* Set extra pointer to show end of data */
        table[ns + 1] = sparseptr;
      read_delim(rfile, &delim);
    }
    else {
      printf("#Warning: Unknown field name %s.\n", kbm_buffer);
      skip_gap_expression(rfile, &delim);
    }
  } while (delim != ')');

  if (!transitionsset && !filenameset) {
    fprintf(stderr, "transitions and filename fields are not set.\n");
    exit(1);
  }
  if (filenameset)
    /* In this case, the storage_type has to be as specified by the format field
     */
    tableptr->table_type = tableptr->printing_format;
}

/* Read the fsa *fsaptr from rfile, assigning space as required.
 * If maxstates is greater than the actual number of states, then
 * space will be assigned for maxstates states, to allow more states
 * to be added later (this only makes sense with dense storage_type).
 * If assignment is true, an assignment to an fsa is read.
 * The name is returned in *name, which is assumed to have enough space.
 */
void fsa_read(FILE *rfile, fsa *fsaptr, storage_type table_storage_type, int dr,
              int maxstates, boolean assignment, char *name)
{
  int delim, i, j, k, ct, ns = 0, ne = 0, *ia, *buf1, *buf2, *swapbuf, bufsize;
  boolean isFSAset, statesset, alphabetset, initialset, acceptingset, flagsset,
      tableset, in, compressed;

  if (kbm_print_level >= 3)
    printf("    #Calling fsa_read.\n");
  isFSAset = FALSE;
  isFSAset = FALSE;
  statesset = FALSE;
  alphabetset = FALSE;
  initialset = FALSE;
  acceptingset = FALSE;
  flagsset = FALSE;
  tableset = FALSE;

  fsa_init(fsaptr);

  if (assignment) {
    read_ident(rfile, kbm_buffer, &delim, FALSE);
    if (delim != ':') {
      fprintf(stderr, "#Input error: file must contain a record assignment\n");
      exit(1);
    }
    strcpy(name, kbm_buffer);
    check_next_char(rfile, '=');
  }

  read_ident(rfile, kbm_buffer, &delim, FALSE);
  if (delim != '(' || strcmp(kbm_buffer, "rec") != 0) {
    fprintf(stderr, "#Input error: \"rec(\" expected\n");
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
    if (strcmp(kbm_buffer, "isFSA") == 0) {
      isFSAset = TRUE;
      read_ident(rfile, kbm_buffer, &delim, FALSE);
      if (strcmp(kbm_buffer, "true") != 0) {
        fprintf(stderr, "#Input error: isFSA field must equal \"true\"\n");
        exit(1);
      }
    }
    else if (strcmp(kbm_buffer, "states") == 0) {
      statesset = TRUE;
      srec_read(rfile, fsaptr->states, maxstates);
      ns = fsaptr->states->size;
      read_delim(rfile, &delim);
    }
    else if (strcmp(kbm_buffer, "alphabet") == 0) {
      alphabetset = TRUE;
      srec_read(rfile, fsaptr->alphabet, 0);
      ne = fsaptr->alphabet->size;
      read_delim(rfile, &delim);
    }
    else if (strcmp(kbm_buffer, "flags") == 0) {
      flagsset = TRUE;
      check_next_char(rfile, '[');
      do {
        read_string(rfile, kbm_buffer, &delim);
        for (i = 0; i < num_kbm_flag_strings; i++)
          if (strcmp(kbm_buffer, kbm_flag_names[i]) == 0)
            fsaptr->flags[(kbm_flag_strings)i] = TRUE;
      } while (delim != ']');
      read_delim(rfile, &delim);
      /* If the fsa is not known to be deterministic (or (25.7.95.) possibly
       * multiple start-state deterministic), then we should store is in
       * sparse format
       */
      if (!fsaptr->flags[DFA] && !fsaptr->flags[MIDFA]) {
        table_storage_type = SPARSE;
        dr = 0;
      }
    }
    else if (strcmp(kbm_buffer, "initial") == 0 ||
             strcmp(kbm_buffer, "accepting") == 0) {
      /* We'll handle these together since they are so similar. */
      compressed = FALSE;
      bufsize = 1024;
      in = strcmp(kbm_buffer, "initial") == 0;
      if (!statesset) {
        fprintf(
            stderr,
            "Error: states field must precede initial and accepting fields.\n");
        exit(1);
      }
      ct = 0;
      tmalloc(buf1, int, bufsize);
      /* We don't know how long the list will be in advance */
      check_next_char(rfile, '[');
      do {
        read_int(rfile, &i, &delim);
        if (i < 0 || i > ns) {
          fprintf(stderr,
                  "Invalid state number in initial or accepting list.\n");
          exit(1);
        }
        if (i > 0) {
          ct++;
          if (delim == '.') {
            compressed = TRUE;
            if (ct != 1) {
              fprintf(stderr,
                      "Error in format of initial or accepting field.\n");
              exit(1);
            }
            check_next_char(rfile, '.');
            read_int(rfile, &j, &delim);
            if (j >= i && j <= ns) {
              if (delim != ']') {
                fprintf(stderr,
                        "Error in format of initial or accepting field.\n");
                exit(1);
              }
              ct = j - i + 1;
              if (ct == 1 || ct != ns || in) {
                /* if ct = ns, we don't store the list of accept states. */
                tmalloc(ia, int, ct + 1);
                if (in)
                  fsaptr->initial = ia;
                else
                  fsaptr->accepting = ia;
                for (k = 1; k <= ct; k++)
                  ia[k] = k + i - 1;
              }
            }
            else {
              fprintf(stderr,
                      "Error in format of initial or accepting field.\n");
              exit(1);
            }
          }
          else {
            compressed = FALSE;
            if (ct >= bufsize) {
              bufsize *= 2;
              tmalloc(buf2, int, bufsize);
              for (j = 1; j < ct; j++)
                buf2[j] = buf1[j];
              tfree(buf1);
              swapbuf = buf1;
              buf1 = buf2;
              buf2 = swapbuf;
            }
            buf1[ct] = i;
          }
        } /* if (i>0) */
      } while (delim != ']');
      if (!compressed) {
        tmalloc(ia, int, ct + 1);
        if (in)
          fsaptr->initial = ia;
        else
          fsaptr->accepting = ia;
        for (i = 1; i <= ct; i++)
          ia[i] = buf1[i];
      }
      tfree(buf1);
      if (in) {
        initialset = TRUE;
        fsaptr->num_initial = ct;
      }
      else {
        acceptingset = TRUE;
        fsaptr->num_accepting = ct;
      }
      read_delim(rfile, &delim);
    }
    else if (strcmp(kbm_buffer, "table") == 0) {
      if (!statesset) {
        fprintf(stderr, "Error: states field must precede table fields.\n");
        exit(1);
      }
      if (!alphabetset) {
        fprintf(stderr, "Error: alphabet field must precede table fields.\n");
        exit(1);
      }
      tableset = TRUE;
      if (fsaptr->alphabet->type == PRODUCT)
        k = fsaptr->alphabet->base->size;
      else
        k = -1;
      if (maxstates < ns)
        maxstates = ns;
      if (!fsaptr->flags[DFA] && !fsaptr->flags[MIDFA])
        table_read(rfile, fsaptr->table, table_storage_type, dr, ns, maxstates,
                   ne, TRUE);
      else
        table_read(rfile, fsaptr->table, table_storage_type, dr, ns, maxstates,
                   ne, FALSE);
      read_delim(rfile, &delim);
    }
    else {
      printf("#Warning: Unknown field name %s.\n", kbm_buffer);
      skip_gap_expression(rfile, &delim);
    }
  } while (delim != ')');

  if (!isFSAset || !statesset || !alphabetset || !initialset || !acceptingset ||
      !flagsset || !tableset) {
    fprintf(stderr, "One of the compulsory fsa-fields is not set.\n");
    exit(1);
  }
  if (assignment)
    read_delim(rfile, &delim);
}

/* Read the transition-table of the fsa *fsaptr which is stored in the
 * file with *file in unformatted form.
 * *file should be opened and closed externally to the function.
 * This is used by the functions in fsalogic.c
 */
void compressed_transitions_read(fsa *fsaptr, FILE *rfile)
{
  int ns, ne, nt, **table, *tab_ptr, len, i, j;

  ns = fsaptr->states->size;
  ne = fsaptr->alphabet->size;
  nt = fsaptr->table->numTransitions;

  if (fsaptr->table->table_type == DENSE) {
    /* it is a pity that the table was output in transposed form! */
    fsa_table_init(fsaptr->table, ns, ne);
    table = fsaptr->table->table_data_ptr;
    for (i = 1; i <= ns; i++)
      for (j = 1; j <= ne; j++)
        fread((void *)(table[j] + i), sizeof(int), (size_t)1, rfile);
  }
  else {
    tmalloc(fsaptr->table->table_data_ptr, int *, ns + 2);
    tmalloc(fsaptr->table->table_data_ptr[0], int, 2 * nt + 1);
    tab_ptr = fsaptr->table->table_data_ptr[0];
    table = fsaptr->table->table_data_ptr;
    for (i = 1; i <= ns; i++) {
      table[i] = tab_ptr;
      fread((void *)&len, sizeof(int), (size_t)1, rfile);
      if (len > 0)
        fread((void *)tab_ptr, sizeof(int), (size_t)len, rfile);
      tab_ptr += len;
    }
    table[ns + 1] = tab_ptr;
  }
}
