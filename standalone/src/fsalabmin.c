/* fsalabmin.c 3/1/98.
 * Minimizes a labeled finite state automaton using state labels as
 * distinct categories of states on minimization.
 * Can either use stdin/stdout or files.
 *
 * SYNOPSIS:  fsalabmin [-ip d/s] [-op d/s] [-silent] [-v] [filename]
 *
 * Input is from filename (or stdin if not specified) ,
 *   which should contain an fsa with labeled state set.
 * Output is to filename.labmin, or stdout.
 *
 * OPTIONS:
 * -ip d/s      input in dense or sparse format - dense is default
 * -op d/s      output in dense or sparse format - default is as in current
 *               value of table->printing_format, in the fsa.
 * -v           verbose
 * -silent      no diagnostics
 * -l/-h        large/huge hash-tables (for big examples)
 *
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

static void badusage(void);

int main(int argc, char *argv[])
{
  int arg;
  fsa testfsa;
  char inf[100], outf[100], fsaname[100];
  storage_type ip_store = DENSE;
  boolean op_format_set = FALSE;
  storage_type op_format = DENSE;

  setbuf(stdout, (char *)0);
  setbuf(stderr, (char *)0);

  inf[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg], "-ip") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      if (strcmp(argv[arg], "d") == 0)
        ip_store = DENSE;
      else if (strcmp(argv[arg], "s") == 0)
        ip_store = SPARSE;
      else
        badusage();
    }
    else if (strcmp(argv[arg], "-op") == 0) {
      arg++;
      op_format_set = TRUE;
      if (arg >= argc)
        badusage();
      if (strcmp(argv[arg], "d") == 0)
        op_format = DENSE;
      else if (strcmp(argv[arg], "s") == 0)
        op_format = SPARSE;
      else
        badusage();
    }
    else if (strcmp(argv[arg], "-silent") == 0)
      kbm_print_level = 0;
    else if (strcmp(argv[arg], "-v") == 0)
      kbm_print_level = 2;
    else if (strcmp(argv[arg], "-vv") == 0)
      kbm_print_level = 3;
    else if (strcmp(argv[arg], "-l") == 0)
      kbm_large = TRUE;
    else if (strcmp(argv[arg], "-h") == 0)
      kbm_huge = TRUE;
    else {
      if (argv[arg][0] == '-')
        badusage();
      if (strcmp(inf, ""))
        badusage();
      strcpy(inf, argv[arg]);
    }
    arg++;
  }

  if (stringlen(inf) != 0) {
    strcpy(outf, inf);
    strcat(outf, ".labmin");

    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf);
      exit(1);
    }
  }
  else
    rfile = stdin;

  fsa_read(rfile, &testfsa, ip_store, 0, 0, TRUE, fsaname);

  if (stringlen(inf) != 0)
    fclose(rfile);

  if (kbm_print_level > 1)
    printf("  #Number of states of fsa before labeled minimization = %d.\n",
           testfsa.states->size);
  if (fsa_labeled_minimize(&testfsa) == -1)
    exit(1);
  if (kbm_print_level > 1)
    printf("  #Number of states of fsa after labeled minimization = %d.\n",
           testfsa.states->size);

  if (op_format_set)
    testfsa.table->printing_format = op_format;
  strcat(fsaname, "_labmin");

  if (stringlen(inf) != 0)
    wfile = fopen(outf, "w");
  else
    wfile = stdout;

  fsa_print(wfile, &testfsa, fsaname);

  if (stringlen(inf) != 0)
    fclose(wfile);
  if (wfile != stdout && kbm_print_level > 0)
    printf("#Minimized fsa with %d states computed.\n", testfsa.states->size);

  fsa_clear(&testfsa);
  exit(0);
}

void badusage(void)
{
  fprintf(stderr, "Usage: fsalabmin [-ip d/s] [-op d/s] [-silent] [-v] [-l/-h] "
                  "[filename]\n");
  exit(1);
}
