/* fsacount.c 27/10/94.
 * 20/3/96 - added "-is n" option, to change the initial state of the fsa to
 * n (useful for coset reduction automata).
 *
 * Counts the accepted language of a fsa
 * This outputs to stdout only.
 *
 * SYNOPSIS: fsacount [-is n] [-ip d/s] [-silent] [-v] [filename]\n");
 *
 * Input is from filename or stdin, which should contain a fsa.
 *
 * OPTIONS:
 * -is n	change initial state of fsa to n.
 * -ip d/s      input in dense or sparse format - dense is default
 * -v           verbose
 * -silent      no diagnostics
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile;

static void badusage(void);

int main(int argc, char *argv[])
{
  int arg, ct, n;
  fsa testfsa;
  char inf[100], fsaname[100];
  storage_type ip_store = DENSE;

  setbuf(stdout, (char *)0);
  setbuf(stderr, (char *)0);

  inf[0] = '\0';
  n = 0;
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg], "-is") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      n = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-ip") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      if (strcmp(argv[arg], "d") == 0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's')
        ip_store = SPARSE;
      else
        badusage();
    }
    else if (strcmp(argv[arg], "-silent") == 0)
      kbm_print_level = 0;
    else if (strcmp(argv[arg], "-v") == 0)
      kbm_print_level = 2;
    else if (strcmp(argv[arg], "-vv") == 0)
      kbm_print_level = 3;
    else {
      if (argv[arg][0] == '-')
        badusage();
      if (strcmp(inf, ""))
        badusage();
      strcpy(inf, argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf) == 0)
    rfile = stdin;
  else if ((rfile = fopen(inf, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf);
    exit(1);
  }
  fsa_read(rfile, &testfsa, ip_store, 0, 0, TRUE, fsaname);
  if (stringlen(inf))
    fclose(rfile);
  if (n > testfsa.states->size) {
    fprintf(stderr, "Error: specified initial state is too large.\n");
    exit(1);
  }
  if (n > 0 && testfsa.num_initial > 0) {
    testfsa.initial[1] = n;
    /* This may destroy various properties of the automata */
    testfsa.flags[MINIMIZED] = FALSE;
    testfsa.flags[BFS] = FALSE;
    testfsa.flags[ACCESSIBLE] = FALSE;
    testfsa.flags[TRIM] = FALSE;
  }

  ct = fsa_count(&testfsa);
  if (ct == -1)
    exit(1);
  if (ct == -2)
    printf("#The language accepted is infinite.\n");
  else
    printf("#The language accepted has size %d.\n", ct);

  fsa_clear(&testfsa);
  exit(0);
}

void badusage(void)
{
  fprintf(stderr,
          "Usage: fsacount [-is n] [-ip d/s] [-silent] [-v] [filename]\n");
  exit(1);
}
