/* fsaswapcoords.c 15/4/96.
 *
 * Swaps coordinates of a 2-variable fsa.  That is it replaces transitions
 * s - (a,b) -> t  by  s - (b,a) -> t, for a,b in the base-alphabet.
 *
 * SYNOPSIS:  fsaswapcoords [-op d/s] [-v] [-silent] [filename1 filename2]
 *
 * Input is from filename1 or stdin and should contain a 2-variable fsa
 * Output to stdout or filename2.
 * Input is always in dense format.
 *
 * OPTIONS:
 * -op d/s      output in dense or sparse format - default is as in current
 *               value of table->printing_format, in the fsa.
 * -v		verbose
 * -silent	no diagnostics
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
  boolean op_format_set = FALSE;
  storage_type op_format = SPARSE;

  setbuf(stdout, (char *)0);
  setbuf(stderr, (char *)0);

  inf[0] = '\0';
  outf[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg], "-op") == 0) {
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
    else if (argv[arg][0] == '-')
      badusage();
    else {
      if (argv[arg][0] == '-')
        badusage();
      if (strcmp(outf, ""))
        badusage();
      if (strcmp(inf, "") == 0)
        strcpy(inf, argv[arg]);
      else
        strcpy(outf, argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf) == 0)
    rfile = stdin;
  else if ((rfile = fopen(inf, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf);
    exit(1);
  }

  fsa_read(rfile, &testfsa, DENSE, 0, 0, TRUE, fsaname);
  if (stringlen(inf) != 0)
    fclose(rfile);

  if (fsa_swap_coords(&testfsa) == -1)
    exit(1);

  if (op_format_set)
    testfsa.table->printing_format = op_format;

  base_prefix(fsaname);
  strcat(fsaname, "_swap_coords");
  if (stringlen(outf) == 0)
    wfile = stdout;
  else
    wfile = fopen(outf, "w");
  fsa_print(wfile, &testfsa, fsaname);
  if (stringlen(outf) != 0)
    fclose(wfile);

  fsa_clear(&testfsa);
  exit(0);
}

void badusage(void)
{
  fprintf(
      stderr,
      "Usage: fsaswapcoords [-op d/s] [-silent] [-v] [filename1 filename2]\n");
  exit(1);
}
