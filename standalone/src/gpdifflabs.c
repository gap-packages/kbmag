/* gpdifflabs.c 18/1/98
 * Input a two-variable fsa reading pairs of words of an automatic group,
 * and output an fsa which accepts the same language but with states labeled
 * by the associated word-differences.
 *
 * SYNOPSIS:
 * gpdifflabs [-diff1] [-op d/s] [-silent] [-v] [-l/-h] [-f] groupname fsaname
 *
 * Input is from groupname.fsaname and groupname.diff2
 *  (and possibly from groupname.diff1 or groupname.diff1c)
 *   called).
 * Output is to groupname.fsaname.difflabs
 *
 * OPTIONS:
 * -op d/s    output in dense or sparse format - sparse is default
 * -v	      verbose
 * -silent    no diagnostics
 * -l/-h      large/huge hash-tables (for big examples)
 * -diff1/-diff2/-diff1c
 *            input from groupname.diff1, diff2 or diff1c for word-reduction.
 *            groupname.diff2 is default.
 * -f         read the transition table repeatedly from file while mimimizing.
 *            this avoids storing the large table, but is a little slower.
 *
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"

static FILE *rfile, *wfile;

static void badusage(void);
int (*reduce_word)(gen *w, reduction_struct *rs_rws);

int main(int argc, char *argv[])
{
  int arg;
  fsa fsaip, *difflabsptr;
  char inf1[100], inf2[100], outf[100], fsaname[100], tempfilename[100];
  reduction_struct rs_wd;
  storage_type op_store = SPARSE;
  boolean diff1_ip, diff1c_ip, diff2_ip;
  boolean readback = TRUE;

  setbuf(stdout, (char *)0);
  setbuf(stderr, (char *)0);

  inf1[0] = '\0';
  inf2[0] = '\0';
  arg = 1;
  diff1_ip = diff1c_ip = diff2_ip = FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg], "-op") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      if (strcmp(argv[arg], "d") == 0)
        op_store = DENSE;
      else if (strcmp(argv[arg], "s") == 0)
        op_store = SPARSE;
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
    else if (strcmp(argv[arg], "-diff1") == 0)
      diff1_ip = TRUE;
    else if (strcmp(argv[arg], "-diff2") == 0)
      diff2_ip = TRUE;
    else if (strcmp(argv[arg], "-diff1c") == 0)
      diff1c_ip = TRUE;
    else {
      if (argv[arg][0] == '-')
        badusage();
      if (strcmp(inf2, "") == 0) {
        strcpy(inf2, argv[arg]);
      }
      else {
        strcpy(inf1, inf2);
        strcat(inf1, ".");
        strcat(inf1, argv[arg]);
      }
    }
    arg++;
  }

  if (stringlen(inf1) == 0)
    badusage();

  strcpy(tempfilename, inf1);
  strcat(tempfilename, "temp_d_XXX");

  if (diff1_ip)
    strcat(inf2, ".diff1");
  else if (diff1c_ip)
    strcat(inf2, ".diff1c");
  else
    strcat(inf2, ".diff2");

  strcpy(outf, inf1);
  strcat(outf, ".difflabs");

  /* First read word-difference machine for word-reduction */
  if ((rfile = fopen(inf2, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf2);
    exit(1);
  }
  tmalloc(rs_wd.wd_fsa, fsa, 1);
  fsa_read(rfile, rs_wd.wd_fsa, DENSE, 0, 0, TRUE, fsaname);
  fclose(rfile);
  if (fsa_table_dptr_init(rs_wd.wd_fsa) == -1)
    exit(1);

  /* Now read main input fsa */
  if ((rfile = fopen(inf1, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf1);
    exit(1);
  }
  fsa_read(rfile, &fsaip, DENSE, 0, 0, TRUE, fsaname);
  fclose(rfile);

  difflabsptr =
      fsa_difflabs(&fsaip, &rs_wd, op_store, TRUE, tempfilename, readback);

  if (difflabsptr == 0)
    exit(1);

  if (kbm_print_level > 1)
    printf("  #Number of states of labeled machine before minimisation = %d.\n",
           difflabsptr->states->size);
  if (readback) {
    if (fsa_labeled_minimize(difflabsptr) == -1)
      exit(1);
  }
  else if (fsa_ip_labeled_minimize(difflabsptr) == -1)
    exit(1);
  if (kbm_print_level > 1)
    printf("  #Number of states of labeled machine after minimisation = %d.\n",
           difflabsptr->states->size);

  base_prefix(fsaname);
  strcat(fsaname, ".difflabs");
  wfile = fopen(outf, "w");
  fsa_print(wfile, difflabsptr, fsaname);
  fclose(wfile);

  if (kbm_print_level > 0)
    printf("#Labeled word-difference machine with %d states computed.\n",
           difflabsptr->states->size);

  fsa_clear(difflabsptr);
  tfree(difflabsptr);
  tfree(rs_wd.wd_fsa);
  exit(0);
}

void badusage(void)
{
  fprintf(stderr,
          "Usage: gpdifflabs [-diff1] [-op d/s] [-silent] [-v] [-l/-h]\n");
  fprintf(stderr, "                   [-f] groupname fsaname.\n");
  exit(1);
}
