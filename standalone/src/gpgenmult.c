/* gpgenmult.c 3/11/94.
 * 6/8/98 large scale reorganisation to eliminate globals, etc.
 * 5/2/98 change generators from type char to type `gen'.
 *
 * SYNOPSIS:
 * gpgenmult [-op d/s] [-silent] [-v] [-l/-h] [-c] [-mwd maxwdiffs]
 *           [-m maxeqns] [-ns] [-f] groupname
 *
 * Input is from groupname.wa and groupname.diff2
 *  (and possibly from groupname.diff1 if -c option is
 *   called).
 * Output is to groupname.gm
 *  (or possibly to groupname.diff1 if -c option is called).
 *
 * OPTIONS:
 * -op d/s	output in dense or sparse format - sparse is default
 * -v		verbose
 * -silent	no diagnostics
 * -l/-h	large/huge hash-tables (for big examples)
 * -c		(correction)
 *              If equations are discovered which proves the word-acceptor
 *              to be incorrect, then the first word-difference machine
 *              (which should be in file groupname.diff1) is updated by making
 *              it accept these equations.
 *              There is no point in calling this option if gpwa was run
 *              with input from groupname.diff2, since such an equation
 *              cannot occur in that case.
 * -mwd maxwdiffs
 *              At most maxwdiffs word-differences possible.
 * -m  maxeqns
 *		(only relevant if -c is called)
 *              Abort the multiplier checking process after finding maxeqns
 *              offending words w (see above) -  default is MAXEQNS
 * -ns		Don't stop if nontrivial equation found in word-acceptor
 *		language.
 * -f           read the transition table repeatedly from file while mimimizing.
 *              this avoids storing the large table, but is a little slower.
 *
 * EXIT STATUS:
 * If new equations are discovered, then the exit status is 2
 * (whether or not the correction option was called).
 * Otherwise, with normal output to groupname.gm, status is 0.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"
#define MAXWDIFFS 4096
#define MAXEQNS 512
#define MAXSUBWDLEN 8192

static FILE *rfile, *wfile;

static void badusage(void);
int (*reduce_word)(gen *w, reduction_struct *rs_rws);

int main(int argc, char *argv[])
{
  int arg, i, *inv, ngens, maxwdiffs, maxeqns;
  fsa wa, diff1, diff2, *genmultptr;
  char inf1[100], inf2[100], inf3[100], outf[100], fsaname[100],
      tempfilename[100];
  reduction_equation *eqnptr;
  reduction_struct rs_wd;
  boolean correction = FALSE;
  boolean foundeqns;
  storage_type op_store = SPARSE;
  boolean eqnstop = TRUE;
  boolean readback = TRUE;

  setbuf(stdout, (char *)0);
  setbuf(stderr, (char *)0);

  maxwdiffs = MAXWDIFFS;
  maxeqns = MAXEQNS;
  inf1[0] = '\0';
  arg = 1;
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
    else if (strcmp(argv[arg], "-c") == 0)
      correction = TRUE;
    else if (strcmp(argv[arg], "-ns") == 0)
      eqnstop = FALSE;
    else if (strcmp(argv[arg], "-f") == 0)
      readback = FALSE;
    else if (strcmp(argv[arg], "-mwd") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      maxwdiffs = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-m") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      maxeqns = atoi(argv[arg]);
    }
    else {
      if (argv[arg][0] == '-')
        badusage();
      if (strcmp(inf1, "") != 0)
        badusage();
      else
        strcpy(inf1, argv[arg]);
    }
    arg++;
  }

  strcpy(tempfilename, inf1);
  strcat(tempfilename, "temp_triples_XXX");

  strcpy(inf2, inf1);
  strcat(inf2, ".diff2");

  if (correction) {
    strcpy(inf3, inf1);
    strcat(inf3, ".diff1");
  }

  strcpy(outf, inf1);
  strcat(outf, ".gm");

  strcat(inf1, ".wa");

  if ((rfile = fopen(inf1, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf1);
    exit(1);
  }
  fsa_read(rfile, &wa, DENSE, 0, 0, TRUE, fsaname);
  fclose(rfile);
  if ((rfile = fopen(inf2, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf2);
    exit(1);
  }
  fsa_read(rfile, &diff2, DENSE, 0, 0, TRUE, fsaname);
  fclose(rfile);

  if (correction)
    tmalloc(eqnptr, reduction_equation, maxeqns) else
    {
      eqnptr = 0;
      maxeqns = 0;
    }

  genmultptr = fsa_triples(&wa, &diff2, op_store, TRUE, tempfilename, eqnptr,
                           maxeqns, eqnstop, &foundeqns, readback);

  if (foundeqns) { /*This is the case where new equations were found. */
    if (correction) {
      if (kbm_print_level > 1)
        printf("  #Altering wd-machine to make it accept new equations.\n");
      if ((rfile = fopen(inf3, "r")) == 0) {
        fprintf(stderr, "Cannot open file %s.\n", inf3);
        exit(1);
      }
      fsa_read(rfile, &diff1, DENSE, 0, maxwdiffs, TRUE, fsaname);
      fclose(rfile);
      if (fsa_table_dptr_init(&diff1) == -1)
        exit(1);
      reduce_word = diff_reduce;
      if (fsa_table_dptr_init(&diff1) == -1)
        exit(1);

      /* We need to know the inverses of generators - let's just work them out!
       */
      ngens = diff1.alphabet->base->size;
      rs_wd.wd_fsa = &diff2;
      if (calculate_inverses(&inv, ngens, &rs_wd) == -1)
        exit(1);

      i = 0;
      while (eqnptr[i].lhs && i < maxeqns) {
        if (add_wd_fsa(&diff1, eqnptr + i, inv, FALSE, &rs_wd) == -1)
          exit(1);
        i++;
      }

      if (kbm_print_level > 1)
        printf("  #Word-difference machine now has %d states.\n",
               diff1.states->size);

      wfile = fopen(inf3, "w");
      fsa_print(wfile, &diff1, fsaname);
      fclose(wfile);

      tfree(inv);
      fsa_clear(&diff1);
      i = 0;
      while (eqnptr[i].lhs && i < maxeqns) {
        tfree(eqnptr[i].lhs);
        tfree(eqnptr[i].rhs);
        i++;
      }
      tfree(eqnptr);
    }
    fsa_clear(&diff2);
    exit(2);
  }

  if (genmultptr == 0)
    exit(1);

  if (kbm_print_level > 1)
    printf("  #Number of states of triples before minimisation = %d.\n",
           genmultptr->states->size);
  if (readback) {
    if (fsa_labeled_minimize(genmultptr) == -1)
      exit(1);
  }
  else if (fsa_ip_labeled_minimize(genmultptr) == -1)
    exit(1);
  if (kbm_print_level > 1)
    printf("  #Number of states of triples after minimisation = %d.\n",
           genmultptr->states->size);

  base_prefix(fsaname);
  strcat(fsaname, ".gm");
  wfile = fopen(outf, "w");
  fsa_print(wfile, genmultptr, fsaname);
  fclose(wfile);

  if (kbm_print_level > 0)
    printf("#Generalised multiplier with %d states computed.\n",
           genmultptr->states->size);

  fsa_clear(genmultptr);
  tfree(genmultptr);
  if (correction)
    tfree(eqnptr);
  exit(0);
}

void badusage(void)
{
  fprintf(stderr, "Usage: gpgenmult [-op d/s] [-silent] [-v] [-l/-h] [-c] "
                  "[-mwd maxwdiffs]\n");
  fprintf(stderr, "\t\t [-m maxeqns] [-ns] [-f] groupname.\n");
  exit(1);
}
