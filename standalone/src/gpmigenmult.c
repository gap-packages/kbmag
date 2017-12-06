/* gpmigenmult.c 11/10/94.
 * 6/8/98 large scale reorganisation to omit globals, etc.
 * 16/3/96 - changed command-line syntax to
 * gpmigenmult [options] groupname [cosname]
 * where cosname defaults to "cos".
 * Calculates the general multiplier with multiple initial states for a
 * short-lex coset automatic group.
 * Very similar to gpgenmult.c
 *
 * SYNOPSIS:
 * gpmigenmult [-op d/s] [-silent] [-v] [-l/-h] [-c] [-mwd maxwdiffs]
 *           [-m maxeqns] [-ns] groupname [cosname]
 *
 * Input is from groupname.cosname.wa and groupname.cosname.midiff2
 *  (and possibly from groupname.cosname.midiff1 if -c option is called).
 * Output is to groupname.cosname.migm
 *  (or possibly to groupname.cosname.midiff1 if -c option is called).
 *
 * OPTIONS:
 * -op d/s	output in dense or sparse format - sparse is default
 * -v		verbose
 * -silent	no diagnostics
 * -l/-h	large/huge hash-tables (for big examples)
 * -c		(correction)
 *              If equations are discovered which proves the word-acceptor
 *              to be incorrect, then the first word-difference machine
 *              (which should be in file groupname.cosname.midiff1) is updated
 *              by making it accept these equations.
 *              There is no point in calling this option if gpwa was run
 *              with input from groupname.cosname.midiff2, since such an
 *              equation cannot occur in that case.
 * -mwd maxwdiffs
 *              At most maxwdiffs word-differences possible.
 * -m  maxeqns
 *		(only relevant if -c is called)
 *              Abort the multiplier checking process after finding maxeqns
 *              offending words w (see above) -  default is MAXEQNS
 * -ns		Don't stop if nontrivial equation found in word-acceptor
 *		language.
 *
 * EXIT STATUS:
 * If new equations are discovered, then the exit status is 2
 * (whether or not the correction option was called).
 * Otherwise, with normal output to groupname.cosname.migm, status is 0.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"
#define MAXWDIFFS 4096
#define MAXEQNS 512

static FILE *rfile, *wfile;

static void badusage(void);
int (*reduce_word)(gen *w, reduction_struct *rs_rws);

int main(int argc, char *argv[])
{
  int arg, i, ct, *inv, ngens, maxwdiffs, maxeqns;
  fsa wa, diff1, diff2, *migenmultptr;
  char gpname[100], inf1[100], inf2[100], inf3[100], outf[100], fsaname[100],
      tempfilename[100];
  reduction_equation *eqnptr;
  reduction_struct rs_wd;
  boolean correction = FALSE;
  storage_type op_store = SPARSE;
  boolean eqnstop = TRUE;
  boolean foundeqns;
  boolean readback = TRUE;
  boolean seengpname, seencosname;

  setbuf(stdout, (char *)0);
  setbuf(stderr, (char *)0);

  maxwdiffs = MAXWDIFFS;
  maxeqns = MAXEQNS;
  inf1[0] = '\0';
  arg = 1;
  seengpname = seencosname = FALSE;
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
    else if (strcmp(argv[arg], "-f") == 0) {
      readback = FALSE;
      fprintf(stderr, "Sorry - readback option not yet available.\n");
      exit(1);
    }
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
    else if (argv[arg][0] == '-')
      badusage();
    else if (!seengpname) {
      seengpname = TRUE;
      strcpy(gpname, argv[arg]);
    }
    else if (!seencosname) {
      seencosname = TRUE;
      sprintf(inf1, "%s.%s", gpname, argv[arg]);
    }
    else
      badusage();
    arg++;
  }
  if (!seengpname)
    badusage();
  if (!seencosname)
    sprintf(inf1, "%s.cos", gpname);

  strcpy(tempfilename, inf1);
  strcat(tempfilename, "temp_triples_XXX");

  strcpy(inf2, inf1);
  strcat(inf2, ".midiff2");

  if (correction) {
    strcpy(inf3, inf1);
    strcat(inf3, ".midiff1");
  }

  strcpy(outf, inf1);
  strcat(outf, ".migm");

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

  migenmultptr = fsa_mitriples(&wa, &diff2, op_store, TRUE, tempfilename,
                               eqnptr, maxeqns, eqnstop, &foundeqns, readback);

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
      tmalloc(diff1.is_initial, boolean, maxwdiffs + 1);
      for (i = 1; i <= maxwdiffs; i++)
        diff1.is_initial[i] = FALSE;
      for (i = 1; i <= diff1.num_initial; i++)
        diff1.is_initial[diff1.initial[i]] = TRUE;
      reduce_word = diff_reduce_cos;
      if (fsa_table_dptr_init(&diff1) == -1)
        exit(1);

      /* We need to know the inverses of generators - let's just work them out!
       */
      ngens = diff1.alphabet->base->size;
      rs_wd.wd_fsa = &diff2;
      rs_wd.separator = diff2.alphabet->base->size + 1;
      if (calculate_inverses(&inv, ngens, &rs_wd) == -1)
        exit(1);

      i = 0;
      while (eqnptr[i].lhs && i < maxeqns) {
        if (add_wd_fsa_cos(&diff1, eqnptr + i, inv, FALSE, &rs_wd) == -1)
          exit(1);
        i++;
      }
      tfree(diff1.initial);
      tmalloc(diff1.initial, int, diff1.num_initial + 1);
      ct = 0;
      for (i = 1; i <= diff1.states->size; i++)
        if (diff1.is_initial[i])
          diff1.initial[++ct] = i;
      tfree(diff1.is_initial);

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

  if (migenmultptr == 0)
    exit(1);

  if (kbm_print_level > 1)
    printf("  #Number of states of mi-multiplier before minimisation = %d.\n",
           migenmultptr->states->size);
  if (readback) {
    if (midfa_labeled_minimize(migenmultptr) == -1)
      exit(1);
  }
  /*
    else
      fsa_ip_labeled_minimize(migenmultptr);
  */
  if (kbm_print_level > 1)
    printf("  #Number of states of mi-multipler after minimisation = %d.\n",
           migenmultptr->states->size);

  base_prefix(fsaname);
  strcat(fsaname, ".migm");
  wfile = fopen(outf, "w");
  fsa_print(wfile, migenmultptr, fsaname);
  fclose(wfile);

  if (kbm_print_level > 0)
    printf("#Generalised multiplier with %d states computed.\n",
           migenmultptr->states->size);

  fsa_clear(migenmultptr);
  tfree(migenmultptr);
  if (correction)
    tfree(eqnptr);
  exit(0);
}

void badusage(void)
{
  fprintf(stderr, "Usage: gpmigenmult [-op d/s] [-silent] [-v] [-l/-h] [-c] "
                  "[-mwd maxwdiffs]\n");
  fprintf(stderr, "		 [-m maxeqns] [-ns] groupname [cosname].\n");
  exit(1);
}
