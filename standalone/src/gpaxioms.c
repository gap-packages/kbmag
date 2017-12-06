/* gpaxioms.c   14.12.94.
 * 13/10/98 large scale reorganisation to omit globals, etc.
 * 25/5/98 added -n option, which means do not form the generalised
 * length 2 multiplier, but check all group relations, including the
 * inverse relations, by forming composites of the multipliers.
 * This may be advantageous when there is a very large number of
 * generators.
 *
 * 5/2/98 change generators from type char to type `gen'.
 * 1/11/96 added experimental option -x, meaning read group relators from a
 * different file (groupname_x) and do not balance relators when axiom checking.
 * This is for the  case when generators may reduce to words of length
 * greater than one, when using orderings other than shortlex.
 *
 * 8/1/96  - output a file gpname.kbprog.exitcode containing a GAP statement
 *        giving the exit code - for use with GAP interface
 * 15/3/96 changed syntax of -cos call to
 * gpmakefsa -cos groupname [cosname]
 * where cosname defaults to "cos".
 * In the coset case, we can now read the relators from groupname rather than
 * groupname.cosname, which is better.
 *
 * 17/1/96 - remove all of the processing of redundant generators, which is
 * no longer necessary, and merely complicates the program.
 *
 * 25/9/95 -added capability of doing the calculations for coset
 * automatic groups - with the -cos option
 *
 * Carry out the axiom-checking for a short-lex (or wtlex) automatic group.
 *
 * SYNOPSIS:
 * gpaxioms [-ip d/s[dr]] [-op d/s] [-silent] [-v] [-l] [-f] [-s] [-n]
 * [-cos] groupname [-cosname]
 *
 * OPTIONS:
 * -ip d/s[dr]  input in dense or sparse format - dense is default
 * -op d/s      output in dense or sparse format - sparse is default
 * -v           verbose
 * -silent      no diagnostics
 * -l/-h        large/huge hash-tables (for big examples)
 * -f           read the transition table repeatedly from file while mimimizing,
 *              in calls of fsa_genmult2 and fsa_composite.
 *              This avoids storing large tables, but is a little slower.
 * -s		Throw away files immediately after use whenever possible, to
 *              save disk-space. This will slow things down considerably.
 * -n		do not form generalised length 2 multiplier.
 * -cos         Do the calculation for coset automatic groups (by setting
 *              global variable cosets to be TRUE).
 */

#include <stdio.h>

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"

#define MAXEQNS 1024
#define MAXREDUCELEN 2048

static rewriting_system rws, *rwsptr;
static boolean xset = FALSE;

static char gpname[100], cosgpname[100], inf[100], outf[100], outfec[100],
    fsaname[100], tablefilename[100], *rwsfilename;
static fsa genmult, genmult2, *genmult2ptr, mult1, mult2, *compmult;
static int ngens, neqns, *inv, nlabgm2;
static int numstoredmult;
static reduction_equation *eqn;
static gen *lhs, *rhs, ***labgm2;
static char **storedmult;
static boolean allshort;
static storage_type ip_store = DENSE;
static int dr = 0;
static storage_type op_store = SPARSE;
static boolean readback = TRUE;
static boolean keepfiles = TRUE;
static boolean usegm2 = TRUE;
static FILE *rfile, *wfile;

/* Functions defined in this file */

static void balance_equations(void);
static int check_short_relation(void);
static int check_long_relation(void);
static char *file_suffix(gen *w);
static int long_word_multiplier(gen *w, char *s);
static void badusage(void);

int main(int argc, char *argv[])
{
  int arg, i, ct, clr;
  boolean seengpname, seencosname, cosets;

  setbuf(stdout, (char *)0);
  setbuf(stderr, (char *)0);

  rwsptr = &rws;
  rwsptr->maxeqns = MAXEQNS;
  rwsptr->maxreducelen = MAXREDUCELEN;
  rwsptr->maxreducelenset = FALSE;
  rwsptr->cosets = FALSE;
  /* even in the cosets case we read relations from original group file */
  rwsptr->inv_of = 0;
  rwsptr->weight = 0;
  rwsptr->level = 0;
  rwsptr->history = 0;
  rwsptr->slowhistory = 0;
  rwsptr->slowhistorysp = 0;
  rwsptr->preflen = 0;
  rwsptr->prefno = 0;
  arg = 1;
  seengpname = seencosname = cosets = FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg], "-ip") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      if (strcmp(argv[arg], "d") == 0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's') {
        ip_store = SPARSE;
        if (stringlen(argv[arg]) > 1)
          dr = atoi(argv[arg] + 1);
      }
      else
        badusage();
    }
    else if (strcmp(argv[arg], "-op") == 0) {
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
    else if (strcmp(argv[arg], "-f") == 0)
      readback = FALSE;
    else if (strcmp(argv[arg], "-s") == 0)
      keepfiles = FALSE;
    else if (strncmp(argv[arg], "-cos", 4) == 0)
      cosets = TRUE;
    else if (strcmp(argv[arg], "-x") == 0)
      xset = TRUE;
    else if (strcmp(argv[arg], "-n") == 0)
      usegm2 = FALSE;
    else if (argv[arg][0] == '-')
      badusage();
    else if (!seengpname) {
      seengpname = TRUE;
      strcpy(gpname, argv[arg]);
    }
    else if (!seencosname) {
      seencosname = TRUE;
      sprintf(cosgpname, "%s.%s", gpname, argv[arg]);
    }
    else
      badusage();
    arg++;
  }
  if (!seengpname)
    badusage();
  if (cosets && !seencosname)
    sprintf(cosgpname, "%s.cos", gpname);

  if (cosets)
    sprintf(outfec, "%s.axioms.ec", cosgpname);
  else
    sprintf(outfec, "%s.axioms.ec", gpname);

  rwsfilename = cosets ? cosgpname : gpname;
  strcpy(tablefilename, rwsfilename);
  strcat(tablefilename, "temp_axXXX");

  /* First read in the defining relations for the group. */
  strcpy(inf, gpname);
  if (xset)
    strcat(inf, "_x");
  if ((rfile = fopen(inf, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf);
    exit(1);
  }
  read_kbinput_simple(rfile, FALSE, rwsptr);
  fclose(rfile);
  ngens = rws.num_gens;
  neqns = rws.num_eqns;
  inv = rws.inv_of;
  eqn = rws.eqns;

  /* Now balance the equations. */
  balance_equations();

  if (usegm2) {
    allshort = TRUE;
    /* See if all relations are short (length(lhs)=2 ) */
    for (i = 1; i <= neqns; i++)
      if (genstrlen(eqn[i].lhs) > 2) {
        allshort = FALSE;
        break;
      }
  }
  else
    allshort = FALSE;

  if (usegm2) {
    /* Now calculate the general multiplier for words of length 2.
     * If allshort is true, we don't need the transitions - only the state
     * labels.
     */
    strcpy(inf, rwsfilename);
    strcat(inf, ".gm");
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf);
      exit(1);
    }
    fsa_read(rfile, &genmult, ip_store, dr, 0, TRUE, fsaname);
    fclose(rfile);

    if (kbm_print_level > 1)
      printf("  #Calculating general word-length 2 multiplier.\n");
    if (allshort) {
      genmult2ptr = fsa_genmult2(&genmult, op_store, TRUE, "", FALSE);
      if (genmult2ptr == 0)
        exit(1);
      if (kbm_print_level > 1)
        printf("  #Number of states of genmult2 = %d.\n",
               genmult2ptr->states->size);
    }
    else {
      genmult2ptr =
          fsa_genmult2(&genmult, op_store, TRUE, tablefilename, readback);
      if (genmult2ptr == 0)
        exit(1);
      if (kbm_print_level > 1)
        printf("  #Number of states of genmult2 = %d.\n",
               genmult2ptr->states->size);

      if (readback) {
        if (fsa_labeled_minimize(genmult2ptr) == -1)
          exit(1);
      }
      else {
        if (fsa_ip_labeled_minimize(genmult2ptr) == -1)
          exit(1);
      }
      if (kbm_print_level > 1)
        printf("  #Number of states of genmult2 after minimization = %d.\n",
               genmult2ptr->states->size);
      strcpy(fsaname, rws.name);
      strcat(fsaname, ".gm2");
      strcpy(outf, rwsfilename);
      strcat(outf, ".gm2");
      wfile = fopen(outf, "w");
      fsa_print(wfile, genmult2ptr, fsaname);
      if (kbm_print_level > 0)
        printf("#General length-2 multiplier with %d states computed.\n",
               genmult2ptr->states->size);
      fclose(wfile);
    }

    /* Now we check axioms for inverse-relators and short-relators, by simply
     * checking that the state-labels for the lhs and rhs correspond in
     * *genmult2ptr.
     */
    if (kbm_print_level > 0) {
      printf("#Checking inverse and short relations.\n");
    }
    nlabgm2 = genmult2ptr->states->labels->size;
    labgm2 = genmult2ptr->states->labels->wordslist;
    lhs = rws.testword1;
    rhs = rws.testword2;
    for (i = 1; i <= ngens; i++)
      if (inv[i]) {
        lhs[0] = i;
        lhs[1] = inv[i];
        lhs[2] = '\0';
        rhs[0] = '\0';
        if (check_short_relation() == 2)
          exit(2);
      }
    for (i = 1; i <= neqns; i++)
      if (genstrlen(eqn[i].lhs) == 2) {
        lhs = eqn[i].lhs;
        rhs = eqn[i].rhs;
        if (check_short_relation() == 2)
          exit(2);
      }
    fsa_clear(genmult2ptr);
  }

  /* Finally we deal with the other relations, if any */
  if (!allshort) {
    /* If keepfiles is false, then we will throw away every multiplier
     * immediately after it has been used. Otherwise, we will keep them, in case
     * they are needed again. We store a list of words for which we have got the
     * multipliers in storedmult. We first form a rough upper bound on how long
     * this list could get - ngens + total relator length - 1.
     */
    strcpy(fsaname, rws.name);
    strcat(fsaname, ".mult"); /* this is unimportant, since file is temporary */
    if (keepfiles) {
      ct = usegm2 ? ngens : 2 * ngens;
      for (i = 1; i <= neqns; i++)
        if (!usegm2 || genstrlen(eqn[i].lhs) > 2)
          ct += (genstrlen(eqn[i].lhs) + genstrlen(eqn[i].rhs));
      tmalloc(storedmult, char *, ct);
      numstoredmult = 0;
    }

    if (!usegm2)
      for (i = 1; i <= ngens; i++)
        if (inv[i]) {
          lhs = rws.testword1;
          rhs = rws.testword2;
          lhs[0] = i;
          lhs[1] = inv[i];
          lhs[2] = '\0';
          rhs[0] = '\0';
          clr = check_long_relation();
          if (clr == -1)
            exit(1);
          if (clr == 2)
            exit(2);
        }
    for (i = 1; i <= neqns; i++)
      if (!usegm2 || genstrlen(eqn[i].lhs) > 2) {
        lhs = eqn[i].lhs;
        rhs = eqn[i].rhs;
        clr = check_long_relation();
        if (clr == -1)
          exit(1);
        if (clr == 2)
          exit(2);
      }
    if (keepfiles) {
      for (i = 1; i <= numstoredmult; i++) {
        sprintf(outf, "%s.m%s", rwsfilename, storedmult[i]);
        unlink(outf);
        tfree(storedmult[i]);
      }
      tfree(storedmult);
    }
    strcpy(outf, rwsfilename);
    strcat(outf, ".gm2");
    unlink(outf);
  }
  tfree(genmult2ptr);
  rws_clear(&rws);
  if (kbm_print_level > 0)
    printf("#Axiom checking succeeded.\n");
  wfile = fopen(outfec, "w");
  fprintf(wfile, "_ExitCode := 0;\n");
  fclose(wfile);
  exit(0);
}

void balance_equations(void)
{
  int i, l1, l2;
  gen *lhs, *rhs;
  if (kbm_print_level > 1)
    printf("  #Simplifying and balancing inverse-list and relations.\n");

  for (i = 1; i <= neqns; i++) {
    lhs = eqn[i].lhs;
    rhs = eqn[i].rhs;
    l1 = genstrlen(lhs);
    l2 = genstrlen(rhs);
    if (l1 + l2 <= 2) { /*We no longer need keep this equation */
      if (kbm_print_level > 1)
        printf("  #Equation number %d is being discarded.\n", i);
      lhs[0] = rhs[0] = '\0';
    }
    else {           /* balance the lengths of the lhs and rhs. */
      if (l2 > l1) { /* swap lhs and rhs */
        eqn[i].lhs = rhs;
        eqn[i].rhs = lhs;
        lhs = eqn[i].lhs;
        rhs = eqn[i].rhs;
        l1 = genstrlen(lhs);
        l2 = genstrlen(rhs);
      }
      if (!xset)
        while (l1 - l2 > 1) { /* move a generator from lhs to rhs */
          rhs[l2] = inv[lhs[l1 - 1]];
          l2++;
          rhs[l2] = '\0';
          l1--;
          lhs[l1] = '\0';
        }
    }
  }
}

/* Check that the general multiplier automaton *genmult2ptr for words of
 * length two satisfies the short-equation lhs = rhs.
 * This is done merely by looking at the state-labels of *genmult2ptr.
 * The transitions are not needed.
 */
int check_short_relation(void)
{
  int i, j;
  gen **lab;
  boolean foundlhs, foundrhs;
  if (kbm_print_level > 1) {
    kbm_buffer[0] = '\0';
    add_to_buffer(0, "  #Checking short relation:  ");
    add_word_to_buffer(stdout, lhs, rws.gen_name);
    add_to_buffer(0, " = ");
    add_word_to_buffer(stdout, rhs, rws.gen_name);
    printbuffer(stdout);
  }
  /* pad rhs to length 2 if necessary */
  if (genstrlen(rhs) == 0) {
    rhs[0] = rhs[1] = ngens + 1;
    rhs[2] = '\0';
  }
  else if (genstrlen(rhs) == 1) {
    rhs[1] = ngens + 1;
    rhs[2] = '\0';
  }
  /* Search through the state-labels of genmult2ptr.
   * For the relation to be satisfied by the fsa, it must be the case that
   * lhs occurs in a label <=> rhs occurs in that label.
   */
  for (i = 1; i <= nlabgm2; i++) {
    foundlhs = foundrhs = FALSE;
    lab = labgm2[i];
    j = 0;
    while (lab[j]) {
      if (lab[j][0] == lhs[0] && lab[j][1] == lhs[1])
        foundlhs = TRUE;
      if (lab[j][0] == rhs[0] && lab[j][1] == rhs[1])
        foundrhs = TRUE;
      j++;
    }
    if (foundlhs != foundrhs) {
      kbm_buffer[0] = '\0';
      add_to_buffer(0, "#Relation check fails for short relation:  ");
      add_word_to_buffer(stdout, lhs, rws.gen_name);
      add_to_buffer(0, " = ");
      add_word_to_buffer(stdout, rhs, rws.gen_name);
      printbuffer(stdout);
      wfile = fopen(outfec, "w");
      fprintf(wfile, "_ExitCode := 2;\n");
      fclose(wfile);
      return 2;
    }
  }
  return 0;
}

/* Check that the multipliers satisfy the long relation of which the
 * left and right hand sides are store din lhs and rhs, by forming
 * the necessary composites.
 */
int check_long_relation(void)
{
  int j, l;
  char *suffl, *suffr;
  boolean gotl, gotr;
  if (kbm_print_level > 0) {
    kbm_buffer[0] = '\0';
    add_to_buffer(0, "#Checking relation:  ");
    add_word_to_buffer(stdout, lhs, rws.gen_name);
    add_to_buffer(0, " = ");
    if ((l = stringlen(kbm_buffer)) > 44) {
      printbuffer(stdout);
      add_to_buffer(21, "");
    }
    add_word_to_buffer(stdout, rhs, rws.gen_name);
    printbuffer(stdout);
  }
  suffl = file_suffix(lhs);
  suffr = file_suffix(rhs);
  gotl = gotr = FALSE;
  if (keepfiles) {
    /* Check to see if we have either of these multipliers already */
    for (j = 1; j <= numstoredmult; j++) {
      if (strcmp(suffl, storedmult[j]) == 0)
        gotl = TRUE;
      if (strcmp(suffr, storedmult[j]) == 0)
        gotr = TRUE;
    }
  }
  if (!gotl) {
    if (long_word_multiplier(lhs, suffl) == -1)
      return -1;
  }
  if (!gotr) {
    if (long_word_multiplier(rhs, suffr) == -1)
      return -1;
  }
  /* Read in the two multipliers and compare them */
  sprintf(inf, "%s.m%s", rwsfilename, suffl);

  if ((rfile = fopen(inf, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf);
    exit(1);
  }
  fsa_read(rfile, &mult1, ip_store, 0, 0, TRUE, fsaname);
  fclose(rfile);
  sprintf(inf, "%s.m%s", rwsfilename, suffr);
  if ((rfile = fopen(inf, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf);
    exit(1);
  }
  fsa_read(rfile, &mult2, ip_store, 0, 0, TRUE, fsaname);
  fclose(rfile);
  if (!fsa_equal(&mult1, &mult2)) {
    kbm_buffer[0] = '\0';
    add_to_buffer(0, "#Relation check fails for relation:  ");
    add_word_to_buffer(stdout, lhs, rws.gen_name);
    add_to_buffer(0, " = ");
    add_word_to_buffer(stdout, rhs, rws.gen_name);
    printbuffer(stdout);
    wfile = fopen(outfec, "w");
    fprintf(wfile, "_ExitCode := 2;\n");
    fclose(wfile);
    return 2;
  }
  fsa_clear(&mult1);
  fsa_clear(&mult2);
  if (keepfiles) {
    if (gotl)
      tfree(suffl) else storedmult[++numstoredmult] = suffl;
    if (gotr)
      tfree(suffr) else storedmult[++numstoredmult] = suffr;
  }
  else {
    sprintf(inf, "%s.m%s", rwsfilename, suffl);
    unlink(inf);
    sprintf(inf, "%s.m%s", rwsfilename, suffr);
    unlink(inf);
    tfree(suffl);
    tfree(suffr);
  }
  return 0;
}

/* For a word w in the generators, this function returns a corresponding
 * string with the terms of w replaced by integers separated by '_'.
 * This is used as a suffix in the filenames used for storing the
 * corresponding multiplier fsa's.
 */
char *file_suffix(gen *w)
{
  char *s;
  gen *p;
  boolean first;
  int len;
  /* First work out the length of the required string. */
  len = genstrlen(w);
  if (len == 0) {
    tmalloc(s, char, 2);
    s[0] = '0';
    s[1] = '\0';
    return s;
  }
  p = w - 1;
  while (*(++p) != 0)
    len += int_len((int)(*p));
  tmalloc(s, char, len);
  s[0] = '\0';
  first = TRUE;
  p = w - 1;
  while (*(++p) != 0) {
    if (first)
      first = FALSE;
    else
      sprintf(s + stringlen(s), "_");
    sprintf(s + stringlen(s), "%d", *p);
  }
  return s;
}

/* Calculate the multiplier associated with the word w.
 * s is the suffix of the file in which it will be stored.
 * (s has been derived from w by a call of file_suffix).
 */
int long_word_multiplier(gen *w, char *s)
{
  int i, l;
  gen *wl, *wlt, *wr, *wrt;
  char *suffl, *sufflt, *suffr, *suffrt;
  boolean gotl, gotr, gotlt, gotrt;
  if (kbm_print_level >= 3) {
    kbm_buffer[0] = '\0';
    add_to_buffer(0, "  #Calculating multiplier for word:  ");
    add_word_to_buffer(stdout, w, rws.gen_name);
    printbuffer(stdout);
  }
  l = genstrlen(w);

  if (l <= 1) { /* Length <=1 - use fsa_makemult */
    strcpy(inf, rwsfilename);
    strcat(inf, ".gm");
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf);
      exit(1);
    }
    fsa_read(rfile, &genmult, op_store, 0, 0, TRUE, fsaname);
    fclose(rfile);
    if (fsa_makemult(&genmult, w[0]) == -1)
      return -1;
    if (fsa_minimize(&genmult) == -1)
      return -1;
    sprintf(outf, "%s.m%s", rwsfilename, s);
    wfile = fopen(outf, "w");
    fsa_print(wfile, &genmult, fsaname);
    fclose(wfile);
    fsa_clear(&genmult);
  }
  else if (usegm2 && l == 2) { /* Length 2 - use fsa_makemult2 */
    strcpy(inf, rwsfilename);
    strcat(inf, ".gm2");
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf);
      exit(1);
    }
    fsa_read(rfile, &genmult2, op_store, 0, 0, TRUE, fsaname);
    fclose(rfile);
    if (fsa_makemult2(&genmult2, w[0], w[1]) == -1)
      return -1;
    if (fsa_minimize(&genmult2) == -1)
      return -1;
    sprintf(outf, "%s.m%s", rwsfilename, s);
    wfile = fopen(outf, "w");
    fsa_print(wfile, &genmult2, fsaname);
    fclose(wfile);
    fsa_clear(&genmult2);
  }
  else { /* general case - we have to split w up */
    if (l % 2 == 0) {
      tmalloc(wl, gen, l / 2 + 1);
      tmalloc(wr, gen, l / 2 + 1);
      for (i = 0; i < l / 2; i++)
        wl[i] = w[i];
      wl[l / 2] = '\0';
      genstrcpy(wr, w + l / 2);
      suffl = file_suffix(wl);
      suffr = file_suffix(wr);
    }
    else {
      tmalloc(wl, gen, l / 2 + 2);
      tmalloc(wr, gen, l / 2 + 1);
      for (i = 0; i <= l / 2; i++)
        wl[i] = w[i];
      wl[l / 2 + 1] = '\0';
      genstrcpy(wr, w + l / 2 + 1);
      suffl = file_suffix(wl);
      suffr = file_suffix(wr);
    }
    /* See whether we have either of them already */
    gotl = gotr = FALSE;
    if (keepfiles) {
      for (i = 1; i <= numstoredmult; i++) {
        if (strcmp(suffl, storedmult[i]) == 0)
          gotl = TRUE;
        if (strcmp(suffr, storedmult[i]) == 0)
          gotr = TRUE;
      }
    }

    if (keepfiles && l % 2 == 1 && (!gotl || !gotr)) {
      /* In this case, there are two possible ways to split w up -
       * we see if the other way has more multipliers already stored.
       */
      tmalloc(wlt, gen, l / 2 + 1);
      tmalloc(wrt, gen, l / 2 + 2);
      for (i = 0; i < l / 2; i++)
        wlt[i] = w[i];
      wlt[l / 2] = '\0';
      genstrcpy(wrt, w + l / 2);
      sufflt = file_suffix(wlt);
      suffrt = file_suffix(wrt);
      gotlt = gotrt = FALSE;
      for (i = 1; i <= numstoredmult; i++) {
        if (strcmp(sufflt, storedmult[i]) == 0)
          gotlt = TRUE;
        if (strcmp(suffrt, storedmult[i]) == 0)
          gotrt = TRUE;
      }
      if ((gotlt && gotrt) || ((gotlt || gotrt) && !gotl && !gotr)) {
        tfree(wl);
        tfree(wr);
        tfree(suffl);
        tfree(suffr);
        wl = wlt;
        wr = wrt;
        suffl = sufflt;
        suffr = suffrt;
        gotl = gotlt;
        gotr = gotrt;
      }
      else {
        tfree(wlt);
        tfree(wrt);
        tfree(sufflt);
        tfree(suffrt);
      }
    }
    if (!gotl) {
      if (long_word_multiplier(wl, suffl) == -1)
        return -1;
    }
    if (!gotr && genstrcmp(wl, wr) != 0) {
      if (keepfiles) {
        /* Check again to see if we have got it recently */
        for (i = 1; i <= numstoredmult; i++)
          if (strcmp(suffr, storedmult[i]) == 0)
            gotr = TRUE;
      }
      if (!gotr) {
        if (long_word_multiplier(wr, suffr) == -1)
          return -1;
      }
    }
    /* Read back in the two multipliers and form their composite */
    sprintf(inf, "%s.m%s", rwsfilename, suffl);
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf);
      exit(1);
    }
    fsa_read(rfile, &mult1, ip_store, dr, 0, TRUE, fsaname);
    fclose(rfile);
    sprintf(inf, "%s.m%s", rwsfilename, suffr);
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf);
      exit(1);
    }
    fsa_read(rfile, &mult2, ip_store, dr, 0, TRUE, fsaname);
    fclose(rfile);

    compmult =
        fsa_composite(&mult1, &mult2, op_store, TRUE, tablefilename, readback);
    if (compmult == 0)
      return -1;
    fsa_clear(&mult1);
    fsa_clear(&mult2);
    if (readback) {
      if (fsa_minimize(compmult) == -1)
        return -1;
    }
    else {
      if (fsa_ip_minimize(compmult) == -1)
        return -1;
    }
    sprintf(outf, "%s.m%s", rwsfilename, s);
    wfile = fopen(outf, "w");
    fsa_print(wfile, compmult, fsaname);
    fclose(wfile);
    fsa_clear(compmult);
    tfree(compmult);

    if (keepfiles) {
      if (gotl)
        tfree(suffl) else storedmult[++numstoredmult] = suffl;
      if (gotr)
        tfree(suffr) else storedmult[++numstoredmult] = suffr;
    }
    else {
      sprintf(inf, "%s.m%s", rwsfilename, suffl);
      unlink(inf);
      sprintf(inf, "%s.m%s", rwsfilename, suffr);
      unlink(inf);
      tfree(suffl);
      tfree(suffr);
    }
    tfree(wl);
    tfree(wr);
  }
  return 0;
}

void badusage(void)
{
  fprintf(stderr, "Usage: gpaxioms [-ip d/s[dr]] [-op d/s] [-silent] [-v] [-l] "
                  "[-f] [-n]\n");
  fprintf(stderr, "\t\t[-cos] groupname [cosname].\n");
  exit(1);
}
