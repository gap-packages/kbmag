/* gpsubpres.c   16/1/96.
 * 13/10/98 large scale reorganisation to omit globals, etc.
 * 16/3/96 - changed command-line syntax to
 * gpmimult [options] groupname [subfilename]
 * where subfilename defaults to "sub".
 * Find relations of a subgroup of a coset automatic group, using the
 * Schreier generators that are the initial states of the generalised
 * multiplier automaton.
 * It is based on gpaxioms. We form the coset mi-multipliers for the group
 * relators, and then their initial states are the relators of the subgroup.
 *
 * This program assumes that makecosfile, kbprogcos, gpmakefsa -cos,
 * gpaxios -cos, have already been run on groupname.
 *
 * Input is from groupname (for group relators) and groupname.cosfile.gm
 * where cosfile is derived from subfilename as in makecosfile.
 * Output is to groupname.subfilename.pres, in GAP format.
 *
 * SYNOPSIS:
 * gpsubpres [-ip d/s[dr]] [-op d/s] [-silent] [-v] [-l] [-s] [-pref prefix]
 *           groupname [subfilename]
 *
 * OPTIONS:
 * -ip d/s[dr]  input in dense or sparse format - dense is default
 * -op d/s      output in dense or sparse format - sparse is default
 * -v           verbose
 * -silent      no diagnostics
 * -l/-h        large/huge hash-tables (for big examples)
 * -s		Throw away files immediately after use whenever possible, to
 *              save disk-space. This will slow things down considerably.
 * -pref prefix Use the string 'prefix' as prefix for subgroup generators
 *              Their names are 'prefix'1. 'prefix'2, etc.
 *              Default is "_x".
 *              It will also be used as the name of the group in the GAP file.
 */

#include <stdio.h>

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"

#define MAXEQNS 1024
#define MAXREDUCELEN 4096

static rewriting_system rws, *rwsptr;

static char gpname[100], subname[100], cosgpname[100], inf[100], outf[100],
    outfp[100], fsaname[100], prefix[16], tablefilename[100];
static fsa migm, migm2, *migm2ptr;
static int ngens, neqns, *inv, numstoredmult, nsubgens;
static reduction_equation *eqn;
static char **storedmult;
static storage_type ip_store = DENSE;
static int dr = 0;
static storage_type op_store = SPARSE;
static boolean readback = TRUE;
static boolean keepfiles = TRUE;
static boolean first_relator;
static FILE *rfile, *wfile, *wfilep;

/* Functions defined in this file */
static int find_subrels(gen *r);
static int long_word_multiplier(gen *w, char *s);
static void badusage(void);

int main(int argc, char *argv[])
{
  int arg, i, j, ct;
  gen *relator, *ptr, *ptr2;
  boolean seengpname, seensubname;

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

  strcpy(prefix, "_x");
  arg = 1;
  seengpname = seensubname = FALSE;
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
    else if (strcmp(argv[arg], "-s") == 0)
      keepfiles = FALSE;
    else if (strcmp(argv[arg], "-pref") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      strcpy(prefix, argv[arg]);
    }
    else if (argv[arg][0] == '-')
      badusage();
    else if (!seengpname) {
      seengpname = TRUE;
      strcpy(gpname, argv[arg]);
    }
    else if (!seensubname) {
      seensubname = TRUE;
      strcpy(subname, argv[arg]);
    }
    else
      badusage();
    arg++;
  }
  if (!seengpname)
    badusage();
  if (!seensubname)
    strcpy(subname, "sub");
  if (strncmp(subname, "sub", 3) == 0) {
    strcpy(cosgpname, gpname);
    strcat(cosgpname, ".cos");
    strcat(cosgpname, subname + 3);
  }
  else {
    strcpy(cosgpname, gpname);
    strcat(cosgpname, ".");
    strcat(cosgpname, subname);
    strcat(cosgpname, "_cos");
  }

  strcpy(tablefilename, cosgpname);
  strcat(tablefilename, "temp_axXXX");

  /* First read in the defining relations for the group. */
  strcpy(inf, gpname);
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

  /* Now read in the general multiplier, and see how many subgroup generators
   * there are (which is just the number of initial states - 1).
   */
  strcpy(inf, cosgpname);
  strcat(inf, ".migm");
  if ((rfile = fopen(inf, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf);
    exit(1);
  }
  fsa_read(rfile, &migm, ip_store, dr, 0, TRUE, fsaname);
  fclose(rfile);

  nsubgens = migm.num_initial - 1;
  /* The first initial state always corresponds to the identity.
   * Now we can open the output file and commence the output in GAP format.
   */
  sprintf(outfp, "%s.%s.pres", gpname, subname);
  wfilep = fopen(outfp, "w");
  fprintf(wfilep, "%sg := FreeGroup(%d);\n", prefix, nsubgens);
  for (i = 1; i <= nsubgens; i++)
    fprintf(wfilep, "%s%d := %sg.%d;\n", prefix, i, prefix, i);
  fprintf(wfilep, "%s_relators:=[\n", prefix);

  /* Now calculate the general multiplier for words of length 2 */
  if (kbm_print_level > 1)
    printf("  #Calculating general word-length 2 multiplier.\n");
  migm2ptr = fsa_migm2(&migm, op_store, TRUE, tablefilename, readback, prefix);
  if (migm2ptr == 0)
    exit(1);
  if (kbm_print_level > 1)
    printf("  #Number of states of migm2 = %d.\n", migm2ptr->states->size);

  if (readback) { /* always true */
    if (midfa_labeled_minimize(migm2ptr) == -1)
      exit(1);
  }
  /*
    else
      fsa_ip_labeled_minimize(migm2ptr);
  */
  if (kbm_print_level > 1)
    printf("  #Number of states of migm2 after minimization = %d.\n",
           migm2ptr->states->size);
  strcpy(fsaname, rws.name);
  strcat(fsaname, ".migm2");
  strcpy(outf, cosgpname);
  strcat(outf, ".migm2");
  wfile = fopen(outf, "w");
  fsa_print(wfile, migm2ptr, fsaname);
  if (kbm_print_level > 0)
    printf("#General length-2 multiplier with %d states computed.\n",
           migm2ptr->states->size);
  fclose(wfile);
  fsa_clear(migm2ptr);
  tfree(migm2ptr);


  /* If keepfiles is false, then we will throw away every multiplier immediately
   * after it has been used. Otherwise, we will keep them, in case they are
   * needed again.
   * We store a list of words for which we have got the multipliers in
   * storedmult. We first form a rough upper bound on how long this list
   * could get - ngens + total relator length - 1.
   */
  strcpy(fsaname, rws.name);
  strcat(fsaname, ".mimult"); /* this is unimportant, since file is temporary */
  if (keepfiles) {
    ct = ngens;
    for (i = 1; i <= neqns; i++)
      ct += (genstrlen(eqn[i].lhs) + genstrlen(eqn[i].rhs));
    tmalloc(storedmult, char *, ct);
    numstoredmult = 0;
  }

  /* Now we are ready to start building the multipliers for the group relators,
   * which will give rise to the subgroup relators.
   * We use rws.testword1 to store the relators of G as they arise.
   * We start with the inverse relators.
   */
  first_relator = TRUE;
  relator = rws.testword1;
  for (i = 1; i <= ngens; i++) {
    relator[0] = i;
    relator[1] = inv[i];
    relator[2] = '\0';
    if (kbm_print_level > 0) {
      kbm_buffer[0] = '\0';
      add_to_buffer(0, "#Processing relator:  ");
      add_word_to_buffer(stdout, relator, rws.gen_name);
      printbuffer(stdout);
    }
    if (find_subrels(relator) == -1)
      exit(1);
  }

  /* Now the other relators.
   * We first need to get them from equation to relator form.
   */
  for (i = 1; i <= neqns; i++) {
    if (genstrlen(eqn[i].lhs) == 0 && genstrlen(eqn[i].rhs) == 0)
      continue;
    genstrcpy(relator, eqn[i].lhs);
    ptr = relator + genstrlen(relator);
    ptr2 = eqn[i].rhs;
    for (j = genstrlen(ptr2) - 1; j >= 0; j--)
      *(ptr++) = inv[ptr2[j]];
    *ptr = '\0';
    if (genstrlen(relator) == 2 && relator[1] == inv[relator[0]])
      continue; /* since we have already done this one */
    if (kbm_print_level > 0) {
      kbm_buffer[0] = '\0';
      add_to_buffer(0, "#Processing relator:  ");
      add_word_to_buffer(stdout, relator, rws.gen_name);
      printbuffer(stdout);
    }
    if (find_subrels(relator) == -1)
      exit(1);
  }

  fprintf(wfilep, "\n];\n");
  fclose(wfilep);

  if (keepfiles) {
    for (i = 1; i <= numstoredmult; i++) {
      sprintf(outf, "%s.mim%s", cosgpname, storedmult[i]);
      unlink(outf);
      tfree(storedmult[i]);
    }
    tfree(storedmult);
  }
  strcpy(outf, cosgpname);
  strcat(outf, ".migm2");
  unlink(outf);
  rws_clear(&rws);
  exit(0);
}

/* For a word w in the generators, this function returns a corresponding
 * string with the terms of w replaced by integers separated by '_'.
 * This is used as a suffix in the filenames used for storing the
 * corresponding multiplier fsa's.
 */
static char *file_suffix(gen *w)
{
  char *s;
  gen *p;
  boolean first;
  int len;
  /* First work out the length of the required string. */
  len = genstrlen(w);
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

/* Find and output the subgroup relators arising from the group relator */
int find_subrels(gen *r)
{
  char *suff;
  gen ***labnames, *rel, *relend;
  char **alph;
  boolean got, *laboccurs;
  fsa mult;
  int i, j, nlabs;

  suff = file_suffix(r);
  /* First see if we have formed the multiplier for  r  already - if
   * not, build and store it using long_word_multiplier().
   */
  got = FALSE;
  if (keepfiles) {
    for (i = 1; i <= numstoredmult; i++) {
      if (strcmp(suff, storedmult[i]) == 0) {
        got = TRUE;
        break;
      }
    }
  }
  if (!got) {
    if (long_word_multiplier(r, suff) == -1)
      return -1;
  }
  /* Now we read the composite multiplier in */
  sprintf(inf, "%s.mim%s", cosgpname, suff);
  if ((rfile = fopen(inf, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf);
    exit(1);
  }
  fsa_read(rfile, &mult, ip_store, dr, 0, TRUE, fsaname);
  fclose(rfile);
  /* Now we write the words for its initial states into the GAP file.
   * They occur among the names of the labels of the state-set.
   */
  nlabs = mult.states->labels->size;
  tmalloc(laboccurs, boolean, nlabs + 1);
  for (i = 1; i <= nlabs; i++)
    laboccurs[i] = FALSE;
  for (i = 1; i <= mult.states->size; i++)
    laboccurs[mult.states->setToLabels[i]] = TRUE;
  labnames = mult.states->labels->wordslist;
  alph = mult.states->labels->alphabet;
  for (i = 1; i <= nlabs; i++)
    if (laboccurs[i]) {
      j = 0;
      while (labnames[i][j]) {
        rel = labnames[i][j];
        if (*rel != '\0') {
          /* We have a subgroup relator */
          if (first_relator) {
            first_relator = FALSE;
            fprintf(wfilep, "  ");
          }
          else
            fprintf(wfilep, ",\n  ");
          relend = rel + genstrlen(rel) - 1;
          while (rel <= relend) {
            fprintf(wfilep, "%s", alph[*rel]);
            if (rel != relend)
              fprintf(wfilep, "*");
            rel++;
          }
        }
        j++;
      }
    }
  fsa_clear(&mult);
  unlink(inf);
  tfree(suff);
  tfree(laboccurs);
  return 0;
}

/* Calculate the multiplier associated with the word w.
 * s is the suffix of the file in which it will be stored.
 * (s has been derived from w by a call of file_suffix.)
 */
int long_word_multiplier(gen *w, char *s)
{
  int i, l;
  gen *wl, *wlt, *wr, *wrt;
  char *suffl, *sufflt, *suffr, *suffrt;
  boolean gotl, gotr, gotlt, gotrt;
  fsa mult1, mult2, *compmult;
  if (kbm_print_level >= 3) {
    kbm_buffer[0] = '\0';
    add_to_buffer(0, "  #Calculating multiplier for word:  ");
    add_word_to_buffer(stdout, w, rws.gen_name);
    printbuffer(stdout);
  }
  l = genstrlen(w);

  if (l == 1) { /* Length 1 - use fsa_mimakemult */
    strcpy(inf, cosgpname);
    strcat(inf, ".migm");
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf);
      exit(1);
    }
    fsa_read(rfile, &migm, op_store, 0, 0, TRUE, fsaname);
    fclose(rfile);
    if (fsa_mimakemult(&migm, w[0], prefix) == -1)
      return -1;
    if (mimult_minimize(&migm) == -1)
      return -1;
    sprintf(outf, "%s.mim%s", cosgpname, s);
    wfile = fopen(outf, "w");
    fsa_print(wfile, &migm, fsaname);
    fclose(wfile);
    fsa_clear(&migm);
  }
  else if (l == 2) { /* Length 2 - use fsa_mimakemult2 */
    strcpy(inf, cosgpname);
    strcat(inf, ".migm2");
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf);
      exit(1);
    }
    fsa_read(rfile, &migm2, op_store, 0, 0, TRUE, fsaname);
    fclose(rfile);
    if (fsa_mimakemult2(&migm2, w[0], w[1], prefix) == -1)
      return -1;
    mimult_minimize(&migm2);
    sprintf(outf, "%s.mim%s", cosgpname, s);
    wfile = fopen(outf, "w");
    fsa_print(wfile, &migm2, fsaname);
    fclose(wfile);
    fsa_clear(&migm2);
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
      if (long_word_multiplier(wr, suffr) == -1)
        return -1;
    }
    /* Read back in the two multipliers and form their composite */
    sprintf(inf, "%s.mim%s", cosgpname, suffl);
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf);
      exit(1);
    }
    fsa_read(rfile, &mult1, ip_store, dr, 0, TRUE, fsaname);
    fclose(rfile);
    sprintf(inf, "%s.mim%s", cosgpname, suffr);
    if ((rfile = fopen(inf, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf);
      exit(1);
    }
    fsa_read(rfile, &mult2, ip_store, dr, 0, TRUE, fsaname);
    fclose(rfile);

    compmult = fsa_micomposite(&mult1, &mult2, op_store, TRUE, tablefilename,
                               readback);
    fsa_clear(&mult1);
    fsa_clear(&mult2);
    if (readback) /* always true */
      mimult_minimize(compmult);
    /*
        else
          fsa_ip_minimize(compmult);
    */
    sprintf(outf, "%s.mim%s", cosgpname, s);
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
      sprintf(inf, "%s.mim%s", cosgpname, suffl);
      unlink(inf);
      sprintf(inf, "%s.mim%s", cosgpname, suffr);
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
  fprintf(
      stderr,
      "Usage: gpsubpres [-ip d/s[dr]] [-op d/s] [-silent] [-v] [-l] [-f]\n");
  fprintf(stderr, "\t\t  groupname [subname].\n");
  exit(1);
}
