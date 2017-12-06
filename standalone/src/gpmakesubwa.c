/* gpmakesubwa.c 22/1/96.
 * 31/12/98 - altered to make states of type labeled, where label is
 * the coset rep. of coset of subgroup correspondiong to state.
 * 6/8/98 large scale reorganisation to omit globals, etc.
 * 5/2/98 change generators from type char to type `gen'.
 *
 * Build a candidate word-acceptor for those irreducible words in
 * a shortlex automatic group that lie in a given subgroup.
 * This will work, for example, for quasiconvex subgroups of
 * hyperbolic groups.
 *
 * SYNOPSIS:
 *      gpmakesubwa [-w] [-kbprogcos/-diff1cos/-diff2cos]
 *              [-diff1/-diff2/-diff1c] [-mrl maxreducelen] [-nc nochange]
 *		[-v] [-silent] [-l] [-ms maxstates] groupname [subname]
 *
 * subname defaults to "sub".
 * autgroup (or equivalents) should have been run on grouname already.
 * groupname.subname should contain the definition of the subgroup,
 * in the standard format.
 *
 * Two word-reduction routines are required, one for the group elements,
 * and one for the cosets of the subgroup in the group.
 * As in wordreduce, there are four possibilities for the automaton used
 * to perform each of these reductions.
 * However, since the group will have had its automatic structure calculated
 * already, we always use diff_reduction for that, and do not allow
 * rws_reduction.
 * Input is from groupname.diff1, groupname.diff2 (default) or
 * groupname.diff1c for the reduction in the group, and
 * input is from groupname.wa (word-acceptor),
 * groupname.subname.kbprog, groupname.subname.diff1,
 * etc. for the coset reduction.
 *
 * The subgroup generators are input from groupname.subname, or from
 * groupname.subname.words, if -w is called.
 * (-w should be called after a run of gpchecksubwa has found words that
 *  should be accpeted by the subgroup word-acceptor but are not.)
 * Output is to groupname.subname.wa.
 *
 * OPTIONS:
 * -diff1/diff2/diff1c
 *		This determines which finite state automaton is used for
 *		the word-reduction in the group.
 *		The default is groupname.diff2.
 * -kbprogcos/diff1cos/diff2cos
 *  		Similar, for the coset reduction.
 *		Input from groupname.subname.kbprog, etc.
 * -nc	  nochange
 *              Exit when nochange words have been added to the
 *              language of subwa, without subwa changing.
 *		Default is 64.
 * -ms    maxstates
 *              At most maxstates states are allowed in the subgroup
 *		word-acceptor being produced. Default is 32767
 *		represent words in the subgroup can be remembered.
 *		Default is 32767.
 * -v           verbose
 * -silent      no diagnostics
 * -l/-h        large/huge hash-tables (for big examples)
 * -mrl maxreducelen
 *		To change the maximum word-length possible during reduction.
 *		Default is 4095
 *
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "hash.h"
#include "definitions.h"

#define MAXEQNS 32767
#define MAXSTATES 32767
#define MAXREDUCELEN 4095
#define NOCHANGE 64
#define MAXNOCHANGE 4096

static FILE *rfile, *wfile;

int (*reduce_word)(gen *w, reduction_struct *rs_rws);
int (*reduce_word_cos)(gen *w, reduction_struct *rs_rws);

/* Functions defined in this file */
static void fsa_init_subwa(fsa *subwaptr, fsa *gwaptr, gen_hash_table *coshtptr,
                    int ngens, int maxstates);
static int calc_inv(gen *gtestword, int ngens, int *inv, reduction_struct *rsptr);
static void invert_word(gen *gtestword, int *inv);
static int add_word_fsa(fsa *subwaptr, int ngens, int maxstates, gen *gtestword,
                 gen *costestword, char **names, gen_hash_table *coshtptr,
                 reduction_struct *rsptr);
static void badusage(void);

int main(int argc, char *argv[])
{
  int arg, delim, numsubgens, numsubelts, nochangect, eltct, genct, aw;
  char gpname[100], inf_wa[100], inf_gred[100], inf_cosred[100], suffix[100],
      inf_sub[100], fsaname[100], outf[100], tempfilename[100];
  boolean wordfile, diff1_ip, diff2_ip, diff1c_ip, open, rws_ipcos, diff1_ipcos,
      diff2_ipcos;
  gen_hash_table cosht;
  gen *cosht_ptr;
  gen gtestword[MAXREDUCELEN + 1], costestword[MAXREDUCELEN + 1];
  int ngens, *inv;
  int i, l, ns;
  fsa gwa, subwa, *subgwa;
  char **names;
  static gen_hash_table ght;
  rewriting_system rws, *rwsptr;
  reduction_struct grs, cosrs;
  int maxstates = MAXSTATES;
  int nochange = NOCHANGE;

  setbuf(stdout, (char *)0);
  setbuf(stderr, (char *)0);

  rwsptr = &rws;
  rwsptr->maxeqns = MAXEQNS;
  rwsptr->maxreducelen = MAXREDUCELEN;
  rwsptr->maxreducelenset = FALSE;
  rwsptr->inv_of = 0;
  rwsptr->weight = 0;
  rwsptr->level = 0;
  rwsptr->history = 0;
  rwsptr->slowhistory = 0;
  rwsptr->slowhistorysp = 0;
  rwsptr->preflen = 0;
  rwsptr->prefno = 0;
  rwsptr->cosets = FALSE;

  gpname[0] = '\0';
  suffix[0] = '\0';
  arg = 1;
  wordfile = FALSE;
  diff1_ip = diff2_ip = diff1c_ip = rws_ipcos = diff1_ipcos = diff2_ipcos =
      FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg], "-w") == 0)
      wordfile = TRUE;
    else if (strcmp(argv[arg], "-diff1") == 0)
      diff1_ip = TRUE;
    else if (strcmp(argv[arg], "-diff2") == 0)
      diff2_ip = TRUE;
    else if (strcmp(argv[arg], "-diff1c") == 0)
      diff1c_ip = TRUE;
    else if (strcmp(argv[arg], "-kbprogcos") == 0)
      rws_ipcos = TRUE;
    else if (strcmp(argv[arg], "-diff1cos") == 0)
      diff1_ipcos = TRUE;
    else if (strcmp(argv[arg], "-diff2cos") == 0)
      diff2_ipcos = TRUE;
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
    else if (strcmp(argv[arg], "-mrl") == 0) {
      rwsptr->maxreducelenset = TRUE;
      arg++;
      if (arg >= argc)
        badusage();
      rwsptr->maxreducelen = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-nc") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      nochange = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg], "-ms") == 0) {
      arg++;
      if (arg >= argc)
        badusage();
      maxstates = atoi(argv[arg]);
    }
    else {
      if (argv[arg][0] == '-')
        badusage();
      if (strcmp(suffix, ""))
        badusage();
      if (strcmp(gpname, "") == 0)
        strcpy(gpname, argv[arg]);
      else
        strcpy(suffix, argv[arg]);
    }
    arg++;
  }

  if (stringlen(gpname) == 0)
    badusage();

  if (stringlen(suffix) == 0)
    strcpy(suffix, "sub");
  strcpy(inf_sub, gpname);
  strcat(inf_sub, ".");
  strcat(inf_sub, suffix);
  strcpy(outf, inf_sub);
  strcat(outf, ".wa");
  if (wordfile)
    strcat(inf_sub, ".words");

  strcpy(tempfilename, inf_sub);
  strcat(tempfilename, "temp_wa_XXX");

  /* First sort out the reduction automaton and routine for the group */
  strcpy(inf_gred, gpname);
  if (diff1_ip)
    strcat(inf_gred, ".diff1");
  else if (diff2_ip)
    strcat(inf_gred, ".diff2");
  else if (diff1c_ip)
    strcat(inf_gred, ".diff1c");
  else {
    diff2_ip = TRUE;
    strcpy(inf_gred, gpname);
    strcat(inf_gred, ".diff2");
  }

  if ((rfile = fopen(inf_gred, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf_gred);
    exit(1);
  }

  tmalloc(grs.wd_fsa, fsa, 1)
      fsa_read(rfile, grs.wd_fsa, DENSE, 0, 0, TRUE, fsaname);
  fclose(rfile);
  ngens = grs.wd_fsa->alphabet->base->size;
  process_names(grs.wd_fsa->alphabet->base->names, ngens);
  grs.separator = ngens + 1;
  cosrs.separator = ngens + 1;
  /* Set the pointers in the word-difference machine */
  if (fsa_table_dptr_init(grs.wd_fsa) == -1)
    exit(1);

  /* Now the word-reduction machine for cosets */
  if (strncmp(suffix, "sub", 3) == 0) {
    strcpy(inf_cosred, gpname);
    strcat(inf_cosred, ".cos");
    strcat(inf_cosred, suffix + 3);
  }
  else {
    strcpy(inf_cosred, gpname);
    strcat(inf_cosred, ".");
    strcat(inf_cosred, suffix);
    strcat(inf_cosred, "_cos");
  }

  open = FALSE;
  if (rws_ipcos)
    strcat(inf_cosred, ".kbprog");
  else if (diff1_ipcos)
    strcat(inf_cosred, ".midiff1");
  else if (diff2_ipcos)
    strcat(inf_cosred, ".midiff2");
  else {
    strcat(inf_cosred, ".kbprog");
    rfile = fopen(inf_cosred, "r");
    if (rfile) {
      rws_ipcos = TRUE;
      open = TRUE;
    }
    else {
      diff2_ipcos = TRUE;
      strcpy(inf_cosred + stringlen(inf_cosred) - 6, "midiff2");
    }
  }

  if (!open)
    if ((rfile = fopen(inf_cosred, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf_cosred);
      exit(1);
    }

  if (rws_ipcos) {
    read_kbinput_simple(rfile, FALSE, rwsptr);
    fclose(rfile);
    tmalloc(rwsptr->reduction_fsa, fsa, 1);
    strcpy(inf_cosred + stringlen(inf_cosred) - 6, "reduce");
    if ((rfile = fopen(inf_cosred, "r")) == 0) {
      fprintf(stderr, "Cannot open file %s.\n", inf_cosred);
      exit(1);
    }
    fsa_read(rfile, rwsptr->reduction_fsa, DENSE, 0, 0, TRUE, fsaname);
    fclose(rfile);
    process_names(rws.gen_name, ngens);
    tmalloc(rws.history, int, rws.maxreducelen + 1);
    cosrs.rws = rwsptr;
  }
  else {
    tmalloc(cosrs.wd_fsa, fsa, 1);
    fsa_read(rfile, cosrs.wd_fsa, DENSE, 0, 0, TRUE, fsaname);
    fclose(rfile);
    ngens = cosrs.wd_fsa->alphabet->base->size;
    process_names(cosrs.wd_fsa->alphabet->base->names, ngens);
    /* Set the pointers in the word-difference machine */
    fsa_table_dptr_init(cosrs.wd_fsa);
  }

  /* Set the generator names and the reduction algorithms. */
  names = grs.wd_fsa->alphabet->base->names;
  reduce_word = diff_reduce;
  reduce_word_cos = rws_ipcos ? rws_reduce : diff_reduce_cos;

  /* Now read the word-acceptor for the group */
  strcpy(inf_wa, gpname);
  strcat(inf_wa, ".wa");
  if ((rfile = fopen(inf_wa, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf_wa);
    exit(1);
  }
  fsa_read(rfile, &gwa, DENSE, 0, 0, TRUE, fsaname);
  fclose(rfile);

  /* Now we initialise the subgroup word-acceptor that we shall be building */
  fsa_init_subwa(&subwa, &gwa, &cosht, ngens, maxstates);
  /* Calculate inverses of G-generators */
  tmalloc(inv, int, ngens + 1);
  if (calc_inv(gtestword, ngens, inv, &grs) == -1)
    exit(1);
  /* Initialise the hash table for storing the words in the G-generators that
   * lie in the subgroup.
   */
  gen_hash_init(&ght, FALSE, 0, 0, 0);

  /* Now open the file containing the words that generate the subgroup,
   * store them in the hash-table ght, and add them and their inverses to
   * the language accepted by subwa.
   */
  if ((rfile = fopen(inf_sub, "r")) == 0) {
    fprintf(stderr, "Cannot open file %s.\n", inf_sub);
    exit(1);
  }
  read_ident(rfile, kbm_buffer, &delim, FALSE);
  /* this is the name of the record containing the subgenerators */
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
  read_ident(rfile, kbm_buffer, &delim, FALSE);
  if (strcmp(kbm_buffer, "subGenerators") != 0) {
    fprintf(stderr, "Input error. 'subGenerators' list expected in subgroup "
                    "generator file.\n");
    exit(1);
  }
  if (delim != ':') {
    fprintf(stderr, "#Input error: bad 'subgens' list assignment\n");
    exit(1);
  }
  check_next_char(rfile, '=');
  check_next_char(rfile, '[');
  numsubgens = 0;
  numsubelts = 0;
  do {
    if (!read_word(rfile, gtestword, gtestword + rws.maxreducelen, &delim,
                   names, ngens, TRUE)) {
      fprintf(stderr,
              "#Input error: no subgroup generators or missing word.\n");
      exit(1);
    }
    /* Check that it is reduced as a word in G */
    if ((*reduce_word)(gtestword, &grs) == -1)
      exit(1);
    if (genstrlen(gtestword) > 0) {
      /* Copy it into the hash-table and see if it is new */
      genstrcpy(ght.current_ptr, gtestword);
      if (gen_hash_locate(&ght, genstrlen(gtestword) + 1) > numsubgens) {
        /*It is new - so add it to language of subwa */
        numsubgens++;
        if (add_word_fsa(&subwa, ngens, maxstates, gtestword, costestword,
                         names, &cosht, &cosrs) == -1)
          exit(1);
        /* Now try its inverse */
        invert_word(gtestword, inv);
        if ((*reduce_word)(gtestword, &grs) == -1)
          exit(1);
        genstrcpy(ght.current_ptr, gtestword);
        if (gen_hash_locate(&ght, genstrlen(gtestword) + 1) > numsubgens) {
          /*It is new - so add it to language of subwa */
          numsubgens++;
          if (add_word_fsa(&subwa, ngens, maxstates, gtestword, costestword,
                           names, &cosht, &cosrs) == -1)
            exit(1);
        }
      }
    }
  } while (delim != ']');
  fclose(rfile);

  if (numsubgens * numsubgens > nochange) {
    nochange = numsubgens * numsubgens <= MAXNOCHANGE ? numsubgens * numsubgens
                                                      : MAXNOCHANGE;
    if (kbm_print_level > 1)
      printf("  #Due to large number of subgp. gens., increasing nochange to "
             "%d.\n",
             nochange);
  }
  if (kbm_print_level > 0)
    printf("#There are %d subgroup generators (including inverses).\n",
           numsubgens);

  /* Now we start to go through the sugroup elements stored in ght, and
   * multiply them by the subgroup generators to get new words in the
   * subgroup, and add them to the language of subwa.
   * We stop after considering nochange words in the subgroup generators
   * with no change to subwa.
   */
  numsubelts = numsubgens;
  nochangect = 0;
  for (eltct = 1; eltct <= numsubelts && nochangect < nochange; eltct++)
    for (genct = 1; genct <= numsubgens && nochangect < nochange; genct++) {
      genstrcpy(gtestword, gen_hash_rec(&ght, eltct));
      genstrcat(gtestword, gen_hash_rec(&ght, genct));
      /* Reduce it as a word in G */
      if ((*reduce_word)(gtestword, &grs) == -1)
        exit(1);
      if (genstrlen(gtestword) > 0) {
        /* Copy it into the hash-table and see if it is new */
        genstrcpy(ght.current_ptr, gtestword);
        if (gen_hash_locate(&ght, genstrlen(gtestword) + 1) > numsubelts) {
          /*It is new - so add it to language of subwa */
          numsubelts++;
          if (kbm_print_level > 1 &&
              ((numsubelts <= 500 && numsubelts % 100 == 0) ||
               numsubelts % 500 == 0))
            printf("  #Number of subgroup elements stored=%d.\n", numsubelts);
          aw = add_word_fsa(&subwa, ngens, maxstates, gtestword, costestword,
                            names, &cosht, &cosrs);
          if (aw == -1)
            exit(1);
          if (aw == 1)
            nochangect = 0;
          else
            nochangect++;
          /* Now try its inverse */
          invert_word(gtestword, inv);
          if ((*reduce_word)(gtestword, &grs) == -1)
            exit(1);
          genstrcpy(ght.current_ptr, gtestword);
          if (gen_hash_locate(&ght, genstrlen(gtestword) + 1) > numsubgens) {
            /*It is new - so add it to language of subwa */
            numsubelts++;
            if (kbm_print_level > 1 &&
                ((numsubelts <= 500 && numsubelts % 100 == 0) ||
                 numsubelts % 500 == 0))
              printf("  #Number of subgroup elements stored=%d.\n", numsubelts);
            aw = add_word_fsa(&subwa, ngens, maxstates, gtestword, costestword,
                              names, &cosht, &cosrs);
            if (aw == -1)
              exit(1);
            if (aw == 1)
              nochangect = 0;
            else
              nochangect++;
          }
        }
      }
    }

  /* record the coset reps. as labels of the states */
  ns = subwa.states->size;
  subwa.states->type = LABELED;
  tmalloc(subwa.states->labels, srec, 1);
  subwa.states->labels->size = ns;
  subwa.states->labels->type = WORDS;
  subwa.states->labels->alphabet_size = ngens;
  for (i = 1; i <= ngens; i++) {
    l = stringlen(grs.wd_fsa->alphabet->base->names[i]);
    tmalloc(subwa.states->labels->alphabet[i], char, l + 1);
    strcpy(subwa.states->labels->alphabet[i],
           grs.wd_fsa->alphabet->base->names[i]);
  }
  tmalloc(subwa.states->setToLabels, setToLabelsType, ns + 1);
  tmalloc(subwa.states->labels->words, gen *, ns + 1);
  subwa.states->setToLabels[0] = 0;
  for (i = 1; i <= ns; i++) {
    cosht_ptr = gen_hash_rec(&cosht, i);
    l = gen_hash_rec_len(&cosht, i);
    tmalloc(subwa.states->labels->words[i], gen, l + 1);
    genstrcpy(subwa.states->labels->words[i], cosht_ptr);
    subwa.states->setToLabels[i] = i;
  }
  if (kbm_print_level > 1) {
    printf("  #Initial subgroup word-acceptor with %d states computed.\n", ns);
    printf("  #Now and-ing it with group word-acceptor.\n");
  }
  /* Now we "and" the subwa fsa with gwa and minimize */
  subgwa = fsa_laband(&subwa, &gwa, DENSE, TRUE, tempfilename);
  if (kbm_print_level > 1)
    printf("  #Subgroup word-acceptor with %d states before minimization "
           "computed.\n",
           subgwa->states->size);
  if (fsa_labeled_minimize(subgwa) == -1)
    exit(1);

  base_prefix(fsaname);
  strcat(fsaname, ".wa");
  wfile = fopen(outf, "w");
  fsa_print(wfile, subgwa, fsaname);
  fclose(wfile);
  if (kbm_print_level > 0)
    printf("#Subgroup word-acceptor with %d states computed.\n",
           subgwa->states->size);

  gen_hash_clear(&ght);
  gen_hash_clear(&cosht);
  tfree(inv);
  fsa_clear(subgwa);
  tfree(subgwa);
  fsa_clear(grs.wd_fsa);
  tfree(grs.wd_fsa);
  if (rws_ipcos) {
    rws_clear(&rws);
    fsa_clear(rws.reduction_fsa);
    tfree(rws.reduction_fsa);
  }
  else {
    fsa_clear(cosrs.wd_fsa);
    tfree(cosrs.wd_fsa);
  }
  exit(0);
}

/* Initialise the subgroup word-acceptor */
void fsa_init_subwa(fsa *subwaptr, fsa *gwaptr, gen_hash_table *coshtptr,
                    int ngens, int maxstates)
{
  int i;
  fsa_init(subwaptr);


  subwaptr->states->size = 1;

  srec_copy(subwaptr->alphabet, gwaptr->alphabet);

  subwaptr->num_initial = 1;
  tmalloc(subwaptr->initial, int, 2);
  subwaptr->initial[1] = 1;
  /* The initial state is also the single accepting state */
  subwaptr->num_accepting = 1;
  tmalloc(subwaptr->accepting, int, 2);
  subwaptr->accepting[1] = 1;

  subwaptr->flags[DFA] = TRUE;
  subwaptr->flags[ACCESSIBLE] = TRUE;

  fsa_table_init(subwaptr->table, maxstates, ngens);
  subwaptr->table->printing_format = DENSE;
  for (i = 1; i <= ngens; i++)
    set_dense_target(subwaptr->table->table_data_ptr, i, 1, 0);

  /* The states of subwa will be cosets of the subgroup in G.
   * They will be stored as G-words, specifying the minimal coset rep.
   * These words will be stored in the hash-table *coshtptr.
   * We initialise the word for the first state as the empty word.
   */
  gen_hash_init(coshtptr, FALSE, 0, 0, 0);
  coshtptr->current_ptr[0] = '\0';
  if (gen_hash_locate(coshtptr, 1) != 1) {
    fprintf(stderr, "Hash-initialisation problem in fsa_init_subwa.\n");
    exit(1);
  }
}

/* Calculates inverses of generators - essentially the same as the routine
 * calculate_inverses in ../lib/worddiff.c, but it is not convenient to
 * use that here.
 */
int calc_inv(gen *gtestword, int ngens, int *inv, reduction_struct *rsptr)
{
  int i, j;
  for (i = 1; i <= ngens; i++)
    for (j = 1; j <= ngens; j++) {
      gtestword[0] = i;
      gtestword[1] = j;
      gtestword[2] = '\0';
      if ((*reduce_word)(gtestword, rsptr) == -1)
        return -1;
      if (genstrlen(gtestword) == 0) {
        inv[i] = j;
        break;
      }
    }
  return 0;
}

/* Invert the word in gtestword */
void invert_word(gen *gtestword, int *inv)
{
  gen *wb, *we, swap;
  wb = gtestword;
  we = gtestword + genstrlen(gtestword) - 1;
  while (wb < we) {
    swap = inv[*wb];
    *wb = inv[*we];
    *we = swap;
    wb++;
    we--;
  }
  if (wb == we)
    *wb = inv[*wb];
}

/* Alter the fsa subwa to make it accept the word gtestword */
int add_word_fsa(fsa *subwaptr, int ngens, int maxstates, gen *gtestword,
                 gen *costestword, char **names, gen_hash_table *coshtptr,
                 reduction_struct *rsptr)
{
  int state, i, j, glen, coslen, newstate, imstate;
  gen *cosrep, g;
  int changed = 0;
  int **subwa_table = subwaptr->table->table_data_ptr;
  kbm_buffer[0] = '\0';
  add_word_to_buffer(stdout, gtestword, names);
  /* In case there is an error and we need to print gtestword */
  state = 1;
  costestword[0] = rsptr->separator;
  costestword[1] = '\0';
  /* We reduce the word _H*gtestword symbol by symbol, tracing it through
   * subwa as we go.
   */
  glen = genstrlen(gtestword);
  for (i = 0; i < glen; i++) {
    coslen = genstrlen(costestword);
    g = gtestword[i];
    costestword[coslen] = g;
    costestword[coslen + 1] = '\0';
    if ((*reduce_word_cos)(costestword, rsptr) == -1)
      return -1;
    cosrep = costestword;
    while (*cosrep != rsptr->separator)
      cosrep++;
    cosrep++;
    /* Copy the coset-rep into the hash-table, and see if we have it already */
    genstrcpy(coshtptr->current_ptr, cosrep);
    newstate = gen_hash_locate(coshtptr, genstrlen(cosrep) + 1);
    if (newstate > subwaptr->states->size) {
      /* New state! */
      changed = 1;
      if (newstate > maxstates) {
        fprintf(stderr, "Too many states in subwa - increase maxstates.\n");
        exit(1);
      }
      if (kbm_print_level > 1 &&
          ((newstate <= 500 && newstate % 100 == 0) || newstate % 500 == 0))
        printf("  #Number of states in subwa = %d.\n", newstate);
      for (j = 1; j <= ngens; j++)
        set_dense_target(subwa_table, j, newstate, 0);
      subwaptr->states->size = newstate;
      /* should be subwaptr->states->size+1 ! */
    }
    if ((imstate = dense_target(subwa_table, g, state)) &&
        imstate != newstate) {
      fprintf(stderr, "Error tracing word: ");
      printbuffer(stdout);
      exit(1);
    }
    set_dense_target(subwa_table, g, state, newstate);
    state = newstate;
  }
  if (state != 1) {
    fprintf(stderr, "Final error tracing word: ");
    printbuffer(stdout);
    exit(1);
  }
  return changed;
}

void badusage(void)
{
  fprintf(stderr, "Usage: gpmakesubwa [-w] [-kbprogcos/-diff1cos/-diff2cos]\n");
  fprintf(stderr,
          "\t[-diff1/-diff2/-diff1c] [-mrl maxreducelen] [-nc nochange]\n");
  fprintf(stderr,
          "\t[-v] [-silent] [-l] [-ms maxstates] groupname [subname]\n");
  exit(1);
}
