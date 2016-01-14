/* gpchecksubwa.c   22.4.96. 
 * 31/12/98 change to deal with fact that subwa now has state type
 * labeled.
 * 26/10/98 large scale reorganisation to omit globals, etc.
 * 5/2/98 change generators from type char to type `gen'.
 * 6.5.97. corrected bug - not enough space allocated for storedmult.
 * Check the correctness of the subgroup word acceptor output by gpsubwa.
 * If incorrect, output some words in the subgroup that are not
 * accepted by the word accpetor, so that gpsubwa can use them on re-running.
 *
 * SYNOPSIS:
 * gpchecksubwa [-ip d/s[dr]] [-op d/s] [-silent] [-v] [-l] [-f] [-s]
 * 	 	[-m maxwords] groupname [subname]
 *
 * subname defaults to "sub".
 * autcos (or equaivalents) must already have been run on groupname.
 * groupname.subname should contain the definition of the subgroup,
 * in the standard format.
 * Input is from groupname.subname.wa and groupname.gm.
 * Output to (and input from) temporary files groupname.m* (for
 * multipliers) and groupname.subname.submult.
 * If word acceptor is wrong, output of original subgroup generators +
 * offending elements of subgroup to groupname.subname.words.
 *
 * OPTIONS:
 * -ip d/s[dr]  input in dense or sparse format - dense is default
 * -op d/s      output in dense or sparse format - sparse is default
 * -m  maxwords  Abort after finding maxwords offending words w
 *              default is MAXWORDS
 * -v           verbose
 * -silent      no diagnostics
 * -l/-h        large/huge hash-tables (for big examples)
 * -f           read the transition table repeatedly from file while minimizing,
 *              in calls of fsa_composite.
 *              This avoids storing large tables, but is a little slower.
 * -s		Throw away files immediately after use whenever possible, to
 *              save disk-space. This will slow things down considerably.
 */

#include <stdio.h>

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"

#define MAXWORDLEN	2048
#define MAXSUBGENS	1024
#define MAXWORDS 	16

static int  	maxsubgens = MAXSUBGENS,
         	maxwordlen = MAXWORDLEN,
	 	maxwords    = MAXWORDS;

static char gpname[100], subname[100], inf[100], outf[100], fsaname[100],
       tempfilename[100];
static fsa subwa, genmult,  mult, mult1, mult2,
       *compmultptr, *submultptr, *existsptr;
static int ngens, nsubgens, numstoredmult, delim;
static char **names, **storedmult;
static gen *subgen[MAXSUBGENS], testword[MAXWORDLEN+1], **badwords;
static storage_type ip_store = DENSE;
static int dr = 0;
static storage_type op_store = SPARSE;
static boolean readback = TRUE;
static boolean keepfiles = TRUE;
static FILE *rfile, *wfile;

/* Functions defined in this file */
char *file_suffix();
int subgen_multiplier();
void read_subgpgens();
int output_bad_words();
void badusage_gpchecksubwa();

/* Functions used in this file defined in other files: */
void process_names();
void printbuffer();
void add_to_buffer();
int  add_word_to_buffer();
int int_len();
int  fsa_makemult();
fsa  *fsa_composite();
fsa  *fsa_submult();
fsa  *fsa_exists();
int  fsa_swap_coords();
int  fsa_minimize();
int  fsa_ip_minimize();
int words_and_not();
boolean fsa_equal();
void fsa_read();
void fsa_clear();
int  stringlen();
int  genstrlen();
int  genstrcmp();
void genstrcpy();

int 
main (int argc, char *argv[])
{ int arg, i, j, l, ct;
  char *suff;
  boolean gotsuff;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpchecksubwa();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's') {
        ip_store = SPARSE;
        if (stringlen(argv[arg]) > 1)
          dr = atoi(argv[arg]+1);
      }
      else
        badusage_gpchecksubwa();
    }
    else if (strcmp(argv[arg],"-op")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpchecksubwa();
      if (strcmp(argv[arg],"d")==0)
        op_store = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_store = SPARSE;
      else
        badusage_gpchecksubwa();
    }
    else if (strcmp(argv[arg],"-silent")==0)
      kbm_print_level = 0;
    else if (strcmp(argv[arg],"-v")==0)
      kbm_print_level = 2;
    else if (strcmp(argv[arg],"-vv")==0)
      kbm_print_level = 3;
    else if (strcmp(argv[arg],"-l")==0)
      kbm_large = TRUE;
    else if (strcmp(argv[arg],"-h")==0)
      kbm_huge = TRUE;
    else if (strcmp(argv[arg],"-f")==0)
      readback = FALSE;
    else if (strcmp(argv[arg],"-s")==0)
      keepfiles = FALSE;
    else if (strcmp(argv[arg],"-m")==0) {
      arg++;
      if (arg >= argc)
        badusage_gpchecksubwa();
      maxwords = atoi(argv[arg]);
    }
    else {
       if (argv[arg][0] == '-')
         badusage_gpchecksubwa();
       if (strcmp(gpname,"")!=0 && strcmp(subname,"")!=0)
         badusage_gpchecksubwa();
       if (strcmp(gpname,"")!=0)
         strcpy(subname,argv[arg]);
       else
         strcpy(gpname,argv[arg]);
    }
    arg++;
  }
  if (stringlen(gpname)==0)
    badusage_gpchecksubwa();
  if (stringlen(subname)==0)
     strcpy(subname,"sub");
  
  sprintf(tempfilename,"%s_%stemp_axXXX",gpname,subname);


/* First read in the candidate for the subgroup automaton. */
  sprintf(inf,"%s.%s.wa",gpname,subname);
  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
  }
  fsa_read(rfile,&subwa,DENSE,0,0,TRUE,fsaname);
  fclose(rfile);
/* Since this now has states of type labeled, we need to remove this structure, or
 * fsa_equal will not work in the correctness test.
*/
  srec_clear(subwa.states->labels);
  tfree(subwa.states->labels);
  tfree(subwa.states->setToLabels);
  subwa.states->type=SIMPLE;
  fsa_minimize(&subwa);
  if (kbm_print_level>1)
    printf("  #Number of states of subwa after minimisation = %d.\n",
      subwa.states->size);


  ngens = subwa.alphabet->size;
  names = subwa.alphabet->names;
  process_names(names,ngens);

/* Now we read in the subgroup generators. */
  sprintf(inf,"%s.%s",gpname,subname);
  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
  }
  read_subgpgens();
  fclose(rfile);

  if (keepfiles) {
 /* Assign space for storedmult; storedmult[i] will be the file suffix where
  * the i-th multiplier automaton is stored.
  */
    ct = nsubgens;
    for (i=0;i<nsubgens;i++)
      ct += 2*genstrlen(subgen[i]);
    tmalloc(storedmult,char *,ct);
    numstoredmult = 0;
  }

/* Now, for each subgroup generator, form the corresponding multiplier
 * automaton in the group, intersect its language with that of the
 * candidate subgroup word acceptor, and check its closure on multiplying
 * by that subgroup generator (on either side).
 */
  for (i=0;i<nsubgens;i++) {
    if (kbm_print_level > 0) {
      kbm_buffer[0] = '\0';
      add_to_buffer(0,"#Processing subgroup generator:  ");
      add_word_to_buffer(stdout,subgen[i],names);
      printbuffer(stdout,kbm_buffer);
    }
    suff = file_suffix(subgen[i]);
    gotsuff = FALSE;
    if (keepfiles) {
/* Check to see if we have of this multiplier already */
      for (j=1;j<=numstoredmult;j++) {
        if (strcmp(suff,storedmult[j])==0)
          gotsuff = TRUE;
      }
    }
    if (!gotsuff) {
      if (subgen_multiplier(subgen[i],suff)==-1) exit(1);
    }

    sprintf(inf,"%s.m%s",gpname,suff);
    if ((rfile = fopen(inf,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf);
        exit(1);
    }
    fsa_read(rfile,&mult,DENSE,0,0,TRUE,fsaname);
    fclose(rfile);
    if (kbm_print_level>1) {
      printf("  #Number of states of multiplier = %d.\n",
        mult.states->size);
      printf("  #Intersecting with candidate subgroup word-acceptor.\n");
    }
    submultptr=fsa_submult(&subwa,&mult,op_store,FALSE,tempfilename,
								  readback);
    if (submultptr==0)
      exit(1);
    fsa_clear(&mult);
    if (kbm_print_level>1)
      printf("  #Number of states of submultptr before minimisation = %d.\n",
        submultptr->states->size);
    if (readback) {
      if (fsa_minimize(submultptr)==-1) exit(1);
    }
    else {
      if (fsa_ip_minimize(submultptr)==-1) exit(1);
    }
    if (kbm_print_level>1)
      printf("  #Number of states of submultptr after minimisation = %d.\n",
        submultptr->states->size);

/* As usual, we output and input again, in case we want to change storage types.
 */
    base_prefix(fsaname);
    strcat(fsaname,".submult");
    sprintf(outf,"%s.%s.submult",gpname,subname);
    wfile = fopen(outf,"w");
    fsa_print(wfile,submultptr,fsaname);
    fclose(wfile);
    fsa_clear(submultptr);

    if ((rfile = fopen(outf,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",outf);
        exit(1);
    }
    fsa_read(rfile,submultptr,DENSE,0,0,TRUE,fsaname);
    fclose(rfile);
    if (kbm_print_level>1)
      printf("  #Projecting onto left side.\n");
    existsptr = fsa_exists(submultptr,op_store,FALSE,tempfilename);
    if (existsptr==0) exit(1);
    if (kbm_print_level>1)
      printf(
        "  #Number of states of left-projection before minimisation = %d.\n",
          existsptr->states->size);
    if (fsa_minimize(existsptr)==-1) exit(1);
    if (kbm_print_level>1)
      printf(
        "  #Number of states of left-projection after minimisation = %d.\n",
          existsptr->states->size);
    if (!fsa_equal(&subwa,existsptr)) {
      kbm_buffer[0] = '\0';
      add_to_buffer(0,"#Subgroup automaton check (on left) fails for generator:  ");
      add_word_to_buffer(stdout,subgen[i],names);
      printbuffer(stdout,kbm_buffer);
      tfree(submultptr);
      unlink(outf);
      if (output_bad_words()==-1)
        exit(1);
      exit(2);
    }
    fsa_clear(existsptr);
    tfree(existsptr);

    if (kbm_print_level>1)
      printf("  #Projecting onto right side.\n");
    if (fsa_swap_coords(submultptr)==-1)
       exit(1);
    existsptr = fsa_exists(submultptr,op_store,TRUE,tempfilename);
    if (existsptr==0) exit(1);
    if (kbm_print_level>1)
      printf(
        "  #Number of states of right-projection before minimisation = %d.\n",
          existsptr->states->size);
    if (fsa_minimize(existsptr)==-1) exit(1);
    if (kbm_print_level>1)
      printf(
        "  #Number of states of right-projection after minimisation = %d.\n",
          existsptr->states->size);
    if (!fsa_equal(&subwa,existsptr)) {
      kbm_buffer[0] = '\0';
      add_to_buffer(0,"#Subgroup automaton check (on right) fails for generator:  ");
      add_word_to_buffer(stdout,subgen[i],names);
      printbuffer(stdout,kbm_buffer);
      tfree(submultptr);
      unlink(outf);
      if (output_bad_words()==-1)
         exit(1);
      exit(2);
    }
    fsa_clear(existsptr);
    tfree(existsptr);
    tfree(submultptr);
    unlink(outf);

    if (keepfiles) {
      if (gotsuff) tfree(suff)
      else storedmult[++numstoredmult] = suff;
    }
    else {
      sprintf(inf,"%s.m%s",gpname,suff); unlink(inf);
      tfree(suff);
    }
  }

  for (i=0;i<nsubgens;i++)
    tfree(subgen[i]);
  fsa_clear(&subwa);
  tfree(badwords);
  if (keepfiles) {
    for (i=1;i<=numstoredmult;i++) {
      sprintf(outf,"%s.m%s",gpname,storedmult[i]);
      unlink(outf);
      tfree(storedmult[i]);
    }
    tfree(storedmult);
  }
  if (kbm_print_level>0)
    printf("#Subgroup automata validity checking succeeded.\n");
  exit(0);
}

char *
file_suffix(w)
	gen *w;
/* For a word w in the generators, this function returns a corresponding
 * string with the terms of w replaced by integers separated by '_'.
 * This is used as a suffix in the filenames used for storing the
 * corresponding multiplier fsa's.
 */
{ char *s;
  gen *p;
  boolean first;
  int len;
/* First work out the length of the required string. */
  len = genstrlen(w);
  p = w-1;
  while (*(++p) != 0)
    len += int_len((int)(*p));
  tmalloc(s,char,len);
  s[0] = '\0';
  first = TRUE;
  p = w-1;
  while (*(++p) != 0) {
    if (first)
      first = FALSE;
    else
      sprintf(s+stringlen(s),"_");
    sprintf(s+stringlen(s),"%d",*p);
  }
  return s;
}

int
subgen_multiplier(w,s)
	gen *w;
       char *s;
/* Calculate the multiplier associated with the word w.
 * s is the suffix of the file in which it will be stored.
 * (s has been derived from w by a call of file_suffix).
 */
{ int i, l;
  gen *wl, *wlt, *wr, *wrt;
  char *suffl, *sufflt, *suffr, *suffrt;
  boolean gotl, gotr, gotlt, gotrt;
  if (kbm_print_level >= 3) {
    kbm_buffer[0] = '\0';
    add_to_buffer(0,"  #Calculating multiplier for word:  ");
    add_word_to_buffer(stdout,w,names);
    printbuffer(stdout,kbm_buffer);
  }
  l = genstrlen(w);

  if (l==1) { /* Length 1 - use fsa_makemult */
    strcpy(inf,gpname);
    strcat(inf,".gm");
    if ((rfile = fopen(inf,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf);
        exit(1);
    }
    fsa_read(rfile,&genmult,op_store,0,0,TRUE,fsaname);
    fclose(rfile);
    if (fsa_makemult(&genmult,w[0])==-1)
      return -1;
    if (fsa_minimize(&genmult)==-1)
      return -1;
    sprintf(outf,"%s.m%s",gpname,s);
    wfile = fopen(outf,"w");
    fsa_print(wfile,&genmult,fsaname);
    fclose(wfile);
    fsa_clear(&genmult);
  }
  else { /* general case - we have to split w up */
    if (l%2 == 0) {
      tmalloc(wl,gen,l/2 + 1); tmalloc(wr,gen,l/2 + 1);
      for (i=0;i<l/2;i++) wl[i]=w[i];
      wl[l/2]='\0';
      genstrcpy(wr,w+l/2);
      suffl = file_suffix(wl); suffr = file_suffix(wr);
    }
    else  {
      tmalloc(wl,gen,l/2 + 2); tmalloc(wr,gen,l/2 + 1);
      for (i=0;i<=l/2;i++) wl[i]=w[i];
      wl[l/2 + 1]='\0';
      genstrcpy(wr,w+l/2+1);
      suffl = file_suffix(wl); suffr = file_suffix(wr);
    }
/* See whether we have either of them already */
    gotl = gotr = FALSE;
    if (keepfiles) {
      for (i=1;i<=numstoredmult;i++) {
        if (strcmp(suffl,storedmult[i])==0)
          gotl = TRUE;
        if (strcmp(suffr,storedmult[i])==0)
          gotr = TRUE;
      }
    }

    if (keepfiles && l%2==1 && (!gotl || !gotr)) {
/* In this case, there are two possible ways to split w up -
 * we see if the other way has more multipliers already stored.
 */
      tmalloc(wlt,gen,l/2 + 1); tmalloc(wrt,gen,l/2 + 2);
      for (i=0;i<l/2;i++) wlt[i]=w[i];
      wlt[l/2]='\0';
      genstrcpy(wrt,w+l/2);
      sufflt = file_suffix(wlt); suffrt = file_suffix(wrt);
      gotlt = gotrt = FALSE;
      for (i=1;i<=numstoredmult;i++) {
        if (strcmp(sufflt,storedmult[i])==0)
          gotlt = TRUE;
        if (strcmp(suffrt,storedmult[i])==0)
          gotrt = TRUE;
      }
      if ((gotlt && gotrt) || ((gotlt || gotrt) && !gotl && !gotr)) {
        tfree(wl); tfree(wr); tfree(suffl); tfree(suffr);
        wl=wlt; wr=wrt; suffl=sufflt; suffr=suffrt; gotl=gotlt; gotr=gotrt;
      }
      else {
        tfree(wlt); tfree(wrt); tfree(sufflt); tfree(suffrt);
      }
    }
    if (!gotl) {
      if (subgen_multiplier(wl,suffl)==-1)
         return -1;
    }
    if (!gotr && genstrcmp(wl,wr)!=0) {
      if (keepfiles) {
      /* Check again to see if we have got it recently */
        for (i=1;i<=numstoredmult;i++)
          if (strcmp(suffr,storedmult[i])==0)
            gotr = TRUE;
      }
      if (!gotr) {
        if (subgen_multiplier(wr,suffr)==-1)
           return -1;
      }
    }
/* Read back in the two multipliers and form their composite */
    sprintf(inf,"%s.m%s",gpname,suffl);
    if ((rfile = fopen(inf,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf);
        exit(1);
    }
    fsa_read(rfile,&mult1,ip_store,dr,0,TRUE,fsaname);
    fclose(rfile);
    sprintf(inf,"%s.m%s",gpname,suffr);
    if ((rfile = fopen(inf,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf);
        exit(1);
    }
    fsa_read(rfile,&mult2,ip_store,dr,0,TRUE,fsaname);
    fclose(rfile);

    compmultptr =
        fsa_composite(&mult1,&mult2,op_store,TRUE,tempfilename,readback);
    if (compmultptr==0)
      return -1;
    if (readback) {
      if (fsa_minimize(compmultptr)==-1)
        return -1;
    }
    else {
      if (fsa_ip_minimize(compmultptr)==-1)
        return -1;
    }
    sprintf(outf,"%s.m%s",gpname,s);
    wfile = fopen(outf,"w");
    fsa_print(wfile,compmultptr,fsaname);
    fclose(wfile);
    fsa_clear(compmultptr);
    tfree(compmultptr);

    if (keepfiles) {
      if (gotl) tfree(suffl)
      else storedmult[++numstoredmult] = suffl;
      if (gotr) tfree(suffr)
      else storedmult[++numstoredmult] = suffr;
    }
    else {
      sprintf(inf,"%s.m%s",gpname,suffl); unlink(inf);
      sprintf(inf,"%s.m%s",gpname,suffr); unlink(inf);
      tfree(suffl); tfree(suffr);
    }
    tfree(wl); tfree(wr);
  }

  return 0;
}

void 
read_subgpgens (void)
/* Read subgroup generators from rfile (assumed to be already open) */
{ 
  nsubgens=0;
  read_ident(rfile,kbm_buffer,&delim,FALSE);
    /* this is the name of the record containing the subgenerators */
  if (delim != ':'){
    fprintf(stderr,
        "#Input error: file must contain a record assignment\n");
    exit(1);
  }
  check_next_char(rfile,'=');
  read_ident(rfile,kbm_buffer,&delim,FALSE);
  if (delim != '(' || strcmp(kbm_buffer,"rec")!=0){
    fprintf(stderr,
        "#Input error: file must contain a record assignment\n");
    exit(1);
  }
  read_ident(rfile,kbm_buffer,&delim,FALSE);
    if (strcmp(kbm_buffer,"subGenerators")!=0) {
    fprintf(stderr,
    "Input error. 'subGenerators' list expected in subgroup generator file.\n");
    exit(1);
  }
  if (delim != ':'){
    fprintf(stderr,
        "#Input error: bad 'subgens' list assignment\n");
    exit(1);
  }
  check_next_char(rfile,'=');
  check_next_char(rfile,'[');
  nsubgens=0;
  do {
    if (!read_word(rfile,testword,testword+maxwordlen,
                             		&delim,names,ngens,TRUE)) {
      fprintf(stderr,
        "#Input error: no subgroup generators or missing word.\n");
      exit(1);
    }
    if (nsubgens+1>maxsubgens) {
      fprintf(stderr,
        "#Input error: too many subgroup generators.\n");
      exit(1);
    }
    tmalloc(subgen[nsubgens],gen,genstrlen(testword)+1);
    genstrcpy(subgen[nsubgens],testword);
    nsubgens++;
  } while (delim!=']');
}

int 
output_bad_words (void)
/* *existsptr and subwa are unequal. We nedd to find some words accepted
 * by subwa but not by *existsptr.
 * The function words_and_not will do this.
 * We then output the words, along with the original subgroup generators,
 * so that they can be used in the next run of gpsubwa.
 */
{ int numwords, i;
  tmalloc(badwords,gen *,maxwords)
  numwords = words_and_not(&subwa,existsptr,badwords,maxwords);
  if (numwords==-1)
    return -1;
  if (numwords==0) {
    fprintf(stderr,"Error: No offending subwords found!\n");
    return -1;
  }
  sprintf(outf,"%s.%s.words",gpname,subname);
/* We first see if there is already a list of words in the output file.
 * If so, then we want to include them as well in the new output.
 */
  if (rfile=fopen(outf,"r")){
  /* We replace out existing list of subgroup generators with the one in this
   * file
   */
    for(i=0;i<nsubgens;i++)
      tfree(subgen[i])
    read_subgpgens();
    fclose(rfile);
  }
  if (kbm_print_level>0)
    printf("  #Outputting %d subgroup generators + %d offending words.\n",
              nsubgens,numwords);
  wfile=fopen(outf,"w");
  fprintf(wfile,"_RWS_Sub_words := rec(\n  subGenerators:=[\n");
  /* First write the original subgroup generators */
  for (i=0;i<nsubgens;i++) {
    kbm_buffer[0] = '\0';
    add_to_buffer(4,"");
    add_word_to_buffer(wfile,subgen[i],names);
    add_to_buffer(0,",");
    printbuffer(wfile,kbm_buffer);
    tfree(subgen[i]);
  }
  /* And now the offending words */
  for (i=0;i<numwords;i++) {
    kbm_buffer[0] = '\0';
    add_to_buffer(4,"");
    add_word_to_buffer(wfile,badwords[i],names);
    if (i!=numwords-1)
      add_to_buffer(0,",");
    printbuffer(wfile,kbm_buffer);
    tfree(badwords[i]);
  }
  fprintf(wfile,"  ];\n);\n");
  fclose(wfile);
  fsa_clear(existsptr);
  tfree(existsptr);
  tfree(badwords);
  fsa_clear(&subwa);
  return 0;
}


void 
badusage_gpchecksubwa (void)
{
   fprintf(stderr,
"Usage: gpchecksubwa [-ip d/s[dr]] [-op d/s] [-silent] [-v] [-l] [-f]\n");
   fprintf(stderr,
 "\t\t[-m maxwords] groupname [subname].\n"
  );
	exit(1);
}
