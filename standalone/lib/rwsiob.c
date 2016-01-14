/* rwsio2.c 18/1/95
 * 9/1/98 change type of generators form char to `gen'.
 * This is the second file (first if rwsio.c) containing i/o functions for
 * re-writing systems. Some of the routines here are simplified versions
 * of those in rwsio.c, used when we are merely reading in a re-writing system
 * and not applying Knuth-Bendix to it.
 * These are used, for example, by the progrmas gpaxioms and reducewords.
 */

#include <stdio.h>

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "externals.h"


/* Functions defined in this file */
void read_kbinput_simple();
void read_gens();
void read_inverses();
void read_eqns_simple();
void rws_clear();
void read_subgens();
void print_rws_simple();

/* Functions used in this file defined in other files: */
void printbuffer();
void add_to_buffer();
int add_word_to_buffer();
void check_next_char();
void read_ident();
void read_delim();
void skip_gap_expression();
boolean read_int();
boolean read_string();
void process_names();
boolean read_word();
void set_separator();
void genstrcpy();
int genstrcmp();
int genstrlen();
int stringlen();

void
read_kbinput_simple(rfile,check,rwsptr)
        FILE *rfile;
        boolean check;
	rewriting_system *rwsptr;
/* This is a simplified version of read_kbinput() in rwsio.c.
 * It is used when a rewriting system will be read in but not altered.
 * If check is true, then the words in the equations are checked for
 * validity - this could make input slower if there are many equations
 */
{ int delim, n, i, j;
  boolean isRWS=FALSE, seengens=FALSE, seeneqns=FALSE;

  read_ident(rfile,rwsptr->name,&delim,FALSE);
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

/* main loop reading the fields of the record follows. */
  do{
    read_ident(rfile,kbm_buffer,&delim,FALSE);
    if (delim != ':'){
      fprintf(stderr,
          "#Input error: bad record field assignment\n");
      exit(1);
    }
    check_next_char(rfile,'=');
    if (strcmp(kbm_buffer,"isRWS")==0){
      isRWS = TRUE;
      read_ident(rfile,kbm_buffer,&delim,FALSE);
      if (strcmp(kbm_buffer,"true")!=0){
        fprintf(stderr,
            "#Input error: isRWS field must equal \"true\"\n");
        exit(1);
      }
    }
    else if (strcmp(kbm_buffer,"isConfluent")==0) {
      read_ident(rfile,kbm_buffer,&delim,FALSE);
      rwsptr->confluent = strcmp(kbm_buffer,"true")==0;
    }
    else if (strcmp(kbm_buffer,"maxeqns")==0){
      read_int(rfile,&n,&delim);
      if (rwsptr->inv_of!=0){
        fprintf(stderr,
            "#Input error: 'maxeqns' field must precede 'inverses' field\n");
        exit(1);
      }
/* We will exclude ridiculously small values of limit parameters. */
      if (n>16) {
         rwsptr->maxeqns = n;
	 rwsptr->maxeqnsset = TRUE;
      }
    }
    else if (strcmp(kbm_buffer,"maxreducelen")==0) {
      read_int(rfile,&n,&delim);
      if (n>4096 && !rwsptr->maxreducelenset)
        rwsptr->maxreducelen = n;
    }
    else if (strcmp(kbm_buffer,"tidyint")==0) {
      read_int(rfile,&n,&delim);
      rwsptr->tidyintset=TRUE;
      rwsptr->tidyint=n;
    }
    else if (strcmp(kbm_buffer,"maxstates")==0 ||
       strcmp(kbm_buffer,"confnum")==0 || strcmp(kbm_buffer,"sorteqns")==0 ||
       strcmp(kbm_buffer,"maxoplen")==0 || strcmp(kbm_buffer,"maxstoredlen")==0 ||
       strcmp(kbm_buffer,"maxwdiffs")==0 || strcmp(kbm_buffer,"silent")==0 ||
         strcmp(kbm_buffer,"verbose")==0)
	skip_gap_expression(rfile,&delim);
    else if (strcmp(kbm_buffer,"generatorOrder")==0){
      read_gens(rfile,rwsptr);
      process_names(rwsptr->gen_name,rwsptr->num_gens);
      seengens = TRUE;
      read_delim(rfile,&delim);
    }
    else if (strcmp(kbm_buffer,"inverses")==0){
      if (!seengens){
        fprintf(stderr,
          "#Input error: generator field must precede inverses field\n");
        exit(1);
      }
      read_inverses(rfile,rwsptr);
      read_delim(rfile,&delim);
    }
    else if (strcmp(kbm_buffer,"ordering")==0) {
      read_string(rfile,kbm_buffer,&delim);
      if (strcmp(kbm_buffer,"shortlex")==0)
        rwsptr->ordering = SHORTLEX;
      else if  (strcmp(kbm_buffer,"recursive")==0)
        rwsptr->ordering = RECURSIVE;
      else if (strcmp(kbm_buffer,"rt_recursive")==0)
        rwsptr->ordering = RT_RECURSIVE;
      else if (strcmp(kbm_buffer,"wtlex")==0)
        rwsptr->ordering = WTLEX;
      else if (strcmp(kbm_buffer,"wreathprod")==0)
        rwsptr->ordering = WREATHPROD;
      else if (strcmp(kbm_buffer,"none")==0)
        rwsptr->ordering = NONE;
      else{
        fprintf(stderr,
            "#Input error: invalid string for ordering field\n");
        exit(1);
      }
    }
    else if (strcmp(kbm_buffer,"weight")==0){
      if (!seengens){
        fprintf(stderr,
          "#Input error: generator field must precede weight field\n");
        exit(1);
      }
      tmalloc(rwsptr->weight,int,rwsptr->num_gens+1);
      check_next_char(rfile,'[');
      for (n=1;n<=rwsptr->num_gens;n++) {
          read_int(rfile,rwsptr->weight+n,&delim);
          if ((n<rwsptr->num_gens && delim!=',') ||
               (n==rwsptr->num_gens && delim!=']')){
            fprintf(stderr,"#Input error: ',' or ']' expected.\n");
            exit(1);
          }
      }
      read_delim(rfile,&delim);
    }
    else if (strcmp(kbm_buffer,"level")==0){
      if (!seengens){
        fprintf(stderr,
          "#Input error: generator field must precede level field\n");
        exit(1);
      }
      tmalloc(rwsptr->level,int,rwsptr->num_gens+1);
      check_next_char(rfile,'[');
      for (n=1;n<=rwsptr->num_gens;n++) {
        read_int(rfile,rwsptr->level+n,&delim);
        if (rwsptr->level[n]<=0) {
          fprintf(stderr,
             "#Input error: levels must be positive integers.\n");
          exit(1);
        }
        if (!(n<rwsptr->num_gens && delim==',') &&
                                  !(n==rwsptr->num_gens&& delim==']')){
          fprintf(stderr,
            "#Input error:  format of level field wrong\n");
          exit(1);
        }
      }
      read_delim(rfile,&delim);
    }
    else if (strcmp(kbm_buffer,"equations")==0){
      if (rwsptr->num_gens!=0 && rwsptr->inv_of==0){
        fprintf(stderr,"#Input error: record must have 'inverses' field\n");
        exit(1);
      }
      if (rwsptr->maxeqnsset) 
       /* increase it by rwsptr->num_gens, to avoid a possible difficulty with
        * the inverse equations.
        */
         rwsptr->maxeqns += rwsptr->num_gens;
/* Set separator in cosets case. */
      if (rwsptr->cosets) set_separator(rwsptr);
      tmalloc(rwsptr->eqns,reduction_equation,rwsptr->maxeqns+1);
      tmalloc(rwsptr->testword1,gen,rwsptr->maxreducelen+1);
      tmalloc(rwsptr->testword2,gen,rwsptr->maxreducelen+1);
      rwsptr->num_eqns=0;
      read_eqns_simple(rfile,check,rwsptr);
      read_delim(rfile,&delim);
      seeneqns = TRUE;
    }
    else if (strcmp(kbm_buffer,"done")==0){
      if (!seeneqns){
        fprintf(stderr,
            "#Input error: 'equations' field must precede 'done' field\n");
        exit(1);
      }
      check_next_char(rfile,'[');
      read_delim(rfile,&delim);
      if (delim!='[' && delim!=']'){
        fprintf(stderr,"#Input error: '[' or ']' expected.\n");
        exit(1);
      }
      if (delim=='[') while (1){
        read_int(rfile,&i,&delim);
        if (delim=='.'){
          check_next_char(rfile,'.');
          read_int(rfile,&j,&delim);
        }

        read_delim(rfile,&delim);
        if (delim==']')
          break;
        if (delim!=','){
          fprintf(stderr,"#Input error: ',' expected.\n");
          exit(1);
        }
        check_next_char(rfile,'[');
      }
      read_delim(rfile,&delim);
    }
    else {
      printf("#Warning: Unknown record field: %s\n",kbm_buffer);
      skip_gap_expression(rfile,&delim);
    }
    if (delim != ')' && delim != ','){
      fprintf(stderr,
          "#Input error:  field %s assignment must end ',' or ')', not %c\n",
               kbm_buffer,delim);
      exit(1);
    }
  } while (delim != ')');

  check_next_char(rfile,';');
  if (!isRWS){
    fprintf(stderr,
        "#Input error: record must have 'isRWS' field\n");
    exit(1);
  }
  if (rwsptr->num_gens!=0 && rwsptr->inv_of==0){
    fprintf(stderr,
        "#Input error: record must have 'inverses' field\n");
    exit(1);
  }
}

void
read_gens(rfile,rwsptr)
        FILE * rfile;
	rewriting_system *rwsptr;
/* Read the list of generator names into the array rws.gen_name, and
 * set rws.num_gens equal to the number of generators.
 */
{ int delim;
  rwsptr->num_gens=0;
  check_next_char(rfile,'[');
  tmalloc(rwsptr->gen_name,char *,MAXGEN+1);
  do{
    read_ident(rfile,kbm_buffer,&delim,TRUE);
    if (delim!=',' && delim!=']'){
      fprintf(stderr,"#Input error: ',' or ']' expected.\n");
      exit(1);
    }
    else if (stringlen(kbm_buffer)==0 && rwsptr->num_gens==0 && delim==']')
      return; /* no generators */
    else{
      rwsptr->num_gens++;
      if (rwsptr->num_gens>MAXGEN){
        fprintf(stderr, "#Sorry - too many generators.\n");
        exit(1);
      }
      tmalloc(rwsptr->gen_name[rwsptr->num_gens],char,stringlen(kbm_buffer)+1);
      strcpy(rwsptr->gen_name[rwsptr->num_gens],kbm_buffer);
    }
  } while (delim != ']');
/* Add the padding-symbol to the end of the list - not always needed,
 * but no harm.
 */
  tmalloc(rwsptr->gen_name[rwsptr->num_gens+1],char,2);
  strcpy(rwsptr->gen_name[rwsptr->num_gens+1],"_");
}

void
read_inverses(rfile,rwsptr)
        FILE * rfile;
	rewriting_system *rwsptr;
/* The list of inverses is read.
 * An inverse inv(g) of a generator g satisfies g.inv(g) = inv(g).g = 1 -
 * i.e. this lists only 2-sided inverses
 * so the inv function must be involutory.
 * If the monoid is a group, then of course all generators have inverses.
 * In general, the list may have gaps.
 */
{ int g, i, ino, delim;
  check_next_char(rfile,'[');
  tmalloc(rwsptr->inv_of,int,MAXGEN+2);
  for (i=1;i<=rwsptr->num_gens;i++)
    rwsptr->inv_of[i] = 0;
  g = 0;
  do{
    read_ident(rfile,kbm_buffer,&delim,TRUE);
    if (delim!=',' && delim!=']'){
      fprintf(stderr,"#Input error: ',' or ']' expected.\n");
      exit(1);
    }
    else if (rwsptr->num_gens==0 && delim==']') /* no generators */
      return;
    else{
      g++;
      if (g>rwsptr->num_gens){
          fprintf(stderr,"#Input error: inverse list too long.\n");
        exit(1);
      }
      if (stringlen(kbm_buffer)==0)
        ino=0;
      else{
        if (kbm_algno == -1) {
          ino = 0;
          for (i=1;i<=rwsptr->num_gens;i++)
          if (strcmp(kbm_buffer,rwsptr->gen_name[i])==0) {
            ino = i;
            break;
          }
          if (ino==0) {
            fprintf(stderr,
                      "#Input error: unknown generator in inverses list.\n");
            exit(1);
          }
        }
        else {
          ino = (kbm_algno==0) ?
              kbm_gen_no[*kbm_buffer] : kbm_gen_no[atoi(kbm_buffer+kbm_algno)];
          if (ino==0 || strcmp(kbm_buffer,rwsptr->gen_name[ino]) != 0){
            fprintf(stderr,
                "#Input error: unknown generator in inverses list.\n");
            exit(1);
          }
        }
        if (rwsptr->inv_of[ino]!=0 && rwsptr->inv_of[ino]!=g){
          fprintf(stderr,"#Input error: inverse list must be involutory.\n");
          exit(1);
        }
      }
      rwsptr->inv_of[g]=ino;
    }
  } while (delim != ']');
  rwsptr->inv_of[rwsptr->num_gens+1] = rwsptr->num_gens+1;
    /* In case there is a padding symbol */
}

void
read_eqns_simple(rfile,check,rwsptr)
        FILE *rfile;
        boolean check;
	rewriting_system *rwsptr;
/* Read the initial reduction equations  -
 * simplified version of "read_eqns" in rwsio.c
 * Here we simply read them in and store them without any processing.
 */
{ int delim, i, ct, l1, l2, max;
  gen *test1 = rwsptr->testword1, *test2 = rwsptr->testword2;
  check_next_char(rfile,'[');
  read_delim(rfile,&delim);
  if (delim==']')
    return;
  if (delim!='['){
    fprintf(stderr,"#Input error: '[' expected.\n");
    exit(1);
  }
  ct = 0;
  while (1){
    read_word(rfile,test1,test1+rwsptr->maxreducelen,
                      &delim,rwsptr->gen_name,rwsptr->num_gens,check);
    if (delim!=','){
      fprintf(stderr,"#Input error: ',' expected.\n");
      exit(1);
    }
    read_word(rfile,test2,test2+rwsptr->maxreducelen,
			&delim,rwsptr->gen_name,rwsptr->num_gens,check);
    if (delim!=']'){
      fprintf(stderr,"#Input error: ']' expected.\n");
      exit(1);
    }
    ct++;
    if (ct >= rwsptr->maxeqns){
      printf("#Too many equations - increase maxeqns to get started.\n");
      exit(1);
    }
    l1 = genstrlen(test1); l2 = genstrlen(test2);
    max = l1>l2 ? l1 : l2;
/* We assign the same space for both sides, since we may be balancing them
 * later.
 */
    tmalloc(rwsptr->eqns[ct].lhs,gen,max+1);
    genstrcpy(rwsptr->eqns[ct].lhs,test1);
    tmalloc(rwsptr->eqns[ct].rhs,gen,max+1);
    genstrcpy(rwsptr->eqns[ct].rhs,test2);

    read_delim(rfile,&delim);
    if (delim==']')
      break;
    if (delim!=','){
      fprintf(stderr,"#Input error: ',' expected.\n");
      exit(1);
    }
    check_next_char(rfile,'[');
  }

  rwsptr->num_eqns += ct;
}

void
rws_clear(rwsptr)
        rewriting_system *rwsptr;
/* Free the assigned space associated with a rewriting-system,
 * excluding its reduction_automaton, which should be freed separately
 * with fsa_clear, if it is present.
 */
{ int i;
        for (i=1;i<=rwsptr->num_eqns;i++) {
                tfree((rwsptr->eqns)[i].lhs);
                tfree((rwsptr->eqns)[i].rhs);
        }
        tfree(rwsptr->eqns);
        for (i=1;i<=rwsptr->num_gens+1;i++)
                tfree(rwsptr->gen_name[i]);
        tfree(rwsptr->gen_name);
        tfree(rwsptr->weight);
        tfree(rwsptr->level);
        tfree(rwsptr->inv_of);
        tfree(rwsptr->history);
        tfree(rwsptr->slowhistory);
        tfree(rwsptr->slowhistorysp);
        tfree(rwsptr->preflen);
        tfree(rwsptr->prefno);
        tfree(rwsptr->testword1);
        tfree(rwsptr->testword2);
}

void
read_subgens(rfile,words,names,inverses,rwsptr)
        FILE *rfile;
	gen **words;
	boolean names;
	boolean inverses;
	rewriting_system *rwsptr;
/* Read a list of subgroup generators from the (open) file rfile, putting them
 * into words.
 * If names is true, then names for the new generators are also read in,
 * and if inverses is true, inverses are inserted after these names,
 * provided that they are not already in the file.
 * These names are inserted straight into rws.gen_name
 */
{ int ng, numsubgens, invgen, invgenno, i, delim;
  gen *subgenword;
  boolean seensubgens, seensubgennames, seeninversenames, foundname;

  if (inverses && !names) {
    fprintf(stderr,
         "#Do not call read_subgens with inverses true and names false.\n");
    exit(1);
  }
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
    fprintf(stderr,"#Input error: file must contain a record assignment\n");
    exit(1);
  }

/* main loop reading the fields of the record follows. */
  seensubgens=seensubgennames=seeninversenames=FALSE;
  do{
    read_ident(rfile,kbm_buffer,&delim,FALSE);
    if (delim != ':'){
      fprintf(stderr,"#Input error: bad record field assignment\n");
      exit(1);
    }
    check_next_char(rfile,'=');
    if (strcmp(kbm_buffer,"subGenerators")==0) {
      seensubgens=TRUE;
      subgenword=rwsptr->testword1;
      check_next_char(rfile,'[');
      numsubgens=0;
      do {
        if (!read_word(rfile,subgenword,subgenword+rwsptr->maxreducelen,
                       &delim,rwsptr->gen_name,rwsptr->num_gens,TRUE)) {
          fprintf(stderr,
            "#Input error: no subgroup generators or missing word.\n");
          exit(1);
        }
        numsubgens++;
        tmalloc(words[numsubgens],gen,genstrlen(subgenword)+1);
        genstrcpy(words[numsubgens],subgenword);
      } while (delim!=']');
      words[numsubgens+1]=0; /* To mark end of list of new words */
    
      rwsptr->num_gens++;
      if (rwsptr->num_gens>MAXGEN){
        fprintf(stderr,"#Sorry - too many generators.\n");
        exit(1);
      }
      ng=rwsptr->num_gens; /* no. of original generators + 1 for separator */
      rwsptr->inv_of[ng]=0;
      tmalloc(rwsptr->gen_name[ng],char,3);
      strcpy(rwsptr->gen_name[ng],"_H");
      read_delim(rfile,&delim);
    }
    else if (strcmp(kbm_buffer,"subGeneratorNames")==0) {
      if (names) {
        if (!seensubgens){
          fprintf(stderr,
   "#Input error. 'subGenerators' list must precede 'subGeneratorNames.\n");
          exit(1);
        }
        seensubgennames=TRUE;
        if (rwsptr->num_gens+numsubgens>MAXGEN ||
            (inverses && (rwsptr->num_gens+2*numsubgens>MAXGEN))) {
          fprintf(stderr,
            "#Sorry -  too many monoid generators.\n");
          exit(1);
        }
        check_next_char(rfile,'[');
        for (i=1;i<=numsubgens;i++) {
           read_ident(rfile,kbm_buffer,&delim,TRUE);
           if (delim!=',' && delim!=']'){
             fprintf(stderr,"#Input error: ',' or ']' expected.\n");
             exit(1);
           }
           if (stringlen(kbm_buffer)==0){
             fprintf(stderr,"#Input error: missing subGenerator name.\n");
             exit(1);
           }
           rwsptr->num_gens++;
           rwsptr->inv_of[rwsptr->num_gens]=0;
           tmalloc(rwsptr->gen_name[rwsptr->num_gens],char,
                                              stringlen(kbm_buffer)+1);
           strcpy(rwsptr->gen_name[rwsptr->num_gens],kbm_buffer);
        }
        if (delim!=']') {
          fprintf(stderr,
      "#Input error: ']' expected at end of 'subGeneratorNames' assignment\n");
          exit(1);
        }
        read_delim(rfile,&delim);
      }
      else 
        skip_gap_expression(rfile,&delim);
    }
    else if (strcmp(kbm_buffer,"subGeneratorInverseNames")==0) {
      if (names) {
        if (!seensubgennames){
          fprintf(stderr,
   "#Input error: 'subGeneratorNames' list must precede inverses.\n");
          exit(1);
        }
        seeninversenames=TRUE;
        if (rwsptr->num_gens+numsubgens>MAXGEN) {
          fprintf(stderr,"#Sorry - too many generators.\n");
          exit(1);
        }
        check_next_char(rfile,'[');
        invgen=ng;
        do {
           read_ident(rfile,kbm_buffer,&delim,TRUE);
           if (delim!=',' && delim!=']'){
             fprintf(stderr,"#Input error: ',' or ']' expected.\n");
             exit(1);
           }
           invgen++;
           if (invgen>rwsptr->num_gens){
               fprintf(stderr,"#Input error: inverse list too long.\n");
             exit(1);
           }
           if (stringlen(kbm_buffer)!=0) {
             foundname=FALSE;
             for(i=1;i<=numsubgens;i++)
               if (strcmp(kbm_buffer,rwsptr->gen_name[ng+i])==0) {
                 foundname=TRUE;
                 invgenno=ng+i;
                 rwsptr->inv_of[invgen]=invgenno;
                 if (rwsptr->inv_of[invgenno]!=0 &&
                            rwsptr->inv_of[invgenno]!=invgen) {
                    fprintf(stderr,
                        "#Input error: inverse list must be involutory.\n");
                    exit(1);
                 }
                 rwsptr->inv_of[invgenno]=invgen;
               }
             if (!foundname) {
               fprintf(stderr,
                  "#Input error: unknown name in inverse list.\n");
               exit(1);
             }
           }
        }  while (delim != ']');
        read_delim(rfile,&delim);
      }
      else 
        skip_gap_expression(rfile,&delim);
    }
    else {
      printf("#Warning: Unknown record field: %s\n",kbm_buffer);
      skip_gap_expression(rfile,&delim);
    }
    if (delim != ')' && delim != ','){
      fprintf(stderr,
          "#Input error:  field %s assignment must end ',' or ')', not %c\n",
               kbm_buffer,delim);
      exit(1);
    }
  } while (delim != ')');
  check_next_char(rfile,';');

  if (!seensubgens) {
    fprintf(stderr,"#Input error: record contains no subGenerators field.\n");
    exit(1);
  }
  if (names && !seensubgennames) {
    fprintf(stderr,
             "#Input error: record contains no subGeneratorNames field.\n");
    exit(1);
  }
  if (inverses && !seeninversenames) {
      /* We introduce standard inverse names */
    for (i=1;i<=numsubgens;i++) {
      rwsptr->inv_of[ng+i]=ng+numsubgens+i;
      rwsptr->inv_of[ng+numsubgens+i]=ng+i;
      strcpy(kbm_buffer,rwsptr->gen_name[ng+i]);
      strcat(kbm_buffer,"^-1");
      rwsptr->num_gens++;
      tmalloc(rwsptr->gen_name[rwsptr->num_gens],char,stringlen(kbm_buffer)+1);
      strcpy(rwsptr->gen_name[rwsptr->num_gens],kbm_buffer);
    }
  }
}

void
print_rws_simple(wfile,rwsptr)
	FILE *wfile;
	rewriting_system *rwsptr;
/* A simplified version of print_kboutput() when we have merely
 * edited the file.
 */
{ int i,  n;

  sprintf(kbm_buffer,"%s := rec(",rwsptr->name);
  printbuffer(wfile);
  add_to_buffer(16,"isRWS");
  sprintf(kbm_buffer+stringlen(kbm_buffer)," := true,");
  printbuffer(wfile);

  if (rwsptr->confluent) {
    add_to_buffer(16,"isConfluent");
    sprintf(kbm_buffer+stringlen(kbm_buffer)," := true,");
    printbuffer(wfile);
  }

  if (rwsptr->tidyintset) {
    add_to_buffer(16,"tidyint");
    sprintf(kbm_buffer+stringlen(kbm_buffer)," := %d,",rwsptr->tidyint);
    printbuffer(wfile);
  }
  add_to_buffer(16,"generatorOrder");
  sprintf(kbm_buffer+stringlen(kbm_buffer)," := [");
  for (i=1;i<=rwsptr->num_gens;i++){
    if (i==1 || stringlen(kbm_buffer)+stringlen(rwsptr->gen_name[i]) <= 76){
       if (i>1)
          add_to_buffer(0,",");
       sprintf(kbm_buffer+stringlen(kbm_buffer),"%s",rwsptr->gen_name[i]);
    }
    else {
      add_to_buffer(0,",");
      printbuffer(wfile);
      add_to_buffer(21,"");
      sprintf(kbm_buffer+stringlen(kbm_buffer),"%s",rwsptr->gen_name[i]);
    }
  }
  add_to_buffer(0,"],");
  printbuffer(wfile);

  add_to_buffer(16,"ordering");
  if (rwsptr->ordering==SHORTLEX)
    sprintf(kbm_buffer+stringlen(kbm_buffer)," := \"shortlex\",");
  else if (rwsptr->ordering==RECURSIVE)
    sprintf(kbm_buffer+stringlen(kbm_buffer)," := \"recursive\",");
  else if (rwsptr->ordering==RT_RECURSIVE)
    sprintf(kbm_buffer+stringlen(kbm_buffer)," := \"rt_recursive\",");
  else if (rwsptr->ordering==WTLEX)
    sprintf(kbm_buffer+stringlen(kbm_buffer)," := \"wtlex\",");
  else if (rwsptr->ordering==WREATHPROD)
    sprintf(kbm_buffer+stringlen(kbm_buffer)," := \"wreathprod\",");
  else if (rwsptr->ordering==NONE)
    sprintf(kbm_buffer+stringlen(kbm_buffer)," := \"none\",");
  printbuffer(wfile);

  if (rwsptr->ordering==WTLEX) {
    add_to_buffer(16,"weight");
    sprintf(kbm_buffer+stringlen(kbm_buffer)," := [");
    for (i=1;i<=rwsptr->num_gens;i++){
      if (i>1) add_to_buffer(0,",");
      sprintf(kbm_buffer+stringlen(kbm_buffer),"%d",rwsptr->weight[i]);
    }
    add_to_buffer(0,"],");
    printbuffer(wfile);
  }

  if (rwsptr->ordering==WREATHPROD) {
    add_to_buffer(16,"level");
    sprintf(kbm_buffer+stringlen(kbm_buffer)," := [");
    for (i=1;i<=rwsptr->num_gens;i++){
      if (i>1) add_to_buffer(0,",");
      sprintf(kbm_buffer+stringlen(kbm_buffer),"%d",rwsptr->level[i]);
    }
    add_to_buffer(0,"],");
    printbuffer(wfile);
  }

  add_to_buffer(16,"inverses");
  sprintf(kbm_buffer+stringlen(kbm_buffer)," := [");
  for (i=1;i<=rwsptr->num_gens;i++){
    if (i>1)
      add_to_buffer(0,",");
    if (rwsptr->inv_of[i] != 0){
      if (stringlen(kbm_buffer)+
                    stringlen(rwsptr->gen_name[rwsptr->inv_of[i]]) > 76){
        printbuffer(wfile);
        add_to_buffer(21,"");
      }
      sprintf(kbm_buffer+stringlen(kbm_buffer),
                       "%s",rwsptr->gen_name[rwsptr->inv_of[i]]);
    }
  }
  add_to_buffer(0,"],");
  printbuffer(wfile);

  add_to_buffer(16,"equations");
  sprintf(kbm_buffer+stringlen(kbm_buffer)," := [");
  for (i=1;i<=rwsptr->num_eqns;i++){
    printbuffer(wfile);
    add_to_buffer(10,"[");
    n=add_word_to_buffer(wfile,rwsptr->eqns[i].lhs,rwsptr->gen_name);
    sprintf(kbm_buffer+stringlen(kbm_buffer),",");
    if (n>0 || stringlen(kbm_buffer)>40){
      printbuffer(wfile);
      add_to_buffer(12,"");
    }
    add_word_to_buffer(wfile,rwsptr->eqns[i].rhs,rwsptr->gen_name);
    if (i==rwsptr->num_eqns)
      sprintf(kbm_buffer+stringlen(kbm_buffer),"]");
    else
      sprintf(kbm_buffer+stringlen(kbm_buffer),"],");
  }
  printbuffer(wfile);
  add_to_buffer(8,"]");
  printbuffer(wfile);

  sprintf(kbm_buffer,");");
  printbuffer(wfile);
}
