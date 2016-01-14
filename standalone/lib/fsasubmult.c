/* file fsasubmult.c  23/4/96
 * 29/9/98 large-scale re-organisation.
 * 13/1/98 changes for the `gen' type replacing char for generators.
 * This file contains the procedure fsa_submult (minor modification of
 * fsa_triples).
 * Used in program gpchecksubwa to intersect a multiplier (both coordinates)
 * with the language accepted by the candidate subgroup word-acceptor.
 * It also contains words_and_not, for generating words w, such that
 * w*s is currently not accepted by the subgroup word-acceptor, for some
 * subgroup generator s.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "rws.h"
#include "externals.h"

/* Functions defined in this file: */
fsa * fsa_submult();
int words_and_not();

/* Functions used in this file and defined elsewhere */
boolean srec_equal();
boolean fsa_equal();
int sparse_target();
void fsa_init();
int  fsa_table_dptr_init();
void fsa_set_is_accepting();
void srec_copy();
void fsa_clear();
void fsa_clear_rws();
void compressed_transitions_read();
void short_hash_init();
int short_hash_locate();
void short_hash_clear();
unsigned short* short_hash_rec();
int stringlen();

fsa *
fsa_submult(subwaptr,multptr,op_table_type,destroy,tempfilename,readback)
	fsa *subwaptr, *multptr;
	storage_type op_table_type;
	boolean destroy;
	char *tempfilename;
	boolean readback;
/* *subwaptr is intended to be a candidate subgroup word-acceptor of an
 * automatic group (but could be any single-variable dfa).
 * *multptr is assumed to be a multiplier of the same automatic
 * group (but could be anyn 2-variable dfa with base alphabet equal to
 * the alphabet of *subwaptr). Both are assumed to be stored in dense-format.
 * This routine constructs the fsa of which the states are triples (s1,s2,d),
 * with s1 and s2 states of *subwaptr and d a state of *multptr.
 * (More precisely, if *subwaptr has n states, then s1 and s2 may also be equal
 * to n+1, meaning that the end of string symbol has been read on lhs or rhs,
 * with *subwaptr in an accepted state.)
 * The alphabet is 2-variable with base the alphabet of *subwaptr
 * (i.e. the same alphabet as *multptr).
 * The alphabet member (g1,g2) maps (s1,s2,d) to (s1^g1,s2^g2,d^(g1,g2))
 * if all three components are nonzero, and to zero otherwise.
 * The accept-states are those in which s1,s2,d are accept-states, or
 * s1 or s2 = n+1 (see above).
 * The transition-table of the resulting fsa is output in the usual way to
 * file tempfilename with table-type specified by op_table_type, before
 * minimisation.
 * Short hash-tables will be used, so this routine won't work if *subwaptr
 * or *multptr has more than MAXUSHORT states.
 *
 */
{
  int **subwatable, ***multtable,  ngens, ngens1, nsswa1, ne, nsswa, ns,
      *fsarow, nt, cstate, csswa1, csswa2, csmult, im, i, e, len, ct;
  unsigned short *ht_ptr;
  boolean  dense_op, acc;
  fsa *submultptr;
  short_hash_table ht;
  FILE *tempfile, *fopen();
  gen g1, g2;

  if (kbm_print_level>=3)
    printf("    #Calling fsa_submultptr.\n");

  if (!subwaptr->flags[DFA] || !multptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_submultptr only applies to DFA's.\n");
    return 0;
  }
  if (multptr->alphabet->type!=PRODUCT || multptr->alphabet->arity!=2) {
    fprintf(stderr,"Error in fsa_submultptr: second fsa must be 2-variable.\n");
    return 0;
  }
  if (!srec_equal(multptr->alphabet->base,subwaptr->alphabet)) {
    fprintf(stderr,"Error in fsa_submultptr: fsa's alphabet's don't match.\n");
    return 0;
  }
  if (subwaptr->states->size>=MAXUSHORT || multptr->states->size>=MAXUSHORT) {
    fprintf(stderr,
       "Error in fsa_submultptr: one of the fsa's has too many states.\n");
    return 0;
  }

  if (fsa_table_dptr_init(multptr)==-1) return 0;

  tmalloc(submultptr,fsa,1);
  fsa_init(submultptr);
  srec_copy(submultptr->alphabet,multptr->alphabet);
  submultptr->flags[DFA] = TRUE;
  submultptr->flags[ACCESSIBLE] = TRUE;
  submultptr->flags[BFS] = TRUE;

  ngens = subwaptr->alphabet->size;
  ngens1 = ngens+1;
  ne = multptr->alphabet->size;

  if (ne != ngens1*ngens1-1) {
   fprintf(stderr,
       "Error: in a 2-variable fsa, alphabet size should = ngens^2 - 1.\n");
    return 0;
  }

  subwatable = subwaptr->table->table_data_ptr;
  multtable = multptr->table->table_data_dptr;

  dense_op = op_table_type==DENSE;

  submultptr->num_initial = 1;
  tmalloc(submultptr->initial,int,2);
  submultptr->initial[1] = 1;
  submultptr->table->table_type = op_table_type;
  submultptr->table->denserows = 0;
  submultptr->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(submultptr->table->filename,char,stringlen(tempfilename)+1);
    strcpy(submultptr->table->filename,tempfilename);
  }
  
  fsa_set_is_accepting(multptr);
  /* We do not call fsa_ptr_is_accepting on subwaptr, since we need an extra
   * place in it for the end-of-string state (which will be accepting).
   */
  nsswa=subwaptr->states->size;
  nsswa1=nsswa+1;
  tmalloc(subwaptr->is_accepting,boolean,nsswa+2);
  if (subwaptr->num_accepting==nsswa) {
    for (i=1;i<=nsswa;i++)
      subwaptr->is_accepting[i]=TRUE;
  }
  else {
    for (i=1;i<=nsswa;i++)
      subwaptr->is_accepting[i]=FALSE;
    for (i=1;i<=subwaptr->num_accepting;i++)
      subwaptr->is_accepting[subwaptr->accepting[i]]=TRUE;
  }
  subwaptr->is_accepting[nsswa1]=TRUE;

  short_hash_init(&ht,TRUE,3,0,0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = subwaptr->initial[1];
  ht_ptr[1] = subwaptr->initial[1];
  ht_ptr[2] = multptr->initial[1];
  im = short_hash_locate(&ht,3);
  if (im!=1) {
    fprintf(stderr,"Hash-initialisation problem in fsa_submult.\n");
    return 0;
  }
  if ((tempfile=fopen(tempfilename,"w"))==0){
    fprintf(stderr,"Error: cannot open file %s\n",tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow,int,ne)
  else
    tmalloc(fsarow,int,2*ne+1)
 
  cstate = 0;
  if (dense_op)
    len = ne; /* The length of the fsarow output. */
  nt = 0; /* Number of transitions in submultptr */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level>=3) {
      if ((cstate<=1000 && cstate%100==0)||(cstate<=10000 && cstate%1000==0)||
          (cstate<=100000 && cstate%5000==0) || cstate%50000==0)
       printf("    #cstate = %d;  number of states = %d.\n",cstate,ht.num_recs);
    }
    ht_ptr = short_hash_rec(&ht,cstate);
    csswa1 = ht_ptr[0]; csswa2 = ht_ptr[1];
    csmult = ht_ptr[2];
    if (!dense_op)
      len = 0;
    e = 0; /* e is the number of the edge corresponding to the pair (g1,g2) */
    for (g1=1;g1<=ngens1;g1++) for (g2=1;g2<=ngens1;g2++) {
      e++;
/* Calculate action of generator-pair (g1,g2) on state cstate */
      if (g1==ngens1 && g2==ngens1)
        continue;
      ht_ptr = ht.current_ptr;
      ht_ptr[2] = dense_dtarget(multtable,g1,g2,csmult);
      if (ht_ptr[2]==0)
        im=0;
      else {
        if (csswa1==nsswa1) {
          ht_ptr[0] = g1==ngens1 ?  nsswa1 : 0;
        }
        else {
          ht_ptr[0] = g1==ngens1 ? (subwaptr->is_accepting[csswa1] ? nsswa1 : 0)
                                 :  dense_target(subwatable,g1,csswa1);
        }
        if (ht_ptr[0]==0)
          im=0;
        else {
         if (csswa2==nsswa1) {
          ht_ptr[1] = g2==ngens1 ?  nsswa1 : 0;
         }
         else {
          ht_ptr[1] = g2==ngens1 ? (subwaptr->is_accepting[csswa2] ? nsswa1 : 0)
                                 :  dense_target(subwatable,g2,csswa2);
         }
         if (ht_ptr[1]==0)
          im=0;
          else
            im = short_hash_locate(&ht,3);
        }
      }

      if (dense_op)
         fsarow[e-1] = im;
      else if (im>0) {
         fsarow[++len] = e;
         fsarow[++len] = im;
      }
      if (im>0)
        nt++;
    }  /* for (g1=1;g1<=ngens1; ... */
    if (!dense_op)
      fsarow[0] = len++;
    fwrite((void *)fsarow,sizeof(int),(size_t)len,tempfile);
  }  /*while (++cstate <= ht.num_recs) */

  fclose(tempfile);

  submultptr->states->type = SIMPLE;
  ns = submultptr->states->size = ht.num_recs;
  submultptr->table->numTransitions = nt;

  if (kbm_print_level>=3) {
    printf("    #Calculated transitions - %d states, %d transitions.\n",ns,nt);
    printf("    #Now calculating state labels.\n");
  }
  /* Now we locate the accept states */
  tmalloc(submultptr->is_accepting,boolean,ns+1);
  for (i=1;i<=ns;i++)
    submultptr->is_accepting[i]=FALSE;
  
  ct=0;
  for (i=1;i<=ns;i++) {
    ht_ptr = short_hash_rec(&ht,i);
    acc =
    submultptr->is_accepting[i] = subwaptr->is_accepting[ht_ptr[0]] &&
                                  subwaptr->is_accepting[ht_ptr[1]] &&
                                   multptr->is_accepting[ht_ptr[2]];
    if (acc) ct++;
  }

  submultptr->num_accepting = ct;
  if (ct==1 || ct != ns) {
    tmalloc(submultptr->accepting,int,ct+1);
    ct = 0;
    for (i=1;i<=ns;i++) if (submultptr->is_accepting[i])
      submultptr->accepting[++ct] = i;
  }
  tfree(submultptr->is_accepting);

  short_hash_clear(&ht);
  tfree(fsarow);
/* Now read the transition table back in */
  if (readback) {
    tempfile = fopen(tempfilename,"r");
    compressed_transitions_read(submultptr,tempfile);
    fclose(tempfile);
    unlink(tempfilename);
  }
  tfree(subwaptr->is_accepting);
  tfree(multptr->is_accepting);
  if (destroy) {
    fsa_clear(subwaptr); fsa_clear(multptr);
  }

  return submultptr;
}

int 
words_and_not (
/* Generate at most maxwords words accepted by *fsaptr1 but not by *fsaptr2.
 * Store them in words[0], words[1],..
 * fsa's may have at most 65536 states.
 */
    fsa *fsaptr1,
    fsa *fsaptr2,
    gen **words,
    int maxwords
)
{
  int **table1, **table2, ne, ns, dr1, dr2, bstate, bg, numwords,
      cstate, csa, csb, im, i, g, len;
  unsigned short *ht_ptr;
  boolean dense_ip1, dense_ip2;
  short_hash_table ht;
  int maxv = 65536;
  struct vertexd {
     gen g;
     int  state;
  } *definition, *newdef;
/* This is used to store the defining transition for the states of the new fsa.
 * If definition[i] = v, then state i is defined by the transition from
 * state v.state, with forst generator v.g (the second generator (from *fsaptr2)
 * does not need to be remembered).
 * State 1 does not have a definition.
 */

  if (kbm_print_level>=3)
    printf("    #Calling words_and_not.\n");
  if (!fsaptr1->flags[DFA] || !fsaptr2->flags[DFA]){
    fprintf(stderr,"Error: words_and_not only applies to DFA's.\n");
    return -1;
  }

  if (!srec_equal(fsaptr1->alphabet,fsaptr2->alphabet)) {
    fprintf(stderr,"Error in words_and_not: fsa's have different alphabets.\n");
    return -1;
  }

  if (fsaptr1->states->size>=MAXUSHORT || fsaptr2->states->size>=MAXUSHORT) {
    fprintf(stderr,
         "Sorry - one of the fsa's in words_and_not has too many states.\n");
    return -1;
  }
  if (fsaptr1->flags[RWS])
    fsa_clear_rws(fsaptr1);

  if (fsaptr2->flags[RWS])
    fsa_clear_rws(fsaptr2);

  if (fsaptr1->num_initial==0 || fsaptr2->num_initial==0) {
    fprintf(stderr,
           "One of the fsa's in words_and_not has no initial states.\n");
    fprintf(stderr,"Sorry - this case has not been catered for!\n");
    return -1;
  }

  ne = fsaptr1->alphabet->size;

  fsa_set_is_accepting(fsaptr1);
  fsa_set_is_accepting(fsaptr2);
  table1 = fsaptr1->table->table_data_ptr;
  table2 = fsaptr2->table->table_data_ptr;

  dense_ip1 = fsaptr1->table->table_type==DENSE;
  dense_ip2 = fsaptr2->table->table_type==DENSE;
  dr1 = fsaptr1->table->denserows;
  dr2 = fsaptr2->table->denserows;
  
  short_hash_init(&ht,TRUE,2,0,0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = fsaptr1->initial[1];
  ht_ptr[1] = fsaptr2->initial[1];
  im = short_hash_locate(&ht,2);
  if (im!=1) {
    fprintf(stderr,"Hash-initialisation problem in words_and_not.\n");
    return -1;
  }
 
/* Set up the array of structures to remember state-definitions. */
  tmalloc(definition, struct vertexd, maxv);
  ns=1;

  cstate = 0;
  numwords=0;

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level>=3) {
      if ((cstate<=1000 && cstate%100==0)||(cstate<=10000 && cstate%1000==0)||
          (cstate<=100000 && cstate%5000==0) || cstate%50000==0)
       printf("    #cstate = %d;  number of states = %d.\n",cstate,ht.num_recs);
    }
    ht_ptr = short_hash_rec(&ht,cstate);
    csa = ht_ptr[0]; csb = ht_ptr[1];
    for (g=1;g<=ne;g++) {
/* Calculate action of generator g on state cstate */
      ht_ptr = ht.current_ptr;
      ht_ptr[0] = csa ? target(dense_ip1,table1,g,csa,dr1) : 0;
      ht_ptr[1] = csb ? target(dense_ip2,table2,g,csb,dr2) : 0;
      if (ht_ptr[0]==0)
        im = 0;
      else {
        im = short_hash_locate(&ht,2);
        if (im>ns) {
        /* Check if this is an accept state of *fsaptr1 but not by *fsaptr2.
         * If so, work out a word leading to it and store it.
         */
          if (fsaptr1->is_accepting[ht_ptr[0]] &&
              !fsaptr2->is_accepting[ht_ptr[1]]) {
            /* First see how long the word is */
            len = 1;
            bg = g; bstate = cstate;
            while (bstate != 1) {
              len++;
              bg = definition[bstate].g;
              bstate = definition[bstate].state;
            }
            /* Now allocate space for it */
            tmalloc(words[numwords],gen,len+1);
            words[numwords][len] = 0;
            bg = g; bstate = cstate;
            while (1) {
              words[numwords][--len] = bg;
              if (bstate==1)
                break;
              bg = definition[bstate].g;
              bstate = definition[bstate].state;
            }
            numwords++;
            if (kbm_print_level>=3)
              printf("    #Found offending word number %d.\n",numwords);
  
            if (numwords >=maxwords) {
              tfree(definition);
              short_hash_clear(&ht);
              if (kbm_print_level >= 2)
                printf("  #Found %d new words. Aborting.\n",maxwords);
              return numwords;
            }
          }
        /* Remember definition of new state */
          ns++;
          if (ns==maxv) { /* need room for more definitions */
            if (kbm_print_level>=3)
              printf("    #Allocating more space for vertex definitions.\n");
            tmalloc(newdef,struct vertexd,2*maxv);
            for (i=1;i<maxv;i++)
              newdef[i] = definition[i];
            tfree(definition);
            definition = newdef;
            maxv *= 2;
          }
          definition[ns].g = g;
          definition[ns].state = cstate;
        }
      }
    }
  }

  tfree(definition);
  short_hash_clear(&ht);
  tfree(fsaptr1->is_accepting);
  tfree(fsaptr2->is_accepting);

  return numwords;
}
