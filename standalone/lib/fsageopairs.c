/* file fsageopairs.c  15/4/96
 * 29/9/98 large-scale re-organisation.
 * 13/1/98 - changes for `gen' type of generator replacing char.
 * 
 * The functions in this file are adaptated from those in fsatriples.c.
 * They are used as part of a procedure to construct the geodesic
 * word-acceptor and geodesic pairs fsa for a word-hyperbolic group.
 *
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "rws.h"
#include "externals.h"

/* Functions defined in this file: */
fsa * fsa_geopairs();
fsa * fsa_geopairs_short();
fsa * fsa_geopairs_int();
int  fsa_checkgeowa();
int  fsa_checkgeowa_short();
int  fsa_checkgeowa_int();

/* Functions used in this file and defined elsewhere */
boolean srec_equal();
void fsa_init();
int  fsa_table_dptr_init();
void fsa_set_is_accepting();
void compressed_transitions_read();
void srec_copy();
void fsa_clear();
void short_hash_init();
int short_hash_locate();
void short_hash_clear();
unsigned short* short_hash_rec();
void hash_init();
int hash_locate();
void hash_clear();
int * hash_rec();
int stringlen();

fsa *
fsa_geopairs(waptr,diffptr,op_table_type,destroy,tempfilename,readback)
	fsa *waptr, *diffptr;
	storage_type op_table_type;
	boolean destroy;
	char *tempfilename;
	boolean readback;
/* *waptr is assumed to be the word-acceptor of an automatic group.
 * (In particular, all states should be accepting.)
 * *diffptr is assumed to be a word-difference machine of the same automatic
 * group. Both are assumed to be stored in dense-format.
 * This routine constructs the fsa of which the states are geopairsptr (st,d),
 * with st a state of *waptr and d a state of *diffptr.
 * The alphabet is 2-variable with base the alphabet of *waptr
 * (i.e. the same alphabet as *diffptr).
 * The alphabet member (g1,g2) maps (st,d) to (st^g2,d^(g1,g2))
 * if all three components are nonzero, and to zero otherwise,
 * but only when g1 and g2 are members of the base-alphabet itself, and
 * not the end-of-string symbol. This is because we want the constructed
 * 2-variable fsa to words of the same length only.
 * The effect will be to accept a pair of words (w1,w2) if the pair is
 * accepted by *diffptr, w2 is accepted by *waptr, and w1 has the same
 * length as w2.
 * The transition-table of the resulting fsa is output in the usual way to
 * file tempfilename with table-type specified by op_table_type, before
 * minimisation.
 */
{

  if (kbm_print_level>=3)
    printf("    #Calling fsa_geopairs.\n");
  if (waptr->states->size<MAXUSHORT && diffptr->states->size<MAXUSHORT)
     return fsa_geopairs_short(waptr,diffptr,op_table_type,destroy,
			tempfilename,readback);
  else
     return fsa_geopairs_int(waptr,diffptr,op_table_type,destroy,
			tempfilename,readback);
}

fsa *
fsa_geopairs_short(waptr,diffptr,op_table_type,destroy,tempfilename,readback)
	fsa *waptr, *diffptr;
	storage_type op_table_type;
	boolean destroy;
	char *tempfilename;
	boolean readback;
{
  int **watable, ***difftable, identity, ngens, ngens1, ne, ns, *fsarow,
      nt, cstate, cswa, csdiff, im, i, e, len, ct;
  unsigned short *ht_ptr;
  boolean  dense_op;
  fsa *geopairsptr;
  short_hash_table ht;
  FILE *tempfile, *fopen();
  gen g1, g2;

  if (!waptr->flags[DFA] || !diffptr->flags[DFA]){
    fprintf(stderr,"Error: fsa__geopairsptr only applies to DFA's.\n");
    return 0;
  }
  if (waptr->alphabet->type!=IDENTIFIERS) {
    fprintf(stderr,"Error in fsa_geopairsptr: first fsa has wrong type.\n");
    return 0;
  }
  if (waptr->num_accepting != waptr->states->size) {
    fprintf(stderr,
       "Error in fsa_geopairsptr: first fsa should be a word-acceptor.\n");
    return 0;
  }
  if (diffptr->alphabet->type!=PRODUCT || diffptr->alphabet->arity!=2) {
    fprintf(stderr,
          "Error in fsa_geopairsptr: second fsa must be 2-variable.\n");
    return 0;
  }
/*
  if (diffptr->states->type!=WORDS) {
    fprintf(stderr,
       "Error in fsa_geopairsptr: second fsa must be word-difference type.\n");
    return 0;
  }
*/
  if (!srec_equal(diffptr->alphabet->base,waptr->alphabet)) {
    fprintf(stderr,"Error in fsa_geopairsptr: fsa's alphabet's don't match.\n");
    return 0;
  }

  if (fsa_table_dptr_init(diffptr)==-1) return 0;
  fsa_set_is_accepting(diffptr);

  tmalloc(geopairsptr,fsa,1);
  fsa_init(geopairsptr);
  srec_copy(geopairsptr->alphabet,diffptr->alphabet);
  geopairsptr->states->type = SIMPLE;
  geopairsptr->flags[DFA] = TRUE;
  geopairsptr->flags[ACCESSIBLE] = TRUE;
  geopairsptr->flags[BFS] = TRUE;

  ngens = waptr->alphabet->size;
  ngens1 = ngens+1;
  ne = diffptr->alphabet->size;

  if (ne != ngens1*ngens1-1) {
   fprintf(stderr,
       "Error: in a 2-variable fsa, alphabet size should = ngens^2 - 1.\n");
    return 0;
  }

  watable = waptr->table->table_data_ptr;
  difftable = diffptr->table->table_data_dptr;

  dense_op = op_table_type==DENSE;

  geopairsptr->num_initial = 1;
  tmalloc(geopairsptr->initial,int,2);
  geopairsptr->initial[1] = 1;
  geopairsptr->table->table_type = op_table_type;
  geopairsptr->table->denserows = 0;
  geopairsptr->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(geopairsptr->table->filename,char,stringlen(tempfilename)+1);
    strcpy(geopairsptr->table->filename,tempfilename);
  }

  short_hash_init(&ht,TRUE,2,0,0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = waptr->initial[1];
  ht_ptr[1] =identity = diffptr->initial[1];
  im = short_hash_locate(&ht,2);
  if (im!=1) {
    fprintf(stderr,"Hash-initialisation problem in fsa_geopairsptr.\n");
    return 0;
  }
/* Just in case we are using the diff1 machine as *diffptr, we should
 * make sure that it accepts the diagonal.
 */
  for (g1=1;g1<=ngens;g1++)
     set_dense_dtarget(difftable,g1,g1,identity,identity);
  
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
  nt = 0; /* Number of transitions in geopairsptr */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level>=3) {
      if ((cstate<=1000 && cstate%100==0)||(cstate<=10000 && cstate%1000==0)||
          (cstate<=100000 && cstate%5000==0) || cstate%50000==0)
       printf("    #cstate = %d;  number of states = %d.\n",cstate,ht.num_recs);
    }
    ht_ptr = short_hash_rec(&ht,cstate);
    cswa = ht_ptr[0];
    csdiff = ht_ptr[1];
    if (!dense_op)
      len = 0;
    e = 0; /* e is the number of the edge corresponding to the pair (g1,g2) */
    for (g1=1;g1<=ngens1;g1++) for (g2=1;g2<=ngens1;g2++) {
      e++;
/* Calculate action of generator-pair (g1,g2) on state cstate */
      if (g1==ngens1 && g2==ngens1)
        continue;
      if (g1==ngens1 || g2==ngens1)
        im=0; /* no end-of-string symbols accepted */
      else {
        ht_ptr = ht.current_ptr;
        ht_ptr[1] = dense_dtarget(difftable,g1,g2,csdiff);
        if (ht_ptr[1]==0)
          im=0;
        else {
          ht_ptr[0] = dense_target(watable,g2,cswa);
          if (ht_ptr[0]==0)
            im=0;
          else
            im = short_hash_locate(&ht,2);
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

  ns = geopairsptr->states->size = ht.num_recs;
  geopairsptr->table->numTransitions = nt;

  if (kbm_print_level>=3) {
    printf("    #Calculated transitions - %d states, %d transitions.\n",ns,nt);
    printf("    #Now calculating accept states.\n");
  }
  tmalloc(geopairsptr->is_accepting,boolean,ns+1);
  geopairsptr->num_accepting=0;
  for (i=1;i<=ns;i++) {
  /* The state is accepting iff its *diffptr component is accepting */
    ht_ptr = short_hash_rec(&ht,i);
    if (diffptr->is_accepting[ht_ptr[1]]) {
      geopairsptr->num_accepting++;
      geopairsptr->is_accepting[i] = TRUE;
    }   
    else
      geopairsptr->is_accepting[i] = FALSE;
  }
  tmalloc(geopairsptr->accepting,int,geopairsptr->num_accepting+1);
  ct=0;
  for (i=1;i<=ns;i++) if (geopairsptr->is_accepting[i])
    geopairsptr->accepting[++ct]=i;
  tfree(geopairsptr->is_accepting);
  tfree(diffptr->is_accepting);

  short_hash_clear(&ht);
  tfree(fsarow);
  if (readback) {
    tempfile = fopen(tempfilename,"r");
    compressed_transitions_read(geopairsptr,tempfile);
    fclose(tempfile);
    unlink(tempfilename);
  }
  if (destroy) {
    fsa_clear(waptr); fsa_clear(diffptr);
  }

  return geopairsptr;
}

fsa *
fsa_geopairs_int(waptr,diffptr,op_table_type,destroy,tempfilename,readback)
	fsa *waptr, *diffptr;
	storage_type op_table_type;
	boolean destroy;
	char *tempfilename;
	boolean readback;
{
  int **watable, ***difftable, identity, ngens, ngens1, ne, ns, *fsarow,
      nt, cstate, cswa, csdiff, im, i, e, len, ct;
  int *ht_ptr;
  boolean  dense_op;
  fsa *geopairsptr;
  hash_table ht;
  FILE *tempfile, *fopen();
  gen g1, g2;

  if (!waptr->flags[DFA] || !diffptr->flags[DFA]){
    fprintf(stderr,"Error: fsa__geopairsptr only applies to DFA's.\n");
    return 0;
  }
  if (waptr->alphabet->type!=IDENTIFIERS) {
    fprintf(stderr,"Error in fsa_geopairsptr: first fsa has wrong type.\n");
    return 0;
  }
  if (waptr->num_accepting != waptr->states->size) {
    fprintf(stderr,
       "Error in fsa_geopairsptr: first fsa should be a word-acceptor.\n");
    return 0;
  }
  if (diffptr->alphabet->type!=PRODUCT || diffptr->alphabet->arity!=2) {
    fprintf(stderr,
      "Error in fsa_geopairsptr: second fsa must be 2-variable.\n");
    return 0;
  }
/*
  if (diffptr->states->type!=WORDS) {
    fprintf(stderr,
       "Error in fsa_geopairsptr: second fsa must be word-difference type.\n");
    return 0;
  }
*/
  if (!srec_equal(diffptr->alphabet->base,waptr->alphabet)) {
    fprintf(stderr,"Error in fsa_geopairsptr: fsa's alphabet's don't match.\n");
    return 0;
  }

  if (fsa_table_dptr_init(diffptr)==-1) return 0;
  fsa_set_is_accepting(diffptr);

  tmalloc(geopairsptr,fsa,1);
  fsa_init(geopairsptr);
  srec_copy(geopairsptr->alphabet,diffptr->alphabet);
  geopairsptr->states->type = SIMPLE;
  geopairsptr->flags[DFA] = TRUE;
  geopairsptr->flags[ACCESSIBLE] = TRUE;
  geopairsptr->flags[BFS] = TRUE;

  ngens = waptr->alphabet->size;
  ngens1 = ngens+1;
  ne = diffptr->alphabet->size;

  if (ne != ngens1*ngens1-1) {
   fprintf(stderr,
       "Error: in a 2-variable fsa, alphabet size should = ngens^2 - 1.\n");
    return 0;
  }

  watable = waptr->table->table_data_ptr;
  difftable = diffptr->table->table_data_dptr;

  dense_op = op_table_type==DENSE;

  geopairsptr->num_initial = 1;
  tmalloc(geopairsptr->initial,int,2);
  geopairsptr->initial[1] = 1;
  geopairsptr->table->table_type = op_table_type;
  geopairsptr->table->denserows = 0;
  geopairsptr->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(geopairsptr->table->filename,char,stringlen(tempfilename)+1);
    strcpy(geopairsptr->table->filename,tempfilename);
  }

  hash_init(&ht,TRUE,2,0,0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = waptr->initial[1];
  ht_ptr[1] =identity = diffptr->initial[1];
  im = hash_locate(&ht,2);
  if (im!=1) {
    fprintf(stderr,"Hash-initialisation problem in fsa_geopairsptr.\n");
    return 0;
  }
/* Just in case we are using the diff1 machine as *diffptr, we should
 * make sure that it accepts the diagonal.
 */
  for (g1=1;g1<=ngens;g1++)
     set_dense_dtarget(difftable,g1,g1,identity,identity);
  
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
  nt = 0; /* Number of transitions in geopairsptr */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level>=3) {
      if ((cstate<=1000 && cstate%100==0)||(cstate<=10000 && cstate%1000==0)||
          (cstate<=100000 && cstate%5000==0) || cstate%50000==0)
       printf("    #cstate = %d;  number of states = %d.\n",cstate,ht.num_recs);
    }
    ht_ptr = hash_rec(&ht,cstate);
    cswa = ht_ptr[0];
    csdiff = ht_ptr[1];
    if (!dense_op)
      len = 0;
    e = 0; /* e is the number of the edge corresponding to the pair (g1,g2) */
    for (g1=1;g1<=ngens1;g1++) for (g2=1;g2<=ngens1;g2++) {
      e++;
/* Calculate action of generator-pair (g1,g2) on state cstate */
      if (g1==ngens1 && g2==ngens1)
        continue;
      if (g1==ngens1 || g2==ngens1)
        im=0; /* no end-of-string symbols accepted */
      else {
        ht_ptr = ht.current_ptr;
        ht_ptr[1] = dense_dtarget(difftable,g1,g2,csdiff);
        if (ht_ptr[1]==0)
          im=0;
        else {
          ht_ptr[0] = dense_target(watable,g2,cswa);
          if (ht_ptr[0]==0)
            im=0;
          else
            im = hash_locate(&ht,2);
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

  ns = geopairsptr->states->size = ht.num_recs;
  geopairsptr->table->numTransitions = nt;

  if (kbm_print_level>=3) {
    printf("    #Calculated transitions - %d states, %d transitions.\n",ns,nt);
    printf("    #Now calculating accept states.\n");
  }
  tmalloc(geopairsptr->is_accepting,boolean,ns+1);
  geopairsptr->num_accepting=0;
  for (i=1;i<=ns;i++) {
  /* The state is accepting iff its *diffptr component is accepting */
    ht_ptr = hash_rec(&ht,i);
    if (diffptr->is_accepting[ht_ptr[1]]) {
      geopairsptr->num_accepting++;
      geopairsptr->is_accepting[i] = TRUE;
    }   
    else
      geopairsptr->is_accepting[i] = FALSE;
  }
  tmalloc(geopairsptr->accepting,int,geopairsptr->num_accepting+1);
  ct=0;
  for (i=1;i<=ns;i++) if (geopairsptr->is_accepting[i])
    geopairsptr->accepting[++ct]=i;
  tfree(geopairsptr->is_accepting);
  tfree(diffptr->is_accepting);

  hash_clear(&ht);
  tfree(fsarow);
  if (readback) {
    tempfile = fopen(tempfilename,"r");
    compressed_transitions_read(geopairsptr,tempfile);
    fclose(tempfile);
    unlink(tempfilename);
  }
  if (destroy) {
    fsa_clear(waptr); fsa_clear(diffptr);
  }

  return geopairsptr;
}

int 
fsa_checkgeowa (fsa *geowaptr, fsa *diffptr, reduction_equation *eqnptr, int maxeqns)
/* *geowaptr is a candidate for the geodesic word-acceptor of a word-
 * hyperbolic group, and diffptr a word-difference machine for reducing
 * geodesic words to their shortlex normal form.
 * (In particular, all states of geowaptr should be accepting.)
 * Both are assumed to be stored in dense-format.
 * This routine checks the correctness of these fsa's by
 * constructing the fsa of which the states are triples (s1,s2,d),
 * with s1 and s2 states of *geowaptr and d a state of *diffptr, or s1=0.
 * The alphabet is 2-variable with base the alphabet of *geowaptr
 * (i.e. the same alphabet as *diffptr).
 * The alphabet member (g1,g2) maps (s1,s2,d) to (s1^g1,s2^g2,d^(g1,g2))
 * if the second and third components are nonzero, and to zero otherwise.
 * As with fsa_geopairs, the end-of string symbol is not allowed for g1,g2.
 * This fsa is not required itself, so its transition table is not stored.
 * Short hash-tables will be used, so this routine won't work if *geowaptr
 * or *diffptr has more than MAXUSHORT states.
 *
 * If, during the construction, a state (0,s2,1) (1=identity) is found,
 * then there is an equation w1=w2, with w1 and w2 both geodesics, and
 * w1 accepted by *geowaptr, but w2 not accepted. Thus *geowptr is
 * incorrect, and the word w1 is remembered in as eqnptr[i].lhs, for
 * i=0,1,...  
 * A maximum of maxeqns such left-hand-sides are returned as eqnptr[i].lhs
 * The function returns the number of equations found (so if it returns 0
 * the *geowaptr is proved correct).
 */
{
  if (kbm_print_level>=3)
    printf("    #Calling fsa_checkgeowa.\n");
  if (geowaptr->states->size<MAXUSHORT && diffptr->states->size<MAXUSHORT)
    return fsa_checkgeowa_short(geowaptr,diffptr,eqnptr,maxeqns);
  else
    return fsa_checkgeowa_int(geowaptr,diffptr,eqnptr,maxeqns);
}

int 
fsa_checkgeowa_short (fsa *geowaptr, fsa *diffptr, reduction_equation *eqnptr, int maxeqns)
{
  int **watable, ***difftable, identity, ngens, ngens1, ne, ns, len, im,
      cstate, cswa1, cswa2, csdiff, i, bstate, numeqns;
  unsigned short *ht_ptr;
  short_hash_table ht;
  gen g1, g2, bg1;
  int maxv = 65536;
  struct vertexd {
     gen g1;
     int  state;
  } *definition, *newdef; 
/* This is used to store the defining transition for the states.
 * If definition[i] = v, then state i is defined by the transition from
 * state v.state, with generator (v.g1,v.g2) -
 * but we don't need to rememeber g2.
 * State 1 does not have a definition.
 */

  if (!geowaptr->flags[DFA] || !diffptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_checkgeowa only applies to DFA's.\n");
    return -1;
  }
  if (geowaptr->alphabet->type!=IDENTIFIERS) {
    fprintf(stderr,"Error in fsa_checkgeowa: first fsa has wrong type.\n");
    return -1;
  }
  if (diffptr->alphabet->type!=PRODUCT || diffptr->alphabet->arity!=2) {
    fprintf(stderr,"Error in fsa_checkgeowa: second fsa must be 2-variable.\n");
    return -1;
  }
  if (diffptr->states->type!=WORDS) {
    fprintf(stderr,
       "Error in fsa_checkgeowa: second fsa must be word-difference type.\n");
    return -1;
  }
  if (!srec_equal(diffptr->alphabet->base,geowaptr->alphabet)) {
    fprintf(stderr,"Error in fsa_checkgeowa: fsa's alphabet's don't match.\n");
    return -1;
  }

  fsa_set_is_accepting(geowaptr);
  if (fsa_table_dptr_init(diffptr)==-1) return -1;

  tmalloc(definition, struct vertexd, maxv);
  ns=1;

  ngens = geowaptr->alphabet->size;
  ngens1 = ngens+1;
  ne = diffptr->alphabet->size;

  if (ne != ngens1*ngens1-1) {
   fprintf(stderr,
       "Error: in a 2-variable fsa, alphabet size should = ngens^2 - 1.\n");
    return -1;
  }

  watable = geowaptr->table->table_data_ptr;
  difftable = diffptr->table->table_data_dptr;

  short_hash_init(&ht,TRUE,3,0,0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = geowaptr->initial[1];
  ht_ptr[1] = geowaptr->initial[1];
  ht_ptr[2] =identity = diffptr->initial[1];
  im = short_hash_locate(&ht,3);
  if (im!=1) {
    fprintf(stderr,"Hash-initialisation problem in fsa_checkgeowa.\n");
    return -1;
  }
/* Just in case we are using the diff1 machine as *diffptr, we should
 * make sure that it accepts the diagonal.
 */
  for (g1=1;g1<=ngens;g1++)
     set_dense_dtarget(difftable,g1,g1,identity,identity);
  
 
  cstate = 0;

  numeqns = 0; /* this becomes nonzero when we have started collecting
                * equations of equal words both accepted by word-acceptor.
                */
  while (++cstate <= ht.num_recs) {
    if (kbm_print_level>=3) {
      if ((cstate<=1000 && cstate%100==0)||(cstate<=10000 && cstate%1000==0)||
          (cstate<=100000 && cstate%5000==0) || cstate%50000==0)
       printf("    #cstate = %d;  number of states = %d.\n",cstate,ht.num_recs);
    }
    ht_ptr = short_hash_rec(&ht,cstate);
    cswa1 = ht_ptr[0]; cswa2 = ht_ptr[1];
    csdiff = ht_ptr[2];
    for (g1=1;g1<=ngens1;g1++) for (g2=1;g2<=ngens1;g2++) {
/* Calculate action of generator-pair (g1,g2) on state cstate */
      if (g1==ngens1 || g2==ngens1)
        continue;
      ht_ptr = ht.current_ptr;
      ht_ptr[2] = dense_dtarget(difftable,g1,g2,csdiff);
      if (ht_ptr[2]==0)
        continue;
      ht_ptr[0] = cswa1==0 ? 0 : dense_target(watable,g1,cswa1);
      ht_ptr[1] = dense_target(watable,g2,cswa2);
      if (ht_ptr[1]==0)
        continue;
      if (!geowaptr->is_accepting[ht_ptr[0]] && ht_ptr[2]==identity) {
 /* This means that we have found a word that should be accepted by
  * *geowaptr but isn't. We remember is as eqnptr[numeqns].lhs
  */
        if (kbm_print_level>0 && numeqns==0)
          printf(
              "#Geodesic word found not accepted by *geowaptr.\n");
       /* First we calculate the length of the word */
        if (kbm_print_level>=3)
          printf("    #Calculating word number %d.\n",numeqns+1);
        len = 1;
        bg1 = g1;  bstate = cstate;
        while (bstate != 1) {
          len++;
          bg1 = definition[bstate].g1;
          bstate = definition[bstate].state;
        }
        /* Now we allocate space for it and store it - 
         */
        tmalloc(eqnptr[numeqns].lhs,gen,len+1);
        eqnptr[numeqns].lhs[len] = 0;
        bg1 = g1;  bstate = cstate;
        while (1) {
          eqnptr[numeqns].lhs[--len] = bg1;
          if (bstate==1)
            break;
          bg1 = definition[bstate].g1;
          bstate = definition[bstate].state;
        }
        numeqns++;
        if (numeqns>=maxeqns) { /* exit */
          if (kbm_print_level>=2 && maxeqns>0)
              printf("  #Found %d new words - aborting.\n",maxeqns);
          short_hash_clear(&ht);
          tfree(definition);
          return numeqns;
        }
        else eqnptr[numeqns].lhs = 0; /* to mark how many we have later */
      }
      im = short_hash_locate(&ht,3);
      if (im>ns) {
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
        definition[ns].g1 = g1;
        definition[ns].state = cstate;
      }
  
    }  /* for (g1=1;g1<=ngens1; ... */
  }  /*while (++cstate <= ht.num_recs) */
  if (kbm_print_level>=3)
    printf("    #Test machine has %d states.\n",ht.num_recs);

  short_hash_clear(&ht);
  tfree(definition);
  if (numeqns>0 && kbm_print_level>=2)
    printf("  #Found %d new words - aborting with algorithm complete.\n",
                  numeqns);
  return numeqns;
}

int 
fsa_checkgeowa_int (fsa *geowaptr, fsa *diffptr, reduction_equation *eqnptr, int maxeqns)
{
  int **watable, ***difftable, identity, ngens, ngens1, ne, ns, len, im,
      cstate, cswa1, cswa2, csdiff, i, bstate, numeqns;
  int *ht_ptr;
  hash_table ht;
  gen g1, g2, bg1;
  int maxv = 65536;
  struct vertexd {
     gen g1;
     int  state;
  } *definition, *newdef; 
/* This is used to store the defining transition for the states.
 * If definition[i] = v, then state i is defined by the transition from
 * state v.state, with generator (v.g1,v.g2) -
 * but we don't need to rememeber g2.
 * State 1 does not have a definition.
 */

  if (!geowaptr->flags[DFA] || !diffptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_checkgeowa only applies to DFA's.\n");
    return -1;
  }
  if (geowaptr->alphabet->type!=IDENTIFIERS) {
    fprintf(stderr,"Error in fsa_checkgeowa: first fsa has wrong type.\n");
    return -1;
  }
  if (diffptr->alphabet->type!=PRODUCT || diffptr->alphabet->arity!=2) {
    fprintf(stderr,"Error in fsa_checkgeowa: second fsa must be 2-variable.\n");
    return -1;
  }
  if (diffptr->states->type!=WORDS) {
    fprintf(stderr,
       "Error in fsa_checkgeowa: second fsa must be word-difference type.\n");
    return -1;
  }
  if (!srec_equal(diffptr->alphabet->base,geowaptr->alphabet)) {
    fprintf(stderr,"Error in fsa_checkgeowa: fsa's alphabet's don't match.\n");
    return -1;
  }

  fsa_set_is_accepting(geowaptr);
  if (fsa_table_dptr_init(diffptr)==-1) return -1;

  tmalloc(definition, struct vertexd, maxv);
  ns=1;

  ngens = geowaptr->alphabet->size;
  ngens1 = ngens+1;
  ne = diffptr->alphabet->size;

  if (ne != ngens1*ngens1-1) {
   fprintf(stderr,
       "Error: in a 2-variable fsa, alphabet size should = ngens^2 - 1.\n");
    return -1;
  }

  watable = geowaptr->table->table_data_ptr;
  difftable = diffptr->table->table_data_dptr;

  hash_init(&ht,TRUE,3,0,0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = geowaptr->initial[1];
  ht_ptr[1] = geowaptr->initial[1];
  ht_ptr[2] =identity = diffptr->initial[1];
  im = hash_locate(&ht,3);
  if (im!=1) {
    fprintf(stderr,"Hash-initialisation problem in fsa_checkgeowa.\n");
    return -1;
  }
/* Just in case we are using the diff1 machine as *diffptr, we should
 * make sure that it accepts the diagonal.
 */
  for (g1=1;g1<=ngens;g1++)
     set_dense_dtarget(difftable,g1,g1,identity,identity);
  
 
  cstate = 0;

  numeqns = 0; /* this becomes nonzero when we have started collecting
                * equations of equal words both accepted by word-acceptor.
                */
  while (++cstate <= ht.num_recs) {
    if (kbm_print_level>=3) {
      if ((cstate<=1000 && cstate%100==0)||(cstate<=10000 && cstate%1000==0)||
          (cstate<=100000 && cstate%5000==0) || cstate%50000==0)
       printf("    #cstate = %d;  number of states = %d.\n",cstate,ht.num_recs);
    }
    ht_ptr = hash_rec(&ht,cstate);
    cswa1 = ht_ptr[0]; cswa2 = ht_ptr[1];
    csdiff = ht_ptr[2];
    for (g1=1;g1<=ngens1;g1++) for (g2=1;g2<=ngens1;g2++) {
/* Calculate action of generator-pair (g1,g2) on state cstate */
      if (g1==ngens1 || g2==ngens1)
        continue;
      ht_ptr = ht.current_ptr;
      ht_ptr[2] = dense_dtarget(difftable,g1,g2,csdiff);
      if (ht_ptr[2]==0)
        continue;
      ht_ptr[0] = cswa1==0 ? 0 : dense_target(watable,g1,cswa1);
      ht_ptr[1] = dense_target(watable,g2,cswa2);
      if (ht_ptr[1]==0)
        continue;
      if (!geowaptr->is_accepting[ht_ptr[0]] && ht_ptr[2]==identity) {
 /* This means that we have found a word that should be accepted by
  * *geowaptr but isn't. We remember is as eqnptr[numeqns].lhs
  */
        if (kbm_print_level>0 && numeqns==0)
          printf(
              "#Geodesic word found not accepted by *geowaptr.\n");
       /* First we calculate the length of the word */
        if (kbm_print_level>=3)
          printf("    #Calculating word number %d.\n",numeqns+1);
        len = 1;
        bg1 = g1;  bstate = cstate;
        while (bstate != 1) {
          len++;
          bg1 = definition[bstate].g1;
          bstate = definition[bstate].state;
        }
        /* Now we allocate space for it and store it - 
         */
        tmalloc(eqnptr[numeqns].lhs,gen,len+1);
        eqnptr[numeqns].lhs[len] = 0;
        bg1 = g1;  bstate = cstate;
        while (1) {
          eqnptr[numeqns].lhs[--len] = bg1;
          if (bstate==1)
            break;
          bg1 = definition[bstate].g1;
          bstate = definition[bstate].state;
        }
        numeqns++;
        if (numeqns>=maxeqns) { /* exit */
          if (kbm_print_level>=2 && maxeqns>0)
              printf("  #Found %d new words - aborting.\n",maxeqns);
          hash_clear(&ht);
          tfree(definition);
          return numeqns;
        }
        else eqnptr[numeqns].lhs = 0; /* to mark how many we have later */
      }
      im = hash_locate(&ht,3);
      if (im>ns) {
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
        definition[ns].g1 = g1;
        definition[ns].state = cstate;
      }
  
    }  /* for (g1=1;g1<=ngens1; ... */
  }  /*while (++cstate <= ht.num_recs) */

  hash_clear(&ht);
  tfree(definition);
  if (numeqns>0 && kbm_print_level>=2)
    printf("  #Found %d new words - aborting with algorithm complete.\n",
                  numeqns);
  return numeqns;
}
