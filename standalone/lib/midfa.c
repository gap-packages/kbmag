/* file midfa.c  4.8.95.
 *
 * 2/3/99 Bug fix in midfa_labeled_minimize();
 * Must have at least two iterations of main loop.
 * 
 * This file contains routines for processing fsa's which are non-deterministic,
 * in that they have more than one start-state, but have a deterministic
 * transition table. They are called "midfa" and have the flag "MIDFA" set.
 * They occur naturally in coset automatic group programs
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "externals.h"

/* Functions defined in this file: */
fsa *midfa_determinize();
fsa *midfa_determinize_short();
fsa *midfa_determinize_int();
int  midfa_minimize();
int  midfa_labeled_minimize();

/* Functions used in this file and defined elsewhere */
int sparse_target();
void fsa_init();
void fsa_table_init();
void fsa_set_is_initial();
void fsa_set_is_accepting();
void fsa_set_is_accessible();
void srec_copy();
void fsa_copy();
void fsa_clear();
void srec_clear();
void compressed_transitions_read();
void hash_init();
void short_hash_init();
int  hash_locate();
int  short_hash_locate();
void hash_clear();
void short_hash_clear();
int* hash_rec();
unsigned short* short_hash_rec();
int hash_rec_len();
int short_hash_rec_len();

fsa *
midfa_determinize(fsaptr,op_table_type,destroy,tempfilename)
	fsa *fsaptr;
	storage_type op_table_type;
	boolean destroy;
	char *tempfilename;
/* The fsa *fsaptr must be a midfa.
 * The returned fsa accepts the same language but is deterministic.
 */
{
  if (kbm_print_level>=3)
    printf("    #Calling midfa_determinize.\n");
  if (fsaptr->states->size < MAXUSHORT)
    return midfa_determinize_short(fsaptr,op_table_type,destroy,tempfilename);
  else
    return midfa_determinize_int(fsaptr,op_table_type,destroy,tempfilename);
}

fsa *
midfa_determinize_short(fsaptr,op_table_type,destroy,tempfilename)
	fsa *fsaptr;
	storage_type op_table_type;
	boolean destroy;
	char *tempfilename;
{
  int **table, ngens, nssi,  ns, dr, *fsarow,
      nt, cstate, csi, im, i, g1, len, ct;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre,
                 *cs_ptr, *cs_ptre, *ptr;
  boolean dense_ip, dense_op;
  short_hash_table ht;
  fsa *det;
  FILE *tempfile, *fopen();

  if (kbm_print_level>=3)
    printf("    #Calling midfa_determinize_short.\n");
  if (!fsaptr->flags[MIDFA]){
    fprintf(stderr,"Error: midfa_determinize only applies to MIDFA's.\n");
    return 0;
  }

  if (fsaptr->num_initial<=1) {
/* Deterministic already, so simply copy and return */
  	tmalloc(det,fsa,1);
	fsa_copy(det,fsaptr);
	det->flags[MIDFA]=FALSE;
	det->flags[DFA]=TRUE;
	return det;
  }

  tmalloc(det,fsa,1);
  fsa_init(det);
  srec_copy(det->alphabet,fsaptr->alphabet);
  det->flags[DFA] = TRUE;
  det->flags[ACCESSIBLE] = TRUE;
  det->flags[BFS] = TRUE;

  det->states->type = SIMPLE;

  det->table->table_type = op_table_type;
  det->table->denserows = 0;
  det->table->printing_format = op_table_type;

  if (fsaptr->num_initial==0) {
    det->num_initial = 0;
    det->num_accepting = 0;
    det->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return det;
  }
  ngens = det->alphabet->size;

  fsa_set_is_accepting(fsaptr);

  dense_ip = fsaptr->table->table_type==DENSE;
  dr = fsaptr->table->denserows;
  dense_op = op_table_type==DENSE;
  table = fsaptr->table->table_data_ptr;

  det->num_initial = 1;
  tmalloc(det->initial,int,2);
  det->initial[1] = 1;
  
  short_hash_init(&ht,FALSE,0,0,0);
  ht_ptr = ht.current_ptr;
  nssi = fsaptr->num_initial;
  for (i=0;i<nssi;i++)
    ht_ptr[i] = fsaptr->initial[i+1];
  im = short_hash_locate(&ht,i);
/* Each state in 'det' will be represented as a subset of the set of states
 * of *fsaptr. The initial state contains the initial states
 * of *fsaptr.
 * A subset is an accept-state if it contains an accept state of *fsaptr
 * The subsets will be stored as variable-length records in the hash-table,
 * always in increasing order.
 */
  if (im!=1) {
    fprintf(stderr,"Hash-initialisation problem in midfa_determinize.\n");
    return 0;
  }
  if ((tempfile=fopen(tempfilename,"w"))==0){
    fprintf(stderr,"Error: cannot open file %s\n",tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow,int,ngens)
  else
    tmalloc(fsarow,int,2*ngens+1)
 
  cstate = 0;
  if (dense_op)
    len = ngens; /* The length of the fsarow output. */
  nt = 0; /* Number of transitions in det */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level>=3) {
      if ((cstate<=1000 && cstate%100==0)||(cstate<=10000 && cstate%1000==0)||
          (cstate<=100000 && cstate%5000==0) || cstate%50000==0)
       printf("    #cstate = %d;  number of states = %d.\n",cstate,ht.num_recs);
    }
    cs_ptr = short_hash_rec(&ht,cstate);
    cs_ptre = short_hash_rec(&ht,cstate) + short_hash_rec_len(&ht,cstate) - 1;
    if (!dense_op)
      len = 0;

    for (g1=1;g1<=ngens;g1++) {
/* Calculate action of generator g1 on state cstate  - to get the image, we
 * simply apply it to each state in the subset of states representing cstate.
 */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb-1;
      ptr = cs_ptr-1;
      while (++ptr <= cs_ptre) {
        csi = target(dense_ip,table,g1,*ptr,dr);
        if (csi==0)
          continue;
        if (ht_ptrb>ht_ptre || csi> *ht_ptre) {
/* We have a new state for the image subset to be added to the end */
          *(++ht_ptre) = csi;
        }
        else {
          ht_chptr = ht_ptrb;
          while (*ht_chptr < csi)
            ht_chptr++;
          if (csi < *ht_chptr) {
/* we have a new state for the image subset to be added in the middle */
            ht_ptr = ++ht_ptre;
            while (ht_ptr > ht_chptr) {
              *ht_ptr = *(ht_ptr-1);
              ht_ptr--;
            }
            *ht_ptr = csi;
          }
        }
      }
      im = short_hash_locate(&ht,ht_ptre-ht_ptrb+1);
      if (dense_op)
         fsarow[g1-1] = im;
      else if (im>0) {
         fsarow[++len] = g1;
         fsarow[++len] = im;
      }
      if (im>0)
        nt++;
    }
    if (!dense_op)
      fsarow[0] = len++;
    fwrite((void *)fsarow,sizeof(int),(size_t)len,tempfile);
  }
  fclose(tempfile);

  ns = det->states->size = ht.num_recs;
  det->table->numTransitions = nt;

/* Locate the accept states. A state is an accept state if and only if
 * the subset representing it contains an accept state of *fsaptr.
 */
  tmalloc(det->is_accepting,boolean,ns+1);
  for (i=1;i<=ns;i++)
    det->is_accepting[i] = FALSE;
  ct = 0;
  for (cstate=1;cstate<=ns;cstate++) {
    cs_ptr = short_hash_rec(&ht,cstate);
    cs_ptre = short_hash_rec(&ht,cstate) + short_hash_rec_len(&ht,cstate) - 1;
/* See if the set contains an accept-state */
    ptr = cs_ptr-1;
    while (++ptr <= cs_ptre) if (fsaptr->is_accepting[*ptr]) {
      det->is_accepting[cstate] = TRUE;
      ct++;
      break;
    }
  }

  det->num_accepting = ct;
  if (ct==1 || ct != ns) {
    tmalloc(det->accepting,int,ct+1);
    ct = 0;
    for (i=1;i<=ns;i++) if (det->is_accepting[i])
      det->accepting[++ct] = i;
  }
  tfree(fsaptr->is_accepting);
  tfree(det->is_accepting);
  short_hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

/* Now read the transition table back in */
  tempfile = fopen(tempfilename,"r");
  compressed_transitions_read(det,tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return det;
}

fsa *
midfa_determinize_int(fsaptr,op_table_type,destroy,tempfilename)
	fsa *fsaptr;
	storage_type op_table_type;
	boolean destroy;
	char *tempfilename;
{
  int **table, ngens, nssi, ns, dr, *fsarow,
      nt, cstate, csi, im, i, g1, len, ct;
  int *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre, *ptr;
  boolean dense_ip, dense_op;
  hash_table ht;
  fsa *det;
  FILE *tempfile, *fopen();

  if (kbm_print_level>=3)
    printf("    #Calling midfa_determinize_int.\n");
  if (!fsaptr->flags[MIDFA]){
    fprintf(stderr,"Error: midfa_determinize only applies to MIDFA's.\n");
    return 0;
  }

  if (fsaptr->num_initial<=1) {
/* Deterministic already, so simply copy and return */
  	tmalloc(det,fsa,1);
	fsa_copy(det,fsaptr);
	det->flags[MIDFA]=FALSE;
	det->flags[DFA]=TRUE;
	return det;
  }

  tmalloc(det,fsa,1);
  fsa_init(det);
  srec_copy(det->alphabet,fsaptr->alphabet);
  det->flags[DFA] = TRUE;
  det->flags[ACCESSIBLE] = TRUE;
  det->flags[BFS] = TRUE;

  det->states->type = SIMPLE;

  det->table->table_type = op_table_type;
  det->table->denserows = 0;
  det->table->printing_format = op_table_type;

  if (fsaptr->num_initial==0) {
    det->num_initial = 0;
    det->num_accepting = 0;
    det->states->size = 0;
    if (destroy)
      fsa_clear(fsaptr);
    return det;
  }
  ngens = det->alphabet->size;

  fsa_set_is_accepting(fsaptr);

  dense_ip = fsaptr->table->table_type==DENSE;
  dr = fsaptr->table->denserows;
  dense_op = op_table_type==DENSE;
  table = fsaptr->table->table_data_ptr;

  det->num_initial = 1;
  tmalloc(det->initial,int,2);
  det->initial[1] = 1;
  
  hash_init(&ht,FALSE,0,0,0);
  ht_ptr = ht.current_ptr;
  nssi = fsaptr->num_initial;
  for (i=0;i<nssi;i++)
    ht_ptr[i] = fsaptr->initial[i+1];
  im = hash_locate(&ht,i);
/* Each state in 'det' will be represented as a subset of the set of states
 * of *fsaptr. The initial state contains the initial states
 * of *fsaptr.
 * A subset is an accept-state if it contains an accept state of *fsaptr
 * The subsets will be stored as variable-length records in the hash-table,
 * always in increasing order.
 */
  if (im!=1) {
    fprintf(stderr,"Hash-initialisation problem in midfa_determinize.\n");
    return 0;
  }
  if ((tempfile=fopen(tempfilename,"w"))==0){
    fprintf(stderr,"Error: cannot open file %s\n",tempfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow,int,ngens)
  else
    tmalloc(fsarow,int,2*ngens+1)
 
  cstate = 0;
  if (dense_op)
    len = ngens; /* The length of the fsarow output. */
  nt = 0; /* Number of transitions in det */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level>=3) {
      if ((cstate<=1000 && cstate%100==0)||(cstate<=10000 && cstate%1000==0)||
          (cstate<=100000 && cstate%5000==0) || cstate%50000==0)
       printf("    #cstate = %d;  number of states = %d.\n",cstate,ht.num_recs);
    }
    cs_ptr = hash_rec(&ht,cstate);
    cs_ptre = hash_rec(&ht,cstate) + hash_rec_len(&ht,cstate) - 1;
    if (!dense_op)
      len = 0;

    for (g1=1;g1<=ngens;g1++) {
/* Calculate action of generator g1 on state cstate  - to get the image, we
 * simply apply it to each state in the subset of states representing cstate.
 */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb-1;
      ptr = cs_ptr-1;
      while (++ptr <= cs_ptre) {
        csi = target(dense_ip,table,g1,*ptr,dr);
        if (csi==0)
          continue;
        if (ht_ptrb>ht_ptre || csi> *ht_ptre) {
/* We have a new state for the image subset to be added to the end */
          *(++ht_ptre) = csi;
        }
        else {
          ht_chptr = ht_ptrb;
          while (*ht_chptr < csi)
            ht_chptr++;
          if (csi < *ht_chptr) {
/* we have a new state for the image subset to be added in the middle */
            ht_ptr = ++ht_ptre;
            while (ht_ptr > ht_chptr) {
              *ht_ptr = *(ht_ptr-1);
              ht_ptr--;
            }
            *ht_ptr = csi;
          }
        }
      }
      im = hash_locate(&ht,ht_ptre-ht_ptrb+1);
      if (dense_op)
         fsarow[g1-1] = im;
      else if (im>0) {
         fsarow[++len] = g1;
         fsarow[++len] = im;
      }
      if (im>0)
        nt++;
    }
    if (!dense_op)
      fsarow[0] = len++;
    fwrite((void *)fsarow,sizeof(int),(size_t)len,tempfile);
  }
  fclose(tempfile);

  ns = det->states->size = ht.num_recs;
  det->table->numTransitions = nt;

/* Locate the accept states. A state is an accept state if and only if
 * the subset representing it contains an accept state of *fsaptr.
 */
  tmalloc(det->is_accepting,boolean,ns+1);
  for (i=1;i<=ns;i++)
    det->is_accepting[i] = FALSE;
  ct = 0;
  for (cstate=1;cstate<=ns;cstate++) {
    cs_ptr = hash_rec(&ht,cstate);
    cs_ptre = hash_rec(&ht,cstate) + hash_rec_len(&ht,cstate) - 1;
/* See if the set contains an accept-state */
    ptr = cs_ptr-1;
    while (++ptr <= cs_ptre) if (fsaptr->is_accepting[*ptr]) {
      det->is_accepting[cstate] = TRUE;
      ct++;
      break;
    }
  }

  det->num_accepting = ct;
  if (ct==1 || ct != ns) {
    tmalloc(det->accepting,int,ct+1);
    ct = 0;
    for (i=1;i<=ns;i++) if (det->is_accepting[i])
      det->accepting[++ct] = i;
  }
  tfree(fsaptr->is_accepting);
  tfree(det->is_accepting);
  hash_clear(&ht);
  tfree(fsarow);

  if (destroy)
    fsa_clear(fsaptr);

/* Now read the transition table back in */
  tempfile = fopen(tempfilename,"r");
  compressed_transitions_read(det,tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return det;
}

int 
midfa_minimize (fsa *fsaptr)
/* This is the function for midfa's which might have more than
 * two categories of states. 
 */
{ int *block_numa, *block_numb, *block_swap, ct, ss, sst, *gotlist, i, j, k, l,
       len, *ptr, *ptre, *ptr2, *ptr2e, *ht_ptr,
       ne, ns_orig, **table, ns_final, ns_new, num_iterations;
  hash_table ht;
  boolean fixed, *got, ok, acc;

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
"Sorry: midfa_minimize unavailable for sparse storage with dense rows.\n");
    return -1;
  }
  if (kbm_print_level>=3)
    printf("    #Calling midfa_minimize.\n");
  if (!fsaptr->flags[MIDFA]){
    fprintf(stderr,"Error: midfa_minimize only applies to MIDFA's.\n");
    return -1;
  }
  if (fsaptr->flags[MINIMIZED])
    return 0;

  acc = fsaptr->flags[ACCESSIBLE]  || fsaptr->flags[TRIM];

  ne = fsaptr->alphabet->size;
  table = fsaptr->table->table_data_ptr;
  ns_orig = fsaptr->states->size;
  if (ns_orig==0) {
    fsaptr->flags[TRIM] = TRUE;
    fsaptr->flags[MINIMIZED] = TRUE;
    return 0;
  }


/* Throw away any existing structure on the state-set. */
  srec_clear(fsaptr->states);
  fsaptr->states->type = SIMPLE;

/* We now test to see which start-states can lead to success.
 * Those that cannot will cease to be start-states.
 */
  fsa_set_is_accepting(fsaptr);
  fsa_set_is_initial(fsaptr);

  tmalloc(gotlist,int,ns_orig+1);
  tmalloc(got,boolean,ns_orig+1);
  for (ss=1;ss<=fsaptr->num_initial;ss++) {
    sst = fsaptr->initial[ss];
    if (fsaptr->is_accepting[sst])
      continue;
    ok = FALSE;
    for (i=1;i<=ns_orig;i++)
      got[i] = FALSE;
    got[sst] = TRUE;
    gotlist[1] = sst;
    ct = 1;
    for (i=1;i<=ct;i++) {
      k = gotlist[i];
      if (fsaptr->table->table_type == DENSE)
        for (j=1;j<=ne;j++){
          l = table[j][k];
          if (l>0 && !got[l]) {
            if (fsaptr->is_accepting[l]) {
              ok = TRUE;
              break;
            }
            got[l]=TRUE; gotlist[++ct]=l;
          }
        }
      else {
        ptr=table[k]; ptre=table[k+1];
        while (ptr<ptre) {
          l = *(++ptr);
          if (l>0 && !got[l]) {
            if (fsaptr->is_accepting[l]) {
              ok = TRUE;
              break;
            }
            got[l]=TRUE; gotlist[++ct]=l;
          }
          ptr++;
        }
      }
    }
    if (!ok) {
      fsaptr->is_initial[sst] = FALSE;
      acc = FALSE;
    }
  }
  tfree(gotlist);
  tfree(got);
  ct = 0;
  for (i=1;i<=ns_orig;i++) if (fsaptr->is_initial[i])
    ct++;
  if (ct!=fsaptr->num_initial) {
    fsaptr->num_initial = ct;
    tfree(fsaptr->initial);
    tmalloc(fsaptr->initial,int,ct+1);
    ct=0;
    for (i=1;i<=ns_orig;i++) if (fsaptr->is_initial[i])
      fsaptr->initial[++ct] = i;
  }
  tfree(fsaptr->is_initial);
  tfree(fsaptr->is_accepting);
  if (!acc)
    fsa_set_is_accessible(fsaptr);

  tmalloc(block_numa,int,ns_orig+1); tmalloc(block_numb,int,ns_orig+1);
  for (i=0;i<=ns_orig;i++)
    block_numb[i]=0;
/* Start with block_numa equal to the accept/reject division
 * Remember that state/block number 0 is always failure with no hope.
 */
  if (fsaptr->num_accepting == ns_orig) {
    block_numa[0]=0;
    for (i=1;i<=ns_orig;i++) if (acc || fsaptr->is_accessible[i])
      block_numa[i] = 1;
    else
      block_numa[i] = 0;
  }
  else {
    for (i=0;i<=ns_orig;i++)
      block_numa[i] = 0;
    for (i=1;i<=fsaptr->num_accepting;i++)
      if (acc || fsaptr->is_accessible[fsaptr->accepting[i]])
        block_numa[fsaptr->accepting[i]] = 1;
  }

  fixed = fsaptr->table->table_type==DENSE;

  ns_new=1;
  num_iterations = 0;
/* The main refinement loop follows. */
  do {
    num_iterations++;
    ns_final = ns_new;
/* Turn off excessive printing at this point */
    j=kbm_print_level; kbm_print_level=1;
    hash_init(&ht,fixed,ne+1,0,0);
    kbm_print_level=j;
    if (kbm_print_level>=3)
      printf("    #Iterating - number of state categories = %d.\n",ns_new);
    block_numb[0] = 0;
    for (i=1;i<=ns_orig;i++) if (acc || fsaptr->is_accessible[i]){
  /* Insert the encoded form of the transitions from state i into the hashtable
   * preceded by the current block number of i.
   */
      len = fixed ? ne+1 : table[i+1]-table[i]+1;
      ptr = ht.current_ptr;
      *ptr = block_numa[i];
      if (fixed) {
        for (j=1;j<len;j++)
          ptr[j] = block_numa[table[j][i]];
        l = len;
      }
      else {
        l = 0;
        for (j=1;j<len;j+=2) {
          k = block_numa[table[i][j]];
          if (k > 0){
            ptr[++l] = table[i][j-1];
            ptr[++l] = k;
          }
        }
        if (l>0 || *ptr>0)
          l++;
/* For technical reasons, we want the zero record to be empty */
      }
      block_numb[i] = hash_locate(&ht,l);
    }
    else block_numb[i]=0;
    ns_new = ht.num_recs;
    block_swap=block_numa; block_numa=block_numb; block_numb=block_swap;
    if (ns_new > ns_final)
      hash_clear(&ht);
  } while (ns_new > ns_final);
  
/* At this stage, either ns_final = ns_new, or the fsa has empty accepted
 * language, ns_new=0 and ns_final=1.
 */
  
  fsaptr->flags[ACCESSIBLE] = TRUE;
  fsaptr->flags[MINIMIZED] = TRUE;

  if (ns_new==0) {
/* This is the awkward case of no states - always causes problems! */
    fsaptr->states->size=0;
    fsaptr->num_initial=0;
    tfree(fsaptr->initial);
    fsaptr->num_accepting = 0;
    tfree(fsaptr->accepting);
    tfree(fsaptr->table->table_data_ptr[0]);
    tfree(fsaptr->table->table_data_ptr);
  }
  else if (ns_final<ns_orig){
/* Re-define the fsa fields  */
    fsaptr->states->size = ns_final;

   if (fsaptr->num_initial == ns_orig) {
      fsaptr->num_initial = ns_final;
      if (ns_final==1) {
        tmalloc(fsaptr->initial,int,2);
        fsaptr->initial[1] = 1;
      }
    }
    else {
      tmalloc(fsaptr->is_initial,boolean,ns_final+1);
      for (i=1;i<=ns_final;i++)
        fsaptr->is_initial[i] = FALSE;
      for (i=1;i<=fsaptr->num_initial;i++)
        fsaptr->is_initial[block_numa[fsaptr->initial[i]]] = TRUE;
      fsaptr->num_initial = 0;
      for (i=1;i<=ns_final;i++) if (fsaptr->is_initial[i])
        fsaptr->num_initial++;
      tfree(fsaptr->initial);
      tmalloc(fsaptr->initial,int,fsaptr->num_initial+1);
      j = 0;
      for (i=1;i<=ns_final;i++) if (fsaptr->is_initial[i])
        fsaptr->initial[++j] = i;
      tfree(fsaptr->is_initial);
    }

    if (fsaptr->num_accepting == ns_orig) {
      fsaptr->num_accepting = ns_final;
      if (ns_final==1) {
        tmalloc(fsaptr->accepting,int,2);
        fsaptr->accepting[1] = 1;
      }
    }
    else {
      tmalloc(fsaptr->is_accepting,boolean,ns_final+1);
      for (i=1;i<=ns_final;i++)
        fsaptr->is_accepting[i] = FALSE;
      for (i=1;i<=fsaptr->num_accepting;i++)
        fsaptr->is_accepting[block_numa[fsaptr->accepting[i]]] = TRUE;
      fsaptr->num_accepting = 0;
      for (i=1;i<=ns_final;i++) if (fsaptr->is_accepting[i])
        fsaptr->num_accepting++;
      tfree(fsaptr->accepting);
      tmalloc(fsaptr->accepting,int,fsaptr->num_accepting+1);
      j = 0;
      for (i=1;i<=ns_final;i++) if (fsaptr->is_accepting[i])
        fsaptr->accepting[++j] = i;
      tfree(fsaptr->is_accepting);
    }

/* Finally copy the transition table data from the hash-table back to the fsa */
    tfree(fsaptr->table->table_data_ptr[0]);
    tfree(fsaptr->table->table_data_ptr);
    if (fixed){
      fsa_table_init(fsaptr->table,ns_final,ne);
      table = fsaptr->table->table_data_ptr;
      for (i=1;i<=ns_final;i++) {
        ht_ptr = hash_rec(&ht,i);
        for (j=1;j<=ne;j++)
          table[j][i] = ht_ptr[j];
      }
    }
    else{
      tmalloc(fsaptr->table->table_data_ptr,int *,ns_final+2);
      tmalloc(fsaptr->table->table_data_ptr[0],int,ht.tot_space-ns_final);
      table = fsaptr->table->table_data_ptr;
      table[1] = ptr = table[0];
      for (i=1;i<=ns_final;i++){
        ht_ptr = hash_rec(&ht,i);
        ptr2 = ht_ptr+1;
        ptr2e = ht_ptr + hash_rec_len(&ht,i) - 1;
        while (ptr2 <= ptr2e)
          *(ptr++) = *(ptr2++);
        table[i+1] = ptr;
      }
    }
  }
  hash_clear(&ht);
  tfree(block_numa);
  tfree(block_numb);
  tfree(fsaptr->is_accessible);
  if (kbm_print_level>=3)
    printf("    #Number of iterations = %d.\n",num_iterations);
  return 0;
}

int 
midfa_labeled_minimize (fsa *fsaptr)
/* This is the minimization function for midfa's which might have more than
 * two categories of states. 
 * We use the labeled set-record type to identify the categories, so *fsaptr
 * must have state-set of labeled type.
 * In the "midfa" case, fsaptr->accepting is used to distinguish the
 * labeled accept-states from the labeled start-states.
 */
{ int *block_numa, *block_numb, *block_swap, ct, ss, sst, *gotlist, i, j, k, l,
       len, *ptr, *ptre, *ptr2, *ptr2e, *ht_ptr,
       ne, ns_orig, **table, ns_final, ns_new, num_iterations;
  hash_table ht;
  boolean fixed, *occurs, *got, ok, acc;

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
"Sorry: midfa_labeled_minimize unavailable for sparse storage with dense rows.\n");
    return -1;
  }
  if (kbm_print_level>=3)
    printf("    #Calling midfa_labeled_minimize.\n");
  if (!fsaptr->flags[MIDFA]){
    fprintf(stderr,"Error: midfa_labeled_minimize only applies to MIDFA's.\n");
    return -1;
  }

  if (fsaptr->states->type != LABELED) {
    fprintf(stderr,
        "Error: in midfa_labeled_minimize state-set must have type labeled.\n");
    return -1;
  }

  acc = fsaptr->flags[ACCESSIBLE]  || fsaptr->flags[TRIM];

  ne = fsaptr->alphabet->size;
  table = fsaptr->table->table_data_ptr;
  ns_orig = fsaptr->states->size;
  if (ns_orig==0)
    return 0;

/* We now test to see which start-states can lead to success.
 * Those that cannot will cease to be start-states.
 */
  fsa_set_is_accepting(fsaptr);
  fsa_set_is_initial(fsaptr);

  tmalloc(gotlist,int,ns_orig+1);
  tmalloc(got,boolean,ns_orig+1);
  for (ss=1;ss<=fsaptr->num_initial;ss++) {
    sst = fsaptr->initial[ss];
    if (fsaptr->is_accepting[sst])
      continue;
    ok = FALSE;
    for (i=1;i<=ns_orig;i++)
      got[i] = FALSE;
    got[sst] = TRUE;
    gotlist[1] = sst;
    ct = 1;
    for (i=1;i<=ct;i++) {
      k = gotlist[i];
      if (fsaptr->table->table_type == DENSE)
        for (j=1;j<=ne;j++){
          l = table[j][k];
          if (l>0 && !got[l]) {
            if (fsaptr->is_accepting[l]) {
              ok = TRUE;
              break;
            }
            got[l]=TRUE; gotlist[++ct]=l;
          }
        }
      else {
        ptr=table[k]; ptre=table[k+1];
        while (ptr<ptre) {
          l = *(++ptr);
          if (l>0 && !got[l]) {
            if (fsaptr->is_accepting[l]) {
              ok = TRUE;
              break;
            }
            got[l]=TRUE; gotlist[++ct]=l;
          }
          ptr++;
        }
      }
    }
    if (!ok) {
      fsaptr->is_initial[sst] = FALSE;
      acc = FALSE;
    }
  }
  tfree(gotlist);
  tfree(got);
  ct = 0;
  for (i=1;i<=ns_orig;i++) if (fsaptr->is_initial[i])
    ct++;
  if (ct!=fsaptr->num_initial) {
    fsaptr->num_initial = ct;
    tfree(fsaptr->initial);
    tmalloc(fsaptr->initial,int,ct+1);
    ct=0;
    for (i=1;i<=ns_orig;i++) if (fsaptr->is_initial[i])
      fsaptr->initial[++ct] = i;
  }
  tfree(fsaptr->is_initial);
  tfree(fsaptr->is_accepting);
  if (!acc)
    fsa_set_is_accessible(fsaptr);

/* Start with block_numa equal to the subdivision defined by the labeling.  */
  tmalloc(occurs,boolean,fsaptr->states->labels->size+1);
  for (i=1;i<=fsaptr->states->labels->size;i++)
    occurs[i] = FALSE;
  tmalloc(block_numa,int,ns_orig+1);
  tmalloc(block_numb,int,ns_orig+1);
  ns_new = 0;
  block_numa[0] = 0; /* The zero state is always regarded as having label 0 */
  for (i=1;i<=ns_orig;i++) if (acc || fsaptr->is_accessible[i]) {
    j = fsaptr->states->setToLabels[i];
    if (j>0 && !occurs[j]) {
      occurs[j] = TRUE;
      ns_new++;
    }
    block_numa[i] = j;
  }
  tfree(occurs);
  if (ns_new==0) ns_new=1; /* a patch for the case when there are no labels */

  fixed = fsaptr->table->table_type==DENSE;

  num_iterations = 0;
/* The main refinement loop follows. */
  do {
    num_iterations++;
    ns_final = ns_new;
/* Turn off excessive printing at this point */
    j=kbm_print_level; kbm_print_level=1;
    hash_init(&ht,fixed,ne+1,0,0);
    kbm_print_level=j;
    if (kbm_print_level>=3)
      printf("    #Iterating - number of state categories = %d.\n",ns_new);
    block_numb[0] = 0;
    for (i=1;i<=ns_orig;i++) if (acc || fsaptr->is_accessible[i]){
  /* Insert the encoded form of the transitions from state i into the hashtable
   * preceded by the current block number of i.
   */
      len = fixed ? ne+1 : table[i+1]-table[i]+1;
      ptr = ht.current_ptr;
      *ptr = block_numa[i];
      if (fixed) {
        for (j=1;j<len;j++)
          ptr[j] = block_numa[table[j][i]];
        l = len;
      }
      else {
        l = 0;
        for (j=1;j<len;j+=2) {
          k = block_numa[table[i][j]];
          if (k > 0){
            ptr[++l] = table[i][j-1];
            ptr[++l] = k;
          }
        }
        if (l>0 || *ptr>0)
          l++;
/* For technical reasons, we want the zero record to be empty */
      }
      block_numb[i] = hash_locate(&ht,l);
    }
    else block_numb[i]=0;
    ns_new = ht.num_recs;
    block_swap=block_numa; block_numa=block_numb; block_numb=block_swap;
    if (ns_new>ns_final || num_iterations==1)
      hash_clear(&ht);
  } while (ns_new>ns_final || num_iterations==1);
/* We must have at least two iterations, because the first time through
 * we have the lables rather than the states in the transition table.
 */
  
/* At this stage, either ns_final = ns_new, or the fsa has empty accepted
 * language, ns_new=0 and ns_final=1.
 */
  
  fsaptr->flags[ACCESSIBLE] = TRUE;

  if (ns_new==0) {
/* This is the awkward case of no states - always causes problems! */
    fsaptr->states->size=0;
    fsaptr->num_initial=0;
    tfree(fsaptr->initial);
    fsaptr->num_accepting = 0;
    tfree(fsaptr->accepting);
    tfree(fsaptr->table->table_data_ptr[0]);
    tfree(fsaptr->table->table_data_ptr);
  }
  else if (ns_final<ns_orig){
/* Re-define the fsa fields  */
    fsaptr->states->size = ns_final;

    for (i=1;i<=ns_orig;i++)
      block_numb[block_numa[i]] = fsaptr->states->setToLabels[i];
    for (i=1;i<=ns_final;i++)
      fsaptr->states->setToLabels[i] = block_numb[i];

   if (fsaptr->num_initial == ns_orig) {
      fsaptr->num_initial = ns_final;
      if (ns_final==1) {
        tmalloc(fsaptr->initial,int,2);
        fsaptr->initial[1] = 1;
      }
    }
    else {
      tmalloc(fsaptr->is_initial,boolean,ns_final+1);
      for (i=1;i<=ns_final;i++)
        fsaptr->is_initial[i] = FALSE;
      for (i=1;i<=fsaptr->num_initial;i++)
        fsaptr->is_initial[block_numa[fsaptr->initial[i]]] = TRUE;
      fsaptr->num_initial = 0;
      for (i=1;i<=ns_final;i++) if (fsaptr->is_initial[i])
        fsaptr->num_initial++;
      tfree(fsaptr->initial);
      tmalloc(fsaptr->initial,int,fsaptr->num_initial+1);
      j = 0;
      for (i=1;i<=ns_final;i++) if (fsaptr->is_initial[i])
        fsaptr->initial[++j] = i;
      tfree(fsaptr->is_initial);
    }

    if (fsaptr->num_accepting == ns_orig) {
      fsaptr->num_accepting = ns_final;
      if (ns_final==1) {
        tmalloc(fsaptr->accepting,int,2);
        fsaptr->accepting[1] = 1;
      }
    }
    else {
      tmalloc(fsaptr->is_accepting,boolean,ns_final+1);
      for (i=1;i<=ns_final;i++)
        fsaptr->is_accepting[i] = FALSE;
      for (i=1;i<=fsaptr->num_accepting;i++)
        fsaptr->is_accepting[block_numa[fsaptr->accepting[i]]] = TRUE;
      fsaptr->num_accepting = 0;
      for (i=1;i<=ns_final;i++) if (fsaptr->is_accepting[i])
        fsaptr->num_accepting++;
      tfree(fsaptr->accepting);
      tmalloc(fsaptr->accepting,int,fsaptr->num_accepting+1);
      j = 0;
      for (i=1;i<=ns_final;i++) if (fsaptr->is_accepting[i])
        fsaptr->accepting[++j] = i;
      tfree(fsaptr->is_accepting);
    }

/* Finally copy the transition table data from the hash-table back to the fsa */
    tfree(fsaptr->table->table_data_ptr[0]);
    tfree(fsaptr->table->table_data_ptr);
    if (fixed){
      fsa_table_init(fsaptr->table,ns_final,ne);
      table = fsaptr->table->table_data_ptr;
      for (i=1;i<=ns_final;i++) {
        ht_ptr = hash_rec(&ht,i);
        for (j=1;j<=ne;j++)
          table[j][i] = ht_ptr[j];
      }
    }
    else{
      tmalloc(fsaptr->table->table_data_ptr,int *,ns_final+2);
      tmalloc(fsaptr->table->table_data_ptr[0],int,ht.tot_space-ns_final);
      table = fsaptr->table->table_data_ptr;
      table[1] = ptr = table[0];
      for (i=1;i<=ns_final;i++){
        ht_ptr = hash_rec(&ht,i);
        ptr2 = ht_ptr+1;
        ptr2e = ht_ptr + hash_rec_len(&ht,i) - 1;
        while (ptr2 <= ptr2e)
          *(ptr++) = *(ptr2++);
        table[i+1] = ptr;
      }
    }
  }
  hash_clear(&ht);
  tfree(block_numa);
  tfree(block_numb);
  tfree(fsaptr->is_accessible);
  if (kbm_print_level>=3)
    printf("    #Number of iterations = %d.\n",num_iterations);
  return 0;
}
