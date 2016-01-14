/* file fsaipmin.c - 12. 12. 94.
 * This file contains the routines fsa_ip_minimize and fsa_ip_labeled_minimize.
 * They are based on the minimization functions in fsa.c, but instead of
 * holding the whole of the transtion table of the fsa to be minimized in
 * store, they read it in from file with each iteration.
 * The reading part is as in "compressed_transitions_read".
 */

#include <stdlib.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "externals.h"

/* Functions defined in this file */
int fsa_ip_minimize();
int fsa_ip_labeled_minimize();

/* Functions used in this file and defined elsewhere */
void hash_init();
void hash_clear();
int *hash_rec();
int hash_rec_len();
int hash_locate();
void srec_clear();
void fsa_table_init();

int 
fsa_ip_minimize (fsa *fsaptr)
/* Minimize the fsa *fsaptr, of which transitions are stored externally */
{ int *block_numa, *block_numb, *block_swap, i, j, k, l, len,
       *ptr, *ptr2, *ptr2e, *ht_ptr,
       ne, ns_orig, *fsarow, **table, ns_final, ns_new, num_iterations;
  hash_table ht;
  boolean fixed;
  FILE *rfile, *fopen();

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
"Sorry: fsa_minimize unavailable for sparse storage with dense rows.\n");
    return -1;
  }

  if (kbm_print_level>=3)
    printf("    #Calling fsa_ip_minimize.\n");
  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_minimize only applies to DFA's.\n");
    return -1;
  }
  if (!fsaptr->flags[ACCESSIBLE]){
    fprintf(stderr,"Error: fsa in fsa_labeled_minimize must be accessible.\n");
    return -1;
  }

  ne = fsaptr->alphabet->size;
  ns_orig = fsaptr->states->size;
  if (ns_orig==0) {
    fsaptr->flags[TRIM] = TRUE;
    fsaptr->flags[MINIMIZED] = TRUE;
    return 0;
  }

  /* First throw away any existing structure on the state-set. */
  srec_clear(fsaptr->states);
  fsaptr->states->type = SIMPLE;

  tmalloc(block_numa,int,ns_orig+1); tmalloc(block_numb,int,ns_orig+1);
/* Start with block_numa equal to the accept/reject division
 * Remember that state/block number 0 is always failure with no hope.
 */
  if (fsaptr->num_accepting == ns_orig) {
    block_numa[0] = 0;
    for (i=1;i<=ns_orig;i++)
      block_numa[i] = 1;
  }
  else {
    for (i=0;i<=ns_orig;i++)
      block_numa[i] = 0;
    for (i=1;i<=fsaptr->num_accepting;i++)
      block_numa[fsaptr->accepting[i]] = 1;
  }

  fixed = fsaptr->table->table_type==DENSE;

  if (fixed)
    tmalloc(fsarow,int,ne+1)
  else
    tmalloc(fsarow,int,2*ne)

  ns_new = 1;
  num_iterations = 0;
/* The main refinement loop follows. */
  do {
    if ((rfile=fopen(fsaptr->table->filename,"r"))==0) {
      fprintf(stderr,"#Cannot open file %d.\n",fsaptr->table->filename);
      return -1;
    }
    num_iterations++;
    ns_final = ns_new;
/* Turn off excessive printing at this point */
    j=kbm_print_level; kbm_print_level=1;
    hash_init(&ht,fixed,ne+1,0,0);
    kbm_print_level=j;
    if (kbm_print_level>=3)
      printf("    #Iterating - number of state categories = %d.\n",ns_new);
    block_numb[0] = 0;
    for (i=1;i<=ns_orig;i++){
  /* Insert the encoded form of the transitions from state i into the hashtable
   * preceded by the current block number of i.
   */
      ptr = ht.current_ptr;
      *ptr = block_numa[i];
      if (fixed) {
        fread((void *)(fsarow+1),sizeof(int),(size_t)ne,rfile);
        for (j=1;j<=ne;j++)
          ptr[j] = block_numa[fsarow[j]];
        l = ne+1;
      }
      else {
        fread((void *)&len,sizeof(int),(size_t)1,rfile);
        if (len>0)
          fread((void *)fsarow,sizeof(int),(size_t)len,rfile);
        l = 0;
        for (j=1;j<len;j+=2) {
          k = block_numa[fsarow[j]];
          if (k > 0){
            ptr[++l] = fsarow[j-1];
            ptr[++l] = k;
          }
        }
        if (l>0 || *ptr>0)
          l++;
/* For technical reasons, we want the zero record to be empty */
      }
      block_numb[i] = hash_locate(&ht,l);
    }
    fclose(rfile);
    ns_new = ht.num_recs;
    block_swap=block_numa; block_numa=block_numb; block_numb=block_swap;
    if (ns_new > ns_final)
      hash_clear(&ht);
  } while (ns_new > ns_final);
  
  tfree(fsarow);

/* At this stage, either ns_final = ns_new, or the fsa has empty accepted
 * language, ns_new=0 and ns_final=1.
 */

  fsaptr->flags[TRIM] = TRUE;
  fsaptr->flags[MINIMIZED] = TRUE;

  if (ns_new==0) {
/* This is the awkward case of no states - always causes problems! */
    fsaptr->states->size=0;
    fsaptr->num_initial=0;
    tfree(fsaptr->initial);
    fsaptr->num_accepting = 0;
    tfree(fsaptr->accepting);
    unlink(fsaptr->table->filename);
    tfree(fsaptr->table->filename);
  }
  else {
/* Re-define the fsa fields  */
    fsaptr->states->size = ns_final;

    fsaptr->initial[1] = block_numa[fsaptr->initial[1]];

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
    unlink(fsaptr->table->filename);
    tfree(fsaptr->table->filename);
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
  if (kbm_print_level>=3)
    printf("    #Number of iterations = %d.\n",num_iterations);
  return 0;
}

int 
fsa_ip_labeled_minimize (fsa *fsaptr)
/* This is the minimization function for fsa's which misght have more than
 * two categories of states. 
 * We use the labeled set-record type to identify the categories, so *fsaptr
 * must have state-set of labeled type.
 * Minimize the fsa *fsaptr, of which transitions are stored externally.
 */
{ int *block_numa, *block_numb, *block_swap, i, j, k, l, len,
       *ptr, *ptr2, *ptr2e, *ht_ptr,
       ne, ns_orig, *fsarow, **table, ns_final, ns_new, num_iterations;
  hash_table ht;
  boolean fixed, *occurs;
  FILE *rfile, *fopen();

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
"Sorry: fsa_minimize unavailable for sparse storage with dense rows.\n");
    return -1;
  }
  if (kbm_print_level>=3)
    printf("    #Calling fsa_ip_labeled_minimize.\n");
  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_labeled_minimize only applies to DFA's.\n");
    return -1;
  }
  if (!fsaptr->flags[ACCESSIBLE]){
    fprintf(stderr,"Error: fsa in fsa_labeled_minimize must be accessible.\n");
    return -1;
  }

  if (fsaptr->states->type != LABELED) {
    fprintf(stderr,
        "Error: in fsa_labeled_minimize state=set must have type labeled.\n");
    return -1;
  }

  ne = fsaptr->alphabet->size;
  ns_orig = fsaptr->states->size;
  if (ns_orig==0)
    return 0;

/* Start with block_numa equal to the subdivision defined by the labeling.  */
  tmalloc(occurs,boolean,fsaptr->states->labels->size+1);
  for (i=1;i<=fsaptr->states->labels->size;i++)
    occurs[i] = FALSE;
  tmalloc(block_numa,int,ns_orig+1);
  tmalloc(block_numb,int,ns_orig+1);
  ns_new = 0;
  block_numa[0] = 0; /* The zero state is always regarded as having label 0 */
  for (i=1;i<=ns_orig;i++) {
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

  if (fixed)
    tmalloc(fsarow,int,ne+1)
  else
    tmalloc(fsarow,int,2*ne)

  num_iterations = 0;
/* The main refinement loop follows. */
  do {
    if ((rfile=fopen(fsaptr->table->filename,"r"))==0) {
      fprintf(stderr,"#Cannot open file %d.\n",fsaptr->table->filename);
      return -1;
    }
    num_iterations++;
    ns_final = ns_new;
/* Turn off excessive printing at this point */
    j=kbm_print_level; kbm_print_level=1;
    hash_init(&ht,fixed,ne+1,0,0);
    kbm_print_level=j;
    if (kbm_print_level>=3)
      printf("    #Iterating - number of state categories = %d.\n",ns_new);
    block_numb[0] = 0;
    for (i=1;i<=ns_orig;i++){
  /* Insert the encoded form of the transitions from state i into the hashtable
   * preceded by the current block number of i.
   * First read in the transitions for this row from the file.
   */
      ptr = ht.current_ptr;
      *ptr = block_numa[i];
      if (fixed) {
        fread((void *)(fsarow+1),sizeof(int),(size_t)ne,rfile);
        for (j=1;j<=ne;j++)
          ptr[j] = block_numa[fsarow[j]];
        l = ne+1;
      }
      else {
        fread((void *)&len,sizeof(int),(size_t)1,rfile);
        if (len>0)
          fread((void *)fsarow,sizeof(int),(size_t)len,rfile);
        l = 0;
        for (j=1;j<len;j+=2) {
          k = block_numa[fsarow[j]];
          if (k > 0){
            ptr[++l] = fsarow[j-1];
            ptr[++l] = k;
          }
        }
        if (l>0 || *ptr>0)
          l++;
/* For technical reasons, we want the zero record to be empty */
      }
      block_numb[i] = hash_locate(&ht,l);
    }
    fclose(rfile);
    ns_new = ht.num_recs;
    block_swap=block_numa; block_numa=block_numb; block_numb=block_swap;
    if (ns_new > ns_final)
      hash_clear(&ht);
  } while (ns_new > ns_final);
  
  tfree(fsarow);

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
    unlink(fsaptr->table->filename);
    tfree(fsaptr->table->filename);
  }
  else {
/* Re-define the fsa fields  */
    fsaptr->states->size = ns_final;

    fsaptr->initial[1] = block_numa[fsaptr->initial[1]];

    for (i=1;i<=ns_orig;i++)
      block_numb[block_numa[i]] = fsaptr->states->setToLabels[i];
    for (i=1;i<=ns_final;i++)
      fsaptr->states->setToLabels[i] = block_numb[i];

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
    unlink(fsaptr->table->filename);
    tfree(fsaptr->table->filename);
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
  if (kbm_print_level>=3)
    printf("    #Number of iterations = %d.\n",num_iterations);
  return 0;
}
