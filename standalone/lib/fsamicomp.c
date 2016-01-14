/* file fsamicomp.c  12. 10. 95.
 * 29/9/98 large-scale re-organisation.
 * 13/1/98 changes for `gen' type for generators instead of char.
 * 8.3.97. Small bug (on NeXT) corrected
 * 10.1.96. Added function fsa_mimult2().
 * 31.10.95. Added function fsa_migm2().
 * This file contains the routines for forming the composite multiplier
 * fsa's for coset automatic group with multiple initial states.
 * These are used to derive defining relators for the subgroup.
 */


#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "externals.h"

#define LABHTSIZE 8192

/* Functions defined in this file: */
int  mimult_minimize();
fsa  *fsa_migm2();
fsa  *fsa_migm2_short();
fsa  *fsa_migm2_int();
int  fsa_mimakemult();
int  fsa_mimakemult2();
fsa  *fsa_micomposite();
fsa  *fsa_micomposite_short();
fsa  *fsa_micomposite_int();

/* Functions used in this file and defined elsewhere */
void fsa_table_init();
void fsa_set_is_initial();
void fsa_set_is_accepting();
void fsa_set_is_accessible();
void fsa_init();
void fsa_clear();
void srec_clear();
boolean srec_equal();
void compressed_transitions_read();
void srec_copy();
int sparse_target();
void hash_init();
void short_hash_init();
int  hash_locate();
int  short_hash_locate();
int* hash_rec();
unsigned short* short_hash_rec();
void hash_clear();
void short_hash_clear();
int hash_rec_len();
int int_len();
int stringlen();
int genstrlen();
void genstrcpy();
void genstrcat();

int 
mimult_minimize (fsa *fsaptr)
/* This is the minimization function for composite multipliers
 * for coset automatic groups.
 * These are multiple initial state machines, and the states should be
 * labeled, with the initial states having separate labels.
 * The labels will be lists of words, containing a single word initially.
 * During minimization those initial states which cannot lead to success
 * cease to be initial. If some of the other initial states become
 * amalgamated, then their labels (which represent equal elements in
 * the subgroup) will be concatenated.
 */
{ int *block_numa, *block_numb, *block_swap, ct, ss, sst, *gotlist,
       i, j, k, l, m, len, *ptr, *ptre, *ptr2, *ptr2e, *ht_ptr, ni,
       ne, ns_orig, **table, ns_final, ns_new, num_iterations, nlab, *lablen;
  hash_table ht;
  boolean fixed,  *got, ok, acc;
  gen ***newlabels, ***oldlabels;
  setToLabelsType *labno;

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
  "Sorry: mimult_minimize unavailable for sparse storage with dense rows.\n");
    return -1;
  }
  if (kbm_print_level>=3)
    printf("    #Calling mimult_minimize.\n");
  if (!fsaptr->flags[MIDFA]){
    fprintf(stderr,"Error: mimult_minimize only applies to MIDFA's.\n");
    return -1;
  }

  if (fsaptr->states->type != LABELED) {
    fprintf(stderr,
        "Error: in mimult_minimize state-set must have type labeled.\n");
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

  tmalloc(block_numa,int,ns_orig+1);
  tmalloc(block_numb,int,ns_orig+1);
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

  ns_new = 1;

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

   /* sort out the initial states and their labels -
    * first calculate how many labels there are and how long they are
    */
    ni = fsaptr->num_initial;
    tmalloc(lablen,int,ni+1);
    for (i=1;i<=ni;i++)
      lablen[i]=0;
    tmalloc(labno,setToLabelsType,ns_new+1);
    for (i=1;i<=ns_new;i++)
      labno[i]=0;
    nlab=0;
    for (i=1;i<=ni;i++) {
      k=block_numa[fsaptr->initial[i]];
      if (labno[k]==0)
        labno[k] = ++nlab;
      lablen[labno[k]]++;
    }
    tmalloc(newlabels,gen**,nlab+1);
    oldlabels=fsaptr->states->labels->wordslist;
    for (i=1;i<=nlab;i++)
      tmalloc(newlabels[i],gen*,lablen[i]+1);
    for (i=1;i<=nlab;i++)
      lablen[i]=0;
    for (i=1;i<=ni;i++) {
      j=fsaptr->initial[i];
      k=block_numa[j];
      l=labno[k];
      m=fsaptr->states->setToLabels[j];
      tmalloc(newlabels[l][lablen[l]],gen,genstrlen(oldlabels[m][0])+1);
      genstrcpy(newlabels[l][lablen[l]],oldlabels[m][0]);
      lablen[l]++;
    }
    for (i=1;i<=nlab;i++)
      newlabels[i][lablen[i]]=0;
    for (i=1;i<=fsaptr->states->labels->size;i++) {
      j=0;
      while (oldlabels[i][j]) {
        tfree(oldlabels[i][j]); j++;
      }
      tfree(oldlabels[i]);
    }
    tfree(oldlabels);
    fsaptr->states->labels->wordslist=newlabels;
    fsaptr->states->labels->size=nlab;
    tfree(fsaptr->states->setToLabels);
    fsaptr->states->setToLabels=labno;
    fsaptr->num_initial=nlab;
    tfree(fsaptr->initial);
    tfree(lablen);
    tmalloc(fsaptr->initial,int,nlab+1);
    ct=0;
    for (i=1;i<=ns_new;i++) if (labno[i])
      fsaptr->initial[++ct]=i;

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

fsa *
fsa_migm2(migmptr,op_table_type,destroy,migm2filename,readback,prefix)
        fsa *migmptr;
        storage_type op_table_type;
        boolean destroy;
        char *migm2filename;
        boolean readback;
	char *prefix;
/* *migmptr should be the general mi-multiplier fsa of a
 * cose automatic group.
 * This function calculates the transition table of the general mi-multiplier
 * for products of two generators. This is output (in unformatted form) to the
 * file with name migm2filename, followed by a list of states, which
 * specifies which states are accept-states for which length-two words.
 * It can then be minimised for any such word as required.
 * NOTE - in the mi version readback must be true for the time being.
 * prefix is a string which is used as a prefix for the names of the new
 * generators, on which the subgroup will be presented.
 * They will be called 'prefix'1, 'prefix'2,...
 * (as in fsa_mimakemult).
 */
{
  if (kbm_print_level>=3)
    printf("    #Calling fsa_migm2.\n");
  if (migmptr->states->size < MAXUSHORT)
    return
      fsa_migm2_short(migmptr,op_table_type,
                           destroy,migm2filename,readback,prefix);
  else
    return fsa_migm2_int(migmptr,op_table_type,
                           destroy,migm2filename,readback,prefix);
}

fsa *
fsa_migm2_short(migmptr,op_table_type,destroy,migm2filename,readback,prefix)
        fsa *migmptr;
        storage_type op_table_type;
        boolean destroy;
        char *migm2filename;
        boolean readback;
	char *prefix;
{
  int **table, ne, ngens, ngens1, ns, *fsarow,
      e, e1, e2, es1, ef1, dr, nt, cstate, im, csa, csb, csima, csimb, j1, j2,
      i, j, ct, g1, g2, g3, len, len1, reclen, ninit_ip, ninit_op, pl, nlabs;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre,
                 *cs_ptr, *cs_ptre, *ptr;
  boolean dense_ip, dense_op, got, leftpad, rightpad;
  setToLabelsType *label_ip, *label_op, l1, l2;
  gen **labellist1, **labellist2;
  short_hash_table ht, labelht;
  fsa *migm2ptr;
  srec *labs_op, *labs_ip;
  FILE *tempfile, *fopen();

  if (kbm_print_level>=3)
    printf("    #Calling fsa_migm2_short.\n");
  if (!migmptr->flags[MIDFA]){
    fprintf(stderr,"Error: fsa_migm2 only applies to MIDFA's.\n");
    return 0;
  }

  if (migmptr->alphabet->type!=PRODUCT || migmptr->alphabet->arity!=2) {
    fprintf(stderr,"Error in fsa_migm2: fsa must be 2-variable.\n");
    return 0;
  }

  if (migmptr->states->type!=LABELED) {
    fprintf(stderr,"Error in fsa_migm2: states must be labeled.\n");
    return 0;
  }

  tmalloc(migm2ptr,fsa,1);
  fsa_init(migm2ptr);
  srec_copy(migm2ptr->alphabet,migmptr->alphabet);

  migm2ptr->flags[MIDFA] = TRUE;
  migm2ptr->flags[ACCESSIBLE] = TRUE;

  migm2ptr->table->table_type = op_table_type;
  migm2ptr->table->denserows = 0;
  migm2ptr->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(migm2ptr->table->filename,char,stringlen(migm2filename)+1);
    strcpy(migm2ptr->table->filename,migm2filename);
  }

  ne = migmptr->alphabet->size;
  ngens = migmptr->alphabet->base->size;
  ngens1 = ngens+1;

  if (ne != ngens1*ngens1-1) {
   fprintf(stderr,
     "Error: in a 2-variable fsa, alphabet size should = (ngens+1)^2 - 1.\n");
    return 0;
  }

  fsa_set_is_accepting(migmptr);

  dense_ip = migmptr->table->table_type==DENSE;
  dr = migmptr->table->denserows;
  dense_op = op_table_type==DENSE;
  table = migmptr->table->table_data_ptr;

  short_hash_init(&ht,FALSE,0,0,0);
/* The initial states of *migm2ptr will be pairs (s1,s2), where s1 and s2 are
 * initial states migmptr.
 * Their labels will be in terms of the new subgroup generator 'prefix'i to
 * be introduced.
 * However, their labels may also contain words in the G-generators of length
 * 2 (which occur in the accepting states of *migmptr2), so we will not deal
 * with the labels until later.
 */
  ninit_ip=migmptr->num_initial;
  ninit_op=ninit_ip*ninit_ip;
  migm2ptr->num_initial = ninit_op;
  tmalloc(migm2ptr->initial,int,ninit_op+1);
  for (i=1;i<=ninit_op;i++)
    migm2ptr->initial[i]=i;

  ct=0;
  for (i=1;i<=ninit_ip;i++) for (j=1;j<=ninit_ip;j++) {
    ct++;
    
/* Each state in the composite transition table will be represented as a subset
 * of the set of ordered pairs in which the components are  states of
 * *migmptr.
 * The initial states contain just one such pair, of which the components are
 * the initial states of *migmptr.
 * The subsets will be stored as variable-length records in the hash-table,
 * as a list of pairs in increasing order.
 * If a state is reached from a transition ($,x) or (x,$) (with $ the padding
 * symbol), then it needs to be marked as such, since we do not allow a $
 * to be followed by any other generator.
 * We do this by adding a 1 or a 2 to the end of the statelist - this is
 * recognisable by the fact that the length of the statelist then becomes odd.
 */
    ht_ptr = ht.current_ptr;
    ht_ptr[0] = migmptr->initial[i];
    ht_ptr[1] = migmptr->initial[j];
    im = short_hash_locate(&ht,2);
    if (im!=ct) {
      fprintf(stderr,"Hash-initialisation problem in fsa_migm2.\n");
      return 0;
    }
  }

  if ((tempfile=fopen(migm2filename,"w"))==0){
    fprintf(stderr,"Error: cannot open file %s\n",migm2filename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow,int,ne)
  else
    tmalloc(fsarow,int,2*ne+1)
 
  cstate = 0;
  if (dense_op)
    len = ne; /* The length of the fsarow output. */
  nt = 0; /* Number of transitions in migm2ptr */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level>=3) {
      if ((cstate<=1000 && cstate%100==0)||(cstate<=10000 && cstate%1000==0)||
          (cstate<=100000 && cstate%5000==0) || cstate%50000==0)
       printf("    #cstate = %d;  number of states = %d.\n",cstate,ht.num_recs);
    }
    reclen = short_hash_rec_len(&ht,cstate);
    cs_ptr = short_hash_rec(&ht,cstate);
    cs_ptre = short_hash_rec(&ht,cstate) + reclen - 1;
    /* for (i=0;i<reclen;i++) printf(" %d",cs_ptr[i]); printf("\n"); */
    if (reclen % 2 == 1) {
      if (*cs_ptre==1) {
        leftpad=TRUE;  rightpad=FALSE;
      } else {
        leftpad=FALSE;  rightpad=TRUE;
      }
      cs_ptre--;
    }
    else {
      leftpad=FALSE; rightpad=FALSE;
    }
      
    if (dense_op)
      for (i=0;i<ne;i++) fsarow[i] = 0;
    else
      len = 0;

    e = 0; /* e is the edge number of generator pair (g1,g3) */
    for (g1=1;g1<=ngens1;g1++)  for (g3=1;g3<=ngens1;g3++) {
/* Calculate action of pair (g1,g3) on state cstate  - to get the image, we
 * have to apply ( (g1,g2), (g2,g3) ) to each ordered pair in the subset
 * corresponding to cstate, * and this for each generator g2 of the
 * base-alphabet (including the padding symbol).
 */
      e++;
      if (g1==ngens1 && g3==ngens1)
        continue;
      if ((leftpad && g1<=ngens) || (rightpad && g3<=ngens))
        continue;
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb-1;
      es1 = (g1-1)*ngens1 + 1;
      ef1 = g1*ngens1;
/* As g2 ranges from 1 to ngens+1 in the pair (g1,g2), for fixed g1, the
 * corresponding edge number in the fsa ranges from es1 to ef1.
 *
 * As g2 ranges from 1 to ngens+1 in the pair (g2,g3), for fixed g3, the
 * corresponding edge number in the fsa ranges from g3 upwards, with
 * increments of size ngens+1.
 */

      ptr = cs_ptr;
      while (ptr <= cs_ptre) {
        csa = *(ptr++); csb = *(ptr++);
        for (g2=1,e1=es1,e2=g3; e1<=ef1; g2++,e1++,e2+=ngens1){
          csima = g1==ngens1 && g2==ngens1 ?
                   (migmptr->is_accepting[csa] ? csa : 0) :
                   target(dense_ip,table,e1,csa,dr);
          if (csima==0)
            continue;

          csimb = g2==ngens1 && g3==ngens1 ?
                   (migmptr->is_accepting[csb] ? csb : 0) :
                   target(dense_ip,table,e2,csb,dr);
          if (csimb==0)
            continue;

          if (ht_ptrb>ht_ptre || csima> *(ht_ptre-1) ||
                               (csima== *(ht_ptre-1) &&  csimb > *ht_ptre) ){
/* We have a new state for the image subset to be added to the end */
            *(++ht_ptre) = csima; *(++ht_ptre) = csimb;
          }
          else {
            ht_chptr = ht_ptrb;
            while (*ht_chptr < csima)
              ht_chptr+=2;
            while (*ht_chptr==csima && *(ht_chptr+1)<csimb)
                ht_chptr+=2;
            if (csima < *ht_chptr || csimb < *(ht_chptr+1)) {
/* we have a new state for the image subset to be added in the middle */
              ht_ptr = ht_ptre;
              ht_ptre += 2;
              while (ht_ptr >= ht_chptr) {
                *(ht_ptr+2) = *ht_ptr;
                ht_ptr--;
              }
              *ht_chptr = csima; *(ht_chptr+1) = csimb;
            }
          }
        }
      }
      if (ht_ptre > ht_ptrb) {
        if (g1==ngens1)
          *(++ht_ptre) = 1;
        else if (g3==ngens1)
          *(++ht_ptre) = 2;
      }
      im = short_hash_locate(&ht,ht_ptre-ht_ptrb+1);
      if (im > 0) {
        if (dense_op)
          fsarow[e-1] = im;
        else  {
          fsarow[++len] = e;
          fsarow[++len] = im;
        }
        nt++;
      }
    }
    if (!dense_op)
      fsarow[0] = len++;
    fwrite((void *)fsarow,sizeof(int),(size_t)len,tempfile);
  }
  fclose(tempfile);

  ns = migm2ptr->states->size = ht.num_recs;
  migm2ptr->table->numTransitions = nt;

  if (kbm_print_level>=3)
    printf("    #Calculated transitions - %d states, %d transitions.\n",ns,nt);

/* Locate the accept states Mult_(a*b) for each generator pair (a,b).
 * This is slightly cumbersome, since a states
 * is an accept state if either the  subset representing S contains a
 * pair (s1,s2), where s1 is accept state for Mult_a and s2 for Mult_b,
 * or we can get from to such a state by applying ( ($,g), (g,$) ) to one
 * of the pairs in S, for some generator g.
 * It is most convenient to work out this information taking the states
 * S in reverse order.
 * The information on the accept-states will be stored as labels, which
 * will be lists of words in the generators. Each such list will contain 
 * a1*b1,a2*b2,...,ar*br, where the (ai,bi) are the generator pairs for
 * which that particular state is an accept state.
 * The identity generator will be numbered ngens+1 and given name '_'
 * rather than represented by the empty word. This is so that we can
 * distinguish between multipliers for "_*a" and "a*_" if necessary.
 * HOWEVER, the lists for the initial states will also contain a term
 * 'prefix'i*'prefix'j (a product of two of the new subgroup generators).
 * The label of the first initial state of *migmptr is always the empty
 * word - so the label of initial state i+1 of *migmptr for i>0 will be
 * correspond to the new generator 'prefix'i.
 * The labels will be collected initially in a new hash-table.
 */

  labs_ip=migmptr->states->labels;
  if (labs_ip->alphabet_size != ngens) {
    fprintf(stderr,"Error in fsa_migm2: state label set has wrong size!\n");
    return 0;
  }

  migm2ptr->states->type = LABELED;
  tmalloc(migm2ptr->states->labels,srec,1);
  labs_op = migm2ptr->states->labels;
  labs_op->type=LISTOFWORDS;
/* The alphabet for the labels for *migm2ptr will contain the old
 * generators (1 to ngens), the empty word  ngens = ('_') and the new
 * subgroup generators (ngens+2 to ngens+ninit_ip), with names
 * 'prefix'1 to 'prefix'(ninit_ip-1).
 */
  labs_op->alphabet_size = ngens+ninit_ip;
  for (i=1;i<=ngens;i++) {
    tmalloc(labs_op->alphabet[i],char,stringlen(labs_ip->alphabet[i])+1);
    strcpy(labs_op->alphabet[i],labs_ip->alphabet[i]);
  }
  tmalloc(labs_op->alphabet[ngens1],char,2);
  strcpy(labs_op->alphabet[ngens1],"_");
  if (labs_ip->wordslist[migmptr->initial[1]][0][0]!=0) {
    fprintf(stderr,
            "Error in fsa_migm2 - first initial state not empty word.\n");
    return 0;
  }
  pl=stringlen(prefix);
  for (i=2;i<=ninit_ip;i++) {
    tmalloc(labs_op->alphabet[ngens+i],char,pl+int_len(i-1)+1);
    sprintf(labs_op->alphabet[ngens+i],"%s%d",prefix,i-1);
  }

  label_ip = migmptr->states->setToLabels;
  tmalloc(migm2ptr->states->setToLabels,setToLabelsType,ns+1);
  label_op = migm2ptr->states->setToLabels;
  tmalloc(migm2ptr->is_accepting,boolean,ns+1);
  for (i=1;i<=ns;i++)
    migm2ptr->is_accepting[i] = FALSE;
  short_hash_init(&labelht,FALSE,0,LABHTSIZE,2*LABHTSIZE);

  es1 = ngens*ngens1 + 1;
  ef1 = ngens1*ngens1-1;
  for (cstate=ns;cstate>=1;cstate--) {
/* We work backwards through the states, since we wish to add on additional
 * elements at the end of the list in the hash-table - this destroys
 * later entries, but that doesn't matter, since we have already dealt
 * with them.
 */
    cs_ptr = short_hash_rec(&ht,cstate);
    reclen = short_hash_rec_len(&ht,cstate);
    if (reclen % 2 ==1)
      reclen--; /* The last entry marks the fact that this is a "padded state"*/
    cs_ptre = short_hash_rec(&ht,cstate) + reclen - 1;
/* Apply generators ( ($,g2), (g2,$) ) and see if we get anything new.
 * We won't bother about having them in increasing order this time.
 */
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++); csb = *(ptr++);
      for (e1=es1,e2=ngens1; e1<=ef1; e1++,e2+=ngens1){
        csima = target(dense_ip,table,e1,csa,dr);
        if (csima==0)
          continue;
        csimb = target(dense_ip,table,e2,csb,dr);
        if (csimb==0)
          continue;

  /* See if (csima,csimb) is new */
        ht_chptr = cs_ptr;
        got = FALSE;
        while (ht_chptr < cs_ptre) {
          if (csima == ht_chptr[0] && csimb == ht_chptr[1]) {
            got = TRUE;
            break;
          }
          ht_chptr+=2;
        }
        if (!got) {
  /* add (csima,csimb) to the end */
          *(++cs_ptre) = csima; *(++cs_ptre) = csimb;
        }
      }
    }

  /* Now we see which pairs in the subset are of form (s,t), where s is
   * an accept state for a generator a, and t for a generator b.
   * The list of all such pairs (a,b) will form the label of the state, which
   * will be start with the list of words [a1*b1,a2*b2,..,ar*br], with the
   * (ai,bi) coming in lex-order.
   */

    ht_ptrb = labelht.current_ptr;
    ht_ptre = ht_ptrb-1;
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++); csb = *(ptr++);
      if (((l1=label_ip[csa]) != 0) && ((l2=label_ip[csb]) != 0)) {
        labellist1 = migmptr->states->labels->wordslist[l1];
        labellist2 = migmptr->states->labels->wordslist[l2];
        j1=0;
        while (labellist1[j1]) {
          if (genstrlen(labellist1[j1])>1) {
            j1++;
            continue;
          }
          g1 = labellist1[j1][0];
          if (g1==0) g1=ngens1;
          j2=0;
          while (labellist2[j2]) {
            if (genstrlen(labellist2[j2])>1) {
              j2++;
              continue;
            }
            migm2ptr->is_accepting[cstate]=TRUE;
            g2 = labellist2[j2][0];
            if (g2==0) g2=ngens1;
            if (ht_ptrb>ht_ptre || g1> *(ht_ptre-1) ||
                                 (g1== *(ht_ptre-1) &&  g2 > *ht_ptre) ){
    /* We have a new generator pair to be added to the end */
              *(++ht_ptre) = g1; *(++ht_ptre) = g2;
            }
            else {
              ht_chptr = ht_ptrb;
              while (*ht_chptr < g1)
                ht_chptr+=2;
              while (*ht_chptr==g1 && *(ht_chptr+1)<g2)
                  ht_chptr+=2;
              if (g1 < *ht_chptr || g2 < *(ht_chptr+1)) {
    /* we have a new generator pair to be added in the middle */
                ht_ptr = ht_ptre;
                ht_ptre += 2;
                while (ht_ptr >= ht_chptr) {
                  *(ht_ptr+2) = *ht_ptr;
                  ht_ptr--;
                }
                *ht_chptr = g1; *(ht_chptr+1) = g2;
              }
            }
            j2++;
          }
          j1++;
        }
      }
    }

    if (cstate<=ninit_op && cstate>1) {
/* cstate is an initial state.
 * We have an extra term to add to the label-list, for the product of
 * the two new subgroup generators
 */
      g1 = (cstate-1)/ninit_ip;
      g2 = (cstate-1)%ninit_ip;
      if (g1==0)
        *(++ht_ptre) = ngens1+g2;
      else if (g2==0)
        *(++ht_ptre) = ngens1+g1;
      else {
        *(++ht_ptre) = ngens1+g1; *(++ht_ptre) = ngens1+g2;
      }
    }
/* That completes the calculation of the label for cstate */
    label_op[cstate] = short_hash_locate(&labelht,ht_ptre-ht_ptrb+1);
  }
  short_hash_clear(&ht);

  ct=0;
  for (i=1;i<=ns;i++) if (migm2ptr->is_accepting[i])
    ct++;
  migm2ptr->num_accepting = ct;
  if (ct==1 || ct != ns) {
    tmalloc(migm2ptr->accepting,int,ct+1);
    ct = 0;
    for (i=1;i<=ns;i++) if (migm2ptr->is_accepting[i])
      migm2ptr->accepting[++ct] = i;
  }
  tfree(migm2ptr->is_accepting);
  tfree(migmptr->is_accepting);
  tfree(fsarow);
  if (destroy)
    fsa_clear(migmptr);

/* Finally copy the records from the label hash-table into the set of labels */
  nlabs =
  labs_op->size = labelht.num_recs;
  if (kbm_print_level>=3)
    printf("    #There are %d distinct labels.\n",nlabs);
  tmalloc(labs_op->wordslist,gen **,nlabs+1);
  for (i=1;i<=nlabs;i++) {
    len = short_hash_rec_len(&labelht,i)/2;
    len1 = (short_hash_rec_len(&labelht,i)+1)/2;
    tmalloc(labs_op->wordslist[i],gen *,len1+1);
    ht_ptr = short_hash_rec(&labelht,i);
    for (j=0;j<len;j++) {
      tmalloc(labs_op->wordslist[i][j],gen,3);
      labs_op->wordslist[i][j][0] = ht_ptr[2*j];
      labs_op->wordslist[i][j][1] = ht_ptr[2*j+1];
      labs_op->wordslist[i][j][2] = 0;
    }
    if (len<len1) {
      tmalloc(labs_op->wordslist[i][len],gen,2);
      labs_op->wordslist[i][j][0] = ht_ptr[2*len];
      labs_op->wordslist[i][j][1] = 0;
    }
    labs_op->wordslist[i][len1] = 0;
  }
  short_hash_clear(&labelht);

  if (readback) {
    tempfile = fopen(migm2filename,"r");
    compressed_transitions_read(migm2ptr,tempfile);
    fclose(tempfile);
    unlink(migm2filename);
  }

  return migm2ptr;
}

fsa *
fsa_migm2_int(migmptr,op_table_type,destroy,migm2filename,readback,prefix)
        fsa *migmptr;
        storage_type op_table_type;
        boolean destroy;
        char *migm2filename;
        boolean readback;
	char *prefix;
{
  fprintf(stderr,
	"Sorry - fsa_migm2 is not yet implemented for machines.\n");
  fprintf(stderr,"with more than 65536 states.\n");
  return 0;
}

int 
fsa_mimakemult (fsa *migmptr, int g, char *prefix)
/* This procedure takes the fsa *migmptr produced by fsa_mitriples, 
 * and builds a particular multiple-initial state multiplier Mult_gi.
 * This merely involves setting the accept states of *genmimultptr
 * in accordance with the labels of its states.
 * The labels for the initial states (which will become the subgroup
 * generators) are renamed prefix'1', prefix'2', ..., where prefix is
 * the string argument supplied.
 * g can be 0, for the identity generator, which (in shortlex case) inevitably
 * produces the diagonal of the word-acceptor.
 * This procedure alters its arguments and does not return anything.
 */
{
  int ngens, ns, ni, i, j, ct, pl;
  gen ** labellist;
  setToLabelsType *labno;
  srec *labs;

  if (kbm_print_level>=3)
    printf("    #Calling fsa_mimakemult with generator number %d.\n",g);
  if (!migmptr->flags[MIDFA]){
    fprintf(stderr,"Error: fsa_mimakemult only applies to MIDFA's.\n");
    return -1;
  }

  if (migmptr->alphabet->type!=PRODUCT || migmptr->alphabet->arity!=2) {
    fprintf(stderr,"Error in fsa_mimakemult: fsa must be 2-variable.\n");
    return -1;
  }

  if (migmptr->states->type!=LABELED) {
    fprintf(stderr,"Error in fsa_mimakemult: states of fsa must be labeled.\n");
    return -1;
  }

  ns = migmptr->states->size;
  ngens = migmptr->alphabet->base->size;
  if (g<0 || g>ngens+1) {
    fprintf(stderr,"#Error in fsa_mimakemult: Generator is out of range.\n");
    return -1;
  }
  
  tfree(migmptr->accepting);
  labno = migmptr->states->setToLabels;
  labs = migmptr->states->labels;
  ct = 0;
  for (i=1;i<=ns;i++) if (labno[i]>0) {
    labellist = labs->wordslist[labno[i]];
    j=0;
    while (labellist[j]) {
      if (labellist[j][0]==g && (g==0 || labellist[j][1]==0))
        ct++;
      j++;
    }
  }
  migmptr->num_accepting = ct;
  if (ct<ns || ns==1) { 
    tmalloc(migmptr->accepting,int,ct+1);
    ct = 0;
    for (i=1;i<=ns;i++)if (labno[i]>0) {
      labellist = labs->wordslist[labno[i]];
      j=0;
      while (labellist[j]) {
        if (labellist[j][0]==g && (g==0 || labellist[j][1]==0))
          migmptr->accepting[++ct] = i;
        j++;
      }
    }
  }
/* Finally we relabel the states - only the initial states will now have labels
 * First check that the first initial state has label the empty word -
 * otherwise something has gone badly wrong!
 */
  if (labs->wordslist[migmptr->initial[1]][0][0]!=0) {
    fprintf(stderr,
            "Error in fsa_mimakemult - first initial state not empty word.\n");
    return -1;
  }
  srec_clear(labs);
  ni = migmptr->num_initial;
  labs->size = ni;
  labs->alphabet_size=ni-1;
  tmalloc(labs->wordslist,gen**,ni+1);
  pl=stringlen(prefix);
  for (i=1;i<=ns;i++)
    labno[i]=0;
  
/* The first initial state has label the empty word */
  tmalloc(labs->wordslist[1],gen *,2);
  tmalloc(labs->wordslist[1][0],gen,1);
  labs->wordslist[1][0][0]=0;
  labs->wordslist[1][1]=0;
  labno[migmptr->initial[1]]=1;
  for (i=2;i<=ni;i++) {
    tmalloc(labs->wordslist[i],gen *,2);
    tmalloc(labs->wordslist[i][0],gen,2);
    tmalloc(labs->alphabet[i-1],char,pl+int_len(i-1)+1);
    labs->wordslist[i][0][0]=i-1; labs->wordslist[i][0][1]=0;
    sprintf(labs->alphabet[i-1],"%s%d",prefix,i-1);
    labs->wordslist[i][1]=0;
    labno[migmptr->initial[i]]=i;
  }
  return 0;
}

int 
fsa_mimakemult2 (fsa *migm2ptr, int g1, int g2, char *prefix)
/* This procedure takes the fsa *migm2ptr produced by fsa_migenmult2,
 * and builds a particular length-2 multiplier Mult_g1g2.
 * This merely involves locating the accept states.
 * This procedure alters its arguments and does not return anything.
 * prefix is the prefix of the names of the subgroup generators to be used -
 * For a particular group, this MUST be the same throughtout for all calls of
 * fsa_migm2, fsa_mimakemult and fsa_mimakemult2.
 */
{
  int ngens, ns, nlabs, i, j, k, ct, len, ni, preflen, shift,
      alphsize;
  gen ***labellist, ***newlabellist, **oldlist;
  char  **alph;
  boolean *accept, found;
  setToLabelsType *labelnumber;

  if (kbm_print_level>=3)
    printf("    #Calling fsa_mimakemult2 with generators %d and %d.\n",g1,g2);
  if (!migm2ptr->flags[MIDFA]){
    fprintf(stderr,"Error: fsa_mimakemult2 only applies to DFA's.\n");
    return -1;
  }

  if (migm2ptr->alphabet->type!=PRODUCT || migm2ptr->alphabet->arity!=2) {
    fprintf(stderr,"Error in fsa_mimakemult2: fsa must be 2-variable.\n");
    return -1;
  }

  if (migm2ptr->states->type!=LABELED) {
   fprintf(stderr,"Error in fsa_mimakemult2: states of fsa must be labeled.\n");
    return -1;
  }

  if (migm2ptr->states->labels->type!=LISTOFWORDS) {
   fprintf(stderr,"Error in fsa_mimakemult2: labels must be lists of words.\n");
    return -1;
  }

  ns = migm2ptr->states->size;
  nlabs = migm2ptr->states->labels->size;
  ngens = migm2ptr->alphabet->base->size + 1;
  if (g1<=0 || g1>ngens || g2<=0 || g2>ngens) {
    fprintf(stderr,"#Error in fsa_makemult2: A generator is out of range.\n");
    return -1;
  }

  tfree(migm2ptr->accepting);
  tmalloc(accept,boolean,nlabs+1);
  labellist = migm2ptr->states->labels->wordslist;
/* Now we see which labels are accept-labels for the pair (g1,g2) - the
 * label is an accept-label if the list of words which is its name
 * contains g1*g2.
 */
  accept[0] = FALSE;
  for (i=1;i<=nlabs;i++) {
    accept[i] = FALSE;
    j=0;
    while (labellist[i][j]) {
      if (labellist[i][j][0]==g1 && labellist[i][j][1]==g2) {
        accept[i] = TRUE;
        break;
      }
      j++;
    }
  }

/* Now we can see which states are accept-states. A state is an accept-state
 * iff its label is an accept-label.
 * First we count the number.
 */
  ct = 0;
  labelnumber = migm2ptr->states->setToLabels;
  for (i=1;i<=ns;i++) if (accept[labelnumber[i]])
    ct++;

  migm2ptr->num_accepting = ct;
  if (ct<ns || ns==1) {
    tfree(migm2ptr->accepting);
    tmalloc(migm2ptr->accepting,int,ct+1);
    ct = 0;
    for (i=1;i<=ns;i++) if (accept[labelnumber[i]])
      migm2ptr->accepting[++ct] = i;
  }

  tfree(accept);

/* Finally we need to relabel the initial states - each such state will
 * have its own label, consisting of a single word of length at most 2
 * in the subgroup generators - we find it by looking in the existing
 * label for that state.
 * The alphabet for the labels will also need to be changed, since the
 * first few terms in it are group-generators and are not needed any more.
 * We do that first.
 */
  preflen = stringlen(prefix);
  alph = migm2ptr->states->labels->alphabet;
  alphsize = migm2ptr->states->labels->alphabet_size;
  shift=0;
  for (i=1;i<=alphsize;i++) {
    if (strncmp(prefix,alph[i],preflen)==0) {
      shift=i-1;
     /* shift is the number of terms of the alphabet that we will discard */
      break;
    }
  }
  if (i>alphsize) {
    fprintf(stderr,"Error in fsamimakemult2 - subgroup prefix wrong?\n");
    return -1;
  }
  for (i=1;i<=alphsize;i++) {
    if (i>shift) {
      tmalloc(alph[i-shift],char,stringlen(alph[i])+1);
      strcpy(alph[i-shift],alph[i]);
    }
    tfree(alph[i]);
  }
  alphsize -= shift;
  migm2ptr->states->labels->alphabet_size = alphsize;

  ni = migm2ptr->num_initial;
  tmalloc(newlabellist,gen**,ni+1);
  for (i=1;i<=ni;i++) {
    tmalloc(newlabellist[i],gen *,2);
    oldlist = labellist[labelnumber[migm2ptr->initial[i]]];
    j=0;
    found=FALSE;
    while (oldlist[j]) {
      /* see if this name starts with the subgroup generator prefix */
      if (oldlist[j][0]>shift) {
        len = genstrlen(oldlist[j]);
        tmalloc(newlabellist[i][0],gen,len+1);
        genstrcpy(newlabellist[i][0],oldlist[j]);
        for (k=0;k<len;k++)
          newlabellist[i][0][k] -= shift;
        found=TRUE;
        break;
      }
      j++;
    }
    if (!found) {
      /* label is empty word */
      tmalloc(newlabellist[i][0],gen,1);
      newlabellist[i][0][0] = 0;
    }
    newlabellist[i][1]=0;
    labelnumber[migm2ptr->initial[i]] = i;
  }

  for (i=1;i<=nlabs;i++) {
    oldlist=labellist[i];
    j=0;
    while (oldlist[j]) {
      tfree(oldlist[j]);
      j++;
    }
    tfree(oldlist);
  }
  tfree(migm2ptr->states->labels->wordslist);
  migm2ptr->states->labels->size = ni;
  migm2ptr->states->labels->wordslist = newlabellist;
  return 0;
}

fsa *
fsa_micomposite(mult1ptr,mult2ptr,op_table_type,destroy,compfilename,readback)
	fsa *mult1ptr, *mult2ptr;
	storage_type op_table_type;
	boolean destroy;
	char *compfilename;
        boolean readback;
/* *mult1ptr and *mult2ptr should be multiplier fsa's of an automatic group.
 * This function calculates the composite of these two multipliers.
 * So if *mult1ptr is the mutiplier for the word w1 and *mult2ptr for w2,
 * then the returned fsa is the multiplier for w1*w2.
 */
{
  if (kbm_print_level>=3)
    printf("    #Calling fsa_micomposite.\n");
  if (mult1ptr->states->size < MAXUSHORT && mult2ptr->states->size < MAXUSHORT)
    return fsa_micomposite_short(mult1ptr,mult2ptr,op_table_type,
                                                destroy,compfilename,readback);
  else
    return fsa_micomposite_int(mult1ptr,mult2ptr,op_table_type,
                                                destroy,compfilename,readback);
}

fsa *
fsa_micomposite_short(mult1ptr,mult2ptr,op_table_type,
                                                  destroy,compfilename,readback)
	fsa *mult1ptr, *mult2ptr;
	storage_type op_table_type;
	boolean destroy;
	char *compfilename;
        boolean readback;
{
  int **table1, **table2, ne, ngens, ngens1, ns, *fsarow,
      e, e1, e2, es1, ef1, dr1, dr2, nt, cstate, im, csa, csb, csima, csimb,
      i, j, l1, l2, ct, g1, g2, g3, len, reclen, ni1, ni2, ni;
  unsigned short *ht_ptr, *ht_chptr, *ht_ptrb, *ht_ptre,
                 *cs_ptr, *cs_ptre, *ptr;
  boolean dense_ip1, dense_ip2, dense_op, got, leftpad, rightpad;
  short_hash_table ht;
  fsa *micompositeptr;
  srec *labs, *labs1, *labs2;
  FILE *tempfile, *fopen();

  if (kbm_print_level>=3)
    printf("    #Calling fsa_micomposite_short.\n");
  if (!mult1ptr->flags[MIDFA] || !mult2ptr->flags[MIDFA]){
    fprintf(stderr,"Error: fsa_micomposite only applies to MIDFA's.\n");
    return 0;
  }

  if (mult1ptr->alphabet->type!=PRODUCT || mult1ptr->alphabet->arity!=2) {
    fprintf(stderr,"Error in fsa_micomposite: fsa must be 2-variable.\n");
    return 0;
  }
  if (mult2ptr->alphabet->type!=PRODUCT || mult2ptr->alphabet->arity!=2) {
    fprintf(stderr,"Error in fsa_micomposite: fsa must be 2-variable.\n");
    return 0;
  }

  if (!srec_equal(mult1ptr->alphabet,mult2ptr->alphabet)) {
    fprintf(stderr,
            "Error in fsa_micomposite: fsa's must have same alphabet.\n");
    return 0;
  }

  if (mult1ptr->states->type!=LABELED) {
    fprintf(stderr,"Error in fsa_micomposite: states must be labeled.\n");
    return 0;
  }
  if (mult2ptr->states->type!=LABELED) {
    fprintf(stderr,"Error in fsa_micomposite: states must be labeled.\n");
    return 0;
  }

  tmalloc(micompositeptr,fsa,1);
  fsa_init(micompositeptr);
  srec_copy(micompositeptr->alphabet,mult1ptr->alphabet);
  micompositeptr->states->type = LABELED;
  micompositeptr->flags[MIDFA] = TRUE;
  micompositeptr->flags[ACCESSIBLE] = TRUE;

  micompositeptr->table->table_type = op_table_type;
  micompositeptr->table->denserows = 0;
  micompositeptr->table->printing_format = op_table_type;
  if (!readback) {
    tmalloc(micompositeptr->table->filename,char,stringlen(compfilename)+1);
    strcpy(micompositeptr->table->filename,compfilename);
  }

  ne = mult1ptr->alphabet->size;
  ngens = mult1ptr->alphabet->base->size;
  ngens1 = ngens+1;

  if (ne != ngens1*ngens1-1) {
   fprintf(stderr,
     "Error: in a 2-variable fsa, alphabet size should = (ngens+1)^2 - 1.\n");
    return 0;
  }

  fsa_set_is_accepting(mult1ptr);
  fsa_set_is_accepting(mult2ptr);

  dense_ip1 = mult1ptr->table->table_type==DENSE;
  dr1 = mult1ptr->table->denserows;
  dense_ip2 = mult2ptr->table->table_type==DENSE;
  dr2 = mult2ptr->table->denserows;
  dense_op = op_table_type==DENSE;
  table1 = mult1ptr->table->table_data_ptr;
  table2 = mult2ptr->table->table_data_ptr;

  short_hash_init(&ht,FALSE,0,0,0);
/* Sort out initial states of *micompositeptr -
 * these will be pairs (s1,s2), where s1 and s2 are initial states
 * of *multptr1 and *multptr2, respectively.
 * Their labels will be the products of the corresponding labels of s1,s2.
 */
  ni1=mult1ptr->num_initial; ni2=mult2ptr->num_initial;
  ni=ni1*ni2;
  micompositeptr->num_initial = ni;
  tmalloc(micompositeptr->initial,int,ni+1);
  for (i=1;i<=ni;i++)
    micompositeptr->initial[i]=i;
  tmalloc(micompositeptr->states->labels,srec,1);
  labs = micompositeptr->states->labels;
  labs1=mult1ptr->states->labels; labs2=mult2ptr->states->labels;
  labs->size = ni;
  labs->type=LISTOFWORDS;
  labs->alphabet_size = labs1->alphabet_size;
  for (i=1;i<=labs->alphabet_size;i++) {
    tmalloc(labs->alphabet[i],char,stringlen(labs1->alphabet[i])+1);
    strcpy(labs->alphabet[i],labs1->alphabet[i]);
  }
  tmalloc(labs->wordslist,gen**,ni+1);
  ct=0;
  for (i=1;i<=ni1;i++) for (j=1;j<=ni2;j++) {
    ct++;
    tmalloc(labs->wordslist[ct],gen*,2);
    l1=genstrlen(labs1->wordslist[i][0]); l2=genstrlen(labs2->wordslist[j][0]);
    tmalloc(labs->wordslist[ct][0],gen,l1*l2+1);
    genstrcpy(labs->wordslist[ct][0],labs1->wordslist[i][0]);
    genstrcat(labs->wordslist[ct][0],labs2->wordslist[j][0]);
    labs->wordslist[ct][1]=0;
    
/* Each state in the composite transition table will be represented as a subset
 * of the set of ordered pairs in which the first component is a state in
 * *multptr1 and the second a state in *multptr2.
 * The initial states contain just one such pair, of which the components are
 * the initial states of *mult1ptr and *multptr2.
 * The subsets will be stored as variable-length records in the hash-table,
 * as a list of pairs in increasing order.
 * If a state is reached from a transition ($,x) or (x,$) (with $ the padding
 * symbol), then it needs to be marked as such, since we do not allow a $
 * to be followed by any other generator.
 * We do this by adding a 1 or a 2 to the end of the statelist - this is
 * recognisable by the fact that the length of the statelist then becomes odd.
 */
    ht_ptr = ht.current_ptr;
    ht_ptr[0] = mult1ptr->initial[i];
    ht_ptr[1] = mult2ptr->initial[j];
    im = short_hash_locate(&ht,2);
    if (im!=ct) {
      fprintf(stderr,"Hash-initialisation problem in fsa_micomposite.\n");
      return 0;
    }
  }

  if ((tempfile=fopen(compfilename,"w"))==0){
    fprintf(stderr,"Error: cannot open file %s\n",compfilename);
    return 0;
  }
  if (dense_op)
    tmalloc(fsarow,int,ne)
  else
    tmalloc(fsarow,int,2*ne+1)
 
  cstate = 0;
  if (dense_op)
    len = ne; /* The length of the fsarow output. */
  nt = 0; /* Number of transitions in micompositeptr */

  while (++cstate <= ht.num_recs) {
    if (kbm_print_level>=3) {
      if ((cstate<=1000 && cstate%100==0)||(cstate<=10000 && cstate%1000==0)||
          (cstate<=100000 && cstate%5000==0) || cstate%50000==0)
       printf("    #cstate = %d;  number of states = %d.\n",cstate,ht.num_recs);
    }
    reclen = short_hash_rec_len(&ht,cstate);
    cs_ptr = short_hash_rec(&ht,cstate);
    cs_ptre = short_hash_rec(&ht,cstate) + reclen - 1;
    /* for (i=0;i<reclen;i++) printf(" %d",cs_ptr[i]); printf("\n"); */
    if (reclen % 2 == 1) {
      if (*cs_ptre==1) {
        leftpad=TRUE;  rightpad=FALSE;
      } else {
        leftpad=FALSE;  rightpad=TRUE;
      }
      cs_ptre--;
    }
    else {
      leftpad=FALSE; rightpad=FALSE;
    }
      
    if (dense_op)
      for (i=0;i<ne;i++) fsarow[i] = 0;
    else
      len = 0;

    e = 0; /* e is the edge number of generator pair (g1,g3) */
    for (g1=1;g1<=ngens1;g1++)  for (g3=1;g3<=ngens1;g3++) {
/* Calculate action of pair (g1,g3) on state cstate  - to get the image, we
 * have to apply ( (g1,g2), (g2,g3) ) to each ordered pair in the subset
 * corresponding to cstate, * and this for each generator g2 of the
 * base-alphabet (including the padding symbol).
 */
      e++;
      if (g1==ngens1 && g3==ngens1)
        continue;
      if ((leftpad && g1<=ngens) || (rightpad && g3<=ngens))
        continue;
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb-1;
      es1 = (g1-1)*ngens1 + 1;
      ef1 = g1*ngens1;
/* As g2 ranges from 1 to ngens+1 in the pair (g1,g2), for fixed g1, the
 * corresponding edge number in the fsa ranges from es1 to ef1.
 *
 * As g2 ranges from 1 to ngens+1 in the pair (g2,g3), for fixed g3, the
 * corresponding edge number in the fsa ranges from g3 upwards, with
 * increments of size ngens+1.
 */

      ptr = cs_ptr;
      while (ptr <= cs_ptre) {
        csa = *(ptr++); csb = *(ptr++);
        for (g2=1,e1=es1,e2=g3; e1<=ef1; g2++,e1++,e2+=ngens1){
          csima = g1==ngens1 && g2==ngens1 ?
                   (mult1ptr->is_accepting[csa]>0 ? csa : 0) :
                   target(dense_ip1,table1,e1,csa,dr1);
          if (csima==0)
            continue;

          csimb = g2==ngens1 && g3==ngens1 ?
                   (mult2ptr->is_accepting[csb]>0 ? csb : 0) :
                   target(dense_ip2,table2,e2,csb,dr2);
          if (csimb==0)
            continue;

          if (ht_ptrb>ht_ptre || csima> *(ht_ptre-1) ||
                               (csima== *(ht_ptre-1) &&  csimb > *ht_ptre) ){
/* We have a new state for the image subset to be added to the end */
            *(++ht_ptre) = csima; *(++ht_ptre) = csimb;
          }
          else {
            ht_chptr = ht_ptrb;
            while (*ht_chptr < csima)
              ht_chptr+=2;
            while (*ht_chptr==csima && *(ht_chptr+1)<csimb)
                ht_chptr+=2;
            if (csima < *ht_chptr || csimb < *(ht_chptr+1)) {
/* we have a new state for the image subset to be added in the middle */
              ht_ptr = ht_ptre;
              ht_ptre += 2;
              while (ht_ptr >= ht_chptr) {
                *(ht_ptr+2) = *ht_ptr;
                ht_ptr--;
              }
              *ht_chptr = csima; *(ht_chptr+1) = csimb;
            }
          }
        }
      }
      if (ht_ptre > ht_ptrb) {
        if (g1==ngens1)
          *(++ht_ptre) = 1;
        else if (g3==ngens1)
          *(++ht_ptre) = 2;
      }
      im = short_hash_locate(&ht,ht_ptre-ht_ptrb+1);
      if (im > 0) {
        if (dense_op)
          fsarow[e-1] = im;
        else  {
          fsarow[++len] = e;
          fsarow[++len] = im;
        }
        nt++;
      }
    }
    if (!dense_op)
      fsarow[0] = len++;
    fwrite((void *)fsarow,sizeof(int),(size_t)len,tempfile);
  }
  fclose(tempfile);

  ns = micompositeptr->states->size = ht.num_recs;
  micompositeptr->table->numTransitions = nt;

  if (kbm_print_level>=3)
    printf("    #Calculated transitions - %d states, %d transitions.\n",ns,nt);

/* Locate the accept states. This is slightly cumbersome, since a state
 * is an accept state if either the corresponding subset contains a
 * a pair (s1,s2), where s1 is and accept state of *mult1ptr and s2 an
 * accept state of *mult2ptr, or we can get from some such state to an
 * accept state by applying elements ( ($,x), (x,$ ).
 * We will need to use the array micompositeptr->is_accepting.
 */

  tmalloc(micompositeptr->is_accepting,boolean,ns+1);
  for (i=1;i<=ns;i++)
    micompositeptr->is_accepting[i] = FALSE;
  ct = 0;
  es1 = ngens*ngens1 + 1;
  ef1 = ngens1*ngens1-1;
  for (cstate=ns;cstate>=1;cstate--) {
/* We work backwards through the states, since we wish to add on additional
 * elements at the end of the list in the hash-table - this destroys
 * later entries, but that doesn't matter, since we have already dealt
 * with them.
 */
    cs_ptr = short_hash_rec(&ht,cstate);
    reclen = short_hash_rec_len(&ht,cstate);
    if (reclen % 2 ==1)
      reclen--; /* The last entry marks the fact that this is a "padded state"*/
    cs_ptre = short_hash_rec(&ht,cstate) + reclen - 1;
/* First see if the set itself contains an accept-state */
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++); csb = *(ptr++);
      if (mult1ptr->is_accepting[csa] && mult2ptr->is_accepting[csb]) {
        micompositeptr->is_accepting[cstate] = TRUE;
        ct++;
        break;
      }
    }
    if (micompositeptr->is_accepting[cstate])
      continue;
/* Next apply generators ( ($,g2), (g2,$) ) and see if we get anything new.
 * We won't bother about having them in increasing order this time.
 */
    ptr = cs_ptr;
    while (ptr <= cs_ptre) {
      csa = *(ptr++); csb = *(ptr++);
      for (e1=es1,e2=ngens1; e1<=ef1; e1++,e2+=ngens1){
        csima = target(dense_ip1,table1,e1,csa,dr1);
        if (csima==0)
          continue;
        csimb = target(dense_ip2,table2,e2,csb,dr2);
        if (csimb==0)
          continue;

  /* see if (csima,csimb) is accepting */
        if (mult1ptr->is_accepting[csima] && mult2ptr->is_accepting[csimb]) {
          micompositeptr->is_accepting[cstate] = TRUE;
          ct++;
          break;
        }
  /* now see if it is new */
        ht_chptr = cs_ptr;
        got = FALSE;
        while (ht_chptr < cs_ptre) {
          if (csima == ht_chptr[0] && csimb == ht_chptr[1]) {
            got = TRUE;
            break;
          }
          ht_chptr+=2;
        }
        if (!got) {
  /* add (csima,csimb) to the end */
          *(++cs_ptre) = csima; *(++cs_ptre) = csimb;
        }
      }
      if (micompositeptr->is_accepting[cstate])
        continue;
    }
  }

  micompositeptr->num_accepting = ct;
  if (ct==1 || ct != ns) {
    tmalloc(micompositeptr->accepting,int,ct+1);
    ct = 0;
    for (i=1;i<=ns;i++) if (micompositeptr->is_accepting[i])
      micompositeptr->accepting[++ct] = i;
  }
  tfree(micompositeptr->is_accepting);
  tfree(mult1ptr->is_accepting);
  tfree(mult2ptr->is_accepting);
  short_hash_clear(&ht);
  tfree(fsarow);
  if (destroy) {
    fsa_clear(mult1ptr); fsa_clear(mult2ptr);
  }

  /* Set the setToLabels field of micompositeptr->states */
  tmalloc(micompositeptr->states->setToLabels,setToLabelsType,ns+1);
  for (i=1;i<=ni;i++)
    micompositeptr->states->setToLabels[i]=i;
  for (i=ni+1;i<=ns;i++)
    micompositeptr->states->setToLabels[i]=0;
  if (readback) {
    tempfile = fopen(compfilename,"r");
    compressed_transitions_read(micompositeptr,tempfile);
    fclose(tempfile);
    unlink(compfilename);
  }

  return micompositeptr;
}

fsa *
fsa_micomposite_int(
           mult1ptr,mult2ptr,op_table_type,destroy,compfilename,readback)
	fsa *mult1ptr, *mult2ptr;
	storage_type op_table_type;
	boolean destroy;
	char *compfilename;
        boolean readback;
{
 fprintf(stderr,
    "Sorry - fsa_micomposite is not yet implemented for machines.\n");
  fprintf(stderr,"with more than 65536 states.\n");
  return 0;
}
