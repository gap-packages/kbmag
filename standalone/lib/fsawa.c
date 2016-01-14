/* file fsawa.c 8/11/94
 * 6/8/98 large scale reorganisation to eliminante externals, etc.
 * This file essentially consists of the function fsa_wa
 * (although this function calls fsa_wa_int or (more usually)
 * fsa_wa_short, the latter using the short hash table functions).
 * For general methodology, see comment at top of file fsalogic.c.
 *
 * This function is intended to be called only in the construction of the
 * word-acceptor of a shortlex automatic group.
 * It works on the output of a word-difference machine for the group "anded"
 * with the "greater-than" automaton.
 * fsa_wa works directly with the word-difference machine itself, and 
 * appears to be faster.
 * *fsaptr  is the word-difference machine.
 * The returned fsa accepts a word w_1 iff  w_1 contains no subword x_1 such
 * that (x_1,x_2) is accepted by *fsaptr and x_2 < x_1 in the shortlex ordering,
 * for some word x_2 (with the usual padding conventions).
 * It is based on the function fsa_exists.
 *
 * The states of the fsa  *wa that we are calculating consist of subsets of
 * the "and" of *fsaptr with the "lhs greater-than rhs" automaton. Since the
 * latter has  4 states, the elements of these subsets are technically
 * pairs of the form (s,i), where s is a state of *fsaptr, and 1<=i<=4.
 * Here i=1 means lhs=rhs, i=2 means lhs>rhs with equal lengths,
 * i=3 means rhs>lhs with equal lengths, and i=4 means lhs is longer than rhs. 
 * In fact i=1 never occurs (except in the initial state, which is special)
 * and if (s,2) and (s,3) both occur together, then we can omit (s,3), since
 * any path from (s,3) to failure will also be a path from (s,2) to failure.
 * (This is probably the main reason why the direct algorithm appears to
 *  perform better than fsa_nosub_exists.)
 * In the records in the hash-table, in which the subsets are stored,
 * (s,2) is stores as s, (s,3) as ndiff+s
 * (where ndiff = no. of states of *fsaptr), and (s,4) as 2*ndiff + s.
 *
 * This function assumes that *fsaptr is a word-difference machine, with a
 * unique accept state, which should be equal to the initial state, and
 * map onto the identity element of the group.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "externals.h"

/* Functions defined in this file: */
fsa * fsa_wa();
fsa * fsa_wa_short();
fsa * fsa_wa_int();

/* Functions used in this file and defined elsewhere */
void fsa_init();
int  fsa_table_dptr_init();
void srec_copy();
void fsa_clear();
void compressed_transitions_read();
void short_hash_init();
int short_hash_locate();
void short_hash_clear();
unsigned short* short_hash_rec();
int short_hash_rec_len();
void hash_init();
int hash_locate();
void hash_clear();
int* hash_rec();
int hash_rec_len();

fsa *
fsa_wa(fsaptr,op_table_type,destroy,tempfilename)
	fsa *fsaptr;
	storage_type op_table_type;
	boolean destroy;
	char *tempfilename;
{
  if (kbm_print_level>=3)
    printf("    #Calling fsa_wa.\n");
  if (3*fsaptr->states->size < MAXUSHORT)
    return fsa_wa_short(fsaptr,op_table_type,destroy,tempfilename);
  else
    return fsa_wa_int(fsaptr,op_table_type,destroy,tempfilename);
}

fsa *
fsa_wa_short(fsaptr,op_table_type,destroy,tempfilename)
	fsa *fsaptr;
	storage_type op_table_type;
	boolean destroy;
	char *tempfilename;
{ int  ***dtable, ne, ngens, ndiff, ns, *fsarow, nt, cstate, cs, csdiff, csi,
       im, i, k, g1, g2, len, identity;
  unsigned short *ht_ptr, *ht_ptrb, *ht_ptre,
                 *cs_ptr, *cs_ptre, *ptr;
  boolean dense_op, no_trans, good;
  char *cf;
  short_hash_table ht;
  fsa *wa;
  FILE *tempfile, *fopen();

  if (kbm_print_level>=3)
    printf("    #Calling fsa_wa_short.\n");
  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_wa only applies to DFA's.\n");
     return 0;
  }

  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr,"Error in fsa_wa: fsa must be 2-variable.\n");
    return 0;
  }
  if (fsaptr->states->type != WORDS) {
    fprintf(stderr,"Error in fsa_wa: fsa must be word-difference type.\n");
    return 0;
  }

  tmalloc(wa,fsa,1);
  fsa_init(wa);
  srec_copy(wa->alphabet,fsaptr->alphabet->base);
  wa->flags[DFA] = TRUE;
  wa->flags[ACCESSIBLE] = TRUE;
  wa->flags[BFS] = TRUE;

  ne = fsaptr->alphabet->size;
  ngens = wa->alphabet->size;
  ndiff = fsaptr->states->size;

  if (ne != (ngens+1)*(ngens+1)-1) {
   fprintf(stderr,
       "Error: in a 2-variable fsa, alphabet size should = ngens^2 - 1.\n");
    return 0;
  }

  identity = fsaptr->accepting[1]; /* assumed to be unique */
  if (fsaptr->num_accepting!=1 || (identity != fsaptr->initial[1])) {
    fprintf(stderr,"Error: Input to fsa_wa not a word-difference machine.\n");
    return 0;
  }

  if (fsaptr->table->table_type!=DENSE) {
     fprintf(stderr,
      "Error: function fsa_wa can only be called with a densely-stored fsa.\n");
     return 0;
  }
  dense_op = op_table_type==DENSE;
  if (fsa_table_dptr_init(fsaptr)== -1) return 0;
  dtable = fsaptr->table->table_data_dptr;

  wa->states->type = SIMPLE;
  wa->num_initial = 1;
  tmalloc(wa->initial,int,2);
  wa->initial[1] = 1;
  wa->table->table_type = op_table_type;
  wa->table->denserows = 0;
  wa->table->printing_format = op_table_type;
  
  short_hash_init(&ht,FALSE,0,0,0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = identity;
  im = short_hash_locate(&ht,1);
  if (im== -1) return 0;
/* See discussion at top of file for storing of states of *wa.
 * Only the initial state which consists of the singleton {identity} contains
 * identity. 
 */
  if (im!=1) {
    fprintf(stderr,"Hash-initialisation problem in fsa_wa.\n");
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
  nt = 0; /* Number of transitions in exists */
  tmalloc(cf,char,ndiff+1);

/* As we build up the subset that represents a state of *wa, we use the
 * characteristic function cf, to record what we have found already.
 * For n a state number  of *fsaptr,
 * cf[n] is an integer between 0 and 7 with following
 * meanings (see comment at top of file for notation):
 *
 * cf[n] = 0  -  n nas not been found at all
 * cf[n] = 1  -  not used
 * cf[n] = 2  -  (n,2) has been found but not (n,4) 
 * cf[n] = 3  -  (n,3) has been found but not (n,2) or (n,4).
 * cf[n] = 4  -  (n,4) has been found but not (n,2) or (n,3)
 * cf[n] = 5  -  not used
 * cf[n] = 6  -  (n,2) and (n,4) have been found.
 * cf[n] = 7  -  (n,3) and (n,4) have been found but not (n,2).
 */ 

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
 * have to apply (g1,g2) to each element in the subset corresponding to cstate,
 * and this for each generator g2 of the base-alphabet (including the padding
 * symbol).
 * Since we are excluding words that contain subwords w_1 s.t. (w_1,w_2) is
 * accepted by *fsaptr, we also have to apply (g1,g2) to the initial state
 * of *fsaptr.
 */
      for (i=1;i<=ndiff;i++)
        cf[i] = 0;
      ptr = cs_ptr-1;
      no_trans = FALSE;
/* We will set no_trans to be true if we find that the transition leads to
 * failure.
 */
      while (ptr <= cs_ptre) {
/* We add the initial state of *fsaptr to the subset representing cstate */
        cs = ptr<cs_ptr ? identity : *ptr;
        csdiff = cs%ndiff;
        if (csdiff==0) csdiff = ndiff;
   /* csdiff is the state of *fsaptr corresponding to cs */
        ptr++;
        if (cs > 2*ndiff) {
/* The state csdiff is one where lhs>rhs. We can assume that the length of w_1
 * does not exceed that of w_2 by more than 2 in a substitution.
 * Thus either the action of generator g1 leads immediately to failure, or
 * we can forget about this state.
 */
          csi = dense_dtarget(dtable,g1,ngens+1,csdiff);
          if (csi==identity) {
            no_trans = TRUE;
            break;
          }
          continue;
        }
        for (g2=1;g2<=ngens+1;g2++){
          csi =  dense_dtarget(dtable,g1,g2,csdiff);
          if (csi==0)
            continue;
          if (g2==ngens+1) { /*lhs gets longer than rhs */
            if (csi==identity) {
              no_trans = TRUE;
              break;
            }
            if (cf[csi] < 4)
               cf[csi] += 4;
          }
          else {
            good = cs==identity ? g2<g1 : cs<=ndiff;
            if (csi==identity) {
              if (good)  {
                no_trans = TRUE;
                break;
              }
              continue;
            }
            if (good)
              cf[csi] =  cf[csi]<=3 ? 2 : 6; 
            else if (cf[csi]==0 || cf[csi]==4)
              cf[csi]+=3;
          }
        }
        if (no_trans)
          break;
      }
      if (no_trans) {
        if (dense_op)
          fsarow[g1-1] = 0;
        continue;
      }
/* Now we have the image stored in the array cf, and we translate it to a list
 * and insert it into the hash-table.
 */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb-1;
      for (i=1;i<=ndiff;i++) {
        k = cf[i];
        if (k==2)
          *(++ht_ptre) = i;
        else if (k==3)
          *(++ht_ptre) = ndiff+i;
        else if (k==4)
          *(++ht_ptre) = 2*ndiff+i;
        else if (k==6) {
          *(++ht_ptre) = 2*ndiff+i;
          *(++ht_ptre) = i;
        }
        else if (k==7) {
          *(++ht_ptre) = 2*ndiff+i;
          *(++ht_ptre) = ndiff+i;
        }
      }
      im = short_hash_locate(&ht,ht_ptre-ht_ptrb+1);
      if (im== -1) return 0;
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

  short_hash_clear(&ht);
  tfree(fsarow);
  tfree(cf);

  ns = wa->states->size = ht.num_recs;
  wa->table->numTransitions = nt;

/* All states of wa will be accept states. */
  wa->num_accepting = ns;
  if (ns==1) {
    tmalloc(wa->accepting,int,2);
    wa->accepting[1] = 1;
  }
  tfree(fsaptr->is_accepting);
  if (destroy)
    fsa_clear(fsaptr);

/* Now read the transition table back in */
  tempfile = fopen(tempfilename,"r");
  compressed_transitions_read(wa,tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return wa;
}

fsa *
fsa_wa_int(fsaptr,op_table_type,destroy,tempfilename)
	fsa *fsaptr;
	storage_type op_table_type;
	boolean destroy;
	char *tempfilename;
{ int  ***dtable, ne, ngens, ndiff, ns, *fsarow, nt, cstate, cs, csdiff, csi,
       im, i, k, g1, g2, len, identity;
  int *ht_ptr, *ht_ptrb, *ht_ptre, *cs_ptr, *cs_ptre, *ptr;
  boolean dense_op, no_trans, good;
  char *cf;
  hash_table ht;
  fsa *wa;
  FILE *tempfile, *fopen();

  if (kbm_print_level>=3)
    printf("    #Calling fsa_wa_short.\n");
  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_wa only applies to DFA's.\n");
    return 0;
  }

  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr,"Error in fsa_wa: fsa must be 2-variable.\n");
    return 0;
  }
  if (fsaptr->states->type != WORDS) {
    fprintf(stderr,"Error in fsa_wa: fsa must be word-difference type.\n");
    return 0;
  }

  tmalloc(wa,fsa,1);
  fsa_init(wa);
  srec_copy(wa->alphabet,fsaptr->alphabet->base);
  wa->flags[DFA] = TRUE;
  wa->flags[ACCESSIBLE] = TRUE;
  wa->flags[BFS] = TRUE;

  ne = fsaptr->alphabet->size;
  ngens = wa->alphabet->size;
  ndiff = fsaptr->states->size;

  if (ne != (ngens+1)*(ngens+1)-1) {
   fprintf(stderr,
       "Error: in a 2-variable fsa, alphabet size should = ngens^2 - 1.\n");
    return 0;
  }

  identity = fsaptr->accepting[1]; /* assumed to be unique */
  if (fsaptr->num_accepting!=1 || (identity != fsaptr->initial[1])) {
    fprintf(stderr,"Error: Input to fsa_wa not a word-difference machine.\n");
    return 0;
  }

  if (fsaptr->table->table_type!=DENSE) {
     fprintf(stderr,
      "Error: function fsa_wa can only be called with a densely-stored fsa.\n");
     return 0;
  }
  dense_op = op_table_type==DENSE;
  if (fsa_table_dptr_init(fsaptr)== -1) return 0;
  dtable = fsaptr->table->table_data_dptr;

  wa->states->type = SIMPLE;
  wa->num_initial = 1;
  tmalloc(wa->initial,int,2);
  wa->initial[1] = 1;
  wa->table->table_type = op_table_type;
  wa->table->denserows = 0;
  wa->table->printing_format = op_table_type;
  
  hash_init(&ht,FALSE,0,0,0);
  ht_ptr = ht.current_ptr;
  ht_ptr[0] = identity;
  im = hash_locate(&ht,1);
  if (im== -1) return 0;
/* See discussion at top of file for storing of states of *wa.
 * Only the initial state which consists of the singleton {identity} contains
 * identity. 
 */
  if (im!=1) {
    fprintf(stderr,"Hash-initialisation problem in fsa_wa.\n");
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
  nt = 0; /* Number of transitions in exists */
  tmalloc(cf,char,ndiff+1);

/* As we build up the subset that represents a state of *wa, we use the
 * characteristic function cf, to record what we have found already.
 * For n a state number  of *fsaptr,
 * cf[n] is an integer between 0 and 7 with following
 * meanings (see comment at top of file for notation):
 *
 * cf[n] = 0  -  n nas not been found at all
 * cf[n] = 1  -  not used
 * cf[n] = 2  -  (n,2) has been found but not (n,4) 
 * cf[n] = 3  -  (n,3) has been found but not (n,2) or (n,4).
 * cf[n] = 4  -  (n,4) has been found but not (n,2) or (n,3)
 * cf[n] = 5  -  not used
 * cf[n] = 6  -  (n,2) and (n,4) have been found.
 * cf[n] = 7  -  (n,3) and (n,4) have been found but not (n,2).
 */ 

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
 * have to apply (g1,g2) to each element in the subset corresponding to cstate,
 * and this for each generator g2 of the base-alphabet (including the padding
 * symbol).
 * Since we are excluding words that contain subwords w_1 s.t. (w_1,w_2) is
 * accepted by *fsaptr, we also have to apply (g1,g2) to the initial state
 * of *fsaptr.
 */
      for (i=1;i<=ndiff;i++)
        cf[i] = 0;
      ptr = cs_ptr-1;
      no_trans = FALSE;
/* We will set no_trans to be true if we find that the transition leads to
 * failure.
 */
      while (ptr <= cs_ptre) {
/* We add the initial state of *fsaptr to the subset representing cstate */
        cs = ptr<cs_ptr ? identity : *ptr;
        csdiff = cs%ndiff;
        if (csdiff==0) csdiff = ndiff;
   /* csdiff is the state of *fsaptr corresponding to cs */
        ptr++;
        if (cs > 2*ndiff) {
/* The state csdiff is one where lhs>rhs. We can assume that the length of w_1
 * does not exceed that of w_2 by more than 2 in a substitution.
 * Thus either the action of generator g1 leads immediately to failure, or
 * we can forget about this state.
 */
          csi = dense_dtarget(dtable,g1,ngens+1,csdiff);
          if (csi==identity) {
            no_trans = TRUE;
            break;
          }
          continue;
        }
        for (g2=1;g2<=ngens+1;g2++){
          csi =  dense_dtarget(dtable,g1,g2,csdiff);
          if (csi==0)
            continue;
          if (g2==ngens+1) { /*lhs gets longer than rhs */
            if (csi==identity) {
              no_trans = TRUE;
              break;
            }
            if (cf[csi] < 4)
               cf[csi] += 4;
          }
          else {
            good = cs==identity ? g2<g1 : cs<=ndiff;
            if (csi==identity) {
              if (good)  {
                no_trans = TRUE;
                break;
              }
              continue;
            }
            if (good)
              cf[csi] =  cf[csi]<=3 ? 2 : 6; 
            else if (cf[csi]==0 || cf[csi]==4)
              cf[csi]+=3;
          }
        }
        if (no_trans)
          break;
      }
      if (no_trans) {
        if (dense_op)
          fsarow[g1-1] = 0;
        continue;
      }
/* Now we have the image stored in the array cf, and we translate it to a list
 * and insert it into the hash-table.
 */
      ht_ptrb = ht.current_ptr;
      ht_ptre = ht_ptrb-1;
      for (i=1;i<=ndiff;i++) {
        k = cf[i];
        if (k==2)
          *(++ht_ptre) = i;
        else if (k==3)
          *(++ht_ptre) = ndiff+i;
        else if (k==4)
          *(++ht_ptre) = 2*ndiff+i;
        else if (k==6) {
          *(++ht_ptre) = 2*ndiff+i;
          *(++ht_ptre) = i;
        }
        else if (k==7) {
          *(++ht_ptre) = 2*ndiff+i;
          *(++ht_ptre) = ndiff+i;
        }
      }
      im = hash_locate(&ht,ht_ptre-ht_ptrb+1);
      if (im== -1) return 0;
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

  hash_clear(&ht);
  tfree(fsarow);
  tfree(cf);

  ns = wa->states->size = ht.num_recs;
  wa->table->numTransitions = nt;

/* All states of wa will be accept states. */
  wa->num_accepting = ns;
  if (ns==1) {
    tmalloc(wa->accepting,int,2);
    wa->accepting[1] = 1;
  }
  tfree(fsaptr->is_accepting);
  if (destroy)
    fsa_clear(fsaptr);

/* Now read the transition table back in */
  tempfile = fopen(tempfilename,"r");
  compressed_transitions_read(wa,tempfile);
  fclose(tempfile);

  unlink(tempfilename);

  return wa;
}
