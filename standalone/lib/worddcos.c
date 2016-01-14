/* file worddcos.c 25/7/95
 * 6/2/98 - large scale re-organisation.
 * 13/1/98 changes for the `gen' type replacing char for generators.
 *
 * Copied from worddiff.c, to make file for cosets calculations.
 * All functions have "cos" added to name.
 *
 * Routines for adding equations to become acceptable by a word-difference
 * fsa.  These will be used both by kbprogcos, and later programs (mult and
 * newdiff) that correct the word-difference machines, but the word-reduction
 * algorithm will be different in both cases - in this file it is called
 * reduce_word.
 */

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "externals.h"
#define TESTWORDLEN 4096
#define Ggen(x) (x<rs->separator)

extern int 	(*reduce_word)();

/* Functions defined in this file: */
int 	initialise_wd_fsa_cos();
int 	build_wd_fsa_cos();
int	add_wd_fsa_cos();
int 	make_full_wd_fsa_cos();
void 	clear_wd_fsa_cos();

/* Functions used in this file defined in other files: */
int add_word_to_buffer();
void srec_copy();
int diff_no();
void fsa_init();
void fsa_table_init();
int  fsa_table_dptr_init();
void genstrcat();
int genstrcmp();
void genstrcpy();
int genstrlen();
int stringlen();

int 
initialise_wd_fsa_cos (fsa *wd_fsaptr, srec *alphptr, int maxwdiffs)
/* Initialise a word-difference automaton, using  *alphptr as base-alphabet.
 * First state is empty word, which is initial and only accepting state.
 * In the cosets situation, there can be more than one initial state.
 */
{ int i, **table;

  fsa_init(wd_fsaptr);

  wd_fsaptr->states->type = WORDS; 
  tmalloc(wd_fsaptr->states->words,gen *,maxwdiffs+1);
  wd_fsaptr->states->alphabet_size = alphptr->size;
  for (i=1;i<=alphptr->size;i++) {
    tmalloc(wd_fsaptr->states->alphabet[i],char,stringlen(alphptr->names[i])+1);
    strcpy(wd_fsaptr->states->alphabet[i],alphptr->names[i]);
  }
  wd_fsaptr->states->size=1;
/* Set up first state, which is the empty word. */
  tmalloc(wd_fsaptr->states->words[1],gen,1);
  wd_fsaptr->states->words[1][0] = 0;

  wd_fsaptr->alphabet->type = PRODUCT;
  wd_fsaptr->alphabet->size = (alphptr->size+1)*(alphptr->size+1) - 1;
  wd_fsaptr->alphabet->arity = 2;
  wd_fsaptr->alphabet->padding = '_';
  tmalloc(wd_fsaptr->alphabet->base,srec,1);
  srec_copy(wd_fsaptr->alphabet->base,alphptr);

  wd_fsaptr->num_accepting = 1;
  tmalloc(wd_fsaptr->accepting,int,2);
  wd_fsaptr->accepting[1] = 1;

  wd_fsaptr->flags[TRIM] = TRUE;
  wd_fsaptr->flags[MIDFA] = TRUE;

  fsa_table_init(wd_fsaptr->table,maxwdiffs,wd_fsaptr->alphabet->size);
  table = wd_fsaptr->table->table_data_ptr;
  for (i=1;i<=wd_fsaptr->alphabet->size;i++)
    set_dense_target(table,i,1,0);
  wd_fsaptr->table->printing_format = SPARSE;
  if (fsa_table_dptr_init(wd_fsaptr)==-1) return -1;
  return 0;
}

int
build_wd_fsa_cos(wd_fsaptr,new_wd,rs)
	fsa *wd_fsaptr;
	boolean *new_wd;
	reduction_struct *rs;
/* Make the word-difference machine from the rewriting system rws */
{ int i, ct, **table;
  boolean new;
  rewriting_system *rwsptr=rs->rws;
  wd_fsaptr->states->size = 1;
  tmalloc(wd_fsaptr->is_initial,boolean,wd_fsaptr->table->maxstates+1);
  for (i=1;i<=wd_fsaptr->table->maxstates;i++)
    wd_fsaptr->is_initial[i] = FALSE;
  wd_fsaptr->is_initial[1] = TRUE;
  wd_fsaptr->num_initial=1;
  table = wd_fsaptr->table->table_data_ptr;
  for (i=1;i<=wd_fsaptr->alphabet->size;i++)
    set_dense_target(table,i,1,0);

  if (new_wd) /* new_wd nonzero means that we wish to note which equations
               * give rise to changes in the table.
               */
    for (i=1;i<=rwsptr->num_eqns;i++)
      new_wd[i] = FALSE;

/* Now add each equation to the fsa. */
  if (kbm_print_level==4)
    printf("New word  differences from equations:\n");
  for (i=1;i<=rwsptr->num_eqns;i++){
     new = add_wd_fsa_cos(wd_fsaptr,rwsptr->eqns+i,rwsptr->inv_of,FALSE,rs);
     if (new== -1)
       return -1;
     if (new_wd && new)
        new_wd[i] = TRUE;
  }
  tmalloc(wd_fsaptr->initial,int,wd_fsaptr->num_initial+1);
  ct = 0;
  for (i=1;i<=wd_fsaptr->states->size;i++) if (wd_fsaptr->is_initial[i])
    wd_fsaptr->initial[++ct] = i;
  tfree(wd_fsaptr->is_initial);

  if (kbm_print_level>=2)
    printf("	#There are %d word-differences.\n",wd_fsaptr->states->size);
  return 0;
}

int
add_wd_fsa_cos(wd_fsaptr,eqn,inv,reverse,rs)
        fsa *wd_fsaptr;
	reduction_equation	*eqn;
	int			*inv;
	boolean			reverse;
        reduction_struct 	*rs;
/* Alter the word-difference machine to make it accept the equation *eqn
 * If reverse is true, then for all transitions added, the inverse transition
 * is also added.
 * WARNING: this is a routine that will get called often.
 * It assumes that wd_fsaptr->is_initial is set, and does not reset
 * wd_fsaptr->initial at the end if new initial states are found.
 * The caller is responsible for doing this resetting when the
 * sequence of calls is finished.
 * It returns 1 or 0, according to whether new word-differences are added.
 */
{ gen *wd1, *wd2, *stw, g1, g2;
  char  **names;
  int i, j, l, l1, l2, maxl, state, image, size_pba, **table, ***wd_table;
  int ans=0;
  gen testword[TESTWORDLEN];
  size_pba = 1 + wd_fsaptr->alphabet->base->size;
  wd1 = eqn->lhs; wd2 = eqn->rhs;
  table = wd_fsaptr->table->table_data_ptr;
  wd_table = wd_fsaptr->table->table_data_dptr;

  if (*wd1 == rs->separator) {
/* First set up the initial state - i.e. the word in H */
    *testword = 0;
    while (*wd2 != rs->separator) {
        if (*wd2==0) {
          fprintf(stderr,
             "Error: separator on LHS but not RHS of equation.\n");
          return -1;
        }
        if Ggen(*wd2) {
          l=genstrlen(testword);
          testword[l]= *wd2; testword[l+1]=0;
        }
        else
          genstrcat(testword,rs->rws->subwordsG[*wd2]);
        wd2++;
    }
    if ((*reduce_word)(testword,rs)==-1)
      return -1;
    image = diff_no(wd_fsaptr,testword);
    if (image==0){ /* new state */
       image = (++wd_fsaptr->states->size);
       if (image > wd_fsaptr->table->maxstates){
       fprintf(stderr,
           "Maximum number of word-differences exceeded. Cannot continue.\n");
         return -1;
       }
       tmalloc(wd_fsaptr->states->words[image],gen,genstrlen(testword)+1);
       genstrcpy(wd_fsaptr->states->words[image],testword);
       for (j=1;j<=wd_fsaptr->alphabet->size;j++)
           set_dense_target(table,j,image,0);
       wd_fsaptr->num_initial++;
       wd_fsaptr->is_initial[image] = TRUE;       
    }
    else if (!wd_fsaptr->is_initial[image]) {
       wd_fsaptr->num_initial++;
       wd_fsaptr->is_initial[image] = TRUE;       
    }
  
    wd1++; wd2++; /* now pointing at beginning of equation in cosets. */
    state = image;
  }
  else if (Ggen(*wd1))
    state = 1;
  else
    return ans;

  l1 = genstrlen(wd1); l2 = genstrlen(wd2);
  maxl = l1>l2 ? l1 : l2;
  if (kbm_print_level==4) {
    names=wd_fsaptr->alphabet->base->names;
    strcpy(kbm_buffer,"  "); add_word_to_buffer(stdout,wd1,names);
    strcat(kbm_buffer," -> "); add_word_to_buffer(stdout,wd2,names);
    printf("%s\n",kbm_buffer);
  }

  for (i=0;i<maxl;i++){
    g1 = i>=l1 ? size_pba : wd1[i];
    g2 = i>=l2 ? size_pba : wd2[i];
    image = dense_dtarget(wd_table,g1,g2,state);
    if (image==0){
      stw=wd_fsaptr->states->words[state];
      l=genstrlen(stw);
      if (g1==size_pba) {
          genstrcpy(testword,stw);
          testword[l]=g2; testword[l+1]=0;
      }
      else if (g2==size_pba) {
          testword[0]=inv[g1];
          genstrcpy(testword+1,stw);
          testword[l+1]=0;
      }
      else {
          testword[0]=inv[g1];
          genstrcpy(testword+1,stw);
          testword[l+1]=g2;
          testword[l+2]=0;
      }
      if ((*reduce_word)(testword,rs)==-1)
        return -1;
      image = diff_no(wd_fsaptr,testword);
      if (image==0){ /* new state */
        if (kbm_print_level==4) {
          strcpy(kbm_buffer,"    ");  add_word_to_buffer(stdout,testword,names);
          printf("%s\n",kbm_buffer);
        }
        image = (++wd_fsaptr->states->size);
        if (image > wd_fsaptr->table->maxstates){
          fprintf(stderr,
            "Maximum number of word-differences exceeded. Cannot continue.\n");
          return -1;
        }
        tmalloc(wd_fsaptr->states->words[image],gen,genstrlen(testword)+1);
        genstrcpy(wd_fsaptr->states->words[image],testword);
        for (j=1;j<=wd_fsaptr->alphabet->size;j++)
           set_dense_target(table,j,image,0);
      }
      set_dense_dtarget(wd_table,g1,g2,state,image);
      ans = TRUE;
    }
    if (reverse)
      set_dense_dtarget(wd_table,inv[g1],inv[g2],image,state);
    state=image;
  }
  if (kbm_print_level>1 && state!=1)
    printf("  #Warning: in add_wd_fsa_cos - equation not valid in group.\n");
  return ans;
}

int 
make_full_wd_fsa_cos (fsa *wd_fsaptr, int *inv, int start_no, reduction_struct *rs)
/* Close the set of word-differences under inversion, and add all possible
 * transitions, starting at state number start_no.
 */
{ int i, j, l, ct, ns, n, g1, g2, size_pba, **table, ***wd_table;
  gen **wdn, *stw, *ptr, *ptre, *ptri;
  gen testword[TESTWORDLEN];

  if (kbm_print_level>=3)
    printf("    #Calling make_full_wd_fsa.\n");
  size_pba = 1 + wd_fsaptr->alphabet->base->size;
  ns = wd_fsaptr->states->size;
  wdn = wd_fsaptr->states->words;
  table = wd_fsaptr->table->table_data_ptr;
  wd_table = wd_fsaptr->table->table_data_dptr;

  tmalloc(wd_fsaptr->is_initial,boolean,wd_fsaptr->table->maxstates+1);
  for (i=1;i<=wd_fsaptr->table->maxstates;i++)
    wd_fsaptr->is_initial[i] = FALSE;
  for (i=1;i<=wd_fsaptr->num_initial;i++)
    wd_fsaptr->is_initial[wd_fsaptr->initial[i]] = TRUE;
  tfree(wd_fsaptr->initial);

  for (i=1;i<=ns;i++){
    ptr = wdn[i];
    ptre = ptr + genstrlen(ptr);
/* invert this word-difference and put into testword. */
    ptri = testword;
    while (--ptre >= ptr)
      *(ptri++) = inv[*ptre];
    *ptri = 0;
    if ((*reduce_word)(testword,rs)==-1)
      return -1;
    
    if ((n=diff_no(wd_fsaptr,testword))==0){ /* new state */
      n = (++wd_fsaptr->states->size);
      if (n > wd_fsaptr->table->maxstates){
        fprintf(stderr,"Too many word-differences. Increase maxwdiffs.\n");
        return -1;
      }
      tmalloc(wd_fsaptr->states->words[n],gen,genstrlen(testword)+1);
      genstrcpy(wd_fsaptr->states->words[n],testword);
      for (j=1;j<=wd_fsaptr->alphabet->size;j++)
         set_dense_target(table,j,n,0);
      if (wd_fsaptr->is_initial[i]) {
         wd_fsaptr->num_initial++;
         wd_fsaptr->is_initial[n] = TRUE;
      }
    }
    else if (wd_fsaptr->is_initial[i] && !wd_fsaptr->is_initial[n]) {
      wd_fsaptr->num_initial++;
      wd_fsaptr->is_initial[n] = TRUE;
    }
  }

/* Now fill out table */
  ns = wd_fsaptr->states->size;
  if (start_no<1)
    start_no = 1;
  for (i=start_no;i<=ns;i++){
    for (g1=1;g1<=size_pba;g1++) for (g2=1;g2<=size_pba;g2++){
      if (g1==size_pba && g2==size_pba)
        continue; /* Don't want padding-symbol on both sides. */
      if ((g1!=size_pba && !Ggen(g1)) || (g2!=size_pba && !Ggen(g2)))
        continue;
      if (dense_dtarget(wd_table,g1,g2,i) == 0) {
        stw=wd_fsaptr->states->words[i];
        l=genstrlen(stw);
        if (g1==size_pba) {
            genstrcpy(testword,stw);
            testword[l]=g2; testword[l+1]=0;
        }
        else if (g2==size_pba) {
            testword[0]=inv[g1];
            genstrcpy(testword+1,stw);
            testword[l+1]=0;
        }
        else {
            testword[0]=inv[g1];
            genstrcpy(testword+1,stw);
            testword[l+1]=g2;
            testword[l+2]=0;
        }
        if ((*reduce_word)(testword,rs)==-1)
          return -1;
        if ((n=diff_no(wd_fsaptr,testword)))
          set_dense_dtarget(wd_table,g1,g2,i,n);
        if (n>0 && n<start_no)
          set_dense_dtarget(wd_table,inv[g1],inv[g2],n,i);
      }
    }
  }
  tmalloc(wd_fsaptr->initial,int,wd_fsaptr->num_initial+1);
  ct = 0;
  for (i=1;i<=wd_fsaptr->states->size;i++) if (wd_fsaptr->is_initial[i])
    wd_fsaptr->initial[++ct] = i;
  tfree(wd_fsaptr->is_initial);
  return 0;
}

void 
clear_wd_fsa_cos (fsa *wd_fsaptr)
/* Clear the state-names for all states except the first. */
{ int i, ns;
  gen **wdn;
  ns = wd_fsaptr->states->size;
  wdn = wd_fsaptr->states->words;

  for (i=2;i<=ns;i++)
    tfree(wdn[i]);
  tfree(wd_fsaptr->initial);
}
