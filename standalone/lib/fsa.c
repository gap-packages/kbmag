/* file fsa.c - 16. 9. 94.
 *
 * 2/3/99 Bug fix in labeled_minimize();
 * Must have at least two iterations of main loop.
 *
 * 9/1/98 change generators from type char to type `gen'.
 * 2/10/97  - made minor changes necessary to handle compact table format.
 *            most functions will not handle this yet however.
 * 27.6.96. - added functions for computing growth function of an fsa
 *            written by Laurent Bartholdi
 * 1.5.96.  - adjusted srec_copy and srec_clear to deal with
 *            srec type "list of Integers".
 * 15.4.96. - added routing fsa_swap_coords().
 *
 * This file contains routines for manipulating finite state automata
 * The functions in this file currently only deal with deterministic fsa's
 *
 * 13.9.95. - wrote in code to handle srec type "list of words"
 * 17.11.94. - implemented labeled srec type and function fsa_labeled_minimize.
 */

#include <stdio.h>
#include <stdlib.h>
#include "defs.h"
#include "fsa.h"
#include "hash.h"
#include "externals.h"

/* Functions defined in this file: */
int sparse_target();
void fsa_init();
void fsa_table_init();
void fsa_set_is_initial();
void fsa_set_is_accepting();
void fsa_set_is_accessible();
int fsa_table_dptr_init();
void srec_copy();
void table_copy();
void fsa_copy();
void srec_clear();
void table_clear();
void fsa_clear();
int fsa_delete_state();
int fsa_permute_states();
int fsa_clear_rws();
int fsa_make_accessible();
int fsa_minimize();
int fsa_labeled_minimize();
int fsa_bfs();
int fsa_count();
int fsa_enumerate();
int fsa_swap_coords();

/* New functions written by Laurent Bartholdi for calculation of
 * growth rate of an fsa
 */
unsigned *fsa_mod_count();	/* count # of accepted words mod. a prime */
unsigned mod_inverse();
int mod_solve();
int fsa_mod_growth();		/* compute growth series mod. a prime */
void mod_normal();
boolean print_poly();
int fsa_growth();
typedef struct {
  int nd, *num, dd, *den;
} fraction;

/* Functions used in this file and defined elsewhere */
void printbuffer();
void hash_init();
void hash_clear();
int *hash_rec();
int hash_rec_len();
int hash_locate();
void add_to_buffer();
int  add_word_to_buffer();
void add_iword_to_buffer();
int int_len();
fsa * fsa_and();
void genstrcpy();
int genstrlen();
int stringlen();

int
sparse_target(g,p1,p2)
	int g;
	int *p1, *p2;
/* p1 points to the beginning of the row of targets from the required state
 * in a sparsely stored fsa, and p2 to the location beyond the end.
 * g is the generator number for which we seek the target.
 * If we don't find one, then there isn't one, and we return 0.
 * This only works for dfa's.
 */
{ while (p1 < p2){
    if (*p1 == g)
      return *(p1+1);
    p1+=2;
  }
  return 0;
}

void
fsa_init(fsaptr)
	fsa *fsaptr;
/* Allocate space for the sub-structures of fsaptr, and zero all pointers. */
{ int i;
  fsaptr->initial = 0;
  fsaptr->accepting = 0;
  fsaptr->is_accepting = 0;
  fsaptr->is_initial = 0;
  fsaptr->is_accessible = 0;

  tmalloc(fsaptr->alphabet,srec,1);
  fsaptr->alphabet->names = 0;
  fsaptr->alphabet->words = 0;
  fsaptr->alphabet->wordslist = 0;
  fsaptr->alphabet->intlist = 0;
  fsaptr->alphabet->base = 0;
  fsaptr->alphabet->type = SIMPLE;
  fsaptr->alphabet->size = 0;
  fsaptr->alphabet->labels = 0;
  fsaptr->alphabet->setToLabels = 0;

  tmalloc(fsaptr->states,srec,1);
  fsaptr->states->names = 0;
  fsaptr->states->words = 0;
  fsaptr->states->wordslist = 0;
  fsaptr->states->intlist = 0;
  fsaptr->states->base = 0;
  fsaptr->states->type = SIMPLE;
  fsaptr->states->size = 0;
  fsaptr->states->labels = 0;
  fsaptr->states->setToLabels = 0;

  for (i=0;i<num_kbm_flag_strings;i++)
    fsaptr->flags[i] = FALSE;
  tmalloc(fsaptr->table,table_struc,1);
  fsaptr->table->filename = 0;
  fsaptr->table->table_data_ptr = 0;
  fsaptr->table->ctable_data_ptr = 0;
  fsaptr->table->table_data_dptr = 0;
  fsaptr->table->comment_state_numbers=FALSE;
}

void
fsa_table_init(tableptr,maxstates,ne)
	table_struc *tableptr;
	int maxstates;
	int ne;
/* Intialize the table_data_ptr field of fsaptr->table,
 * for maxstates states, with table-type dense.
 * ne is the size of the alphabet.
 */
{ int i;
  tableptr->maxstates = maxstates;
  tableptr->table_type =  DENSE;
  tmalloc(tableptr->table_data_ptr,int *,ne+1);
  tmalloc(tableptr->table_data_ptr[0],int,maxstates*ne);
  for (i=1; i <= ne; i++)
      tableptr->table_data_ptr[i] =
          tableptr->table_data_ptr[0] + (i-1)*maxstates - 1;
}

void
fsa_set_is_initial(fsaptr)
/* Set the is_initial field in fsa *fsaptr - should be freed after use  */
	fsa *fsaptr;
{ int ns, i;
  ns = fsaptr->states->size;
  tmalloc(fsaptr->is_initial,boolean,ns+1);
  fsaptr->is_initial[0] = FALSE;
  if (fsaptr->num_initial == ns) {
    for (i=1;i<=ns;i++)
      fsaptr->is_initial[i] = TRUE;
  }
  else {
    for (i=1;i<=ns;i++)
      fsaptr->is_initial[i] = FALSE;
    for (i=1;i<=fsaptr->num_initial;i++)
      fsaptr->is_initial[fsaptr->initial[i]] = TRUE;
  }
}
 
void
fsa_set_is_accepting(fsaptr)
/* Set the is_accepting field in fsa *fsaptr - should be freed after use */
	fsa *fsaptr;
{ int ns, i;
  ns = fsaptr->states->size;
  tmalloc(fsaptr->is_accepting,boolean,ns+1);
  fsaptr->is_accepting[0] = FALSE;
  if (fsaptr->num_accepting == ns) {
    for (i=1;i<=ns;i++)
      fsaptr->is_accepting[i] = TRUE;
  }
  else {
    for (i=1;i<=ns;i++)
      fsaptr->is_accepting[i] = FALSE;
    for (i=1;i<=fsaptr->num_accepting;i++)
      fsaptr->is_accepting[fsaptr->accepting[i]] = TRUE;
  }
}
 
void
fsa_set_is_accessible(fsaptr)
/* Set the is_accessible field in fsa *fsaptr - should be freed after use */
	fsa *fsaptr;
{ int ns, ne, ct, i, *gotlist, **table,  j, k, l, *ptr, *ptre; ;

  ns = fsaptr->states->size;
  ne = fsaptr->alphabet->size;

  tmalloc(gotlist,int,ns+1);
  tmalloc(fsaptr->is_accessible,boolean,ns+1);
  table = fsaptr->table->table_data_ptr;
  ct = 0;
  if (fsaptr->num_initial==ns) {
    for (i=1;i<=ns;i++)
      fsaptr->is_accessible[i] = TRUE;
    return;
  }
  for (i=1;i<=ns;i++)
    fsaptr->is_accessible[i] = FALSE;
  for (i=1;i<=fsaptr->num_initial;i++) {
    fsaptr->is_accessible[fsaptr->initial[i]]=TRUE;
    gotlist[++ct] = fsaptr->initial[i];
  }
  for (i=1;i<=ct;i++) {
    k = gotlist[i];
    if (fsaptr->table->table_type == DENSE)
      for (j=1;j<=ne;j++){
        l = table[j][k];
        if (l>0 && !fsaptr->is_accessible[l]) {
          fsaptr->is_accessible[l]=TRUE; gotlist[++ct]=l;
        }
      }
    else {
      ptr=table[k]; ptre=table[k+1];
      while (ptr<ptre) {
        l = *(++ptr);
        if (l>0 && !fsaptr->is_accessible[l]) {
          fsaptr->is_accessible[l]=TRUE; gotlist[++ct]=l;
        }
        ptr++;
      }
    }
  }
  tfree(gotlist);
}

int
fsa_table_dptr_init(fsaptr)
/* Set the field fsaptr->table->table_data_dptr.
 * This is used for fast access to table entries in 2-variable machines.
 */
	fsa *fsaptr;
{ int i, ngens;
  if (fsaptr->alphabet->type!=PRODUCT || fsaptr->alphabet->arity!=2) {
    fprintf(stderr,"Error in fsa_table_dptr_init: fsa must be 2-variable.\n");
     return -1;
  }
  if (fsaptr->table->table_type != DENSE)  {
    fprintf(stderr,
            "Error in fsa_table_dptr_init: storage-type must be dense.\n");
    return -1;
  }
  ngens = fsaptr->alphabet->base->size;
  if (fsaptr->table->table_data_dptr == 0) {
    tmalloc(fsaptr->table->table_data_dptr,int **,ngens+2);
    for (i=1;i<=ngens+1;i++)
      fsaptr->table->table_data_dptr[i] =
                         fsaptr->table->table_data_ptr + (i-1)*(ngens+1);
  }
  return 0;
}

void
srec_clear(srptr)
/* Deallocate all space used by the set-record fsaptr */
	srec *srptr;
{ int i, j;
  if (srptr==0)
    return;
  if ((srptr->type==IDENTIFIERS || srptr->type==STRINGS) && srptr->names){
    for (i=1;i<=srptr->size;i++)
      tfree(srptr->names[i]);
    tfree(srptr->names);
  }
  if (srptr->type==WORDS && srptr->words){
    for (i=1;i<=srptr->size;i++)
      tfree(srptr->words[i]);
    tfree(srptr->words);
  }
  if (srptr->type==LISTOFWORDS && srptr->wordslist) {
      for (i=1;i<=srptr->size;i++) {
        j=0;
        while (srptr->wordslist[i][j]) {
          tfree(srptr->wordslist[i][j]); j++;
        }
        tfree(srptr->wordslist[i]);
      }
    tfree(srptr->wordslist);
  }
  if (srptr->type==LISTOFINTS && srptr->intlist) {
    for (i=1;i<=srptr->size;i++)
      tfree(srptr->intlist[i])
    tfree(srptr->intlist);
  }
  if (srptr->type==PRODUCT && srptr->base){
    srec_clear(srptr->base);
    tfree(srptr->base);
  }
  if (srptr->type==WORDS || srptr->type==LISTOFWORDS)
    for (i=1;i<=srptr->alphabet_size;i++)
      tfree(srptr->alphabet[i]);
  if (srptr->type==LABELED) {
    srec_clear(srptr->labels);
    tfree(srptr->labels);
    tfree(srptr->setToLabels);
  }
}

void
srec_copy(srptr1,srptr2)
	srec *srptr1, *srptr2;
/* Copy the information in *srptr2 to *srptr1 (same way round as strcpy!)
 * It is assumed that srptr1 points to a zeroed set-record.
 */
{ int i, j, l;
  srptr1->type = srptr2->type;
  srptr1->size = srptr2->size;
  if (srptr1->type==IDENTIFIERS || srptr1->type==STRINGS) {
    tmalloc(srptr1->names,char *,srptr1->size+1);
    for (i=1;i<=srptr1->size;i++) {
      tmalloc(srptr1->names[i],char,stringlen(srptr2->names[i])+1);
      strcpy(srptr1->names[i],srptr2->names[i]);
    }
  }
  if (srptr1->type==WORDS) {
    tmalloc(srptr1->words,gen *,srptr1->size+1);
    for (i=1;i<=srptr1->size;i++) {
      tmalloc(srptr1->words[i],gen,genstrlen(srptr2->words[i])+1);
      genstrcpy(srptr1->words[i],srptr2->words[i]);
    }
  }
  if (srptr1->type==LISTOFWORDS) {
    tmalloc(srptr1->wordslist,gen **,srptr1->size+1);
    for (i=1;i<=srptr1->size;i++) {
      /* First find length of srptr2->wordslist[i] */
      l=0;
      while (srptr2->wordslist[i][l])
        l++;
      tmalloc(srptr1->wordslist[i],gen *,l+1);
      for (j=0;j<l;j++) {
        tmalloc(srptr1->wordslist[i][j],gen,
			genstrlen(srptr2->wordslist[i][j])+1);
        genstrcpy(srptr1->wordslist[i][j],srptr2->wordslist[i][j]);
      }
      srptr1->wordslist[i][l]=0;
    }
  }
  if (srptr1->type==LISTOFINTS) {
    tmalloc(srptr1->intlist,int *,srptr1->size+1);
    for (i=1;i<=srptr1->size;i++) {
      l=srptr2->intlist[i][0];
      tmalloc(srptr1->intlist[i],int,l+1);
      for (j=0;j<=l;j++) {
        srptr1->intlist[i][j] = srptr2->intlist[i][j];
      }
    }
  }
  if (srptr1->type==WORDS || srptr1->type==LISTOFWORDS) {
    srptr1->alphabet_size = srptr2->alphabet_size;
    for (i=1;i<=srptr1->alphabet_size;i++) {
      tmalloc(srptr1->alphabet[i],char,stringlen(srptr2->alphabet[i])+1);
      strcpy(srptr1->alphabet[i],srptr2->alphabet[i]);
    }
  }
  if (srptr1->type==PRODUCT) {
    tmalloc(srptr1->base,srec,1);
    srec_copy(srptr1->base,srptr2->base);
    srptr1->arity = srptr2->arity;
    srptr1->padding = srptr2->padding;
  }
  if (srptr1->type==LABELED) {
    tmalloc(srptr1->labels,srec,1);
    srec_copy(srptr1->labels,srptr2->labels);
    tmalloc(srptr1->setToLabels,setToLabelsType,srptr1->size+1);
    for (i=1;i<=srptr1->size;i++)
      srptr1->setToLabels[i] = srptr2->setToLabels[i];
  }
}


void
table_copy(tableptr1,tableptr2,ne,ns)
	table_struc *tableptr1, *tableptr2;
	int ne, ns;
/* Copy the information in *tableptr2 to *tableptr1 (same way round as strcpy!)
 * It is assumed that tableptr1 points to a zeroed table_struc.
 * ne and ns are the sizes of the alphabet and state-set.
 */
{ int i, j, maxstates, dr, space, *row1, *row2, *ptr1, *ptr2, *ptr2e;
  if (tableptr2->filename) {
    tmalloc(tableptr1->filename,char,stringlen(tableptr2->filename)+1);
    strcpy(tableptr1->filename,tableptr2->filename);
  }
  tableptr1->table_type = tableptr2->table_type;
  tableptr1->printing_format = tableptr2->printing_format;
  tableptr1->comment_state_numbers = tableptr2->comment_state_numbers;
  tableptr1->numTransitions = tableptr2->numTransitions;
  dr = 
  tableptr1->denserows = tableptr2->denserows;
  maxstates =
  tableptr1->maxstates = tableptr2->maxstates;
  
  if (tableptr1->table_type == DENSE) {
    tmalloc(tableptr1->table_data_ptr,int *,ne+1);
    tmalloc(tableptr1->table_data_ptr[0],int,ne*maxstates);
    for (i=1; i <= ne; i++) {
      row2 = tableptr2->table_data_ptr[i];
      row1 = tableptr1->table_data_ptr[i] =
          tableptr1->table_data_ptr[0] + (i-1)*maxstates - 1;
      for (j=1;j<=ns;j++)
        row1[j] = row2[j];
    }
  }
  else {
    tmalloc(tableptr1->table_data_ptr,int *,ns+2);
    if (dr>0) {
      tmalloc(tableptr1->table_data_ptr[0],int,ne*dr);
      for (i=1; i <= dr; i++) {
        row2 = tableptr2->table_data_ptr[i];
        row1 = tableptr1->table_data_ptr[i] =
          tableptr1->table_data_ptr[0] + (i-1)*ne - 1;
        for (j=1;j<=ne;j++)
          row1[j] = row2[j];
      }
      if (ns>dr) {
        space =
           tableptr2->table_data_ptr[ns+1]-tableptr2->table_data_ptr[dr+1];
        tmalloc(tableptr1->table_data_ptr[dr+1],int,space+1);
        ptr1 = tableptr1->table_data_ptr[dr+1];
      }
    }
    else {
      space = tableptr2->table_data_ptr[ns+1]-tableptr2->table_data_ptr[0];
      tmalloc(tableptr1->table_data_ptr[0],int,space+1);
      ptr1 = tableptr1->table_data_ptr[0];
    }
    if (ns>dr) {
      ptr2 = tableptr2->table_data_ptr[dr+1];
      for (i=dr+1;i<=ns;i++) {
        tableptr1->table_data_ptr[i] = ptr1;
        ptr2e = tableptr2->table_data_ptr[i+1];
        while (ptr2 < ptr2e)
          *(ptr1++) = *(ptr2++);
      }
      tableptr1->table_data_ptr[ns+1] = ptr1;
    }
  }
}


void
fsa_copy(fsaptr1,fsaptr2)
	fsa *fsaptr1, *fsaptr2;
/* Copy the information in *fsaptr2 to *fsaptr1 (same way round as strcpy!)
 * It is assumed that fsaptr1 points to a zeroed fsa.
 */
{ int i, ne, ns;
  fsa_init(fsaptr1);
  srec_copy(fsaptr1->alphabet,fsaptr2->alphabet);
  srec_copy(fsaptr1->states,fsaptr2->states);
  ne = fsaptr1->alphabet->size;
  ns = fsaptr1->states->size;

  fsaptr1->num_initial = fsaptr2->num_initial;
  tmalloc(fsaptr1->initial,int,fsaptr1->num_initial+1);
  for (i=1;i<=fsaptr1->num_initial;i++)
    fsaptr1->initial[i] = fsaptr2->initial[i];

  fsaptr1->num_accepting = fsaptr2->num_accepting;
  if (ns==1 || fsaptr1->num_accepting!=ns) {
    tmalloc(fsaptr1->accepting,int,fsaptr1->num_accepting+1);
    for (i=1;i<=fsaptr1->num_accepting;i++)
      fsaptr1->accepting[i] = fsaptr2->accepting[i];
  }

  for (i=0;i<num_kbm_flag_strings;i++)
    fsaptr1->flags[i] = fsaptr2->flags[i];

  table_copy(fsaptr1->table,fsaptr2->table,ne,ns);
}

void
table_clear(tableptr,ns)
/* Deallocate all space used by the table-struc fsaptr */
	table_struc *tableptr;
	int ns;
{
  if (tableptr==0)
    return;
  tfree(tableptr->filename);
  if (tableptr->table_data_ptr) {
    tfree(tableptr->table_data_ptr[0]);
    if (tableptr->table_type==SPARSE &&
                            tableptr->denserows>0 && tableptr->denserows<ns)
      tfree(tableptr->table_data_ptr[tableptr->denserows+1]);
    tfree(tableptr->table_data_ptr);
    tfree(tableptr->ctable_data_ptr);
    tfree(tableptr->table_data_dptr);
  }
}

void
fsa_clear(fsaptr)
/* Deallocate all space used by the fsa *fsaptr */
	fsa	*fsaptr;
{ int ns;
  if (fsaptr==0)
    return;
  srec_clear(fsaptr->states);
  tfree(fsaptr->states);
  srec_clear(fsaptr->alphabet);
  tfree(fsaptr->alphabet);
  tfree(fsaptr->initial);
  tfree(fsaptr->accepting);
  tfree(fsaptr->is_accepting);
  tfree(fsaptr->is_initial);
  tfree(fsaptr->is_accessible);
  ns = fsaptr->states ? fsaptr->states->size : 0;
  table_clear(fsaptr->table,ns);
  tfree(fsaptr->table);
}

int
fsa_delete_state(fsaptr,stateno)
/* Delete state number stateno from the fsa *fsaptr - works for all fsa's.
 * Warning - the arrays fsaptr->is_initial, is_accepting and is_accessible
 * are not updated!
 */
	fsa     *fsaptr;
	int	stateno;
{ int ns, ne, **table, *ptr, *ptr2, *ptr2e, i, j, k, l;
  srec *srptr;

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
"Sorry: fsa_delete_state not available for sparse storage with dense rows.\n");
     return -1;;
  }

  if (kbm_print_level>=3)
    printf("    #Calling fsa_delete_state on state number %d.\n",stateno);
  ne = fsaptr->alphabet->size;
  srptr = fsaptr->states;
  ns = srptr->size;
  if (stateno<=0 || stateno>ns){
    fprintf(stderr,"Error in fsa_delete_stateno - invalid state number.\n");
     return -1;;
  }
  if (srptr->type==IDENTIFIERS || srptr->type==STRINGS){
    tfree(srptr->names[stateno]);
    for (i=stateno;i<ns;i++)
      srptr->names[i] = srptr->names[i+1];
    srptr->names[ns]=0;
  }
  if (srptr->type==WORDS){
    tfree(srptr->words[stateno]);
    for (i=stateno;i<ns;i++)
      srptr->words[i] = srptr->words[i+1];
    srptr->words[ns]=0;
  }
  if (srptr->type==LISTOFWORDS){
    j=0;
    while (srptr->wordslist[stateno][j]) {
      tfree(srptr->wordslist[stateno][j]); j++;
    }
    tfree(srptr->wordslist[stateno]);
    for (i=stateno;i<ns;i++)
      srptr->wordslist[i] = srptr->wordslist[i+1];
    srptr->wordslist[ns]=0;
  }
  if (srptr->type==LISTOFINTS){
    tfree(srptr->intlist[stateno]);
    for (i=stateno;i<ns;i++)
      srptr->intlist[i] = srptr->intlist[i+1];
    srptr->intlist[ns]=0;
  }
  if (srptr->type==LABELED)
    for (i=stateno;i<ns;i++)
      srptr->setToLabels[i] = srptr->setToLabels[i+1];

  for (i=1;i<=fsaptr->num_initial;i++){
    k = fsaptr->initial[i];
    if (k==stateno){
      for (j=i;j<fsaptr->num_initial;j++) {
        l = fsaptr->initial[j+1];
        fsaptr->initial[j] = l>stateno ? l-1 : l;
      }
      fsaptr->num_initial--;
      break;
    }
    else if (k>stateno)
      fsaptr->initial[i] = k-1;
  }

  if (fsaptr->num_accepting==ns) {
    fsaptr->num_accepting--;
    if (ns==2) {
      tmalloc(fsaptr->accepting,int,2);
      fsaptr->accepting[1] = 1;
    }
  }
  else
    for (i=1;i<=fsaptr->num_accepting;i++) {
      k = fsaptr->accepting[i];
      if (k==stateno){
        for (j=i;j<fsaptr->num_accepting;j++){
          l = fsaptr->accepting[j+1];
          fsaptr->accepting[j] = l>stateno ? l-1 : l;
        }
        fsaptr->num_accepting--;
        break;
      }
      else if (k>stateno)
        fsaptr->accepting[i] = k-1;
    }
  
  fsaptr->flags[NFA] = FALSE;
  fsaptr->flags[ACCESSIBLE] = FALSE;
  fsaptr->flags[TRIM] = FALSE;
  fsaptr->flags[BFS] = FALSE;
  fsaptr->flags[MINIMIZED] = FALSE;

  table = fsaptr->table->table_data_ptr;
  if (fsaptr->table->table_type==DENSE){
    for (j=1;j<=ne;j++) {
      for (i=1;i<stateno;i++)
        if (table[j][i] > stateno)
          table[j][i]--;
        else if (table[j][i] == stateno)
          table[j][i]=0;
      for (i=stateno;i<ns;i++) {
         k=table[j][i+1];
         table[j][i] = k<stateno ? k : k==stateno ? 0 : k-1;
      }
    }
  }
  else {
    ptr = fsaptr->table->table_data_ptr[0];
    ptr2 = ptr;
    for (i=1;i<stateno;i++) {
      table[i] = ptr;
      ptr2e = table[i+1];
      while (ptr2<ptr2e){
        if (*(ptr2+1) != stateno) {
          *(ptr++) = *(ptr2++);
          *(ptr++) = *ptr2>stateno ? *ptr2-1 : *ptr2;
          *ptr2++;
        }
        else
          ptr2+=2;
      }
    }
    ptr2 = table[stateno+1];
    for (i=stateno;i<ns;i++) {
      table[i] = ptr;
      ptr2e = table[i+2];
      while (ptr2<ptr2e){
        if (*(ptr2+1) != stateno) {
          *(ptr++) = *(ptr2++);
          *(ptr++) = *ptr2>stateno ? *ptr2-1 : *ptr2;
          *ptr2++;
        }
        else
          ptr2+=2;
      }
    }
    table[ns] = ptr;
  }
  fsaptr->states->size--;
  return 0;
}

int
fsa_permute_states(fsaptr,perm)
/* permute the states of fsa *fsaptr, using perm - works for all fsa's
 * perm should be a permutation of the integers 1 to ns - this is not checked
 * Warning - the arrays fsaptr->is_initial, is_accepting and is_accessible
 * are not updated.
 * ALSO - perm[0] should be 0 !!
 */
	fsa     *fsaptr;
	int	*perm;
{ int ns, ne, *newtable, **newtableptr, **table, *perminv,
      *ptr, *ptr2, *ptr2e, i, j;
  srec *srptr;
  char ** newnames;
  gen ** newwords;
  gen *** newwordslist;
  int ** newintlist;
  setToLabelsType *newsetToLabels;

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
"Sorry: fsa_permute_state not available for sparse storage with dense rows.\n");
    return -1;
  }
  if (kbm_print_level>=3)
    printf("    #Calling fsa_permute_states.\n");
  perm[0] = 0; /* let's make sure! */
  ne = fsaptr->alphabet->size;
  srptr = fsaptr->states;
  ns = srptr->size;
  if (srptr->type==IDENTIFIERS || srptr->type==STRINGS){
    tmalloc(newnames,char *,ns+1);
    for (i=1;i<=ns;i++)
      newnames[perm[i]] = srptr->names[i];
    tfree(srptr->names);
    srptr->names = newnames;
  }
  if (srptr->type==WORDS){
    tmalloc(newwords,gen *,ns+1);
    for (i=1;i<=ns;i++)
      newwords[perm[i]] = srptr->words[i];
    tfree(srptr->words);
    srptr->words = newwords;
  }
  if (srptr->type==LISTOFWORDS){
    tmalloc(newwordslist,gen **,ns+1);
    for (i=1;i<=ns;i++)
      newwordslist[perm[i]] = srptr->wordslist[i];
    tfree(srptr->wordslist);
    srptr->wordslist = newwordslist;
  }
  if (srptr->type==LISTOFINTS){
    tmalloc(newintlist,int *,ns+1);
    for (i=1;i<=ns;i++)
      newintlist[perm[i]] = srptr->intlist[i];
    tfree(srptr->intlist);
    srptr->intlist = newintlist;
  }
  if (srptr->type==LABELED) {
    tmalloc(newsetToLabels,setToLabelsType,ns+1);
    for (i=1;i<=ns;i++)
      newsetToLabels[perm[i]] = srptr->setToLabels[i];
    tfree(srptr->setToLabels);
    srptr->setToLabels = newsetToLabels;
  }

  if (fsaptr->num_initial!=ns) {
    tmalloc(fsaptr->is_initial,boolean,ns+1);
    for (i=1;i<=ns;i++)
      fsaptr->is_initial[i]=FALSE;
    for (i=1;i<=fsaptr->num_initial;i++)
      fsaptr->is_initial[perm[fsaptr->initial[i]]]=TRUE;
    j=0;
    for (i=1;i<=ns;i++) if (fsaptr->is_initial[i])
      fsaptr->initial[++j]=i;
    tfree(fsaptr->is_initial);
  }

  if (fsaptr->num_accepting!=ns) {
    tmalloc(fsaptr->is_accepting,boolean,ns+1);
    for (i=1;i<=ns;i++)
      fsaptr->is_accepting[i]=FALSE;
    for (i=1;i<=fsaptr->num_accepting;i++)
      fsaptr->is_accepting[perm[fsaptr->accepting[i]]]=TRUE;
    j=0;
    for (i=1;i<=ns;i++) if (fsaptr->is_accepting[i])
      fsaptr->accepting[++j]=i;
    tfree(fsaptr->is_accepting);
  }

  fsaptr->flags[BFS] = FALSE;

  table = fsaptr->table->table_data_ptr;
  if (fsaptr->table->table_type==DENSE){
    perm[0] = 0; /* just to make sure! */
    tmalloc(newtable,int,ns*ne);
    for (j=1;j<=ne;j++) {
      ptr = newtable + (j-1)*ns - 1;
      for (i=1;i<=ns;i++)
        ptr[perm[i]] = perm[table[j][i]];
      table[j] = ptr;
    }
    tfree(fsaptr->table->table_data_ptr[0]);
    fsaptr->table->table_data_ptr[0]  = newtable;
  }
  else {
/* We need the inverse of perm in this case */
    tmalloc(perminv,int,ns+1);
    for (i=1;i<=ns;i++)
      perminv[perm[i]] = i;
    tmalloc(newtable,int,table[ns+1]-table[1]);
    tmalloc(newtableptr,int *,ns+2);
    ptr = newtable;
    for (i=1;i<=ns;i++) {
      newtableptr[i] = ptr;
      ptr2 = table[perminv[i]];
      ptr2e = table[perminv[i]+1];
      while (ptr2<ptr2e){
        *(ptr++) = *(ptr2++);
        *(ptr++) = perm[*(ptr2++)];
      }
    }
    newtableptr[ns+1] = ptr;
    tfree(perminv);
    tfree(fsaptr->table->table_data_ptr[0]);
    tfree(fsaptr->table->table_data_ptr);
    fsaptr->table->table_data_ptr = newtableptr;
    fsaptr->table->table_data_ptr[0] = newtable;
  }
  return 0;
}

int
fsa_clear_rws(fsaptr)
/* If *fsaptr is an rws (rewriting-system) automaton, then it may have
 * negative targets, which point to reduction equations.
 * This function simply replaces all of these targets by 0, to make it
 * into a conventional fsa.
 */
	fsa *fsaptr;
{ int ns, ne, **table, *ptr, *ptr2, *ptr2e, i, j;

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
    "Sorry: fsa_clear_rws not available for sparse storage with dense rows.\n");
    return -1;
  }
  if (fsaptr->flags[RWS]==FALSE)
    return 0;

  ne = fsaptr->alphabet->size;
  ns = fsaptr->states->size;

  table = fsaptr->table->table_data_ptr;
  if (fsaptr->table->table_type == DENSE) {
    for (j=1;j<=ne;j++) for (i=1;i<=ns;i++)
      if (table[j][i]<0)
        table[j][i] = 0;
  }
  else {
    ptr = table[1];
    for (i=1;i<=ns;i++) {
      ptr2 = table[i]; ptr2e = table[i+1];
      table[i] = ptr;
      while (ptr2 < ptr2e) {
        if (*(ptr2+1) > 0) {
          *(ptr++) = *(ptr2++); *(ptr++) = *(ptr2++);
        }
        else
          ptr2 += 2;
      }
    }
    table[ns+1] = ptr;
  }

  fsaptr->flags[RWS]=FALSE;
  return 0;
}

int
fsa_make_accessible(fsaptr)
/* Make the fsa *fsaptr accessible - i.e. all states reachable from start-state
 */
        fsa     *fsaptr;
{ int ns, i;
  storage_type st = fsaptr->table->table_type;
  fsa *temp;

  if (st==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
"Sorry: fsa_make_accessible unavailable for sparse storage with dense rows.\n");
    return -1;
  }
  if (kbm_print_level>=3)
    printf("    #Calling fsa_make_accessible.\n");
  if (fsaptr->flags[MINIMIZED] || fsaptr->flags[ACCESSIBLE]
                               || fsaptr->flags[TRIM])
    return 0;

  if (fsaptr->flags[RWS])
    fsa_clear_rws(fsaptr);

  ns = fsaptr->states->size;

  if (fsaptr->num_initial==ns){
    fsaptr->flags[ACCESSIBLE] = TRUE;
    return 0;
  }

/* In the deterministic case, we do it by and-ing it with itself - should write
 * separate code for this really, but it hardly seems worth it.
 * This works faster than deleting redundant states.
 */
  if (fsaptr->flags[DFA] && fsaptr->states->type!=LABELED) {
    temp = fsa_and(fsaptr,fsaptr,st,TRUE,"/tmp/fsa_and_xxx");
    fsa_copy(fsaptr,temp);
    fsa_clear(temp);
    tfree(temp);
    return 0;
  }
    
/* Now find the list of states accessible from the start-state. */
  fsa_set_is_accessible(fsaptr);

/* Now delete inaccessible states */
  for (i=ns;i>=1;i--) if (!fsaptr->is_accessible[i])
    fsa_delete_state(fsaptr,i);

  tfree(fsaptr->is_accessible);
  return 0;
}

int
fsa_minimize(fsaptr)
	fsa	*fsaptr;
/* Minimize the fsa *fsaptr. */
{ int *block_numa, *block_numb, *block_swap, i, j, k, l, len,
       *ptr, *ptr2, *ptr2e, *ht_ptr,
       ne, ns_orig, **table, ns_final, ns_new, num_iterations;
  hash_table ht;
  boolean fixed, acc;

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
"Sorry: fsa_minimize unavailable for sparse storage with dense rows.\n");
    return -1;
  }

  if (kbm_print_level>=3)
    printf("    #Calling fsa_minimize.\n");
  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_minimize only applies to DFA's.\n");
    return -1;
  }
  if (fsaptr->flags[MINIMIZED])
    return 0;

  if (fsaptr->flags[RWS])
    fsa_clear_rws(fsaptr);

  acc = fsaptr->flags[ACCESSIBLE]  || fsaptr->flags[TRIM];
  if (!acc)
    fsa_set_is_accessible(fsaptr);

  ns_orig = fsaptr->states->size;
  if (ns_orig==0) {
    fsaptr->flags[TRIM] = TRUE;
    fsaptr->flags[MINIMIZED] = TRUE;
    tfree(fsaptr->is_accessible);
    return 0;
  }

  /* First throw away any existing structure on the state-set. */
  srec_clear(fsaptr->states);
  fsaptr->states->type = SIMPLE;
  ne = fsaptr->alphabet->size;
  table = fsaptr->table->table_data_ptr;

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
      if (block_numb[i]== -1) return -1;
    }
    else block_numb[i]=0;
    ns_new = ht.num_recs;
    block_swap=block_numa; block_numa=block_numb; block_numb=block_swap;
    if (ns_new > ns_final)
      hash_clear(&ht);
  } while (ns_new > ns_final);
  
  if (kbm_print_level>=4) { /* print out old-new state correspondence */
     printf("Old State   NewState\n");
     for (i=1;i<=ns_orig;i++)
       printf("   %6d     %6d\n",i,block_numa[i]);
  }
     
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
    tfree(fsaptr->table->table_data_ptr[0]);
    tfree(fsaptr->table->table_data_ptr);
  }
  else if (ns_final<ns_orig) {
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
fsa_labeled_minimize(fsaptr)
	fsa	*fsaptr;
/* This is the minimization function for fsa's which might have more than
 * two categories of states. 
 * We use the labeled set-record type to identify the categories, so *fsaptr
 * must have state-set of labeled type.
 * The accepting states should be a union of some of the state
 * categories, or else the accepting states of the result will be
 * meaningless!
 */
{ int *block_numa, *block_numb, *block_swap, i, j, k, l, len,
       *ptr, *ptr2, *ptr2e, *ht_ptr,
       ne, ns_orig, **table, ns_final, ns_new, num_iterations;
  hash_table ht;
  boolean fixed, *occurs, acc;

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
"Sorry: fsa_labeled_minimize unavailable for sparse storage with dense rows.\n"
     );
    return -1;
  }
  if (kbm_print_level>=3)
    printf("    #Calling fsa_labeled_minimize.\n");
  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_labeled_minimize only applies to DFA's.\n");
    return -1;
  }

  if (fsaptr->states->type != LABELED) {
    fprintf(stderr,
        "Error: in fsa_labeled_minimize state-set must have type labeled.\n");
    return -1;
  }

  if (fsaptr->flags[RWS])
    fsa_clear_rws(fsaptr);

  acc = fsaptr->flags[ACCESSIBLE]  || fsaptr->flags[TRIM];
  if (!acc)
    fsa_set_is_accessible(fsaptr);

  ne = fsaptr->alphabet->size;
  table = fsaptr->table->table_data_ptr;
  ns_orig = fsaptr->states->size;
  if (ns_orig==0) {
    tfree(fsaptr->is_accessible);
    return 0;
  }

/* Start with block_numa equal to the subdivision defined by the labeling.  */
  tmalloc(occurs,boolean,fsaptr->states->labels->size+1);
  for (i=1;i<=fsaptr->states->labels->size;i++)
    occurs[i] = FALSE;
  tmalloc(block_numa,int,ns_orig+1);
  tmalloc(block_numb,int,ns_orig+1);
  for (i=0;i<=ns_orig;i++)
    block_numb[i]=0;
  ns_new = 0;
  block_numa[0] = 0; /* The zero state is always regarded as having label 0 */
  for (i=1;i<=ns_orig;i++) if (acc || fsaptr->is_accessible[i]){
    j = fsaptr->states->setToLabels[i];
    if (j>0 && !occurs[j]) {
      occurs[j] = TRUE;
      ns_new++;
    }
    block_numa[i] = j;
  }
  else block_numa[i] = 0;
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
      if (block_numb[i]== -1) return -1;
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
fsa_bfs(fsaptr)
	fsa	*fsaptr;
/* Put the fsa *fsapt into bfs form. */
{  int ns, ne, *perm, *perminv, **table, ct, i, j, s, t;
   boolean *got, dense;

  if (fsaptr->table->table_type==SPARSE && fsaptr->table->denserows>0) {
    fprintf(stderr,
"Sorry: fsa_bfs unavailable for sparse storage with dense rows.\n");
    return -1;
  }
  if (kbm_print_level>=3)
    printf("    #Calling fsa_bfs.\n");
  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_bfs only applies to DFA's.\n");
    return -1;
  }
  if (fsaptr->flags[BFS])
    return 0;

  fsa_make_accessible(fsaptr);

  if (fsaptr->flags[RWS])
    fsa_clear_rws(fsaptr);

  ne = fsaptr->alphabet->size;
  ns = fsaptr->states->size;
  if (ns==0)
    return 0;
 
  dense = fsaptr->table->table_type == DENSE;
  table = fsaptr->table->table_data_ptr;

  tmalloc(got,boolean,ns+1);
  for (i=1;i<=ns;i++)
    got[i] = FALSE;
  tmalloc(perm,int,ns+1);
  perm[0] = 0;
  perm[1] = fsaptr->initial[1];
  got[perm[1]] = TRUE;
  ct = 1;
  i = 1;
  while (i<=ct) {
    s = perm[i];
    for (j=1;j<=ne;j++) {
      t = target(dense,table,j,s,0);
      if (t>0 && !got[t]) {
        perm[++ct] = t;
        got[t] = TRUE;
      }
    }
    i++;
  }

  tfree(got);
/* The inverse of perm is what is required */
  tmalloc(perminv,int,ns+1);
  for (i=0;i<=ns;i++)
    perminv[perm[i]] = i;
  tfree(perm);
  fsa_permute_states(fsaptr,perminv);
  tfree(perminv);
  fsaptr->flags[BFS]=TRUE;
  return 0;
}

int
fsa_count(fsaptr)
	fsa *fsaptr;
/* Count the size of the accepted language of the fsa *fsaptr.
 * Return this size, or -2 if infinite.
 */
{ int i, j, ct, ne, ns, **table, dr,
      *in_degree, *ordered_state_list, *num_acc_words, cstate, im;
  boolean dense;

  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_count only applies to DFA's.\n");
    return -1;
  }
  if (!fsaptr->flags[TRIM])
    if (fsa_minimize(fsaptr)== -1) return -1;

  ne = fsaptr->alphabet->size;
  ns = fsaptr->states->size;
  if (ns==0)
    return 0;

  dr = fsaptr->table->denserows;

/* We first count the number of edges going into each state */
  tmalloc(in_degree,int,ns+1);
  for (i=1;i<=ns;i++)
    in_degree[i] = 0;
  dense = fsaptr->table->table_type==DENSE;
  table = fsaptr->table->table_data_ptr;
  for (i=1;i<=ns;i++) for (j=1;j<=ne;j++) {
    im = target(dense,table,j,i,dr);
    if (im>0)
      in_degree[im]++;
  }

/* Now we try to order the states so that if state s <= state t, then there
 * is no path from state t to state s. If this is not possible, then the
 * accepted language must be infinite.
 */
  cstate = fsaptr->initial[1];
  if (in_degree[cstate] > 0) {
    tfree(in_degree);
    return -2;
  }
  tmalloc(ordered_state_list,int,ns+1);
  ordered_state_list[1] = cstate;

  ct = 1;
  i = 0;
  while (++i<=ct) {
    cstate = ordered_state_list[i];
    for (j=1;j<=ne;j++) {
      im = target(dense,table,j,cstate,dr);
      if (im>0) {
        in_degree[im]--;
        if (in_degree[im]==0) 
          ordered_state_list[++ct] = im;
      }
    }
  }

  if (ct!=ns) {
    tfree(in_degree) tfree(ordered_state_list)
    return -2;
  }

/* We have built the list, so the accepted language is finite. Now we work
 * backwards through the list, calculating the number of accepted words
 * starting at that state.
 * We might as well use the same space as was used by in_degree, which
 * is no longer needed.
 */
  fsa_set_is_accepting(fsaptr);
  num_acc_words = in_degree;
  for (i=ns;i>=1;i--) {
    cstate = ordered_state_list[i];
    num_acc_words[cstate] = 0;
    for (j=1;j<=ne;j++) {
      im = target(dense,table,j,cstate,dr);
      if (im>0)
        num_acc_words[cstate] += num_acc_words[im];
    }
    if (fsaptr->is_accepting[cstate])
      num_acc_words[cstate]++;
  }

  ct = num_acc_words[fsaptr->initial[1]];
  tfree(in_degree) tfree(ordered_state_list) tfree(fsaptr->is_accepting)
  return ct;
}

int
fsa_enumerate(wfile,fsaptr,min,max,putcomma,stateno)
	FILE *wfile;
	fsa *fsaptr;
	int min, max;
	boolean putcomma;
	int stateno;
/* Enumerate the subset of the language of the finite state automaton *fsaptr,
 * consisting of those words having length l satisfying min <= l <= max.
 * Since there is no point in storing these words currently, they are
 * printed out to the file wfile, with all but the last one to be printed
 * followed by a comma and carriage return.
 * 1 is returned if some words are found - otherwise 0.
 * If putcomma is true, then the first word to be printed is preceded by comma
 * and carriage-return (to handle the case when this function is called
 * repeatedly).
 * If stateno is 1, then the number of the accept state reched by an
 * accepted word is printed.
 * If stateno is 2, then fsaptr->states should have type 'labeled', and
 * the labels of the accept-states reached by the words are printed.
 */
{ int i, g1, g2, ne, ngens, ngens1, **table, dr,
      *cword, firste, clength, clength1, clength2, cstate, im, *statelist;
  boolean dense, done, backtrack, foundword, prod, numbers;
  gen *cword1, *cword2;
  char **names;

  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_enumerate only applies to DFA's.\n");
    return -1;
  }

  if (stateno==2 && fsaptr->states->type != LABELED) {
    fprintf(stderr,
        "Error: in fsa_enumerate state-set must have type labeled.\n");
    return -1;
  }

  if (fsaptr->num_initial==0)
    return 0;

  ne = fsaptr->alphabet->size;

  dr = fsaptr->table->denserows;

  dense = fsaptr->table->table_type==DENSE;
  table = fsaptr->table->table_data_ptr;

  tmalloc(cword,int,max+1);
  /* to hold the current word in the enumeration */

/* "names" will be used to store the symbols used for printing. If no natural
 * names are available, then we just use the numbers of the edges.
 */
  prod = fsaptr->alphabet->type==PRODUCT;
  if (prod) {
    if (fsaptr->alphabet->arity!=2){
      fprintf(stderr,
	"Sorry  can only cope with two-variable product alphabets.\n");
      return 0;
    }
    ngens = fsaptr->alphabet->base->size;
    ngens1 = ngens+1;
    numbers = fsaptr->alphabet->base->type==SIMPLE ||
              fsaptr->alphabet->base->type==LABELED ||
              fsaptr->alphabet->base->type==WORDS ||
              fsaptr->alphabet->base->type==LISTOFWORDS ||
              fsaptr->alphabet->base->type==LISTOFINTS;
    if (!numbers){
      names = fsaptr->alphabet->base->names;
      tmalloc(names[ngens1],char,2);
      strcpy(names[ngens1],"_");
    }
    tmalloc(cword1,gen,max+1); tmalloc(cword2,gen,max+1);
   /* These are used for the two components of the word cword = [cword1,cword2].
    */
  }
  else {
    numbers = fsaptr->alphabet->type==SIMPLE ||
	      fsaptr->alphabet->type==LABELED ||
              fsaptr->alphabet->type==WORDS ||
              fsaptr->alphabet->type==LISTOFWORDS ||
	      fsaptr->alphabet->type==LISTOFINTS;
    if (!numbers)
        names = fsaptr->alphabet->names;
  }
  if (numbers) { /* define the integral names. */
    tmalloc(names,char *,ne+1);
    for (i=1;i<=ne;i++) {
      tmalloc(names[i],char,int_len(i)+1);
      sprintf(names[i],"%d",i);
    }
  }

  *kbm_buffer = '\0';
  tmalloc(statelist,int,max+1);
 /* this is used to store the state history on scanning the current word. */
  for (i=0;i<=max;i++)
    cword[i] = 0;
  clength = 0;
  statelist[0] = fsaptr->initial[1];
  fsa_set_is_accepting(fsaptr);
  done = FALSE;
  foundword=FALSE;
/* Backtrack search can now begin */
  while (!done) {
  /* first see if we want the current word - if so, print it */
    if (clength>=min && fsaptr->is_accepting[statelist[clength]]) {
      if (putcomma || foundword)
        fprintf(wfile,",\n");
      if (stateno) add_to_buffer(0,"[");
      foundword = TRUE;
      if (prod) { /* split word into components and print them */
        clength1 = clength2 = 0;
        for (i=0;i<clength;i++) {
          g1 = (cword[i]-1)/ngens1 + 1; g2 = (cword[i]-1)%ngens1 + 1;
          /*if (g1<ngens1)*/ cword1[clength1++] = g1;
          /*if (g2<ngens1)*/ cword2[clength2++] = g2;
        }
        cword1[clength1] = 0; cword2[clength2] = 0;
        add_to_buffer(0," [");
        add_word_to_buffer(wfile,cword1,names);
        add_to_buffer(0,",");
        add_word_to_buffer(wfile,cword2,names);
        add_to_buffer(0,"]");
      }
      else {
        add_to_buffer(0," ");
        add_iword_to_buffer(wfile,cword,names);
      }
      if (stateno==1)
        sprintf(kbm_buffer+stringlen(kbm_buffer),",%d]",statelist[clength]);
      if (stateno==2)
        sprintf(kbm_buffer+stringlen(kbm_buffer),",%d]",
                fsaptr->states->setToLabels[statelist[clength]]);

      fprintf(wfile,"%s",kbm_buffer);
      *kbm_buffer = '\0';
    }
  /* Now proceed to next word in the search */
    firste = 1;
    backtrack = TRUE;
    while (backtrack && !done) {
      if (clength<max) {
        cstate = statelist[clength];
        i = firste-1;
        while (backtrack && ++i<=ne) 
          if ((im =target(dense,table,i,cstate,dr)) > 0) { /* found next node */
            cword[clength++] = i;
            statelist[clength] = im;
            backtrack = FALSE;
          }
      }
      if (backtrack) {
        if (clength==0)
          done = TRUE;
        else {
          firste = cword[--clength]+1;
          cword[clength] = 0;
        }
      }
    }
  }
  
  if (numbers) {
    for (i=1;i<=ne;i++) tfree(names[i]);
    tfree(names);
  }
  tfree(fsaptr->is_accepting);
  tfree(cword);
  if (prod) {
    tfree(cword1); tfree(cword2);
  }
  tfree(statelist);

  return (int)foundword;
}

int
fsa_swap_coords(fsaptr)
        fsa *fsaptr;
/* *fsaptr must be a two-variable fsa, in dense format. This routine
 * alters *fsaptr by swapping the variable. That is it replaces transitions
 * s - (a,b) -> t  by  s - (b,a) -> t, for a,b in the base-alphabet.
 */
{ int  ***dtable, ngens1, ns, g1, g2, st, st1, st2;

  if (kbm_print_level>=3)
    printf("    #Calling fsa_swap_coords.\n");
  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_swap_coords only applies to DFA's.\n");
    return -1;
  }

  if (fsaptr->alphabet->type != PRODUCT || fsaptr->alphabet->arity != 2) {
    fprintf(stderr,"Error in fsa_swap_coords: fsa must be 2-variable.\n");
    return -1;
  }
 
  if (fsaptr->table->table_type!=DENSE) {
     fprintf(stderr,
 "Error: function fsa_swap_coords must be called with a densely-stored fsa.\n");
     return -1;
  }

  fsaptr->flags[BFS] = FALSE;
  fsa_table_dptr_init(fsaptr);
  ns = fsaptr->states->size;
  ngens1 = fsaptr->alphabet->base->size + 1;
  dtable = fsaptr->table->table_data_dptr;

  for (st=1;st<=ns;st++) {
    for (g1=1;g1<=ngens1;g1++) for (g2=1;g2<g1;g2++) {
      st1=dense_dtarget(dtable,g1,g2,st);
      st2=dense_dtarget(dtable,g2,g1,st);
      set_dense_dtarget(dtable,g1,g2,st,st2);
      set_dense_dtarget(dtable,g2,g1,st,st1);
    }
  }
  return 0;
}

/****************************************************************
 * NEW FSA STUFF - by  Laurent Bartholdi
 ****************************************************************/

unsigned
*fsa_mod_count(fsaptr,p,num)
  fsa *fsaptr;
  unsigned p;
  unsigned num;
/* fsa_mod_count() computes the number of elements of length i in the
   accepted language, for all 0 <= i <= n where n=#of states in fsa.
   All computations are mod. p
 */
{
  unsigned *state_count, *new_count, *count, n, dr, i, j, k;
  int **table;
  boolean dense;

  if (!fsaptr->flags[DFA]){
    fprintf(stderr,"Error: fsa_mod_count only applies to DFA's.\n");
    return 0;
  }
  if (!fsaptr->flags[TRIM]){
    printf("#WARNING: fsa_mod_count applied to fsa not known to be trim.\n");
    printf("#It will be minimized before proceeding.\n");
    if (fsa_minimize(fsaptr)== -1) return 0;
  }

  n = fsaptr->states->size;
  dense = fsaptr->table->table_type==DENSE;
  table = fsaptr->table->table_data_ptr;
  dr = fsaptr->table->denserows;

  tmalloc(state_count,unsigned,n+1);	/* # of words ending at given state */
  tmalloc(new_count,unsigned,n+1);  /* new # of words ending at given state */
  tmalloc(count,unsigned,num+1);	/* the answer */

  for (i=1;i<=n;i++) state_count[i] = 0;
  for (i=1;i<=fsaptr->num_initial;i++) state_count[fsaptr->initial[i]]++;

  for (i=0;i<=num;i++) {
    count[i] = 0;
    for (j=1;j<=fsaptr->num_accepting;j++)
      count[i] = (count[i] + state_count[fsaptr->num_accepting == n ?
                  j : fsaptr->accepting[j]]) % p;

    for (j=1;j<=n;j++) new_count[j] = 0;
    for (j=1;j<=n;j++)
    for (k=1;k<=fsaptr->alphabet->size;k++) {
      int im = target(dense,table,k,j,dr);
      if (im>0) new_count[im] = (new_count[im] + state_count[j]) % p;
    }
    for (j=1;j<=n;j++) state_count[j] = new_count[j];
  }
  tfree(state_count);
  tfree(new_count);

  return count;
}

unsigned
mod_inverse(i,p)
  unsigned i;
  unsigned p;
{
  unsigned m = i, n = p; int a = 1, b = 0, c = 0, d = 1;
  	/* we have a*i+b*p = m, c*i+d*p = n at all times;
	   further m<n */
  while (m != 0) {
    unsigned q = n / m, tm = m; int ta = a, tb = b;
    m = n - q*m, a = c - q*a, b = d - q*b;
    n = tm, c = ta, d = tb;
  }
  if (n != 1) fprintf(stderr,"In mod_inverse(): cannot compute");
  return (c+p) % p;
}

int
mod_solve(A,B,p,n)
  int **A;
  int *B;
  unsigned p;
  unsigned n;
/* solve A*B=A[n] in n-dimensional matrices and vectors, mod. p.
   the return value is the smallest possible size of B,
   or -1 if the computation could not be performed. */
{
  unsigned degree = n; int i, j, k;

  for (i=0;i<n;i++) {	/* clean up the ith column */
    int inv, pivot = -1;
    for (j=i;j<n;j++)
      if (A[j][i] != 0) { pivot = j; break; }
    if (pivot < 0) {	/* oops... singular matrix ? */
      for (j=i;j<n;j++) if (A[j][n] != 0) {
        fprintf(stderr,"In mod_solve(): Singular matrix\n");
	return -1;
      }
      degree = i;
      break;
    }
    if (A[i][i] == 0)
      for (j=i;j<=n;j++) A[i][j] = (A[i][j] + A[pivot][j]) % p;
    inv = mod_inverse(A[i][i],p);
    for (j=i;j<=n;j++) A[i][j] = (A[i][j] * inv) % p;
    for (j=i+1;j<n;j++) for(k=n;k>=i;k--)
      A[j][k] = (A[j][k] + (p-A[j][i])*A[i][k]) % p;
  }

  for (i=degree-1; i>=0;i--) {
    B[i] = A[i][n];
    for (j=0;j<i;j++) {
      A[j][n] = (A[j][n] + (p-A[j][i])*A[i][n]) % p;
      A[j][i] = 0;
    }
  }
  return degree;
}

int
fsa_mod_growth(fsaptr,f,p)
  fsa *fsaptr;
  fraction *f;
  unsigned p;
{
  unsigned *count, n, i, j; int **A;
  
  n = fsaptr->states->size;
  tmalloc(A,int *,n);
  for (i=0;i<n;i++)
    tmalloc(A[i],int,n+1);
  tmalloc(f->num,int,n+1);
  tmalloc(f->den,int,n+1);

  count = fsa_mod_count(fsaptr,p,2*n);
  if (count==0) return -1;
  for (i=0;i<n;i++) {
    for (j=0;j<n;j++)
      A[i][j] = count[n+i-j];
    A[i][n] = (p-count[i+n+1]) % p;
  }
  f->den[0] = 1;
  f->dd = mod_solve(A,f->den+1,p,n);

  for (i = 0; i <= n; i++) f->num[i] = 0;
  for (i = 0; i <= n; i++)
  for (j = 0; j <= f->dd && i+j <= n; j++)
    f->num[i+j] = (f->num[i+j] + count[i] * f->den[j]) % p;
  for (i=n;;i--)
    if (f->num[i]!=0) { f->nd = i; break; };

  for (i=0;i<n;i++)
    tfree(A[i]);
  tfree(A);
  return 0;
}

void
mod_normal (poly,d,p)
  int *poly;
  unsigned d;
  unsigned p;
{
  int i;
  for (i = 0; i <= d; i++) {
    poly[i] %= p;
    if (poly[i] < 0) poly[i] += p;
    if (poly[i] > p/2) poly[i] -= p;
  }
}

boolean
print_poly(f,poly,d,var)
  FILE *f;
  int *poly;
  unsigned d;
  char *var;
/* Edited by dfh to buffer printing and insert new-lines
 * returns true if it prints a new line, otherwise false.
 */
{
  boolean first = TRUE, ans = FALSE;
  int i, bufflen;

  bufflen=strlen(kbm_buffer);
  for (i = 0; i <= d; i++)
  if (poly[i] != 0) {
    if (first) {
      if (poly[i]>0 && (i==0 || poly[i]>1))
         sprintf(kbm_buffer+strlen(kbm_buffer),"%d",poly[i]);
      else if (poly[i]<0 && (i==0 || poly[i]<-1))
         sprintf(kbm_buffer+strlen(kbm_buffer),"%d",poly[i]);
      else if (poly[i]==-1)
         sprintf(kbm_buffer+strlen(kbm_buffer),"-");
    }
    else {
      if (poly[i]>1)
         sprintf(kbm_buffer+strlen(kbm_buffer)," + %d",poly[i]);
      else if (poly[i]<-1)
         sprintf(kbm_buffer+strlen(kbm_buffer)," - %d",-poly[i]);
      else if (poly[i]==1)
         sprintf(kbm_buffer+strlen(kbm_buffer)," + ");
      else if (poly[i]==-1)
         sprintf(kbm_buffer+strlen(kbm_buffer)," - ");
    }
    if (i >= 1) {
      if (poly[i]==1 || poly[i]== -1)
        sprintf(kbm_buffer+strlen(kbm_buffer),"%s",var);
      else
        sprintf(kbm_buffer+strlen(kbm_buffer),"*%s",var);
    }
    if (i >= 2)
      sprintf(kbm_buffer+strlen(kbm_buffer),"^%d",i);
    if (strlen(kbm_buffer)>66 && i<d) {
      printbuffer(f);
      add_to_buffer(bufflen+1,"");
      ans=TRUE;
    }
    first = FALSE;
  }
  if (first) fprintf(f,"0");
  return ans;
}

/*
void
print_poly(FILE *f, int *poly, unsigned d, char *var)
{
  boolean first = TRUE;
  int i;

  for (i = 0; i <= d; i++)
  if (poly[i] != 0) {
    if (first) {
      if (poly[i] > 0) fprintf(f,"%d", poly[i]);
      else fprintf(f,"-%d", -poly[i]);
    } else {
      if (poly[i] > 0) fprintf(f," + %d", poly[i]);
      else fprintf(f," - %d", -poly[i]);
    }
    if (i >= 1) fprintf(f,"*%s", var);
    if (i >= 2) fprintf(f,"^%d", i);

    first = FALSE;
  }
  if (first) fprintf(f,"0");
}
*/

int
fsa_growth(wfile,fsaptr,primes,var)
  FILE *wfile;
  fsa *fsaptr;
  unsigned *primes;
  char *var;
{
  boolean cr;
  fraction f, newf;
  int i;
  boolean consistent=TRUE;
  boolean printres;
  boolean firstprime=TRUE;

  while(*primes) {
    printres=FALSE;
    fprintf(wfile,"#result modulo prime %d:",*primes);
    if (kbm_print_level >= 2)
      printf("  #Computing growth modulo %d\n",*primes);
    
    if (fsa_mod_growth(fsaptr, &newf, *primes)== -1) return -1;
    mod_normal(newf.den, newf.dd, *primes);
    mod_normal(newf.num, newf.nd, *primes);
    if (firstprime) {
      f = newf;
      printres = TRUE;
      fprintf(wfile,"\n");
    }
    else if (f.dd != newf.dd || f.nd != newf.nd) {
      tfree(f.num); tfree(f.den);
      f = newf;
      consistent=FALSE;
      printres = TRUE;
    } else {
      boolean fixup = FALSE;
      for (i = 0; i <= newf.dd; i++)
        if (newf.den[i] != f.den[i]) {
          fixup = TRUE;
          f.den[i] = newf.den[i];
        }
      for (i = 0; i <= newf.nd; i++)
        if (newf.num[i] != f.num[i]) {
          fixup = TRUE;
          f.num[i] = newf.num[i];
        }
      if (fixup) {
        consistent=FALSE;
        printres = TRUE;
      }
      tfree(newf.num); tfree(newf.den);
    }
    if (printres) {
      if (firstprime)
        firstprime=FALSE;
      else
        fprintf(wfile,"\n");
      sprintf(kbm_buffer+strlen(kbm_buffer),"(");
      cr=print_poly(wfile,f.num,f.nd,var);
      sprintf(kbm_buffer+strlen(kbm_buffer),")/");
      if (cr || strlen(kbm_buffer)>=40)
        printbuffer(wfile);
      sprintf(kbm_buffer+strlen(kbm_buffer),"(");
      cr=print_poly(wfile,f.den,f.dd,var);
      sprintf(kbm_buffer+strlen(kbm_buffer),");");
      printbuffer(wfile);
    }
    else fprintf(wfile," (as previous)\n");
    primes++;
  }
  if (kbm_print_level >= 2) {
    int m = 0;
    for (i = 0; i <= f.nd; i++)
      if (f.num[i] > m) m = f.num[i]; else if (f.num[i] < -m) m = -f.num[i];
    for (i = 0; i <= f.dd; i++)
      if (f.den[i] > m) m = f.den[i]; else if (f.den[i] < -m) m = -f.den[i];
    printf("  #Degrees %d/%d, Max coefficient %d\n", f.nd, f.dd, m);
  }
  tfree(f.den); tfree(f.num);
  return (int)consistent;
}
