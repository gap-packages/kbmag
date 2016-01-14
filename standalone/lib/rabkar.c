/* file rabkar.c   27.3.95.
 * 6/2/98 - changes for large-scale re-organisation
 * 13/1/98 changes for the `gen' type replacing char for generators.
 * This file contains all routines related to Rabin-Karp data structures for
 * word reduction under kbprog.
 * The word-reduction routines are modified versions of those in rwsreduce.
 * The ones here use both the reduction machine and the Rabin-Karp hash-table.
 */
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "externals.h"

static unsigned
rk_prime_constants[] = {20011,60013,120011,200003,300007,400009,500009,700001,
          1000003,1500007,2000003,5000011,10000019,32000011};
static int rk_num_prime_constants = 14;
/* For use as modulus in hash-tables */
static unsigned rk_bighashmod = 32000011; /* the big modulus chosen */
static unsigned rk_hashmod; /* the modulus chosen */
static int rk_shiftbits; /* 2^rk_shiftbits is factor in hash-function */
static unsigned **rk_plusinc, *rk_minusinc;
                      /* Lookoup table of increments for hash-function */
static int *rk_first_tail, *rk_next_tail;
static unsigned *rk_bighashvaleqn;
  /* All strings have a large hashvalue (taken mod rk_bighashmod) and an
   * ordinary hash value (same thing taken mod rk_hashmod).
   * rk_first_tail[i] for 0<=i < rk_hashmod, is the first equation number whose
   * tail of lhs has hash-value i. *rk_next_tail[i] is the number of an equation
   * with the same hash-value as eqn number i - or -1 if no more.
   * rk_bighashvaleqn holds the big hash value of equation number i.
   * Before we actually compare strings,we check that the big hash values
   * correspond.
   */

/* Functions defined in this file: */
int rk_init();
void rk_reset();
void rk_clear();
void rk_add_lhs();
int slow_rws_reduce_rk();
boolean slow_check_rws_reduce_rk();

/* functions defined in other files and used in this file */
int genstrlen();
int stringlen();

int 
rk_init (rewriting_system *rwsptr)
/* Initialize hash-table and lookup tables for this value of maxeqns */
{ int ng, i, j, tp, maxeqns;
  /* First select a suitable prime */
  maxeqns = rwsptr->maxeqns;
  for (i=0;i<rk_num_prime_constants;i++) if (rk_prime_constants[i] > (3*maxeqns/5)) {
    rk_hashmod = rk_prime_constants[i];
    break;
  }
  if (i==rk_num_prime_constants) {
    fprintf(stderr,"Value of maxeqns is absurdly large! Cannot cope.\n");
    return -1;
  }

  /* Now calculate rk_shiftbits */
  ng = rwsptr->num_gens;
  tp = 2; rk_shiftbits=1;
  while (ng > tp) {
    tp*=2; rk_shiftbits++;
  }
  if (kbm_print_level >= 3)
    printf(
 "    #Initializing Rabin-Karp tables. Maxeqns=%d; Modulus=%d; Shiftbits=%d.\n",
     maxeqns,rk_hashmod,rk_shiftbits);

  /* Now initialize lookup tables */
  tmalloc(rk_plusinc,unsigned *,rwsptr->rkminlen);
  tmalloc(rk_minusinc,unsigned,ng+1);
  for (i=0;i<rwsptr->rkminlen;i++) {
    tmalloc(rk_plusinc[i],unsigned,ng+1);
    if (i==0) for (j=1;j<=ng;j++)
      rk_plusinc[i][j] = j-1; /* j-1 to make values in range [0,ng-1] */
    else for (j=1;j<=ng;j++)
      rk_plusinc[i][j] = (rk_plusinc[i-1][j]<<rk_shiftbits) % rk_bighashmod;
    if (i==rwsptr->rkminlen-1) for (j=1;j<=ng;j++)
      rk_minusinc[j] = rk_plusinc[i][j] ? rk_bighashmod-rk_plusinc[i][j] : 0;
  }

  /* Initialize hash-table */
  tmalloc(rk_first_tail,int,rk_hashmod);
  tmalloc(rk_next_tail,int,maxeqns+1);
  tmalloc(rk_bighashvaleqn,unsigned,maxeqns+1);
}

void 
rk_reset (int maxeqns)
{ int i;
  for (i=0;i<rk_hashmod;i++)
    rk_first_tail[i] = 0;
}


void 
rk_clear (rewriting_system *rwsptr)
{ int i;
  if (kbm_print_level>=3)
    printf("    #Calling rk_clear.\n");
  for (i=0;i<rwsptr->rkminlen;i++)
    tfree(rk_plusinc[i]);
  tfree(rk_plusinc);
  tfree(rk_minusinc);
  tfree(rk_first_tail);
  tfree(rk_next_tail);
  tfree(rk_bighashvaleqn);
}
    
void 
rk_add_lhs (int n, rewriting_system *rwsptr)
/* Calculate the hash-value of the tail of the lhs of equation number n
 * (it is assumed that the length of this lhs is at least rws.rkminlen),
 * and adjoin it to the hash-table.
 */
{ gen *w, *we;
  int i, eqno, neweqno;
  unsigned bighashval, hashval;
  w = rwsptr->eqns[n].lhs;
  we = w+genstrlen(w);
  bighashval = 0;
  for (i=0;i<rwsptr->rkminlen;i++)
    bighashval += rk_plusinc[i][*(--we)];
  bighashval %= rk_bighashmod;
  rk_bighashvaleqn[n] = bighashval;
  hashval = bighashval % rk_hashmod;
  if ((eqno=rk_first_tail[hashval]) == 0)
    rk_first_tail[hashval]=n;
  else {
    while (neweqno=rk_next_tail[eqno]) 
      eqno=neweqno;
    rk_next_tail[eqno] = n;
  }
  rk_next_tail[n]=0;
}

int 
slow_rws_reduce_rk (gen *w, reduction_struct *rs_rws)
/* This is the routine slow_rws_reduce (from rwsreduce.c) adapted to deal
 * in addition with reductions arising from the Rabin-Karp table.
 */
{
  int             len,
                  st,
      j,
      l,
      longer,
      rkminlen,
      **table,
           *histptr,
           *histptre,
           *nextptr,
      subrelno,
      *slowhistorysp,
      **slowhistory;
  unsigned  bighashval,
      hashval;
  gen           *midwd,
                 *ptr1,
                 *ptr2,
                 *ptr,
           *lhs;
  rewriting_system *rwsptr= rs_rws->rws;
  rkminlen = rwsptr->rkminlen;
  slowhistorysp = rwsptr->slowhistorysp,
  slowhistory = rwsptr->slowhistory;

restart:
  midwd = w;
  len = 0;
  table = rwsptr->reduction_fsa->table->table_data_ptr;
  nextptr=slowhistory[0]=slowhistorysp;
  while (*midwd != 0) {
    subrelno=0;
    histptr=slowhistory[len++];
    slowhistory[len]=histptre=nextptr;
    if (nextptr+len-slowhistorysp > rwsptr->maxslowhistoryspace){
      if (kbm_print_level>=3)
          printf(
                "    #maxslowhistoryspace too small; doubling it.\n");
        tfree(rwsptr->slowhistorysp);
      rwsptr->maxslowhistoryspace *= 2;
      tmalloc(rwsptr->slowhistorysp,int,rwsptr->maxslowhistoryspace);
      slowhistorysp = rwsptr->slowhistorysp;
      goto restart;
    }
/* First adjoin image of start state */
    st = dense_target(table,*midwd,1);
    if (st<0)
      subrelno= -st;
    else{
      if (st>0)
        *(nextptr++) = st;
      while (histptr<histptre){
        st = dense_target(table,*midwd,*(histptr++));
        if (st>0)
          *(nextptr++) = st;
        else if (st<0){
          subrelno= -st;
          break;
        }
      }
    }
    if (subrelno==0 && len>=rkminlen) {
  /* Look for a substitution using Rabin-Karp table  -
   * First calculate the hash-value for the word ending at this point
   */
      if (len==rkminlen) {
        bighashval = 0;
        ptr1=midwd;
        for (j=0;j<rkminlen;j++)
          bighashval += rk_plusinc[j][*(ptr1--)];
      }
      else {
        bighashval += rk_minusinc[*(midwd-rkminlen)];
        bighashval = bighashval<<rk_shiftbits;
        bighashval += (*midwd - 1);
      }
      bighashval %= rk_bighashmod;
      hashval = bighashval % rk_hashmod;
      subrelno=rk_first_tail[hashval];
      while (subrelno) {
      /* check if we have read lhs of equation no subrelno */
        lhs = rwsptr->eqns[subrelno].lhs;
        l = genstrlen(lhs);
        if (l <= len &&
            bighashval==rk_bighashvaleqn[subrelno]) {
          ptr1 = lhs;
          ptr2 = midwd-l+1;
          ptr = ptr1+l;
          while (ptr1<ptr) {
            if (*(ptr1) != *(ptr2))
              break;
            ptr1++; ptr2++;
          }
          if (ptr1==ptr) {
            break;
          }
                                }
        subrelno = rk_next_tail[subrelno];
      }
    }
    if (subrelno>0){
      /* subrelno=n means that we have just read the LHS of
       * relation  n. Replace it by RHS, and go back to the
       * beginning of that subword.
                         */
      ptr1 = midwd;
      ptr2 = rwsptr->eqns[subrelno].rhs - 1;
      if ((longer = (genstrlen(rwsptr->eqns[subrelno].rhs) -
                     genstrlen(rwsptr->eqns[subrelno].lhs)))>0) {
        if (genstrlen(w)+longer>=rwsptr->maxreducelen){
           fprintf(stderr,
       "#Error: word too long in reduction - try increasing maxreducelen.\n");
         return -1;
      }
      ptr = w + genstrlen(w);
      while (ptr > midwd) {
          *(ptr + longer) = *ptr;
          ptr--;
        }
        ptr1 += longer;
      }
      len -= genstrlen(rwsptr->eqns[subrelno].lhs);
      midwd = w + len - 1;
      ptr = midwd;
      while (*(++ptr2) != 0)
        *(++ptr) = *ptr2;
      if (ptr != ptr1) {
        while (*(++ptr1) != 0)
          *(++ptr) = *ptr1;
        *(++ptr) = 0;
      }
      histptr = slowhistory[len];
      nextptr = slowhistory[len+1];
      if (len>=rkminlen) {
        bighashval = 0;
        ptr1=midwd;
        for (j=0;j<rkminlen;j++)
          bighashval += rk_plusinc[j][*(ptr1--)];
        bighashval %= rk_bighashmod;
      }
    }
    midwd++;
  }
  return 0;
}

boolean
slow_check_rws_reduce_rk(w,i,rwsptr)
  gen               *w;
  int      i;
  rewriting_system *rwsptr;
/* This is the routine slow_check_rws_reduce (from rwsreduce.c) adapted to deal
 * in addition with reductions arising from the Rabin-Karp table.
 */
{
  int len,
      st,
      j,
      l,
      rkminlen = rwsptr->rkminlen,
      **table,
      subrelno,
      *histptr,
      *histptre,
      *nextptr,
      longer,
      *slowhistorysp = rwsptr->slowhistorysp,
      **slowhistory = rwsptr->slowhistory;
  unsigned  bighashval,
      hashval;
  gen  *midwd,
       *ptr1,
       *ptr2,
       *ptr,
       *lhs;

restart:
  midwd = w;
  len = 0;
  table = rwsptr->reduction_fsa->table->table_data_ptr;
  nextptr=slowhistory[0]=slowhistorysp;
  while (*midwd != 0) {
    histptr=slowhistory[len++];
    slowhistory[len]=histptre=nextptr;
    if (nextptr+len-slowhistorysp > rwsptr->maxslowhistoryspace){
      if (kbm_print_level>=3)
          printf(
                "    #maxslowhistoryspace too small; doubling it.\n");
        tfree(rwsptr->slowhistorysp);
      rwsptr->maxslowhistoryspace *= 2;
      tmalloc(rwsptr->slowhistorysp,int,
                                 rwsptr->maxslowhistoryspace);
      slowhistorysp = rwsptr->slowhistorysp;
      goto restart;
    }
/* First adjoin image of start state */
    st = dense_target(table,*midwd,1);
    if (st<0 && st != -i)
      return FALSE;
    else{
      if (st>0)
        *(nextptr++) = st;
      while (histptr<histptre){
        st = dense_target(table,*midwd,*(histptr++));
        if (st>0)
          *(nextptr++) = st;
        else if (st<0 && st!= -i)
          return FALSE;
      }
    }
    if (len>=rkminlen) {
  /* Look for a substitution using Rabin-Karp table  -
   * First calculate the hash-value for the word ending at this point
   */
      if (len==rkminlen) {
        bighashval = 0;
        ptr1=midwd;
        for (j=0;j<rkminlen;j++)
          bighashval += rk_plusinc[j][*(ptr1--)];
      }
      else {
        bighashval += rk_minusinc[*(midwd-rkminlen)];
        bighashval = bighashval<<rk_shiftbits;
        bighashval += (*midwd - 1);
      }
      bighashval %= rk_bighashmod;
      hashval = bighashval % rk_hashmod;
      subrelno=rk_first_tail[hashval];
      while (subrelno) {
      /* check if we have read lhs of equation no subrelno */
        lhs = rwsptr->eqns[subrelno].lhs;
        l = genstrlen(lhs);
        if (l<=len && subrelno!=i &&
            bighashval==rk_bighashvaleqn[subrelno]) {
          ptr1 = lhs;
          ptr2 = midwd-l+1;
          ptr =  ptr1+l;
          while (ptr1<ptr) {
            if (*(ptr1) != *(ptr2))
              break;
            ptr1++; ptr2++;
          }
          if (ptr1==ptr)
            break;
                                }
        subrelno = rk_next_tail[subrelno];
                        }
      if (subrelno>0)
        return FALSE;
                }
    midwd++;
  }
  return TRUE;
}
