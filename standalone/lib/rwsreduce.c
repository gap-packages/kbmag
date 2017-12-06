/* file reduce.c - created 6/10/94
 * 2/6/98 - large scale re-organisation.
 * 9.1.98. change of `gen' to `char' for generator type
 * 4/10/95 - added condition to return immediately if word-length exceeds
 * maxreducelen/2. This is to save time when word-length is getting out of
 * control. The calling program should check for this after return if
 * necessary.
 *
 * This file contains the various routines for reducing words,
 * using a rewriting system.
 */

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "externals.h"

/* Functions defined in this file: */

/* Reduce "w", by replacing any occurrences of the LHS of the current
 * equations in the rewriting system by their RHS.
 * The reduction fsa for the rewriting system rws is used for this,and it is
 * assumed to be stored in dense format. The complete sequence of
 * states that it goes through on reading "w" is remembered in the array
 * "rws.history".
 */
int rws_reduce(gen *w, reduction_struct *rs_rws)
{
  int len, st, **table, longer, *history;
  gen *midwd, *ptr1, *ptr2, *ptr;
  rewriting_system *rwsptr = rs_rws->rws;
  reduction_equation *eqn;
  history = rwsptr->history;

  table = rwsptr->reduction_fsa->table->table_data_ptr;
  midwd = w;
  len = 0;
  history[0] = 1;
  st = 1;
  while (*midwd != 0) {
    st = history[++len] = dense_target(table, *midwd, st);
    if (st == 0) {
      fprintf(stderr, "#The word for reduction is invalid.\n");
      return -1;
    }
    if (st < 0)
    /* st= -n means that we have just read the LHS or
     * relation  n. Replace it by RHS, and go back to the
     * beginning of that subword. */
    {
      st = -st;
      eqn = &(rwsptr->eqns[st]);
      ptr1 = midwd;
      ptr2 = eqn->rhs - 1;
      if ((longer = genstrlen(eqn->rhs) - genstrlen(eqn->lhs)) > 0) {
        if (genstrlen(w) + longer >= rwsptr->maxreducelen) {
          fprintf(stderr, "#Error: word too long in reduction - try increasing "
                          "maxreducelen.\n");
          return -1;
        }
        ptr = w + genstrlen(w);
        while (ptr > midwd) {
          *(ptr + longer) = *ptr;
          ptr--;
        }
        ptr1 += longer;
        if (genstrlen(w) > rwsptr->maxreducelen / 2)
          return 0;
        /* To save time when length is getting out of control */
      }
      len -= genstrlen(eqn->lhs);
      midwd = w + len - 1;
      ptr = midwd;
      while (*(++ptr2) != 0)
        *(++ptr) = *ptr2;
      if (ptr != ptr1) {
        while (*(++ptr1) != 0)
          *(++ptr) = *ptr1;
        *(++ptr) = 0;
      }
      st = history[len];
      /*	midwd--;*/
    }
    midwd++;
  }
  return 0;
}


/* The version of reduce for the reduction automaton that recognises
 * left hand sides of relations only.
 * This is both slower, and needs more space, since the history has to
 * be stored as a list of subsets of the states, rather than a list of states.
 * The subsets are stored contiguously in the array rws.slowhistorysp, and
 * pointed at by rws.slowhistory.
 */
int slow_rws_reduce(gen *w, reduction_struct *rs_rws)
{
  int len, st, **table, *histptr, *histptre, *nextptr, subrelno, longer,
      *slowhistorysp, **slowhistory;
  gen *midwd, *ptr1, *ptr2, *ptr;
  rewriting_system *rwsptr = rs_rws->rws;
  reduction_equation *eqn;
  slowhistorysp = rwsptr->slowhistorysp, slowhistory = rwsptr->slowhistory;

restart:
  midwd = w;
  len = 0;
  table = rwsptr->reduction_fsa->table->table_data_ptr;
  nextptr = slowhistory[0] = slowhistorysp;
  while (*midwd != 0) {
    subrelno = 0;
    histptr = slowhistory[len++];
    slowhistory[len] = histptre = nextptr;
    if (nextptr + len - slowhistorysp > rwsptr->maxslowhistoryspace) {
      if (kbm_print_level >= 3)
        printf("    #maxslowhistoryspace too small; doubling it.\n");
      tfree(rwsptr->slowhistorysp);
      rwsptr->maxslowhistoryspace *= 2;
      tmalloc(rwsptr->slowhistorysp, int, rwsptr->maxslowhistoryspace);
      slowhistorysp = rwsptr->slowhistorysp;
      goto restart;
    }
    /* First adjoin image of start state */
    st = dense_target(table, *midwd, 1);
    if (st < 0)
      subrelno = -st;
    else {
      if (st > 0)
        *(nextptr++) = st;
      while (histptr < histptre) {
        st = dense_target(table, *midwd, *(histptr++));
        if (st > 0)
          *(nextptr++) = st;
        else if (st < 0) {
          subrelno = -st;
          break;
        }
      }
    }
    if (subrelno > 0) {
      /* subrelno=n means that we have just read the LHS of
       * relation  n. Replace it by RHS, and go back to the
       * beginning of that subword.
       */
      eqn = &(rwsptr->eqns[subrelno]);
      ptr1 = midwd;
      ptr2 = eqn->rhs - 1;
      if ((longer = (genstrlen(eqn->rhs) - genstrlen(eqn->lhs))) > 0) {
        if (genstrlen(w) + longer >= rwsptr->maxreducelen) {
          fprintf(stderr, "#Error: word too long in reduction - try increasing "
                          "maxreducelen.\n");
          return -1;
        }
        ptr = w + genstrlen(w);
        while (ptr > midwd) {
          *(ptr + longer) = *ptr;
          ptr--;
        }
        ptr1 += longer;
        if (genstrlen(w) > rwsptr->maxreducelen / 2)
          return -1;
        /* To save time when length is getting out of control */
      }
      len -= genstrlen(eqn->lhs);
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
      nextptr = slowhistory[len + 1];
    }
    midwd++;
  }
  return 0;
}

/* This is similar to slow_rws_reduce, but it does not change the word  w.
 * It merely checks whether it is reduced or not, and returns true or false.
 * If the second parameter i is greater than 0, then the check is for
 * reducibility ignoring equation number i. (Usually this is used on the left-
 * hand-side of equation i itself.
 */
boolean slow_check_rws_reduce(gen *w, int i, rewriting_system *rwsptr)
{
  int st, **table, *histptr, *histptre, *nextptr,
      *slowhistorysp = rwsptr->slowhistorysp,
      **slowhistory = rwsptr->slowhistory;
  gen *wc = w;

restart:
  table = rwsptr->reduction_fsa->table->table_data_ptr;
  histptr = nextptr = slowhistory[0] = slowhistorysp;
  while (*wc != 0) {
    histptre = nextptr;
    if (nextptr + (wc - w) - slowhistorysp > rwsptr->maxslowhistoryspace) {
      if (kbm_print_level >= 3)
        printf("    #maxslowhistoryspace too small doubling it.\n");
      tfree(rwsptr->slowhistorysp);
      rwsptr->maxslowhistoryspace *= 2;
      tmalloc(rwsptr->slowhistorysp, int, rwsptr->maxslowhistoryspace);
      slowhistorysp = rwsptr->slowhistorysp;
      goto restart;
    }
    while (histptr < histptre) {
      st = dense_target(table, *wc, *(histptr++));
      if (st > 0)
        *(nextptr++) = st;
      else if (st < 0 && st != -i)
        return FALSE;
    }
    st = dense_target(table, *wc, 1);
    if (st > 0)
      *(nextptr++) = st;
    else if (st < 0 && st != -i)
      return FALSE;
    wc++;
  }
  return TRUE;
}
