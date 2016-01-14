/* diffredwl.c  15/1/95
 * 6/8/98 large-scale re-organisation to elimiante externals.
 * 23/9/96 - adapted for V2 of kbmag.
 * Modification of diffreduce.c to cope with wtlex ordering.
 * Copied from old automata package and edited.
 * This file contains the procedure for reducing a word using a
 * word-difference machine *wd_fsa (defined externally).
 */
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "externals.h"

#define MAXV 65536 /* The maximum number of vertices allowed. */

/* Functions defined in this file */
int diff_reduce_wl();
int make_substitution();
/* functions defined in other files used in this file */
int genstrlen();

int
diff_reduce_wl(w,rs_wd)
	gen *w;
	reduction_struct *rs_wd;
/* w is the word to be reduced using the word-difference machine  *wd_fsa.
 * We first use the word-acceptor to locate reducible strings, and then use
 * the function make_substituion to make the actual substitution.
 */
{ int wordlen,  **watable,start,end,i,j,initstate, state;
  fsa *wd_fsa = rs_wd->wd_fsa;
  fsa *wa = rs_wd->wa;
  int *weight = rs_wd->weight;
  boolean reducible;
  w = w-1; /* since code below assumes word is from w[1] .. w[wordlen]. */
  watable = wa->table->table_data_ptr;
  initstate=wa->initial[1];
  reducible=TRUE;
  while (reducible) { 
    reducible=FALSE;
    wordlen=genstrlen(w+1);
    start=1;  end=wordlen;
    state=initstate;
    /* Trace out the word w through the word-acceptor until we get rejection */
    for (i=start;i<=end;i++) {
      if ((state=dense_target(watable,w[i],state)) == 0) {
        reducible=TRUE;
        /* Now we have to find the latest starting point in the subword
         * ending at this position that leads to failure.
         */
        end=i;
        while (start<=end) {
          state=initstate;
          for (j=start+1;j<=end;j++) 
            state=dense_target(watable,w[j],state);
          if (state!=0)
            break;
          start++;
        }
        if (make_substitution(w,start,end,rs_wd)== -1) return -1;;
        break;
      }
    }
  }
  return 0;
}

int
make_substitution(w,start,end,rs_wd)
/* Find and make a substitution in the word w, using *wd_fsa, beginning at
 * position 'start' and ending at position 'end'.
 * This may make the word shorter or longer.
 * It is assumed that wd_fsa->table->table_data_dptr is set up.
 * This function allocates its own space.
 * NOTE: No checks on the validity of the word are carried out.
 */
 gen *w;
 int start, end;
 reduction_struct *rs_wd;
{ int ndiff, ngens, identity, padsymbol, wordlen, ***difftab,
      gct, *gpref, level, gen1, gen2, diff, diffct, newdiff,
      shift, cwordwt, csubwt, i, j;
  fsa *wd_fsa = rs_wd->wd_fsa;
  fsa *wa = rs_wd->wa;
  int *weight = rs_wd->weight;
  int maxreducelen = rs_wd->maxreducelen;
  int maxv=MAXV;
  boolean  *cf, clexprec;
  struct vertexd {
       gen genno;
       int diffno;
       int subwt;
       boolean lexprec;
       struct vertexd *backptr;
  }
       *gptr, *ngptr, *substruc, *cstruc;

/* vertexd is the structure used to store a vertex in the graph of strings
   for possible substitution. The components are as follows.
   backptr - points back to another vertexd, or to zero.
   genno  - the number of the generator at the end of the string.
   diffno - the word difference number of the string defined by following
            backptr back to zero (using genno), relative to the corresponding
            part of the word being reduced.
   subwt - subwt is the total weight of the substituted string up to this
           point.
   lexprec - lexprec is true if the substituted string lexicographically
           precedes the the actual string.
    Another essential component of a vertexd is its level (i.e. the length of
    the string got by chasing back to the beginning of the word)
    but we always calculate this, using
    the integers defined by gpref. (See below))
*/

  if (wd_fsa->alphabet->type != PRODUCT || wd_fsa->alphabet->arity != 2) {
    fprintf(stderr,
        "Error: diff_reduce must be called with a word-difference machine.\n");
    return -1;
  }
  ndiff = wd_fsa->states->size;
  ngens = wd_fsa->alphabet->base->size;
  identity = wd_fsa->initial[1];
  padsymbol = ngens+1;
  wordlen= genstrlen(w+1); /* (word starts at w[1]) */
  difftab = wd_fsa->table->table_data_dptr;

  tmalloc(cf,boolean,ndiff+1);
/* cf is used as a characteristic function, when constructing a subset of the
  set  D  of word differences.
*/

  tmalloc(gpref,int,maxreducelen+1);
  gct= 0;
  gpref[start-1]=0;
/* gpref[n]+1 is the number of vertices that have been defined after reading
 * from position start to position  n  in the word.
 * These vertices are gptr[0],...,gptr[gpref[n]].
 * We start by allocating space for maxv vertices, and setting the
 * vertex that we start with.
 */
  tmalloc(gptr,struct vertexd,maxv);
  gptr[0].genno=0; gptr[0].diffno=identity;
  gptr[0].subwt=0; gptr[0].lexprec=FALSE; gptr[0].backptr=0;

  cwordwt=0;
/* Now we start reading the word from position start */
  level=start;
  while (1) {
    for (i=1;i<=ndiff;i++)
      cf[i]=FALSE;
/* Read the element of the word at position level - the substituted word may
 * be longer than the original, so we may have to read past position 'end',
 * in which case we use the padding symbol.
 */
    gen1= level>end ? padsymbol : w[level];
    cwordwt += weight[gen1];

/* The next loop is over the subset of D defined at the
   previous level, level-1.
*/
    for (diffct= level==start ? 0 : gpref[level-2]+1;diffct<=gpref[level-1];
                                                                   diffct++) {
      cstruc=gptr+diffct;
      diff = cstruc->diffno;
      for (gen2=1;gen2<=ngens+1;gen2++) {
       if ((level==start && gen2==gen1) || (gen1==padsymbol && gen2==padsymbol)
           || (gen2!=padsymbol && cstruc->genno==padsymbol))
         continue;
       csubwt = cstruc->subwt + weight[gen2];
       clexprec= level==start ? gen2<gen1 : cstruc->lexprec;
       /* There is no point in going on if we are passed the end of the word
        * to be reduced and the substituted word has got ahead.
        */
       if (level>=end && (csubwt>cwordwt || (csubwt==cwordwt && !clexprec)))
         continue;
       if (newdiff = dense_dtarget(difftab,gen1,gen2,diff)) {
        if (newdiff==identity) {
          if (csubwt<cwordwt || (csubwt==cwordwt && clexprec)) {
            /* We have found a  substitution */
            if (gen1==padsymbol) {
             /* The substituted word is longer than the original */
              shift = level-end;
              if (wordlen+shift>=maxreducelen) {
                fprintf(stderr,"Sorry - substituted word is too long.\n.");
                return -1;
              }
              for (i=wordlen+1;i>end;i--)
                w[i+shift]=w[i];
              end += shift;
            }
            else if (gen2==padsymbol) {
             /* The substituted word is shorter than the original */
              shift=0;
              while (gen2==padsymbol && cstruc) {
                shift++;
                gen2=cstruc->genno;
                cstruc=cstruc->backptr;
              }
              for(i=end+1;i<=wordlen+1;i++)
                w[i-shift]=w[i];
              end -= shift;
            }
            /* Now make the substitution */
            i=end;
            while (cstruc) {
              w[i--] = gen2;
              gen2=cstruc->genno;
              cstruc=cstruc->backptr;
            }
            if (i!=start-1) {
              fprintf(stderr,
                  "Something has gone horribly wrong in word-reduction.\n");
              return -1;
            }
            goto donesub;
          }
        }
        else {
          if (cf[newdiff])
/* We have this word difference stored already, but we will check to see if
   the current string precedes the existing one.
*/
            for (i=gpref[level-1]+1;;i++) {
              substruc=gptr+i;
              if (substruc->diffno == newdiff) {
                if (csubwt<substruc->subwt || (csubwt==substruc->subwt&&
                                   cstruc->lexprec && !substruc->lexprec)) {
/* The new string is better than the existing one */
                  substruc->genno = gen2;
                  substruc->subwt = csubwt;
                  substruc->lexprec=clexprec;
                  substruc->backptr = cstruc;
                }
                break;
              }
            }
          else
/* This is a new word difference at this level, so we define a new vertexd in
   graph.
*/
          { gct++;
            if (gct >= maxv) {
/* We need more space for vertices. Allocate twice the preceding space and
   copy existing data.
*/
              tmalloc(ngptr,struct vertexd,2*maxv);
              if (kbm_print_level>=3)
                printf("    #Allocating more space in diff_reduce.\n");
              for (i=0;i<maxv;i++) {
                ngptr[i].genno = gptr[i].genno;
                ngptr[i].diffno = gptr[i].diffno;
                ngptr[i].subwt = gptr[i].subwt;
                ngptr[i].lexprec = gptr[i].lexprec;
                substruc = gptr[i].backptr;
                if (substruc==0)
                  ngptr[i].backptr = 0;
                else
                  for (j=i-1;;j--) if (substruc==gptr+j) {
                    ngptr[i].backptr = ngptr+j;
                    break;
                  }
              }
              tfree(gptr);
              gptr=ngptr;
              maxv *= 2;
            }
/* Define the new vertexd. */
            substruc = gptr+gct;
            substruc->genno = gen2;
            substruc->subwt = csubwt;
            substruc->lexprec=clexprec;
            substruc->backptr = cstruc;
            substruc->diffno = newdiff;
            cf[newdiff] = TRUE;
          }
        } /* newdiff ==identity */
       } /* newdiff != 0 */
      } /*End of loop over gen2 */
    } /* end of loop over word differences at previous level */

    gpref[level] = gct;
    level++;
  }

 donesub:
  tfree(gptr);
  tfree(cf);
  tfree(gpref);
  return 0;
}
