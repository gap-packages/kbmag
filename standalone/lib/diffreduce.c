/* diffreduce.c  1/11/95
 * 6/8/98 large-scale re-organisation to eliminate externals.
 * 9/1/98 type of generator changed from char to `gen'
 * Copied from old automata package and edited.
 * This file contains the procedure for reducing a word using a
 * word-difference machine *wd_fsa (defined externally).
 */
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "externals.h"

#define MAXV 65536 /* The maximum number of vertices allowed. */

/* functions defined in this file */

/* w is the word to be reduced using the word-difference machine  *wd_fsa.
 * It is assumed that wd_fsa->table->table_data_dptr is set up.
 * This function allocates its own space.
 * NOTE: No checks on the validity of the word are carried out.
 */
int diff_reduce(gen *w, reduction_struct *rs_wd)
{
  int ndiff, ngens, identity, padsymbol, wordlen, ***difftab, gct, *gpref,
      level, gen1, gen2, diff, diffct = 0, newdiff, olen, nlen, i, j;
  boolean deqi, donesub, *cf;
  fsa *wd_fsa = rs_wd->wd_fsa;
  int maxv = MAXV;
  struct vertexd {
    gen genno;
    int diffno;
    int sublen;
    struct vertexd *backptr;
  } * gptr, *ngptr, *substruc;

  /* vertexd is the structure used to store a vertex in the graph of strings
     for possible substitution. The components are as follows.
     backptr - points back to another vertexd, or to zero.
     genno  - the number of the generator at the end of the string.
     diffno - the word difference number of the string defined by following
              backptr back to zero (using genno), relative to the corresponding
              part of the word being reduced.
     sublen - plus or minus the length of this string. sublen is positive if and
              only if the string lexicographically precedes the
              corresponding part of the word being reduced.
     sublen is put in to save time.
      Another essential component of a vertexd is its level (i.e. the length of
      the string got by chasing back to the beginning of the word)
      but we always calculate this, using
      the integers defined by gpref. (See below))
  */

  if (wd_fsa->alphabet->type != PRODUCT || wd_fsa->alphabet->arity != 2) {
    fprintf(
        stderr,
        "Error: diff_reduce must be called with a word-difference machine.\n");
    return -1;
  }
  ndiff = wd_fsa->states->size;
  ngens = wd_fsa->alphabet->base->size;
  identity = wd_fsa->initial[1];
  padsymbol = ngens + 1;
  wordlen = genstrlen(w);
  if (wordlen <= 0)
    return 0;
  difftab = wd_fsa->table->table_data_dptr;
  w = w - 1; /* since code below assumes word is from w[1] .. w[wordlen]. */

  tmalloc(cf, boolean, ndiff + 1);
  /* cf is used as a characteristic function, when constructing a subset of the
    set  D  of word differences.
  */

  tmalloc(gpref, int, wordlen + 1);
  gct = -1;
  gpref[0] = -1;
  /* gpref[n]+1 is the number of vertices that have been defined after reading
    the first n elements of the word. These vertices are
    gptr[0],...,gptr[gpref[n]]. We start by allocating space for maxv vertices.
  */

  tmalloc(gptr, struct vertexd, maxv);

  /* Now we start reading the word. */
  level = 0;
  while (++level <= wordlen) {
    for (i = 1; i <= ndiff; i++)
      cf[i] = FALSE;
    /* Read the element of the word at position level. */
    gen1 = w[level];

    /* The next loop is over the identity and the subset of D defined at the
       previous level, level-1.
    */
    diff = identity;
    while (1) {
      deqi = diff == identity;
      /* First look for a possible substitution of a shorter string */
      newdiff = dense_dtarget(difftab, gen1, padsymbol, diff);
      if (newdiff == identity) {
        /* Make substitution and reduce length of word by 1. */
        i = level - 1;
        if (!deqi) {
          substruc = gptr + diffct;
          do {
            w[i] = substruc->genno;
            substruc = substruc->backptr;
            i--;
          } while (substruc);
        }
        for (j = level; j < wordlen; j++)
          w[j] = w[j + 1];
        w[wordlen] = 0;
        wordlen--;

        /* Whenever we make a substitution, we have to go back one level more
           than expected, because of our policy of looking ahead for
           substitutions that reduce the length by 2.
        */
        level = i > 0 ? i - 1 : i;
        gct = gpref[level];
        break;
      }
      else if (newdiff && level < wordlen) {
        j = dense_dtarget(difftab, w[level + 1], padsymbol, newdiff);
        if (j == identity)
        /* Make substitution and reduce length of word by 2. */
        {
          i = level - 1;
          if (!deqi) {
            substruc = gptr + diffct;
            do {
              w[i] = substruc->genno;
              substruc = substruc->backptr;
              i--;
            } while (substruc);
          }
          for (j = level; j < wordlen - 1; j++)
            w[j] = w[j + 2];
          w[wordlen - 1] = 0;
          wordlen -= 2;
          level = i > 0 ? i - 1 : i;
          gct = gpref[level];
          break;
        }
      }

      donesub = FALSE;
      /* Now we loop over the generator that is a candidate for substitution
         at this point.
      */
      for (gen2 = 1; gen2 <= ngens; gen2++) {
        newdiff = dense_dtarget(difftab, gen1, gen2, diff);
        if (newdiff) {
          if (newdiff == identity) {
            if (deqi) {
              if (gen2 < gen1) {
                w[level] = gen2;
                level = level > 1 ? level - 2 : level - 1;
                gct = gpref[level];
                donesub = TRUE;
                break;
              }
            }
            else if (gptr[diffct].sublen > 0) {
              /* Make a substitution (by a string of equal length). */
              w[level] = gen2;
              i = level - 1;
              substruc = gptr + diffct;
              do {
                w[i] = substruc->genno;
                substruc = substruc->backptr;
                i--;
              } while (substruc);
              level = i > 0 ? i - 1 : i;
              gct = gpref[level];
              donesub = TRUE;
              break;
            }
          }
          else {
            if (cf[newdiff])
              /* We have this word difference stored already, but we will check
                 to see if the current string precedes the existing one.
              */
              for (i = gpref[level - 1] + 1;; i++) {
                substruc = gptr + i;
                if (substruc->diffno == newdiff) {
                  olen = substruc->sublen;
                  nlen = deqi ? (gen2 < gen1 ? 1 : -1)
                              : (j = (gptr[diffct].sublen)) > 0 ? j + 1 : j - 1;
                  if (nlen > olen) {
                    /* The new string is better than the existing one */
                    substruc->genno = gen2;
                    substruc->sublen = nlen;
                    substruc->backptr = deqi ? 0 : gptr + diffct;
                  }
                  break;
                }
              }
            else
            /* This is a new word difference at this level, so we define a new
               vertexd in graph.
            */
            {
              gct++;
              if (gct >= maxv) {
                /* We need more space for vertices. Allocate twice the preceding
                   space and copy existing data.
                */
                tmalloc(ngptr, struct vertexd, 2 * maxv);
                if (kbm_print_level >= 3)
                  printf("    #Allocating more space in diff_reduce.\n");
                for (i = 0; i < maxv; i++) {
                  ngptr[i].genno = gptr[i].genno;
                  ngptr[i].diffno = gptr[i].diffno;
                  ngptr[i].sublen = gptr[i].sublen;
                  substruc = gptr[i].backptr;
                  if (substruc == 0)
                    ngptr[i].backptr = 0;
                  else
                    for (j = i - 1;; j--)
                      if (substruc == gptr + j) {
                        ngptr[i].backptr = ngptr + j;
                        break;
                      }
                }
                tfree(gptr);
                gptr = ngptr;
                maxv *= 2;
              }
              /* Define the new vertexd. */
              substruc = gptr + gct;
              nlen = deqi ? (gen2 < gen1 ? 1 : -1)
                          : (j = (gptr[diffct].sublen)) > 0 ? j + 1 : j - 1;
              substruc->genno = gen2;
              substruc->diffno = newdiff;
              substruc->sublen = nlen;
              substruc->backptr = deqi ? 0 : gptr + diffct;
              cf[newdiff] = TRUE;
            }
          }
        }
      } /*End of loop over gen2 */

      if (donesub)
        break;

      /* Go on to next word difference from previous level. */
      if (diff == identity) {
        if (level == 1)
          break;
        diffct = gpref[level - 2] + 1;
      }
      else
        diffct++;
      if (diffct > gpref[level - 1])
        break;
      diff = gptr[diffct].diffno;
    } /* end of loop over word differences at previous level */

    gpref[level] = gct;
  }

  tfree(gptr);
  tfree(cf);
  tfree(gpref);
  return 0;
}
