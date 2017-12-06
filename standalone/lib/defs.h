/* file defs.h - 13. 9. 94.  */

/* 13/1/98 added typedef of `gen' for group generator - it is no longer
 * constrained to have type char.
 */
#ifndef KBMAG_DEFS_H
#define KBMAG_DEFS_H

#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <stdlib.h>
#include <unistd.h>

#include <inttypes.h>

#define MAXINT 2147483647
#define MAXSHORT 32767
#define MAXUSHORT 65535
#define MAXCHAR 127
#define MAXUCHAR 255

#define tmalloc(D, T, N)                                                       \
  {                                                                            \
    D = (T *)malloc(sizeof(T) * (N));                                          \
    kbm_store_ptrs++;                                                          \
    if (D == 0) {                                                              \
      fprintf(stderr, "Malloc failed to allocate %" PRIuPTR " bytes.\n",       \
              sizeof(T) * (N));                                                \
      exit(2);                                                                 \
    }                                                                          \
  }
#define tfree(D)                                                               \
  {                                                                            \
    if (D) {                                                                   \
      free((char *)D);                                                         \
      D = 0;                                                                   \
      kbm_store_ptrs--;                                                        \
    }                                                                          \
  }

#define FALSE 0
#define TRUE 1
typedef char boolean;
#define MAXGEN MAXCHAR /* maximum number of generators */
typedef char gen;      /* for generators of monoids and groups */

/* The following macro is used for finding base-prefix of names of fsa's */
#define base_prefix(w)                                                         \
  {                                                                            \
    char *p = w;                                                               \
    while (*p)                                                                 \
      if (*p == '.')                                                           \
        *p = '\0';                                                             \
      else                                                                     \
        p++;                                                                   \
  }

#include "rws.h"

/* function prototypes */
boolean is_int(char *x);
boolean isdelim(int c);
boolean isvalid(int c);
boolean read_int(FILE *rfile, int *integ, int *delim);
boolean read_string(FILE *rfile, char *string, int *delim);
boolean read_word(FILE *rfile, gen *gen_word, gen *end_word, int *delim,
                  char **name, int num_names, boolean check);
int add_expanded_word_to_buffer(FILE *wfile, gen *word, char **symbols);
int add_iword_to_buffer(FILE *wfile, int *word, char **symbols);

int initialise_wd_fsa(fsa *wd_fsaptr, srec *alphptr, int maxwdiffs);
int add_wd_fsa(fsa *wd_fsaptr, reduction_equation *eqn, int *inv,
               boolean reverse, reduction_struct *rsptr);
int build_wd_fsa(fsa *wd_fsaptr, boolean *new_wd, reduction_struct *rsptr);
void clear_wd_fsa(fsa *wd_fsaptr);
int make_full_wd_fsa(fsa *wd_fsaptr, int *inv, int start_no,
                     reduction_struct *rsptr);

int initialise_wd_fsa_cos(fsa *wd_fsaptr, srec *alphptr, int maxwdiffs);
int add_wd_fsa_cos(fsa *wd_fsaptr, reduction_equation *eqn, int *inv,
                   boolean reverse, reduction_struct *rs);
int build_wd_fsa_cos(fsa *wd_fsaptr, boolean *new_wd, reduction_struct *rs);
int make_full_wd_fsa_cos(fsa *wd_fsaptr, int *inv, int start_no,
                         reduction_struct *rs);

int add_word_to_buffer(FILE *wfile, gen *word, char **symbols);
int genstrcmp(gen *c, gen *d);
int genstrlen(gen *c);
int int_len(int n);
int stringlen(char *c);
void add_to_buffer(int n, char *w);
void check_next_char(FILE *rfile, int c);
void genstrcat(gen *c, gen *d);
void genstrcpy(gen *c, gen *d);
void printbuffer(FILE *wfile);
void process_names(char **name, int num_names);
void read_delim(FILE *rfile, int *delim);
void read_ident(FILE *rfile, char *ident, int *delim, boolean inv);

void skip_gap_expression(FILE *rfile, int *delim);

void srec_clear(srec *srptr);
void srec_copy(srec *srptr1, srec *srptr2);
boolean srec_equal(srec *srptr1, srec *srptr2);

int diff_reduce(gen *w, reduction_struct *rs_wd);
int diff_reduce_cos(gen *w, reduction_struct *rs_wd);
int diff_reduce_wl(gen *w, reduction_struct *rs_wd);

int calculate_inverses(int **invptr, int ngens, reduction_struct *rsptr);

int kbprog(rewriting_system *rwsptr);
void should_we_halt(rewriting_system *rwsptr);
void make_fsa_nice(rewriting_system *rwsptr);
void type_sort_eqns_final(rewriting_system *rwsptr);
void typelength_sort_eqns(int n, rewriting_system *rwsptr);
void sort_eqns(int n, rewriting_system *rwsptr);

int midfa_labeled_minimize(fsa *fsaptr);

void print_kboutput(FILE *wfile, rewriting_system *rwsptr);
void print_wdoutput(FILE *wfile, char *suffix, rewriting_system *rwsptr);
void print_rws_simple(FILE *wfile, rewriting_system *rwsptr);

int fsa_checkgeowa(fsa *geowaptr, fsa *diffptr, reduction_equation *eqnptr,
                   int maxeqns);

#endif
