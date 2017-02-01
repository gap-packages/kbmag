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

#define MAXINT 		2147483647
#define MAXSHORT 	32767
#define MAXUSHORT 	65535
#define MAXCHAR 	127
#define MAXUCHAR 	255

#define tmalloc(D,T,N) {D = (T *) malloc(sizeof(T)*(N)); \
 kbm_store_ptrs++;\
  if (D==0) { fprintf(stderr,"Malloc failed to allocate %"PRIuPTR" bytes.\n",\
  sizeof(T)*(N)); exit(2);}}
#define tfree(D) {if (D) {free( (char *) D); D=0; kbm_store_ptrs--;}}

#define FALSE 0
#define TRUE  1
typedef  char boolean;
#define MAXGEN MAXCHAR /* maximum number of generators */
typedef char gen; /* for generators of monoids and groups */

/* The following macro is used for finding base-prefix of names of fsa's */
#define base_prefix(w) {char * p=w; while (*p) if (*p=='.') *p='\0'; else p++;}


/* function prototypes */
extern boolean is_int();
extern boolean isdelim();
extern boolean isvalid();
extern boolean read_int();
extern boolean read_string();
extern boolean read_word();
extern boolean slow_check_rws_reduce_rk();
extern boolean slow_check_rws_reduce();
extern boolean srec_equal();
extern boolean table_equal();
extern int add_expanded_word_to_buffer();
extern int add_iword_to_buffer();
extern int add_wd_fsa_cos();
extern int add_wd_fsa();
extern int add_word_to_buffer();
extern int build_wd_fsa_cos();
extern int build_wd_fsa();
extern int calculate_inverses();
extern int diff_no();
extern int diff_reduce_cos();
extern int diff_reduce_wl();
extern int diff_reduce();
extern int genstrcmp();
extern int genstrlen();
extern int initialise_wd_fsa_cos();
extern int initialise_wd_fsa();
extern int insert();
extern int int_len();
extern int kbprog();
extern int make_full_wd_fsa_cos();
extern int make_full_wd_fsa();
extern int midfa_labeled_minimize();
extern int mimult_minimize();
extern int modify_table();
extern int rk_init();
extern int rws_reduce();
extern int slow_rws_reduce_rk();
extern int slow_rws_reduce();
extern int sparse_target();
extern int stringlen();
extern int words_and_not();
extern void add_to_buffer();
extern void build_quicktable();
extern void check_next_char();
extern void clear_wd_fsa();
extern void compressed_transitions_read();
extern void genstrcat();
extern void genstrcpy();
extern void make_fsa_nice();
extern void output_and_exit_kbprogcos();
extern void print_kboutput();
extern void print_rws_simple();
extern void print_wdoutput();
extern void printbuffer();
extern void process_names();
extern void read_delim();
extern void read_extra_kbinput();
extern void read_gens();
extern void read_ident();
extern void read_inverses();
extern void read_kbinput_simple();
extern void read_kbinput();
extern void read_subgens();
extern void rk_add_lhs();
extern void rk_clear();
extern void rk_reset();
extern void rws_clear();
extern void set_defaults();
extern void set_separator();
extern void should_we_halt();
extern void skip_gap_expression();
extern void sort_eqns();
extern void srec_clear();
extern void srec_copy();
extern void type_sort_eqns_final();
extern void typelength_sort_eqns();


#endif
