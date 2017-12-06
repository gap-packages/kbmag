/* file fsa.h  16.9.94.
 * This header file for finite state automata contains the definitions
 * of the fsa (finite state automaton) and srec (set record) structures.
 * and macros for accessing and setting entries in the transition table.
 *
 * 9/1/98.  New version to allow more than 127 generators.
 *          Generators have type `gen' instead of char, where here we
 *          define `gen' to be unsigned short.
 * 2/10/97. Added the compact storage type for fsa tables.
 * 16.8.96. Added field comment_state_numbers to table_struc structure.
 * 7. 5.96. Added srec_type "list of integers" (LISTOFINTS)
 * 13.9.95. Added srec_type "list of words" (LISTOFWORDS)
 * 25.7.95. Added type "MIDFA" of fsa - this is a fsa that would be
 *	deterministic if it were not for the fact that it may have
 *	multiple initial states. Used for word-difference machines in
 *      coset automatic groups.
 *	Can still have densely stored table.
 * 5. 12. 94. - added sparse table storage with some rows stored densely.
 *            - designed macros for all accessing of table entries.
 * 25. 11. 94. - added filename component to transition table structure,
 *               for possible external storage of table (probably won't be
 *               used in the end).
 * 17.11.94. - implemented labeled format
 */

#ifndef KBMAG_FSA_H
#define KBMAG_FSA_H

typedef enum {
  SIMPLE,
  IDENTIFIERS,
  WORDS,
  LISTOFWORDS,
  LISTOFINTS,
  STRINGS,
  LABELED,
  PRODUCT
} srec_type;
extern char *kbm_type_names[];
typedef enum { DENSE, SPARSE, COMPACT } storage_type;
typedef enum {
  DFA,
  NFA,
  MIDFA,
  MINIMIZED,
  BFS,
  ACCESSIBLE,
  TRIM,
  RWS
} kbm_flag_strings;
#define num_kbm_flag_strings 8
extern char *kbm_flag_names[];
/* definition of kbm_type_names and kbm_flag_names in fsa.c */

typedef short setToLabelsType;
/* for srec field member - may wish to change this */
typedef struct srec {
  /* This mirrors the set record type defined in the GAP format.
   * We won't require the `format' field here, since names will always be
   * stored as a simple list.
   * In the `word' type, the names will be stored as strings of `gen's,
   * and the base component should be of type identifiers, where number i
   * in the string corresponds to the name of identifier number i in the
   * base.names list.
   * A list of integer is stored as a simple list preceded by its length.
   */
  srec_type type;
  int size;
  char **names;     /* Used with identifiers or strings */
  gen **words;      /* The type gen is used with words  */
  gen ***wordslist; /* For list of words type  - if wordslist[i] contains
                     * n words, these will be stored in wordslist[i][j]
                     * for 0<=j<n, with wordslist[i][n] set to 0.
                     */
  int **intlist;    /* For list of integers type - if intlist[i] is a list of
                     * length n, then the integers will be stored as intlist[i][j]
                     * for 1<=j<=n, with intlist[i][0]=n.
                     */
  int arity;        /* for product type */
  char padding; /* for product type - the printing char. for padding symbol */
  char *alphabet[MAXGEN + 1];   /* names of base-alphabet for words */
  int alphabet_size;            /* length of base-alphabet for words */
  struct srec *base;            /* for product type */
  struct srec *labels;          /* for labeled type */
  setToLabelsType *setToLabels; /* for labeled type */
} srec;

typedef struct {
  /* This is used to store the transition table of a finite state automaton.
   * The data structure depends on the table_type.
   * Currently, there are two main types, dense and sparse
   * dense is the simplest and fastest - entries are stored in a 2-dimensional
   * array structure, with rows corresponding to generators. It can be
   * expensive in terms of space.
   * Dense format can only be used for deterministic machines (the
   * dense nondeterministic type is not yet implemented).
   * In sparse storage, the transitions from a given state are stored in
   * a sequence of memory locations, with each transition taking up two
   * locations, the first a generator and the second the target of the
   * transition from  the given state with that generator as label.
   * There is a pointer to this sequence of locations for each state.
   * sparse format is not suitable if new transitions need to be added
   * from a given state once the structure has been set up.
   * If the storage type is sparse, but the "dense_rows" field is a positive
   * integer n, then the transitions for the first n states are stord in dense
   * format, and the remainder in sparse format. This compromise hopefully
   * allows reasonably fast access without using too much space - this is based
   * on the assumption that there will be most transitions for the states with
   * the smallest numbers. The default target mechanism is not yet implemented -
   * if read from an input file, the information will be inserted into the
   * table. and dense format will be used. If the filename pointer is nonzero,
   * then the transition table is not present in the file at all - it is stored
   * externally in unformatted form in the file *filename (possibly with other
   * information). 2/10/97 - a third storage type, compact is added. This is as
   * in sparse, but each (generator,state) pair is stored in a single 4-byte
   * word, with the generator stored in the first byte. (So we have a maximum of
   * 256 edge-label.)
   */
  char *filename;
  storage_type table_type;
  storage_type printing_format;
  /* This specifies the format for printing, which may not be the same as
   * that for storing - again dense only applicable to dfa's.
   */
  boolean comment_state_numbers;
  /* If this is set true, then when printing the table, the entry
   * corresponding to each state is followed by a comment giving the
   * number of that state. This is to increase readability of the table.
   */
  int numTransitions; /* The number of nonzero transitions in the table.
                       * Used mainly when reading in.
                       */
  int maxstates;      /* The maximum number of states for which space has been
                       * allocated
                       * Only really meaningful for dense storage type.
                       */
  int denserows; /* Only applies in sparse storage type - the number of states
                  * for which the transitions are store densely.
                  */
  int **table_data_ptr;
  /* This field is used for setting and accessing the transitions.
   * Its usage will depend on the storage type.
   * Let k be the target of the transition from state i with letter j.
   * For type dense, k will be accessed as table_data_ptr[j][i].
   * For type sparse, table_data_ptr[i] points to a location in table_data
   * which is the beginning of the sequence of transitions from state i.
   * NOTE THIS FUNDAMENTAL DIFFERENCE - for sparse type, the 'i' is  a
   * state number, but for dense type, it would be an edge number.
   * In sparse type, for i<=denserows, table_data_ptr[i][j] = k.
   *
   * In all cases, table_data_ptr[0] will point at the beginning of the
   * data.
   */
  int ***table_data_dptr;
  /* table_data_dptr  is only used for dense storage of 2-variable
   * automata, when it is defined to make table_data_dptr[i1][i2][j]
   * the target of the transition from the state j with edge-label
   * the pair (i1,i2) - this is purely for speed of access.
   * NOTE This last field should be set whenever required using the
   * function fsa_table_dptr_init().
   */
  unsigned int **ctable_data_ptr;
  /* For the compact form of data storage */
} table_struc;

typedef struct {
  /* This mirrors the finite state automaton type in the GAP format.
   */
  srec *states;
  srec *alphabet;
  int num_initial; /* The number of initial states.
                    * The list itself is set whenever this is nonzero.
                    */
  int *initial;
  boolean *is_initial; /* this array is only set when required.
                        * It should be deallocated immediately after use.
                        */
  int num_accepting;   /* The number os accepting states. If this number is
                        * equal to 0 or states->size>1, then the list itself
                        * accepting need not be set.
                        */
  int *accepting;
  boolean *is_accepting;  /* this array is only set when required.
                           * It should be deallocated immediately after use.
                           */
  boolean *is_accessible; /* this array is only set when required.
                           * It should be deallocated immediately after use.
                           */
  boolean flags[num_kbm_flag_strings];
  /* set to TRUE if corresponding flag is set.
   * the entries correspond to flag_list
   */
  table_struc *table;
} fsa;


/* The following macros should be used for accessing and setting transition
 * targets outside of the file fsa.c.
 * They have been designed to provide a stable access, whilst still being
 * reasonably fast - because fast access of table entries is extremely
 * time-critical in many applications.
 * "dense" is intended to be a boolean set to true if the storage type of
 * the table is dense, and false if sparse.
 * "table" should be the table_data_ptr field in either case.
 * "denserows" should be set equal to the denserows component of the table.
 * "e" is the edge-number and "s" the state number for which the target
 * state is required.
 * For sparse format, the function sparse_target (in fsa.c) is called.
 * Use dense_target when the storage type is known to be dense.
 */
#define target(dense, table, e, s, denserows)                                  \
  (dense ? table[e][s]                                                         \
         : s <= denserows ? table[s][e]                                        \
                          : sparse_target(e, table[s], table[s + 1]))
#define dense_target(table, e, s) (table[e][s])
#define set_dense_target(table, e, s, t) (table[e][s] = t)

/* The next two are for accessing and setting targets for 2-variable
 * fsa's stored in dense type.
 * "dtable" should be set equal to the table_data_dptr field.
 */
#define dense_dtarget(dtable, g1, g2, s) (dtable[g1][g2][s])
#define set_dense_dtarget(dtable, g1, g2, s, t) (dtable[g1][g2][s] = t)


/* function prototypes */
extern fsa *fsa_and_not(fsa *fsaptr1, fsa *fsaptr2, storage_type op_table_type,
                        boolean destroy, char *tempfilename);
extern fsa *fsa_and(fsa *fsaptr1, fsa *fsaptr2, storage_type op_table_type,
                    boolean destroy, char *tempfilename);
extern fsa *fsa_concat(fsa *fsaptr1, fsa *fsaptr2, boolean destroy);
extern fsa *fsa_exists(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                       char *tempfilename);
extern fsa *fsa_laband(fsa *fsaptr1, fsa *fsaptr2, storage_type op_table_type,
                       boolean destroy, char *tempfilename);
extern fsa *fsa_not(fsa *fsaptr, storage_type op_table_type);
extern fsa *fsa_or(fsa *fsaptr1, fsa *fsaptr2, storage_type op_table_type,
                   boolean destroy, char *tempfilename);
extern fsa *fsa_star(fsa *fsaptr, boolean destroy);


extern fsa *fsa_composite(fsa *mult1ptr, fsa *mult2ptr,
                          storage_type op_table_type, boolean destroy,
                          char *compfilename, boolean readback);
extern fsa *fsa_genmult2(fsa *genmultptr, storage_type op_table_type,
                         boolean destroy, char *genmult2filename,
                         boolean readback);
extern fsa *fsa_geopairs(fsa *waptr, fsa *diffptr, storage_type op_table_type,
                         boolean destroy, char *tempfilename, boolean readback);
extern fsa *fsa_micomposite(fsa *mult1ptr, fsa *mult2ptr,
                            storage_type op_table_type, boolean destroy,
                            char *compfilename, boolean readback);
extern fsa *fsa_migm2(fsa *migmptr, storage_type op_table_type, boolean destroy,
                      char *migm2filename, boolean readback, char *prefix);
extern fsa *fsa_minkb(fsa *minredptr, fsa *waptr, fsa *diffptr,
                      storage_type op_table_type, boolean destroy,
                      char *tempfilename);
extern fsa *fsa_minred(fsa *waptr, storage_type op_table_type, boolean destroy,
                       char *tempfilename);
extern fsa *fsa_mireverse(fsa *fsaptr, storage_type op_table_type,
                          boolean destroy, char *tempfilename);
extern fsa *fsa_reverse(fsa *fsaptr, storage_type op_table_type,
                        boolean destroy, boolean subsets, char *tempfilename);
extern fsa *fsa_submult(fsa *subwaptr, fsa *multptr, storage_type op_table_type,
                        boolean destroy, char *tempfilename, boolean readback);
extern fsa *fsa_wa_cos(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                       char *tempfilename);
extern fsa *fsa_wa(fsa *fsaptr, storage_type op_table_type, boolean destroy,
                   char *tempfilename);
extern fsa *midfa_determinize(fsa *fsaptr, storage_type op_table_type,
                              boolean destroy, char *tempfilename);
extern fsa *migm_determinize(fsa *migmptr, storage_type op_table_type,
                             boolean destroy, char *tempfilename);
extern fsa *nfa_determinize(fsa *fsaptr, storage_type op_table_type,
                            boolean eps_trans, boolean destroy, boolean subsets,
                            char *tempfilename);

extern boolean fsa_equal(fsa *fsaptr1, fsa *fsaptr2);

extern int fsa_bfs(fsa *fsaptr);
extern int fsa_clear_rws(fsa *fsaptr);
extern int fsa_count(fsa *fsaptr);
extern int fsa_delete_state(fsa *fsaptr, int stateno);
extern int fsa_enumerate(FILE *wfile, fsa *fsaptr, int min, int max,
                         boolean putcomma, int stateno);
extern int fsa_growth(FILE *wfile, fsa *fsaptr, unsigned *primes, char *var);
extern int fsa_ip_labeled_minimize(fsa *fsaptr);
extern int fsa_ip_minimize(fsa *fsaptr);
extern int fsa_labeled_minimize(fsa *fsaptr);
extern int fsa_minimize(fsa *fsaptr);
extern int fsa_swap_coords(fsa *fsaptr);
extern int fsa_table_dptr_init(fsa *fsaptr);

extern void fsa_clear(fsa *fsaptr);
extern void fsa_copy(fsa *fsaptr1, fsa *fsaptr2);
extern void fsa_init(fsa *fsaptr);
extern void fsa_print(FILE *wfile, fsa *fsaptr, char *name);
extern void fsa_read(FILE *rfile, fsa *fsaptr, storage_type table_storage_type,
                     int dr, int maxstates, boolean assignment, char *name);
extern void fsa_set_is_accepting(fsa *fsaptr);
extern void fsa_set_is_accessible(fsa *fsaptr);
extern void fsa_set_is_initial(fsa *fsaptr);
extern void fsa_table_init(table_struc *tableptr, int maxstates, int ne);

extern int words_and_not(fsa *fsaptr1, fsa *fsaptr2, gen **words, int maxwords);

extern int sparse_target(int g, int *p1, int *p2);

int diff_no(fsa *wd_fsaptr, gen *w);

void compressed_transitions_read(fsa *fsaptr, FILE *rfile);

int fsa_makemult(fsa *genmultptr, int g);
int fsa_makemult2(fsa *genmult2ptr, int g1, int g2);

int fsa_mimakemult(fsa *migmptr, int g, char *prefix);
int fsa_mimakemult2(fsa *migm2ptr, int g1, int g2, char *prefix);

int mimult_minimize(fsa *fsaptr);

#endif
