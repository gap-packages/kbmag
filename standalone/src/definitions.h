/* definitions.h  9/11/94
 * 9/1/98 change type of generator from char to `gen' 
 * This file contains definitions of external variables used in all programs
 */
int	kbm_store_ptrs = 0;
  /* This is incremented every time malloc is called
   * and decremented every time free is called.
   * It should be zero whenever exit(0) is called (although this
   * is not normally checked).
   * It will not usually be 0 when exit(1) (error condition) is called.
   */         
int	kbm_print_level = 1;
  /* kbm_print_level = 0 - no printing to stdout
   * kbm_print_level = 1 - progress reports printed (default)
   * kbm_print_level = 2 - diagnostic output.
   */
char 	kbm_buffer[1024];
  /* Used to store words, lines, etc. when reading and printing */
int	kbm_algno;
int	kbm_gen_no[65536]; /* changed 9/1/98 */
  /* To help fast reading of large sets of words, two specials formats
   * for monoid generators are recognised:
   * a) single letter characters (usually 'A' will be inverse of 'a', etc.)
   * b) names of form <prefix><posint>, for a fixed prefix, where posint should
   *    be at most MAXGEN.
   * In case a), the variable kbm_algno is set equal to 0, and the array
   * kbm_gen_no is used to translate from rws.gen_name back to the gneerator
   * number.
   * In case b), kbm_algno is set equal to the length of <prefix> (which must
   * be strictly positive), and kbm_gen_no is defined on the <posint> suffixes
   * to get the generator number back from the name.
   * If neither case a) nor case b) applies then kbm_algno is set equal to -1,
   * and names are located in the list by a straightforward linear search - of
   * course this will be considerably slower for long lists of words.
   */
boolean  kbm_large=FALSE;
boolean  kbm_huge=FALSE;
  /* Means the problem is believed to be large/huge in some sense - the
   * intial size of the hash-tables are made larger.
   */
