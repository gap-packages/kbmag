/* File miscio.c - 11. 10. 94.
 * 6/11/99 added add_expanded_word_to_buffer for dbae.
 * 9/10/98 moved set_separator to this file. More convenient here.
 * 9.1.98. change of `gen' to `char' for generator type - requires
 *         functions genstrlen, genstrcmp, genstrcat to be written
 *         with this type.
 * 21. 9. 95. - return type of read_word changed from void to boolean,
 *              to distinguish between the cases when no word is read, and
 *              when the empty word is read.
 *              do same for read_int, read_string (although not needed yet)
 * 13. 8. 95. - added function read_word_list to read a list of words.
 * 13. 3. 95. - skip_gap_expression written
 * 27. 2. 95. - allowed generators of form string^-1 - read_ident gets
 *              an extra parameter.
 * 12. 12. 94. transferred the function process_names to this file.
 * This file contains some miscellaneous input and output functions that
 * are used by both automata and string-rewriting programs.
 * Also we recode the standard function strlen as stringlen to avoid
 * some type incompatibilities resulting in warning messages on solaris!
 */

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "externals.h"

/* Note: '.' is not included in list of delimiters, since identifiers may
 * contain dots.
 * Integers are exceptional, however, in that they may be terminated by a
 * '.' as well as by as delimiter.
 * identifiers, strings and words are terminated by a delimiter.
 */
boolean isdelim(int c)
{
  return c == '^' || c == '*' || c == '[' || c == ']' || c == ',' || c == '(' ||
         c == '{' || c == '}' || c == ')' || c == ';' || c == '\"' ||
         c == ':' || c == EOF;
}

/* Checks if symbol is valid in an identifier */
boolean isvalid(int c)
{
  return isalpha(c) || isdigit(c) || c == '_' || c == '.';
}

/* This is the basic character-reading function, which all other routines
 * call.
 * It skips over a backslash '\' followed by a newline '\n'.
 * It replaces tabs, newlines and comments (starting with # ending with
 * carriage return) with a space.
 * Otherwise it returns the next character read.
 * Use getc diretcly when readin literal strings.
 */
static int read_char(FILE *rfile)
{
  static int last; /* used to remember a character from the last call */
  int n;
  n = last ? last : getc(rfile);
  /* The input may contain a '\' character which is printed before '\n'
   * -- this is particularly true if the input file is generated by GAP
   */
  while (n == '\\') {
    n = getc(rfile);
    if (n == '\n')
      n = getc(rfile);
    else {
      last = n;
      return (int)'\\';
    }
  }
  if (n == '#')
    while ((n = getc(rfile)) != '\n' && n != EOF)
      ;
  if (n == '\n' || n == '\t')
    return (' ');
  return (n);
}

/* The next non-white character is expected to be 'c'.
   If not exit with error message.
*/
void check_next_char(FILE *rfile, int c)
{
  int n;
  while ((n = read_char(rfile)) == ' ')
    ;
  if (n == '{' && c == '[')
    return;
  if (n == '}' && c == ']')
    return;
  if (n != c) {
    fprintf(stderr, "#Input error: \'%c\' expected (not %c).\n", c, n);
    exit(1);
  }
}

/* Read next delimiter. */
void read_delim(FILE *rfile, int *delim)
{
  int n;
  while ((n = read_char(rfile)) == ' ')
    ;
  if (!isdelim(n)) {
    fprintf(stderr, "#Input error: delimiter expected (not %c).\n", n);
    exit(1);
  }
  *delim = n;
  if (*delim == '{')
    *delim = '[';
  if (*delim == '}')
    *delim = ']';
}

/* Read stuff into token up to next delimiter or space  -
 * leading spaces are removed from stuff.
 */
static void read_token(FILE *rfile, char *token, int *delim)
{
  int n;
  *token = '\0';
  while ((n = read_char(rfile)) == ' ')
    ;
  while (!isdelim(n) && !(n == ' ')) {
    *(token++) = n;
    n = read_char(rfile);
  }
  *token = '\0';
  *delim = n;
  if (*delim == '{')
    *delim = '[';
  if (*delim == '}')
    *delim = ']';
}

/* Skip the next GAP expression -
 * probably not perfect, but should be adequate for the use intended.
 */
void skip_gap_expression(FILE *rfile, int *delim)
{
  int n, br_ct = 0;
  char br_rec[1024];

  while (1) {
    read_token(rfile, kbm_buffer, delim);
    if (strcmp(kbm_buffer, "function") == 0)
      br_rec[br_ct++] = 'f'; /*marks that we are in a function definition */
    else if (strcmp(kbm_buffer, "end") == 0) {
      if (br_ct > 0 && br_rec[br_ct - 1] == 'f')
        br_ct--;
      else {
        fprintf(stderr, "#Input error: \"end\" without \"function\".\n");
        exit(1);
      }
    }
    if (*delim == '\'') {
      n = getc(rfile);
      if (n == '\\')
        n = getc(rfile);
      n = getc(rfile);
      if (n != '\'') {
        fprintf(stderr, "#Input error: ' expected.\n");
        exit(1);
      }
    }
    else if (*delim == '\"') {
      do {
        n = getc(rfile);
        while (n == '\\') {
          n = getc(rfile);
          n = getc(rfile);
        }
        if (n == '\n' || n == EOF) {
          fprintf(stderr, "#Input error: newline or EOF in string.\n");
          exit(1);
        }
      } while (n != '\"');
    }
    else if (*delim == '(' || *delim == '[' || *delim == '{') /*}*/
      br_rec[br_ct++] = *delim;
    else if (*delim == ')' && br_ct > 0) {
      if (br_rec[br_ct - 1] == '(')
        br_ct--;
      else {
        fprintf(stderr, "#Input error: ')' without '('.\n");
        exit(1);
      }
    }
    else if (*delim == ']') {
      if (br_ct > 0 && br_rec[br_ct - 1] == '[')
        br_ct--;
      else {
        fprintf(stderr, "#Input error: ']' without '['.\n");
        exit(1);
      }
    }
    /*{*/
    else if (*delim == '}') {
      if (br_ct > 0 && br_rec[br_ct - 1] == '{') /*}*/
        br_ct--;
      else {
        fprintf(stderr,
                /*{*/ "#Input error: '}' without '{'.\n"); /*}*/
        exit(1);
      }
    }
    else if (br_ct == 0 && (*delim == ',' || *delim == ')' || *delim == ';'))
      break;
    if (br_ct >= 1024) {
      fprintf(stderr, "#Input error: Bracket level too deep.\n");
      exit(1);
    }
  }
}

/* Read next identifier, field name, etc.
 * if inv is true, it is allowed to end ^-1.
 */
void read_ident(FILE *rfile, char *ident, int *delim, boolean inv)
{
  int n;
  char *ptr = ident;
  while ((n = read_char(rfile)) == ' ')
    ;
  while (n != ' ' && !isdelim(n)) {
    *(ptr++) = n;
    n = read_char(rfile);
  }
  if (n == ' ')
    while ((n = read_char(rfile)) == ' ')
      ;
  if (!isdelim(n)) {
    fprintf(stderr,
            "#Input error: delimiter expected to terminate ident (not %c).\n",
            n);
    exit(1);
  }
  if (inv && n == '^') {
    /* With some reluctance, I allow a generator to be called {ident}^-1 */
    *(ptr++) = '^';
    check_next_char(rfile, '-');
    *(ptr++) = '-';
    check_next_char(rfile, '1');
    *(ptr++) = '1';
    read_delim(rfile, &n);
  }
  *ptr = '\0';
  *delim = n;
  if (*delim == '{')
    *delim = '[';
  if (*delim == '}')
    *delim = ']';
}

/* Read next integer - may be empty, when 0 is returned as *integ.
 * NOTE integer can be terminated by a '.' as well as a delimiter
 * FALSE returned if no int read, otherwise TRUE.
 */
boolean read_int(FILE *rfile, int *integ, int *delim)
{
  int n, value = 0;
  boolean neg = FALSE, ans = FALSE;
  while ((n = read_char(rfile)) == ' ')
    ;
  do {
    if (n == '-' && value == 0)
      neg = TRUE;
    else if (isdigit(n)) {
      value = 10 * value + n - '0';
      ans = TRUE;
    }
    else if (n == ' ' || n == '.' || isdelim(n))
      break;
    else {
      fprintf(stderr, "#Input error: integer expected.\n");
      exit(1);
    }
    n = read_char(rfile);
  } while (1);
  if (n == ' ')
    while ((n = read_char(rfile)) == ' ')
      ;
  if (n != '.' && !isdelim(n)) {
    fprintf(stderr,
            "#Input error: delimiter expected to terminate integer (not %c).\n",
            n);
    exit(1);
  }
  if (neg)
    value = -value;
  *integ = value;
  *delim = n;
  if (*delim == '{')
    *delim = '[';
  if (*delim == '}')
    *delim = ']';
  return ans;
}


/* Read next string (enclosed in quotes) - if delim comes first, return
 * empty string as string.
 * FALSE returned if no string read, otherwise TRUE.
 */
boolean read_string(FILE *rfile, char *string, int *delim)
{
  int n;
  char *ptr = string;
  boolean ans = FALSE;
  while ((n = read_char(rfile)) == ' ')
    ;
  if (n == '\"') {
    ans = TRUE;
    do {
      n = getc(rfile);
      while (n == '\\') {
        n = getc(rfile);
        *(ptr++) = n;
        n = getc(rfile);
      }
      if (n == '\n' || n == EOF) {
        fprintf(stderr, "#Input error: newline or EOF in string.\n");
        exit(1);
      }
      if (n != '\"')
        *(ptr++) = n;
      else
        break;
    } while (1);
    read_delim(rfile, delim);
    /* We want the next delimiter after the terminating quotes */
  }
  else if (!isdelim(n)) {
    fprintf(stderr,
            "#Input error: delimiter expected in read_string (not %c).\n", n);
    exit(1);
  }
  else
    *delim = n;
  if (*delim == '{')
    *delim = '[';
  if (*delim == '}')
    *delim = ']';
  *ptr = '\0';
  return ans;
}

/* name is a list of num_names names (probably names of monoid generators).
 * First they are checked for validity - they must start with a letter or
 * underscore, and all characters must be alphanumeric '_' or '.'.
 * (or they can end in ^-1).
 * They are then checked to see if they comply with one of the two
 * special formats a) and b) described at the top of the file rwsio.h.
 * If so, then the external variables kbm_algno and kbm_gen_no are set
 * accordingly. These are used by the next function read_next_word for
 * fast reading of words in the generators.
 * Otherwise, kbm_algno is set to -1, and words are located in the list
 * by a simple search.
 */
void process_names(char **name, int num_names)
{
  int i, j, l;
  char *genname, *genname1, *ptr;

  for (i = 0; i <= MAXGEN; i++)
    kbm_gen_no[i] = 0;
  kbm_algno = 0;
  if (num_names == 0)
    return;
  for (i = 1; i <= num_names; i++) {
    genname = name[i];
    if (stringlen(genname) == 0) {
      fprintf(stderr, "#Input error: a generator name has length 0.\n");
      exit(1);
    }
    if (stringlen(genname) > 1)
      kbm_algno = -1;
    if (!isalpha(genname[0]) && genname[0] != '_') {
      fprintf(stderr,
              "#Input error: generators should start with a letter or `_'.\n");
      exit(1);
    }
    if (kbm_algno == 0) {
      if (kbm_gen_no[genname[0]] != 0) {
        fprintf(stderr, "#Input error: repeated generator name.\n");
        exit(1);
      }
      kbm_gen_no[genname[0]] = i;
    }
  }
  if (kbm_algno == 0)
    return; /* all generators are single letters or underscore. */

  for (i = 1; i <= num_names; i++) {
    genname = name[i];
    l = stringlen(genname);
    for (j = 0; j < l; j++)
      if (!isvalid(genname[j])) {
        if (j != l - 3 || genname[j] != '^' || genname[j + 1] != '-' ||
            genname[j + 2] != '1') {
          fprintf(stderr,
                  "#Input error: generator %s: names must be alphanumeric, "
                  "'_', or '.'.\n",
                  genname);
          exit(1);
        }
        else
          break;
      }
    for (j = 1; j < i; j++)
      if (strcmp(genname, name[j]) == 0) {
        fprintf(stderr, "#Input error: repeated generator name.\n");
        exit(1);
      }
  }

  /* Try to locate prefix  for Case b). */
  genname1 = name[1];
  ptr = genname1 + stringlen(genname1) - 1;
  if (!isdigit(*ptr)) { /* not Case b) */
    kbm_algno = -1;
    return;
  }
  while (isdigit(*ptr))
    ptr--;
  kbm_algno = ptr - genname1 + 1;
  if (atoi(genname1 + kbm_algno) > MAXGEN) { /* numerical subscript too large */
    kbm_algno = -1;
    return;
  }

  kbm_gen_no[atoi(genname1 + kbm_algno)] = 1;
  for (i = 2; i <= num_names; i++) {
    genname = name[i];
    if (stringlen(genname) < kbm_algno + 1) { /* not Case b) */
      kbm_algno = -1;
      return;
    }
    for (j = 0; j < kbm_algno; j++)
      if (genname[j] != genname1[j]) { /* not Case b) */
        kbm_algno = -1;
        return;
      }
    for (j = kbm_algno; j < stringlen(genname); j++)
      if (!isdigit(genname[j])) {
        /* not Case b) */
        kbm_algno = -1;
        return;
      }
    if (atoi(genname + kbm_algno) >
        MAXGEN) { /* numerical subscript too large */
      kbm_algno = -1;
      return;
    }
    kbm_gen_no[atoi(genname + kbm_algno)] = i;
  }
}

/* A word is read into gen_word.
   It is assumed that space is already allocated for the word beginning at
   gen_word and ending at end_word.
   If the word is too long, the process aborts.
   The word must be empty or equal to "IdWord" (equivalent) or have the form
   t1*t2*...tr (for some r>=1), where each ti is either the name of
   a generator, or of form <gen-name>^<integer>.
   2/6/95 - brackets are now allowed up to level 8, so
            expressions like (x*(y*z)^3)^9  are allowed.
   If <integer> is negative, then there must be a generator called
   <gen-name>^-1.
   The word is translated and expanded into a string of generator
   numbers and stored as a string of `gen's in gen_word.
   The external array kbm_gen_no, and the external integer kbm_algno are used
   for the translation - see comment in rwsio.h for explanation
   If check is set true, then the validity of the word is checked -
   using the list "name" of generator names.
   Otherwise it is processed as fast as possible.
   FALSE returned if no word read (delim comes first), otherwise TRUE.
*/
boolean read_word(FILE *rfile, gen *gen_word, gen *end_word, int *delim,
                  char **name, int num_names, boolean check)
{
  int i, g, n, delimchar, bracketlevel;
  gen *ptr, *ptrr, *ptre, *bracketptr[9];
  ptr = gen_word;
  bracketlevel = 0;
  do {
    read_ident(rfile, kbm_buffer, &delimchar, FALSE);
    if (delimchar == '(') {
      if (stringlen(kbm_buffer) != 0) {
        fprintf(stderr, "Input error: '(' in wrong position in word.\n");
        exit(1);
      }
      bracketlevel++;
      if (bracketlevel > 8) {
        fprintf(stderr, "Input error: at most 8 levels of brackets allowed.\n");
        exit(1);
      }
      bracketptr[bracketlevel] = ptr;
      continue;
    }
    if (ptr == gen_word &&
        (strcmp(kbm_buffer, "") == 0 || strcmp(kbm_buffer, "IdWord") == 0))
      break;
    if (kbm_algno == -1) {
      g = 0;
      for (i = 1; i <= num_names; i++)
        if (strcmp(kbm_buffer, name[i]) == 0) {
          g = i;
          break;
        }
      if (g == 0) {
        fprintf(stderr, "#Input error: unknown generator in word.\n");
        exit(1);
      }
    }
    else {
      g = (kbm_algno == 0) ? kbm_gen_no[*kbm_buffer]
                           : kbm_gen_no[atoi(kbm_buffer + kbm_algno)];
      if (check && (g == 0 || strcmp(kbm_buffer, name[g])) != 0) {
        fprintf(stderr, "#Input error: invalid entry in word.\n");
        exit(1);
      }
    }
    if (delimchar == '^') {
      read_int(rfile, &n, &delimchar);
      if (delimchar != '*' && delimchar != ']' && delimchar != ',' &&
          delimchar != ';' && delimchar != ')') {
        fprintf(stderr, "#Input error: ',' '*', ')'  or ']' expected.\n");
        exit(1);
      }
      if (n < 0) {
        /* This is only allowed if we have a generator ending in ^-1 */
        g = 0;
        if (kbm_algno == -1) {
          sprintf(kbm_buffer + stringlen(kbm_buffer), "^-1");
          for (i = 1; i <= num_names; i++)
            if (strcmp(kbm_buffer, name[i]) == 0) {
              g = i;
              break;
            }
        }
        if (g == 0) {
          fprintf(stderr, "#Input error: unknown generator or illegal negative "
                          "power in word.\n");
          exit(1);
        }
        n = -n;
      }
      for (i = 1; i <= n; i++) {
        *(ptr++) = g;
        if (ptr > end_word) {
          fprintf(stderr,
                  "The word being read is too long. Increase maxreducelen.\n");
          exit(1);
        }
      }
    }
    else if (delimchar == '*' || delimchar == ']' || delimchar == ',' ||
             delimchar == ';' || delimchar == ')') {
      *(ptr++) = g;
      if (ptr > end_word) {
        fprintf(stderr,
                "The word being read is too long. Increase maxreducelen.\n");
        exit(1);
      }
    }
    else {
      fprintf(stderr, "#Input error: ',' '^' '*' ';' or ']' expected.\n");
      exit(1);
    }
    while (delimchar == ')') {
      read_delim(rfile, &delimchar);
      while (delimchar == ')') {
        bracketlevel--;
        read_delim(rfile, &delimchar);
      }
      if (bracketlevel <= 0) {
        fprintf(stderr, "Input error: ')' with no matching '('.\n");
        exit(1);
      }
      if (delimchar == '^') {
        read_int(rfile, &n, &delimchar);
        if (delimchar != '*' && delimchar != ']' && delimchar != ',' &&
            delimchar != ';' && delimchar != ')') {
          fprintf(stderr, "#Input error: ',' '*' ')' or ']' expected.\n");
          exit(1);
        }
        if (n <= 0) {
          fprintf(stderr,
                  "#Error: Non-positive powers not allowed in monoid words.\n");
          exit(1);
        }
        ptre = ptr - 1;
        for (i = 1; i < n; i++) {
          ptrr = bracketptr[bracketlevel];
          while (ptrr <= ptre) {
            *(ptr++) = *(ptrr++);
            if (ptr > end_word) {
              fprintf(
                  stderr,
                  "The word being read is too long. Increase maxreducelen.\n");
              exit(1);
            }
          }
        }
      }
      else if (delimchar != '*' && delimchar != ']' && delimchar != ',' &&
               delimchar != ';') {
        fprintf(stderr, "#Input error: ',' '^' '*' ';' or ']' expected.\n");
        exit(1);
      }
      bracketlevel--;
    }
  } while (delimchar != ',' && delimchar != ']' && delimchar != ';');

  if (bracketlevel != 0) {
    fprintf(stderr, "#Input error: brackets do not balance in word.\n");
    exit(1);
  }
  *delim = delimchar;
  if (*delim == '{')
    *delim = '[';
  if (*delim == '}')
    *delim = ']';
  *ptr = 0;
  return (ptr != gen_word || strcmp(kbm_buffer, "IdWord") == 0);
}

/* Read a list of words separated by commas into wordlist, and return the
 * number read. space is the total space available - the program aborts
 * if this is exceeded.
 * The individual words are terminated by the string terminator 0 in
 * wordlist, so that they can be conveniently copied.
 * name, num_names and check are as in read_word.
 */
int read_word_list(FILE *rfile, gen *wordlist, int space, int *delim,
                   char **name, int num_names, int check)
{
  int ct;
  gen *ptr, *ptre;
  ptr = wordlist;
  ptre = wordlist + space - 1;
  ct = 0;
  do {
    read_word(rfile, ptr, ptre, delim, name, num_names, check);
    ct++;
    ptr += (genstrlen(ptr) + 1);
  } while (*delim == ',');
  if (*delim == '{')
    *delim = '[';
  if (*delim == '}')
    *delim = ']';
  return ct;
}

/* prints contents of buffer, followed by new-line to wfile
 * and then clears buffer.
 */
void printbuffer(FILE *wfile)
{
  fprintf(wfile, "%s\n", kbm_buffer);
  *kbm_buffer = '\0';
}

/* w should be a string.
 * Add at least n characters to the end of the string buffer, with w at the end,
 * padding with spaces at beginning
 */
void add_to_buffer(int n, char *w)
{
  int i, nsp;
  nsp = n - stringlen(w);
  for (i = 1; i <= nsp; i++)
    strcat(kbm_buffer, " ");
  strcat(kbm_buffer, w);
}

/* word is a string of `gen's. to be printed as a word in GAP syntax.
 * If gen number i appears in the string, then
 * the gen is to be printed as the string symbols[i].
 * The buffer contains the line to be printed, and the word is
 * appended to the end of the current contents of the buffer.
 * New lines are printed in mid-word if necessary, but not at the
 * end, since the calling function may need to append more.
 * The returned value is the number of newlines inserted.
 */
int add_word_to_buffer(FILE *wfile, gen *word, char **symbols)
{
  int offset, pow, g, len, lg, nln = 0;
  gen *w;
  char sg[256];
  /* 256 here is the maximum length of a generator name in `symbols'. */
  boolean first;
  offset = stringlen(kbm_buffer) + 2; /* remember where word begins on the line,
                                       * in case we need to add new lines. */
  if (offset > 32)
    offset = 32; /* to avoid silly situations */
  w = word;
  if (*w == 0)
    add_to_buffer(0, "IdWord");
  first = TRUE;
  while (*w) {
    g = *(w++);
    pow = 1;
    while (*w == g) {
      pow++;
      w++;
    }
    len = first ? 0 : 1;
    strcpy(sg, symbols[g]);
    len += stringlen(sg);
    if (pow > 1) {
      len += (1 + int_len(pow));
    }
    if (stringlen(kbm_buffer) + len >= 76) { /* new line needed */
      printbuffer(wfile);
      add_to_buffer(offset, "");
      nln++;
    }
    if (!first)
      add_to_buffer(0, "*");
    /* Check if we have a power of a generator ending with ^-1 */
    lg = stringlen(sg);
    if (pow > 1 && lg > 3 && sg[lg - 3] == '^' && sg[lg - 2] == '-' &&
        sg[lg - 1] == '1') {
      sg[lg - 3] = '\0';
      pow = -pow;
    }
    add_to_buffer(0, sg);
    if (pow > 1 || pow < -1)
      sprintf(kbm_buffer + stringlen(kbm_buffer), "^%d", pow);
    first = FALSE;
  }
  return nln;
}

/* The same as add_word_to_buffer, but powers of generators are
 * printed out in full rather than as powers.
 */
int add_expanded_word_to_buffer(FILE *wfile, gen *word, char **symbols)
{
  int offset, g, len, nln = 0;
  gen *w;
  char sg[256];
  /* 256 here is the maximum length of a generator name in `symbols'. */
  boolean first;
  offset = stringlen(kbm_buffer) + 2; /* remember where word begins on the line,
                                       * in case we need to add new lines. */
  if (offset > 32)
    offset = 32; /* to avoid silly situations */
  w = word;
  if (*w == 0)
    add_to_buffer(0, "IdWord");
  first = TRUE;
  while (*w) {
    g = *(w++);
    len = first ? 0 : 1;
    strcpy(sg, symbols[g]);
    len += stringlen(sg);
    if (stringlen(kbm_buffer) + len >= 76) { /* new line needed */
      printbuffer(wfile);
      add_to_buffer(offset, "");
      nln++;
    }
    if (!first)
      add_to_buffer(0, "*");
    add_to_buffer(0, sg);
    first = FALSE;
  }
  return nln;
}

/* This is the same as add_word_to_buffer, except that "word" is a string of
 * integers instead of gens.
 */
int add_iword_to_buffer(FILE *wfile, int *word, char **symbols)
{
  int offset, pow, g, lg, len, nln = 0;
  int *w;
  char sg[128];
  boolean first;
  offset = stringlen(kbm_buffer) + 2; /* remember where word begins on the line,
                                       * in case we need to add new lines. */
  w = word;
  if (*w == 0)
    add_to_buffer(0, "IdWord");
  first = TRUE;
  while (*w) {
    g = *(w++);
    pow = 1;
    while (*w == g) {
      pow++;
      w++;
    }
    len = first ? 0 : 1;
    strcpy(sg, symbols[g]);
    len += stringlen(sg);
    if (pow > 1) {
      len += (1 + int_len(pow));
    }
    if (stringlen(kbm_buffer) + len >= 76) { /* new line needed */
      printbuffer(wfile);
      add_to_buffer(offset, "");
      nln++;
    }
    if (!first)
      add_to_buffer(0, "*");
    /* Check if we have a power of a generator ending with ^-1 */
    lg = stringlen(sg);
    if (pow > 1 && lg > 3 && sg[lg - 3] == '^' && sg[lg - 2] == '-' &&
        sg[lg - 1] == '1') {
      sg[lg - 3] = '\0';
      pow = -pow;
    }
    add_to_buffer(0, sg);
    if (pow > 1 || pow < -1)
      sprintf(kbm_buffer + stringlen(kbm_buffer), "^%d", pow);
    first = FALSE;
  }
  return nln;
}

int
/* The length of the  integer  n */
int_len(int n)
{
  int l = 0;
  if (n < 0) {
    n = -n;
    l = 1;
  }
  while (n != 0) {
    l++;
    n = n / 10;
  }
  return l;
}

/* returns true if the string x is an integer */
boolean is_int(char *x)
{
  int i, l;
  l = stringlen(x);
  if (l == 0 || (l == 1 && x[0] == '-'))
    return FALSE;
  for (i = 0; i < l; i++)
    if (!isdigit(x[i]) && (i != 0 || x[i] != '-'))
      return FALSE;
  return TRUE;
}

/* We recode this standard function, since the solaris version returns a type
 * other than int, which causes irritating warning messages!
 */
int stringlen(char *c)
{
  int l = 0;
  while (*(c++))
    l++;
  return l;
}

int genstrlen(gen *c)
{
  int l = 0;
  while (*(c++))
    l++;
  return l;
}

int genstrcmp(gen *c, gen *d)
{
  while (*c) {
    if (*(c++) != *(d++))
      return 1;
  }
  if (*c != *d)
    return 1;
  return 0;
}

void genstrcat(gen *c, gen *d)
{
  while (*c)
    c++;
  while (*d)
    *(c++) = *(d++);
  *c = 0;
}

void genstrcpy(gen *c, gen *d)
{
  while (*d)
    *(c++) = *(d++);
  *c = 0;
}
/* Locates separator, and checks the level conditions on G-generators and
 * H-generators.
 */
void set_separator(rewriting_system *rwsptr)
{
  int i, lev;
  /* Locate separator */
  rwsptr->separator = 0;
  for (i = 1; i <= rwsptr->num_gens; i++)
    if (strcmp(rwsptr->gen_name[i], "_H") == 0) {
      rwsptr->separator = i;
      break;
    }
  if (rwsptr->separator == 0) {
    fprintf(stderr, "Error - there is no generator named '_H'.\n");
    exit(1);
  }
  if (rwsptr->inv_of[rwsptr->separator]) {
    fprintf(stderr, "Error - generator '_H' should have no inverse!.\n");
    exit(1);
  }

  if (rwsptr->level == 0) {
    fprintf(stderr, "Error - ordering must be WREATHPROD in cosets program.\n");
    exit(1);
  }
  lev = rwsptr->level[rwsptr->separator];
  for (i = 1; i < rwsptr->separator; i++)
    if (rwsptr->level[i] <= lev) {
      fprintf(stderr, "Error: G-generators must precede separator and have "
                      "higher level.\n");
      exit(1);
    }
  for (i = rwsptr->separator + 1; i <= rwsptr->num_gens; i++)
    if (rwsptr->level[i] > lev) {
      fprintf(stderr, "Error: G-generators must follow separator and not have "
                      "higher level.\n");
      exit(1);
    }

  /* Now determine Gislevel, Hislevel, Hhasinverses */
  rwsptr->Gislevel = TRUE;
  lev = 0;
  for (i = 1; i < rwsptr->separator; i++)
    if (lev == 0)
      lev = rwsptr->level[i];
    else if (rwsptr->level[i] != lev) {
      rwsptr->Gislevel = FALSE;
      break;
    }
  rwsptr->Hislevel = TRUE;
  lev = 0;
  for (i = rwsptr->separator + 1; i <= rwsptr->num_gens; i++)
    if (lev == 0)
      lev = rwsptr->level[i];
    else if (rwsptr->level[i] != lev) {
      rwsptr->Hislevel = FALSE;
      break;
    }

  if (rwsptr->finitestop && !rwsptr->Gislevel) {
    printf(
        " #Warning: finiteness test only works when all G-gens have the same weight.\n\
 #Finiteness test swithched off.\n");
    rwsptr->finitestop = FALSE;
  }


  rwsptr->Hhasinverses = TRUE;
  for (i = rwsptr->separator + 1; i <= rwsptr->num_gens; i++)
    if (!rwsptr->inv_of[i]) {
      rwsptr->Hhasinverses = FALSE;
      break;
    }
}
