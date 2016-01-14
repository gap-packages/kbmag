/* wordreduce.c 1/11/94.
 * 6/11/99 re-introduce option to input list of words from filename.
 *         also added -e option (expanded) to output expanded powers.
 * 6/8/98 large scale reorganisation to omit globals, etc.
 * 5/2/98 change generators from type char to type `gen'.
 *
 * 15/3/96 - amalgamated with wordreducecos.c, which was specially written
 * for reducing cosets using a word-difference machines.
 * There is now a -cos option, which means reduce cosets (using either
 * a rewriting system or a word-difference machine).
 * For coset reduction using a rewrting system, the word to be reduced can
 * contain any of available symbols, but to make sense (for H subgroup of G), 
 * it should either be a word in the G-generators alone, or a word in the
 * H-generators alone, or a word of form H-word*_H*G-word.
 * For coset reduction using a word-difference machine, the word to be
 * reduced must either be in the G-generators alone, or have form _H*G-word.
 *
 * Input of words from a filename specified on command line no longer works.
 *
 * 18/1/95 - added options to reduce words using rewriting system.
 * Reduce words using a rewriting system or a word-difference machine.
 *
 * SYNOPSIS:
 *    wordreduce [-kbprog/-diff1/-diff2/-diff1c] [-mrl maxreducelen] [-e]
 *			   	 [-cos] groupname [cosname] [-f filename]
 *
 * If -cos is false: 
 * Input is from groupname.kbprog, groupname.diff1, groupname.diff2 or
 * groupname.diff1c, and stdin.
 *
 * If -cos is true: 
 * cosname defaults to "cos"
 * Input is from groupname.cosname.kbprog, groupname.cosname.midiff1,
 * groupname.cosname.midiff2, and stdin (unless -f filename is used).
 *
 * Output is to stdout (unless -f filename is used).
 *
 * If the optional "-f filename" argument is present, then the file filename
 * should contain an assignment of a list of words to be reduced
 * (e.g. words := [a^3,(a*b)^7];), and output will be a list of reduced words
 * to filename.reduced.
 *
 * OPTIONS:
 * -cos		If set reduce cosets. This changes i/o files.
 *
 * -kbprog/diff1/diff2/diff1c
 *		This determines which finite state automaton is used for
 *		the word-reduction.
 *		If the kbprog flag is called, then a rewriting system is
 *		input from groupname.kbprog
 *				(or, if -cos, groupname.cosname.kbprog).
 *		Otherwise, a word-difference machine is input from the
 *		appropriate file.
 *		The default is groupname.kbprog if that file is present,
 *		and otherwise groupname.diff2.
 *		
 * Words are input interactively to stdin and output to stdout.
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"

#define MAXEQNS         32767
#define MAXREDUCELEN    32767

static FILE *rfile, *wfile;

void  badusage_wordreduce();

/* Functions defined in other files used in this file */
void  read_kbinput_simple();
void  fsa_read();
int   fsa_table_dptr_init();
boolean  read_word();
int   diff_reduce();
int   diff_reduce_cos();
int   rws_reduce();
int   add_word_to_buffer();
int   add_expanded_word_to_buffer();
void  read_ident();
void  read_delim();
void  check_next_char();
void  printbuffer();
void  process_names();
void  fsa_clear();
int   stringlen();
int   genstrlen();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int delim, arg, num_gens, i;
  char gpname[100], cosgpname[100], inf1[100], fsaname[100],
       inf2[100], outf[100];
  boolean rws_ip, diff1_ip, diff2_ip, diff1c_ip, file_ip, expwds, open, first;
  boolean cosets=FALSE;
  rewriting_system rws;
  rewriting_system *rwsptr;
  reduction_struct rs;
  int (*reduce_word)();
  boolean seengpname, seencosname;
  gen 	*gen_word;
  char **gen_names;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  rwsptr= &rws;
  rwsptr->maxeqns = MAXEQNS;
  rwsptr->maxreducelen = MAXREDUCELEN;
  rwsptr->inv_of=0;
  rwsptr->weight=0;rwsptr->level=0;rwsptr->history=0;
  rwsptr->slowhistory=0;rwsptr->slowhistorysp=0;
  rwsptr->preflen=0;rwsptr->prefno=0;
  rs.rws=rwsptr;
  gpname[0] = '\0';
  arg = 1;
  rws_ip = diff1_ip = diff2_ip = diff1c_ip = file_ip = expwds = FALSE;
  seengpname=seencosname=FALSE;
  while (argc > arg) {
    if (strcmp(argv[arg],"-cos")==0)
      cosets = TRUE;
    else if (strcmp(argv[arg],"-kbprog")==0)
      rws_ip = TRUE;
    else if (strcmp(argv[arg],"-diff1")==0)
      diff1_ip = TRUE;
    else if (strcmp(argv[arg],"-diff2")==0)
      diff2_ip = TRUE;
    else if (strcmp(argv[arg],"-diff1c")==0)
      diff1c_ip = TRUE;
    else if (strcmp(argv[arg],"-e")==0)
      expwds = TRUE;
    else if (strcmp(argv[arg], "-mrl") == 0) {
      rwsptr->maxreducelenset = TRUE;
      arg++;
      if (arg >= argc)
        badusage_wordreduce();
      rwsptr->maxreducelen = atoi(argv[arg]);
    }
    else if (strcmp(argv[arg],"-f")==0) {
      file_ip = TRUE;
      arg++;
      if (arg >= argc)
        badusage_wordreduce();
      strcpy(inf2,argv[arg]);
      strcpy(outf,inf2); strcat(outf,".reduced");
    }
    else if (argv[arg][0] == '-')
      badusage_wordreduce();
    else if (!seengpname) {
      seengpname=TRUE;
      strcpy(gpname,argv[arg]);
    }
    else if (!seencosname) {
      seencosname=TRUE;
      sprintf(cosgpname,"%s.%s",gpname,argv[arg]);
    }
    else
      badusage_wordreduce();

    arg++;
  }

  if (!seengpname)
    badusage_wordreduce();
  if (cosets && !seencosname)
    sprintf(cosgpname,"%s.cos",gpname);

  if (cosets) strcpy(inf1,cosgpname);
  else strcpy(inf1,gpname);

  rwsptr->maxreducelen *= 2;
      /* Since rws-reduction returns when half of this length is exceeded. */
  open = FALSE;
  if (rws_ip)
    strcat(inf1,".kbprog");
  else if (diff1_ip)
    {if (cosets) strcat(inf1,".midiff1");else strcat(inf1,".diff1");}
  else if (diff2_ip)
    {if (cosets) strcat(inf1,".midiff2");else strcat(inf1,".diff2");}
  else if (diff1c_ip) {
    if (cosets) {
      fprintf(stderr,"Sorry, diff1c coset reduction is not yet supported.\n");
      exit(1);
    }
    strcat(inf1,".diff1c");
  }
  else {
    strcat(inf1,".kbprog");
    if (rfile = fopen(inf1,"r")) {
      rws_ip = TRUE;
      open = TRUE;
    }
    else {
      diff2_ip = TRUE;
      if (cosets)
        {strcpy(inf1,cosgpname); strcat(inf1,".midiff2");}
      else
        {strcpy(inf1,gpname); strcat(inf1,".diff2");}
    }
  }

  if (!open) 
    if ((rfile = fopen(inf1,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf1);
      exit(1);
    }
 
  if (rws_ip) {
    rwsptr->cosets=cosets;
    tmalloc(rwsptr->reduction_fsa,fsa,1);
    read_kbinput_simple(rfile,FALSE,rwsptr);
    fclose(rfile);
    if (cosets) strcpy(inf1,cosgpname);
    else strcpy(inf1,gpname);
    strcat(inf1,".reduce");
    if ((rfile = fopen(inf1,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf1);
      exit(1);
    }
    fsa_read(rfile,rwsptr->reduction_fsa,DENSE,0,0,TRUE,fsaname);
    fclose(rfile);
    num_gens = rws.num_gens;
    gen_names = rws.gen_name;
    process_names(gen_names,num_gens);
    tmalloc(rws.history,int,rwsptr->maxreducelen+1);
  }
  else {
    tmalloc(rs.wd_fsa,fsa,1);
    fsa_read(rfile,rs.wd_fsa,DENSE,0,0,TRUE,fsaname);
    fclose(rfile);
    num_gens = rs.wd_fsa->alphabet->base->size;
    if (cosets && (diff1_ip || diff2_ip)) {
/* Because of the separator, we copy the names and add "_H" as separator */
      num_gens++;
      tmalloc(gen_names,char *,num_gens+1);
      for (i=1;i<num_gens;i++) {
        tmalloc(gen_names[i],
                  char,stringlen(rs.wd_fsa->alphabet->base->names[i]+1));
        strcpy(gen_names[i],rs.wd_fsa->alphabet->base->names[i]);
      }
      tmalloc(gen_names[num_gens],char,3);
      strcpy(gen_names[num_gens],"_H");
      rs.separator=num_gens;
    }
    else
      gen_names = rs.wd_fsa->alphabet->base->names;
    process_names(gen_names,num_gens);
/* Set the pointers in the word-difference machine */
    if (fsa_table_dptr_init(rs.wd_fsa)==-1) exit(1);
  }

  reduce_word = rws_ip ? rws_reduce : cosets ? diff_reduce_cos : diff_reduce;

  tmalloc(gen_word,gen,rwsptr->maxreducelen);

  if (file_ip) {
/* open file containing list of words, and deal with assignment */
    if ((rfile = fopen(inf2,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf2);
      exit(1);
    }
    wfile = fopen(outf,"w");
    read_ident(rfile,kbm_buffer,&delim,FALSE);
    fprintf(wfile,"%s.reduced := [\n",kbm_buffer);
    if (delim != ':'){
      fprintf(stderr,
        "#Input error: file must contain a list assignment\n");
      exit(1);
    }
    check_next_char(rfile,'=');
    read_delim(rfile,&delim);
    if (delim != '['){
      fprintf(stderr,
        "#Input error: file must contain a list assignment\n");
      exit(1);
    }
    first = TRUE;
  }
  else {
    printf("#Input words for reduction.\n#Separate words with ','.\n");
    printf("#Terminate input with ';'.\n");
    rfile=stdin; wfile=stdout;
  }

  delim = 0;
  while (delim != ';' && delim != ']') {
    read_word(rfile,gen_word,gen_word+rwsptr->maxreducelen,&delim,
		gen_names,num_gens,TRUE);
    reduce_word(gen_word,&rs);
    if (genstrlen(gen_word) > rwsptr->maxreducelen/2) {
      fprintf(wfile,"Word grew too long during reduction!\n");
    }
    else {
      if (file_ip) {
        if (first) first = FALSE;
        else fprintf(wfile,",\n");
      }
      else
        fprintf(wfile,"reduces to:\n");
      strcpy(kbm_buffer,"  ");
      if (expwds)
        add_expanded_word_to_buffer(wfile,gen_word,gen_names);
      else
        add_word_to_buffer(wfile,gen_word,gen_names);
      if (file_ip) fprintf(wfile,"%s",kbm_buffer);
      else fprintf(wfile,"%s\n",kbm_buffer);
    }
  }
  if (file_ip) {
    check_next_char(rfile,';');
    fprintf(wfile,"\n];\n");
    fclose(wfile);
  }

  if (rws_ip) {
    rws_clear(rwsptr);
    fsa_clear(rwsptr->reduction_fsa);
  }
  else {
    fsa_clear(rs.wd_fsa);
    tfree(rs.wd_fsa);
  }
  tfree(gen_word);
  exit(0);
}
 
void
badusage_wordreduce()
{
    fprintf(stderr,
 "Usage: wordreduce [-kbprog/-diff1/-diff2/-diff1c] [-mrl maxreducelen] [-e]\n"
     );
    fprintf(stderr,"\t[-cos] groupname [cosname] [-f filename]\n");
    exit(1);
}
