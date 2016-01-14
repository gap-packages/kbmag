/* fsaprune.c 27/10/98.
 *
 * 26/12/99 introduce -i option to do the opposite, and remove all states
 * that are not targets.
 *  
 * Removes all states of an fsa from which the accepted language is finite.
 *
 * SYNOPSIS:
 *    fsaprune [-ip d/s] [-op d/s] [-silent] [-v] [-a] [-i] [filename]\n");
 * Input is from filename or stdin, which should contain a fsa,
 * output is to filename.prune (or filename.iprune when -i called) or stdout.
 *
 * OPTIONS:
 * -a           make all states of input fsa accepting - algorithm is
 *              easier in this case.
 * -i           instead, remove all states that are not the targets of
 *              any transition, and then make all states initial. The
 *              resulting fsa will be a midfa in this case.
 * -is n	change initial state of fsa to n.
 * -ip d/s      input in dense or sparse format - dense is default
 * -op d/s      output in dense or sparse format - default is as in current
 *               value of table->printing_format, in the fsa.
 * -v           verbose
 * -silent      no diagnostics
 */

#include <stdio.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage();

/* Functions defined in other files used in this file */
int sparse_target();
void  fsa_read();
int   fsa_count();
void  fsa_delete_state();
void  fsa_copy();
void  fsa_clear();
void  fsa_print();
int   stringlen();

int 
main (int argc, char *argv[])
{ int arg, ct, ne, ns, **table, e, s, t;
  fsa testfsa, copyfsa;
  char inf[100],outf[100],fsaname[100];
  boolean all_accepting=FALSE;
  boolean all_initial = FALSE;
  boolean deleting, deleting_s;
  storage_type ip_store = DENSE;
  boolean op_format_set = FALSE;
  storage_type op_format = DENSE;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's')
        ip_store = SPARSE;
      else
        badusage();
    }
    else if (strcmp(argv[arg],"-op")==0) {
      arg++;
      op_format_set=TRUE;
      if (arg >= argc)
        badusage();
      if (strcmp(argv[arg],"d")==0)
        op_format = DENSE;
      else if (strcmp(argv[arg],"s")==0)
        op_format = SPARSE;
      else
        badusage();
    }
    else if (strcmp(argv[arg],"-a")==0)
      all_accepting = TRUE;
    else if (strcmp(argv[arg],"-i")==0)
      all_initial = TRUE;
    else if (strcmp(argv[arg],"-silent")==0)
      kbm_print_level = 0;
    else if (strcmp(argv[arg],"-v")==0)
      kbm_print_level = 2;
    else if (strcmp(argv[arg],"-vv")==0)
      kbm_print_level = 3;
    else {
       if (argv[arg][0] == '-')
         badusage();
       if (strcmp(inf,""))
         badusage();
       strcpy(inf,argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf)!=0) {
    strcpy(outf,inf);
    if (all_initial)
      strcat(outf,".iprune");
    else
      strcat(outf,".prune");

    if ((rfile = fopen(inf,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
    }
  }
  else
    rfile = stdin;

  fsa_read(rfile,&testfsa,ip_store,0,0,TRUE,fsaname);
  if (stringlen(inf))
    fclose(rfile);

  ns = testfsa.states->size;
  ne = testfsa.alphabet->size;
  if (all_accepting) {
    tfree(testfsa.accepting);
    testfsa.num_accepting = ns;
  }
  all_accepting = testfsa.num_accepting == ns;

  /* The state deletions may destroy various properties of the automata */
  testfsa.flags[MINIMIZED]=FALSE;
  testfsa.flags[BFS]=FALSE;
  testfsa.flags[ACCESSIBLE]=FALSE;
  testfsa.flags[TRIM]=FALSE;

  if (all_initial) {
    table = testfsa.table->table_data_ptr;
    deleting=TRUE;
    while (deleting) {
      deleting=FALSE;
      for (s=1;s<=ns;s++) {
        /* if no transitions to state s delete it! */
        deleting_s=TRUE;
        for (e=1;e<=ne;e++) {
          if (!deleting_s)
            break;
          for (t=1;t<=ns;t++) {
            if (target(ip_store==DENSE,table,e,t,0)==s){
              deleting_s=FALSE;
              break;
            }
          }
        }
        if (deleting_s) {
          deleting=TRUE;
          if (kbm_print_level>1)
            printf("  #Deleting state number %d\n",s);
          fsa_delete_state(&testfsa,s);
          ns--;
        }
      }
    }
  }
  else if (all_accepting) {
    table = testfsa.table->table_data_ptr;
    deleting=TRUE;
    while (deleting) {
      deleting=FALSE;
      for (s=ns;s>0;s--) {
        /* if no transitions from state s delete it! */
        deleting_s=TRUE;
        for (e=1;e<=ne;e++)
          if (target(ip_store==DENSE,table,e,s,0)!=0){
            deleting_s=FALSE;
            break;
          }
        if (deleting_s) {
          deleting=TRUE;
          if (kbm_print_level>1)
            printf("  #Deleting state number %d\n",s);
          fsa_delete_state(&testfsa,s);
          ns--;
        }
      }
    }
  }
  else {
    for (s=ns;s>=1;s--) {
      if (kbm_print_level>1 && s%100==0)
         printf("  #state=%d\n",s);
      fsa_copy(&copyfsa,&testfsa);
                /* necessary because fsa_count alters its argument */
      copyfsa.initial[1]=s;
      ct = fsa_count(&copyfsa);
      if (ct==-1) exit(1);
      if (ct!=-2) {
        if (kbm_print_level>1)
          printf("  #Deleting state number %d\n",s);
        fsa_delete_state(&testfsa,s);
      }
      fsa_clear(&copyfsa);
    }
  }

  if (op_format_set)
    testfsa.table->printing_format = op_format;
  strcat(fsaname,"_prune");

  if (stringlen(inf)!=0)
    wfile = fopen(outf,"w");
  else
    wfile = stdout;

  if (all_initial) {
    tfree(testfsa.initial);
    testfsa.num_initial=testfsa.states->size;
    testfsa.flags[DFA]=FALSE;
    testfsa.flags[MIDFA]=TRUE;
  }
  fsa_print(wfile,&testfsa,fsaname);

  if (stringlen(inf)!=0)
    fclose(wfile);
  if (wfile!=stdout && kbm_print_level>0)
    printf("#Pruned fsa with %d states computed.\n",testfsa.states->size);

  fsa_clear(&testfsa);
  exit(0);
}
 
void 
badusage (void)
{
    fprintf(stderr,
  "Usage: fsaprune [-ip d/s] [-op d/s] [-silent] [-v] [-a] [-i] [filename]\n");
    exit(1);
}
