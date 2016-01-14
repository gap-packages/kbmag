/* makecosfile.c   19.1.96.
 * 14/10/98 - large scale changes
 * 5/2/98 change generators from type char to type `gen'.
 *
 * Starting from an input file containing the definition of a rewriting
 * system for a group or monoid, and a file containing a list of
 * words generating a subgroup or submonoid, output a file containing
 * a rewriting system for the group/monoid relative to this substructure.
 * For any of this to make any mathematical sense, it is probably necessary
 * that the substructure, at least, should be a group, since otherwise
 * the notion of cosets is not really meaningful. We shall therefore refer
 * to it as a subgroup from now on.
 *
 * There are two basic possibilities.
 * The first (and default) is just to add the subgroup symbol _H as
 * extra generator, plus relations to make it absorb the subgroup
 * generators when multiplied by them on the right.
 *
 * The second is to do this and, in addition, to add the subgroup
 * generators as extra generators to the RWS, where the corresponding new
 * generators are inserted on the left of the subgroup symbol _H whenever
 * such an absorption takes place.
 * In this case, the subgroup file should also contain the list of names
 * for the new subgroup generators (which should of course be distinct
 * from the main group generators).
 * It may also contain a list of names for inverses of the new generators,
 * but this is not mandatory. Inverses will be supplied automatically
 * if they are not already there, unless the -ni option is called.
 *
 * The subgroup file should contain a GAP record declaration with
 * components 'subGenerators' and optionally 'subGeneratorNames' and
 * 'subGeneratorInverseNames'.
 *
 * In either case, we change the ordering to wreathprod if necessary, and
 * put _H and the subgroup generators at a lower level than the main
 * structure generators.
 *
 * SYNOPSIS:
 * makecosfile [-sg] [-ni] groupname [subname]
 *
 * OPTIONS:
 * -sg	Insert new generators for the subgroup generators
 * -ni  (Only relevant if -sg called.) Do not insert inverse generator names
 *     (of standard form x^-1) for the new subgroup generators. 
 */

#include <stdio.h>

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"

#define MAXEQNS		2048
#define MAXREDUCELEN	4096

static FILE *rfile, *wfile;

/* Functions defined in this file */
void badusage_makecosfile();

/* Functions used in this file defined in other files: */
void read_kbinput_simple();
void read_subgens();
void print_rws_simple();
void rws_clear();
int stringlen();
int genstrlen();
void genstrcpy();

int 
main (int argc, char *argv[])
{ int arg, ngens, neqns, i, *templevel;
  gen **words;
  boolean subgens=FALSE, invsubgens=TRUE;
  rewriting_system rws, *rwsptr;
  reduction_equation *eqn;
  char gpname[100], inf[100], subname[100], outf[100];

  rwsptr= &rws;
  rwsptr->maxeqns = MAXEQNS;
  rwsptr->maxreducelen = MAXREDUCELEN;
  rwsptr->cosets = FALSE;
   /* even in the cosets case we read relations from original group file */

  rwsptr->inv_of=0;
  rwsptr->weight=0;rwsptr->level=0;rwsptr->history=0;
  rwsptr->slowhistory=0;rwsptr->slowhistorysp=0;
  rwsptr->confluent=FALSE;
  rwsptr->tidyintset=FALSE;
  rwsptr->preflen=0;rwsptr->prefno=0;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  gpname[0] = '\0';
  subname[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-sg")==0)
      subgens=TRUE;
    else if (strcmp(argv[arg],"-ni")==0)
      invsubgens=FALSE;
    else {
       if (argv[arg][0] == '-')
         badusage_makecosfile();
       if (strcmp(gpname,"")!=0 && strcmp(subname,"")!=0)
         badusage_makecosfile();
       if (strcmp(gpname,"")!=0)
         strcpy(subname,argv[arg]);
       else
         strcpy(gpname,argv[arg]);
    }
    arg++;
  }
  if (stringlen(gpname)==0)
    badusage_makecosfile();
  strcpy(inf,gpname);
  strcat(inf,".");
  if (stringlen(subname)==0)
     strcpy(subname,"sub");
  strcat(inf,subname);
  if (strncmp(subname,"sub",3)==0) {
    strcpy(outf,gpname);
    strcat(outf,".cos");
    strcat(outf,subname+3);
  }
  else {
    strcpy(outf,gpname);
    strcat(outf,".");
    strcat(outf,subname);
    strcat(outf,"_cos");
  }
  if (!subgens)
    invsubgens=FALSE;
  
/* First read in the defining relations for the group. */
  if ((rfile = fopen(gpname,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",gpname);
      exit(1);
  }
  read_kbinput_simple(rfile,TRUE,rwsptr);
  fclose(rfile);
  if (rws.ordering==WTLEX) {
      fprintf(stderr,
   "Sorry - cannot currently handle subgroup generators in the wtlex case.\n");
      exit(1);
  }
  ngens = rws.num_gens;
  neqns = rws.num_eqns;

/* Now read in the subgroup generators from the separate file. */
  if ((rfile = fopen(inf,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
  }
  tmalloc(words,gen *,MAXGEN+1);
  read_subgens(rfile,words,subgens,invsubgens,rwsptr);
  fclose(rfile);

  rws.separator=ngens+1;
  /* Note ngens remains the original number of main generators, but
   * rws.num_gens is now the total number, including new generators.
   * Adjust the ordering as necessary.
   */
  if (rws.ordering==SHORTLEX) {
    rws.ordering=WREATHPROD;
    tmalloc(rws.level,int,rws.num_gens+1);
    for (i=1;i<=ngens;i++)
       rws.level[i]=2;
    for (i=rws.separator;i<=rws.num_gens;i++)
       rws.level[i]=1;
  }
  else if (rws.ordering==RECURSIVE || rws.ordering==RT_RECURSIVE) {
   /* This will change the ordering back from RT_RECURSIVE to RECURSIVE. */
    rws.ordering=WREATHPROD;
    tmalloc(rws.level,int,rws.num_gens+1);
    for (i=1;i<=ngens;i++)
       rws.level[i]=i+1;
    for (i=rws.separator;i<=rws.num_gens;i++)
       rws.level[i]=1;
  }
  else if (rws.ordering==WREATHPROD) {
    tmalloc(templevel,int,rws.num_gens+1);
    for (i=1;i<=ngens;i++)
       templevel[i]=rws.level[i]+1;
    for (i=rws.separator;i<=rws.num_gens;i++)
       templevel[i]=1;
    tfree(rws.level);
    rws.level=templevel;
  }

  /* Now add the new equations */
  i=1;
  while (words[i]) {
    eqn= &(rws.eqns[++neqns]); 
    tmalloc(eqn->lhs,gen,genstrlen(words[i])+2);
    eqn->lhs[0]=rws.separator;
    genstrcpy(eqn->lhs+1,words[i]);
    tfree(words[i]);
    if (subgens) {
      tmalloc(eqn->rhs,gen,3);
      eqn->rhs[0]= rws.separator+i;
      eqn->rhs[1]= rws.separator;
      eqn->rhs[2]='\0';;
    }
    else {
      tmalloc(eqn->rhs,gen,2);
      eqn->rhs[0]=rws.separator;
      eqn->rhs[1]='\0';;
    }
    i++;
  }
  tfree(words);
  rws.num_eqns=neqns;

  /* Add a suffix to the name of the rewriting system */
  strcat(rws.name,"_Cos");

  /* Now we just output! */
  wfile=fopen(outf,"w");
  print_rws_simple(wfile,rwsptr);
  fclose(wfile);
  rws_clear(&rws);
  exit(0);
}

void 
badusage_makecosfile (void)
{
   fprintf(stderr,"Usage:  makecosfile [-sg] [-ni] groupname [subname] \n");
	exit(1);
}
