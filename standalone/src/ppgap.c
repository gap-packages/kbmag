/* ppgap.c   27.2.95. 
 * 6/8/98 large scale reorganisation to omit globals, etc.
 *
 * Read a kb-input file and make a preprocessor file for GAP
 *
 * SYNOPSIS:
 * ppgap  groupname
 *
 */

#include <stdio.h>

#include "defs.h"
#include "fsa.h"
#include "rws.h"
#include "definitions.h"

#define MAXEQNS		1024
#define MAXREDUCELEN	4096

static FILE *rfile, *wfile;

/* Functions defined in this file */
void badusage_ppgap();

/* Functions used in this file defined in other files: */
void read_kbinput_simple();
void printbuffer();
void add_to_buffer();
void rws_clear();
int  stringlen();

main(argc, argv)
        int             argc;
        char           *argv[];
{ int  i, l, ct;
  boolean first;
  rewriting_system  rws, *rwsptr;
  static char gpname[100],  outf[100];

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  rwsptr= &rws;
  rwsptr->maxeqns = MAXEQNS;
  rwsptr->maxreducelen = MAXREDUCELEN;
  rwsptr->cosets=FALSE;
  rwsptr->inv_of=0;
  rwsptr->weight=0;rwsptr->level=0;rwsptr->history=0;
  rwsptr->slowhistory=0;rwsptr->slowhistorysp=0;
  rwsptr->preflen=0;rwsptr->prefno=0;

  if (argc!=2) badusage_ppgap();
  strcpy(gpname,argv[1]);
  strcpy(outf,gpname); strcat(outf,".gap");
  
/* First read in the defining relations for the group. */
  if ((rfile = fopen(gpname,"r")) == 0) {
    fprintf(stderr,"Cannot open file %s.\n",gpname);
      exit(1);
  }
  read_kbinput_simple(rfile,TRUE,rwsptr);
  fclose(rfile);

  wfile = fopen(outf,"w");

  kbm_buffer[0]='\0';
  add_to_buffer(0,"_RWS.gpMon := FreeGroup(");
  first = TRUE;

  if (rws.num_gens==0) add_to_buffer(0,"0");
  else for (i=1;i<=rws.num_gens;i++){
     l = stringlen(rws.gen_name[i]);
     if (l<=3 || strcmp(rws.gen_name[i]+l-3,"^-1")) {
       if (!first)
          add_to_buffer(0,",");
       first = FALSE;
       sprintf(kbm_buffer+stringlen(kbm_buffer),"\"%s\"",rws.gen_name[i]);
     }
  }
  add_to_buffer(0,");");
  printbuffer(wfile);

  ct = 0;
  for (i=1;i<=rws.num_gens;i++) {
    l = stringlen(rws.gen_name[i]);
    if (l<=3 || strcmp(rws.gen_name[i]+l-3,"^-1")) {
       ct++;
       fprintf(wfile,"%s := _RWS.gpMon.%d;\n",rws.gen_name[i],ct);
    }
  }
  fprintf(wfile,"_ := IdWord;\n");
  fclose(wfile);
  rws_clear(rwsptr);
  exit(0);
}
 
void
badusage_ppgap()
{ fprintf(stderr, "Usage: ppgap groupname.\n");
	exit(1);
}
