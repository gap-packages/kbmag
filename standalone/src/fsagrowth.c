/* fsagrowth.c 22/5/95
 * 20/12/00 minor change to output to file for GAP4 interface.
 * WRITTEN BY LAURENT BARTHOLDI.
 * Counts the growth series of a fsa
 *
 * SYNOPSIS: fsagrowth [-ip d/s] [-v] [-var v] [-primes x,y...] [filename]);
 *
 * Input is from filename, which should contain a fsa.
 * Output is to filename.growth, and contains the growth series
 * of the finite state automaton.
 *
 * OPTIONS:
 * -ip d/s      input in dense or sparse format - dense is default
 * -v		set kbm_print_level to 2
 * -var v	express answer as a rational in v (X default)
 * -primes x,y... specifies the primes modulo which the computations should
 *		be performed. It must be a comma-separated sequence of
 *		integers with no white space. No check is made to ensure the
 *		suggested values are indeed primes.
 *		By default, the computations are done modulo three
 *		cable-wired primes just less than 2^15.
 *		(If you use primes bigger than 2^15, then it is possible that
 *               integer overflow could occur in the routine mod_solve
 *               without you knowing it!)
 *		If the results are not consistent, then a warning is printed to
 *              stderr, and the exit code is 2.
 *              If the results agree with each other, then they are likely
 *              to be correct (in the integers) and the exit code is 0.
 *
 */

#include <stdio.h>
#include <stdlib.h>
#include "defs.h"
#include "fsa.h"
#include "definitions.h"

static FILE *rfile, *wfile;

void  badusage_fsagrowth();

/* Functions defined in other files used in this file */
void  fsa_read();
int  fsa_growth();
void  fsa_clear();
boolean is_int();

int 
main (int argc, char *argv[])
{ int arg, min, max, i, rv;
  fsa testfsa;
  char inf[100], outf[100], fsaname[100], primestr[100], var[100] = "X";
  unsigned primes[100] = { 32749, 32719, 32717, 0}, nprimes = 3;
  storage_type ip_store = DENSE;
  boolean consistent;

  setbuf(stdout,(char*)0);
  setbuf(stderr,(char*)0);

  inf[0] = '\0';
  arg = 1;
  while (argc > arg) {
    if (strcmp(argv[arg],"-ip")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsagrowth();
      if (strcmp(argv[arg],"d")==0)
        ip_store = DENSE;
      else if (argv[arg][0] == 's')
        ip_store = SPARSE;
      else
        badusage_fsagrowth();
    }
    else if (strcmp(argv[arg],"-var")==0) {
      arg++;
      if (arg >= argc)
        badusage_fsagrowth();
      strcpy(var, argv[arg]);
    }
    else if (strcmp(argv[arg],"-v")==0)
      kbm_print_level = 2;
    else if (strcmp(argv[arg],"-primes")==0) {
      char *pptr, *p;
      arg++;
      if (arg >= argc)
        badusage_fsagrowth();
      nprimes = 0;
      strcpy(primestr,argv[arg]); strcat(primestr,",");
      for (pptr = p = primestr; *p; p++)
      if (*p < '0' || *p > '9') {
        *p = 0;
	if (p-pptr >= 1) primes[nprimes++] = atoi(pptr);
	pptr = p+1;
      }
      if (nprimes == 0) badusage_fsagrowth();
    } else {
       if (argv[arg][0] == '-')
         badusage_fsagrowth();
       strcpy(inf,argv[arg]);
    }
    arg++;
  }
  if (stringlen(inf)!=0) {
    strcpy(outf,inf);
    strcat(outf,".growth");

    if ((rfile = fopen(inf,"r")) == 0) {
      fprintf(stderr,"Cannot open file %s.\n",inf);
      exit(1);
    }
  }
  else
    rfile = stdin;
  fsa_read(rfile,&testfsa,ip_store,0,0,TRUE,fsaname);
  if (stringlen(inf)!=0) {
    fclose(rfile);
    wfile = fopen(outf,"w");
  }
  else wfile=stdout;

  fprintf(wfile,"local X; X:=Indeterminate(Rationals,1); return\n\n");
  kbm_buffer[0]='\0';

  primes[nprimes] = 0;
  rv=fsa_growth(wfile,&testfsa,primes,var);
  if (rv== -1) exit(1);
  consistent= (boolean)rv;

  if (stringlen(inf)!=0)
    fclose(wfile);

  fsa_clear(&testfsa);
  if (!consistent) {
    fprintf(stderr,
  "WARNING: The polynomials modulo the primes chosen were not consistent.\n");
    fprintf(stderr,
  "         so the integral coefficients output are unlikely to be correct.\n");
    exit(2);
  }
  exit(0);
}
 
void 
badusage_fsagrowth (void)
{
    fprintf(stderr,
      "Usage: fsagrowth [-ip d/s] [-v] [-primes x,y...] [filename]\n");
    exit(1);
}
