# lib makefile
SHELL=/bin/sh
RANLIB = ranlib
RM = /bin/rm
CC= gcc-fsf-6
COPTS= -O -Wall -Wno-char-subscripts -Wno-maybe-uninitialized -Werror
#COPTS= -O -Wall -Wno-char-subscripts -Wno-maybe-uninitialized -Wstrict-prototypes -Wextra -Werror
LIB = fsalib.a
LIBOBJ =fsa.o fsaio.o hash.o rwsreduce.o miscio.o rwsio.o rwsiob.o worddiff.o\
	worddcos.o kbfns.o fsalogic.o rabkar.o fsaipmin.o fsarevmid.o\
	nfa.o midfa.o fsawa.o fsawacos.o fsatriples.o diffreduce.o\
	fsamitriples.o diffredcos.o diffredwl.o fsacheckmult.o migmdet.o\
	fsageopairs.o fsacomposite.o fsaminkb.o fsamicomp.o fsadifflabs.o\
	fsasubmult.o
$(LIB): $(LIBOBJ)
	ar cr $(LIB) $(LIBOBJ)
	if  which ranlib > /dev/null 2> /dev/null; then ranlib $(LIB); fi
clean:
	$(RM) -f $(LIBOBJ) $(LIB)
	$(RM) -f *\~ core a.out
kbfns.o: kbfns.c
	$(CC) -c $(COPTS) kbfns.c
.c.o:
	${CC} -c $(COPTS) $*.c 
