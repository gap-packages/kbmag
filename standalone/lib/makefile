# lib makefile
SHELL = /bin/sh
RANLIB = ranlib
RM = /bin/rm
CC = gcc
COPTS = -O2 -Wall -Wno-char-subscripts -Wno-maybe-uninitialized -Werror -fPIC
#COPTS= -O -Wall -Wno-char-subscripts -Wno-maybe-uninitialized -Wstrict-prototypes -Wextra -Werror
LIB = fsalib
LIBOBJ = $(LIB).o
STATIC = $(LIB).a
SHARED = $(LIB).so
OBJS   =fsa.o fsaio.o hash.o rwsreduce.o miscio.o rwsio.o rwsiob.o worddiff.o\
        worddcos.o kbfns.o fsalogic.o rabkar.o fsaipmin.o fsarevmid.o\
        nfa.o midfa.o fsawa.o fsawacos.o fsatriples.o diffreduce.o\
        fsamitriples.o diffredcos.o diffredwl.o fsacheckmult.o migmdet.o\
        fsageopairs.o fsacomposite.o fsaminkb.o fsamicomp.o fsadifflabs.o\
        fsasubmult.o
$(STATIC): $(OBJS)
        ar cr $(STATIC) $(OBJS)
        if  which ranlib > /dev/null 2> /dev/null; then ranlib $(STATIC); fi
$(SHARED): $(OBJS)
        ld -r $(OBJS) -o $(LIBOBJ)
        $(CC) -shared $(LIBOBJ) -o $(SHARED)
kbfns.o: kbfns.c
        $(CC) -c $(COPTS) kbfns.c
.c.o:
        ${CC} -c $(COPTS) $*.c
clean:
        $(RM) -f $(OBJS) $(LIBOBJ) $(STATIC) $(SHARED)
