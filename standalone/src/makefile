# src makefile
SHELL   = /bin/sh
CC      = cc
RM = /bin/rm
LIBPATH = ../lib
BIN = ../bin
FSALIB = $(LIBPATH)/fsalib.a

all: \
	$(BIN)/kbprog \
	$(BIN)/autcos \
	$(BIN)/autgroup \
	$(BIN)/fsaand \
	$(BIN)/fsaandnot \
	$(BIN)/fsabfs \
	$(BIN)/fsaconcat \
	$(BIN)/fsacount \
	$(BIN)/fsaenumerate \
	$(BIN)/fsaexists \
	$(BIN)/fsafilter \
	$(BIN)/fsagrowth \
	$(BIN)/fsalabmin \
	$(BIN)/fsalequal \
	$(BIN)/fsamin \
	$(BIN)/fsanot \
	$(BIN)/fsaor \
	$(BIN)/fsaprune \
	$(BIN)/fsareverse \
	$(BIN)/fsastar \
	$(BIN)/fsaswapcoords \
	$(BIN)/gpaxioms \
	$(BIN)/gpcheckmult \
	$(BIN)/gpchecksubwa \
	$(BIN)/gpcomp \
	$(BIN)/gpdifflabs \
	$(BIN)/gpgenmult \
	$(BIN)/gpgenmult2 \
	$(BIN)/gpgeowa \
	$(BIN)/gpmakefsa \
	$(BIN)/gpmakesubwa \
	$(BIN)/gpmicomp \
	$(BIN)/gpmigenmult \
	$(BIN)/gpmigenmult2 \
	$(BIN)/gpmigmdet \
	$(BIN)/gpmimult \
	$(BIN)/gpmimult2 \
	$(BIN)/gpminkb \
	$(BIN)/gpmult \
	$(BIN)/gpmult2 \
	$(BIN)/gpsubpres \
	$(BIN)/gpsubwa \
	$(BIN)/gpwa \
	$(BIN)/kbprogcos \
	$(BIN)/makecosfile \
	$(BIN)/midfadeterminize \
	$(BIN)/nfadeterminize \
	$(BIN)/ppgap \
	$(BIN)/ppgap4 \
	$(BIN)/wordreduce

.c.o:
	${CC} -c $(CFLAGS) -I$(LIBPATH) $*.c

${BIN}/%: %.o $(FSALIB)
	$(CC) $(LDFLAGS) -o $@ $< $(FSALIB)

$(BIN)/autgroup: autgroup
	cp autgroup $(BIN)/autgroup
	chmod +x $(BIN)/autgroup

$(BIN)/autcos: autcos
	cp autcos $(BIN)/autcos
	chmod +x $(BIN)/autcos

$(BIN)/gpsubwa: gpsubwa
	cp gpsubwa $(BIN)/gpsubwa
	chmod +x $(BIN)/gpsubwa

clean:
	$(RM) -f *.o core a.out *\~

.PHONY: clean
