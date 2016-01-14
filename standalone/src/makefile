# src makefile
SHELL   = /bin/sh
SYSTEM = SYSTEMV
CC      = cc
RM = /bin/rm
LIBPATH = ../lib
BIN = ../bin
FSALIB = $(LIBPATH)/fsalib.a

COPTS = -O
CFLAGS = $(COPTS) -I$(LIBPATH)

all:    $(BIN)/kbprog \
	$(BIN)/fsamin $(BIN)/fsalabmin $(BIN)/fsabfs $(BIN)/fsafilter\
	$(BIN)/fsaand $(BIN)/fsaor $(BIN)/fsaandnot\
	$(BIN)/fsanot $(BIN)/fsastar $(BIN)/fsaconcat\
	$(BIN)/fsaexists $(BIN)/nfadeterminize\
        $(BIN)/fsacount $(BIN)/fsaenumerate $(BIN)/fsaswapcoords\
        $(BIN)/fsareverse $(BIN)/fsagrowth $(BIN)/fsaprune $(BIN)/fsalequal\
	$(BIN)/gpwa $(BIN)/gpgenmult $(BIN)/gpcheckmult \
	$(BIN)/gpmult $(BIN)/gpgenmult2 $(BIN)/gpmult2 \
	$(BIN)/gpcomp $(BIN)/gpaxioms $(BIN)/gpminkb $(BIN)/gpdifflabs \
	$(BIN)/gpmakefsa $(BIN)/wordreduce $(BIN)/gpgeowa \
	$(BIN)/ppgap $(BIN)/ppgap4 $(BIN)/autgroup\
	$(BIN)/midfadeterminize $(BIN)/kbprogcos $(BIN)/gpmigenmult\
	$(BIN)/gpmigmdet $(BIN)/gpmimult $(BIN)/gpmigenmult2\
        $(BIN)/gpmimult2 $(BIN)/gpmicomp $(BIN)/gpsubpres\
	$(BIN)/makecosfile $(BIN)/gpmakesubwa $(BIN)/gpchecksubwa\
	$(BIN)/autcos $(BIN)/gpsubwa

.c.o:
	${CC} -c $(CFLAGS) $*.c

${BIN}/kbprog: kbprog.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/kbprog kbprog.o $(FSALIB)

kbprog.o: kbprog.c
	$(CC) -c $(CFLAGS) -D$(SYSTEM) kbprog.c

${BIN}/kbprogcos: kbprogcos.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/kbprogcos kbprogcos.o $(FSALIB)

kbprogcos.o: kbprogcos.c
	$(CC) -c $(CFLAGS) -D$(SYSTEM) kbprogcos.c

${BIN}/fsamin: fsamin.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsamin  fsamin.o $(FSALIB)

${BIN}/fsalabmin: fsalabmin.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsalabmin  fsalabmin.o $(FSALIB)

${BIN}/fsabfs: fsabfs.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsabfs  fsabfs.o $(FSALIB)

${BIN}/fsafilter: fsafilter.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsafilter  fsafilter.o $(FSALIB)

${BIN}/fsaand: fsaand.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsaand  fsaand.o $(FSALIB)

${BIN}/fsaor: fsaor.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsaor  fsaor.o $(FSALIB)

${BIN}/fsaandnot: fsaandnot.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsaandnot  fsaandnot.o $(FSALIB)

${BIN}/fsanot: fsanot.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsanot  fsanot.o $(FSALIB)

${BIN}/fsastar: fsastar.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsastar  fsastar.o $(FSALIB)

${BIN}/fsaconcat: fsaconcat.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsaconcat  fsaconcat.o $(FSALIB)

${BIN}/fsaexists: fsaexists.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsaexists  fsaexists.o $(FSALIB)

${BIN}/nfadeterminize: nfadeterminize.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/nfadeterminize  nfadeterminize.o $(FSALIB)

${BIN}/fsacount: fsacount.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsacount  fsacount.o $(FSALIB)

${BIN}/fsaenumerate: fsaenumerate.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsaenumerate  fsaenumerate.o $(FSALIB)

${BIN}/fsaswapcoords: fsaswapcoords.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsaswapcoords  fsaswapcoords.o $(FSALIB)

${BIN}/fsareverse: fsareverse.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsareverse  fsareverse.o $(FSALIB)

${BIN}/fsagrowth: fsagrowth.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsagrowth  fsagrowth.o $(FSALIB)

${BIN}/fsaprune: fsaprune.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsaprune  fsaprune.o $(FSALIB)

${BIN}/fsalequal: fsalequal.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/fsalequal  fsalequal.o $(FSALIB)

${BIN}/midfadeterminize: midfadeterminize.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/midfadeterminize  midfadeterminize.o $(FSALIB)

${BIN}/gpwa: gpwa.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpwa  gpwa.o $(FSALIB) 

${BIN}/gpgenmult: gpgenmult.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpgenmult  gpgenmult.o $(FSALIB)

${BIN}/gpmigenmult: gpmigenmult.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpmigenmult  gpmigenmult.o $(FSALIB)

${BIN}/gpcheckmult: gpcheckmult.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpcheckmult  gpcheckmult.o $(FSALIB)

${BIN}/gpmult: gpmult.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpmult  gpmult.o $(FSALIB)

${BIN}/gpmimult: gpmimult.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpmimult  gpmimult.o $(FSALIB)

${BIN}/gpgenmult2: gpgenmult2.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpgenmult2  gpgenmult2.o $(FSALIB)

${BIN}/gpmigenmult2: gpmigenmult2.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpmigenmult2  gpmigenmult2.o $(FSALIB)

${BIN}/gpmult2: gpmult2.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpmult2  gpmult2.o $(FSALIB)

${BIN}/gpmimult2: gpmimult2.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpmimult2  gpmimult2.o $(FSALIB)

${BIN}/gpcomp: gpcomp.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpcomp  gpcomp.o $(FSALIB)

${BIN}/gpmicomp: gpmicomp.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpmicomp  gpmicomp.o $(FSALIB)

${BIN}/gpaxioms: gpaxioms.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpaxioms  gpaxioms.o $(FSALIB)

${BIN}/gpsubpres: gpsubpres.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpsubpres  gpsubpres.o $(FSALIB)

${BIN}/gpminkb: gpminkb.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpminkb  gpminkb.o $(FSALIB)

${BIN}/gpdifflabs: gpdifflabs.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpdifflabs  gpdifflabs.o $(FSALIB)

${BIN}/gpmakefsa: gpmakefsa.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpmakefsa  gpmakefsa.o $(FSALIB)

${BIN}/wordreduce: wordreduce.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/wordreduce  wordreduce.o $(FSALIB)

${BIN}/gpgeowa: gpgeowa.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpgeowa  gpgeowa.o $(FSALIB)

${BIN}/gpmigmdet: gpmigmdet.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpmigmdet  gpmigmdet.o $(FSALIB)

${BIN}/makecosfile: makecosfile.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/makecosfile  makecosfile.o $(FSALIB)

${BIN}/gpmakesubwa: gpmakesubwa.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpmakesubwa  gpmakesubwa.o $(FSALIB)

${BIN}/gpchecksubwa: gpchecksubwa.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/gpchecksubwa  gpchecksubwa.o $(FSALIB)

${BIN}/ppgap: ppgap.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/ppgap  ppgap.o $(FSALIB)

${BIN}/ppgap4: ppgap4.o $(FSALIB)
	$(CC) $(CFLAGS) -o ${BIN}/ppgap4  ppgap4.o $(FSALIB)

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
