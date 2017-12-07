#############################################################################
##
#A  rws4.g                  GAP library                  Derek Holt
##
##  This file contains those functions that deal with rewriting systems.
##
##  1.3.00. created this file from GAP3 version rws.g and started adapting
##  it to GAP4.
##
##  1.8.96.
##  Changed the ReorderGenerators command to permute the alphabet
##  themselves, and deleted the generatorOrder field. This avoids the
##  need of permuting columns of fsa's when updating.
##
##  15.3.95.
##  Each (internal) rewriting-system now has components "GpMonSgp" (for the
##  associated group or monoid), "generators" (for the generators, which
##  will include those of GpMonSgp, but may also include inverses
##  in the group case), and "namesGenerators", which again include
##  those of GpMonSgp, but will have names with "^-1" adjoined for inverses. 
##
##  When an externally created file containing a rewriting-system is read in
##  to GAP, a preprocessing external program called "ppgap" is run, which
##  creates a file called "file.gap", which includes necessary declarations
##  of a suitable underlying monoid.
##
##  23.2.95. The internal storage of a rewriting system was changed so
##  that generators are simply numbers in the range [1..ng] for some ng,
##  and words are lists of generator numbers.
##
DeclareInfoClass("InfoRWS");


#############################################################################
#V  _RWS                external variable - the name of the rewriting system
#V  _RWS_Sub            external variable - subgroup of the rewriting system
#V  _RWS_Cos            external variable - coset rewriting system
#V  _RWS.GpMonSgp 	external variable - name of underlying group or monoid
#V  _RWS.FreeGpMonSgp 	external variable - name of underlying group or monoid
#V  _KBExtDir 		external variable - directory of external executables
#V  _KBTmpFileName      external variable - name of temporary file.
#V  _ExitCode           external variable - exit code of programs.
##
_RWS   := rec();
_RWS_Sub   := rec();
_RWS_Cos   := rec();

_ExitCode := 0;

#############################################################################
##
#F  IsConfluentRWS(<x>) . . . . . . . test whether x is a confluent rws
##
##  Public function.
IsConfluentRWS := function ( x )
    if not IsKBMAGRewritingSystemRep(x) then return false; fi;
    if not IsBound(x!.isConfluent) then return false; fi;
    return  x!.isConfluent;
end;

#############################################################################
##
#F  IsGroupRWS(<rws>) . . . test whether all gens of rws <rws> have inverses
##
##  Public function.
IsGroupRWS := function ( rws )
    local gp, g;
    if not IsKBMAGRewritingSystemRep(rws) then return false; fi;
    gp:=true;
    for g in rws!.invAlphabet do
      if g = false then gp:=false; fi;
    od;
    return gp;
end;

#############################################################################
##
#F  IsMonoidRWS(<rws>) . . . does <rws> represent a monid
##
##  This merely returns the value of rws!.hasOne.
##  Note that if this is false, then there should be no inverses!
##  Public function.
IsMonoidRWS := function ( rws )
    if not IsKBMAGRewritingSystemRep(rws) then return false; fi;
    return rws!.hasOne;
end;

#############################################################################
##
#F  LinePrintRWS(<line> [,<filename>]) . . . . . . . print the line x
##
##  LinePrintRWS prints the line (a string) to the terminal (default)
##  or to file filename  if specified, formatting nicely.
##  It works by building up the material to be printed line by line as strings,
##  and calling LinePrintRWS to print each individual line.
LinePrintRWS := function ( arg )
    local line, filename;
    line := arg[1];
    if Length(arg) = 1 then
      filename := "";
    else
      filename := arg[2];
    fi;
    if filename = "" then
      Print(line,"\n");
    else
      AppendTo(filename,line,"\n");
    fi;
end;

#############################################################################
##
#F  FpStructureRWS(<rws>) . finitely presented group or semigroup defining <rws>
##
##  Public function.
FpStructureRWS := function ( rws )
  local F, M, IdWord, rels, gens, ng, i, ig, eqn, w1, w2;
  if not IsKBMAGRewritingSystemRep(rws)  then
     Error("Argument is not an KBMAG rewriting system.");
  fi;
  if IsBound(rws!.GpMonSgp) then
     return rws!.GpMonSgp;
  fi;
  ## We have to calculate it!
  M := rws!.WordMonoid;
  IdWord := One(M);
  rels := Set([]);
  gens := rws!.alphabet;
  ng := Length(rws!.alphabet);
  for i in [1..ng] do
    ig := rws!.invAlphabet[i];
    if ig <> false then
      AddSet(rels,[gens[i]*gens[ig],IdWord]);
      AddSet(rels,[gens[ig]*gens[i],IdWord]);
    fi;
  od;
  for eqn in rws!.equations do
    w1 := ListToWordRWS(eqn[1],gens);
    w2 := ListToWordRWS(eqn[2],gens);
    if w1<>w2 then AddSet(rels,[w1,w2]); fi;
  od;
  #Now convert to external representation.
  F := rws!.FreeGpMonSgp;
  rels := List(rels,r -> [rws!.IntToExt(rws!.ExtIntCorr,r[1]),
                          rws!.IntToExt(rws!.ExtIntCorr,r[2])] );
  if IsGroup(F) then
    rels := List(rels,r -> r[1]/r[2] );
  fi;
    
  rws!.GpMonSgp := F/rels;
  return rws!.GpMonSgp;
end;

#############################################################################
##
#F  IsAvailableNormalFormRWS(<x>) . . . . test whether x has a normal form
##
##  Public function.
IsAvailableNormalFormRWS := function ( x )
    return IsKBMAGRewritingSystemRep(x) and
           IsBound(x!.isAvailableNormalForm) and
                   x!.isAvailableNormalForm=true;
end;

#############################################################################
##
#F  IsAvailableReductionRWS(<x>) . . test whether x has a reduction algorithm
##
##  Public function.
IsAvailableReductionRWS := function ( x )
    return IsKBMAGRewritingSystemRep(x) and
           IsBound(x!.isAvailableReduction)
                 and x!.isAvailableReduction=true;
end;

#############################################################################
##
#F  IsAvailableSizeRWS(<x>) . . test whether x has a size algorithm
##
##  Public function.
IsAvailableSizeRWS := function ( x )
    return IsKBMAGRewritingSystemRep(x) and
           IsBound(x!.isAvailableSize)
                 and x!.isAvailableSize=true;
end;

#############################################################################
##
#F  ResetRWS(<rws>)  . . . . . . . . . . . reset rws after a call of KBRUN.
##
##  Public function.
##  This resets a rewriting system back to the original equations, after a
##  call of KBRUN or AutRWS.
ResetRWS := function ( rws )
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not a rewriting system.");
    fi;
    Unbind(rws!.KBRun);
    Unbind(rws!.isConfluent);
    Unbind(rws!.isAvailableNormalForm);
    Unbind(rws!.isAvailableReduction);
    Unbind(rws!.isAvailableSize);
    Unbind(rws!.warningOn);
    Unbind(rws!.reductionFSA);
    Unbind(rws!.wa);
    Unbind(rws!.diff1);
    Unbind(rws!.diff1c);
    Unbind(rws!.diff2);
    Unbind(rws!.gm);
    if IsBound(rws!.originalEquations) then
       Unbind(rws!.equations);
       rws!.equations := rws!.originalEquations;
       Unbind(rws!.originalEquations);
    fi;
end;

#############################################################################
##
#F  NumberSubgroupRWS(<rws>, <subrws>) . . . number of a subgroup of an <rws>
##
##  <rws> should be a rewriting system and <subrws> a subgroup.
##  The number of the subgroup is returned, or fail if it is not a subgroup.
##  (Should be in rwssub4.g really but needed by next function.)
NumberSubgroupRWS := function(rws, subrws)
  local i;
  if not IsGroupRWS(rws) then
     Error("NumberSubgroupRWS only applies to rewriting systems from groups.");
  fi;
  if not IsKBMAGRewritingSystemRep(subrws) or
                    not IsBound(subrws!.alphabet) then
     Error(
    "Second argument of NumberSubgroupRWS must be have generators.");
  fi;
  if not IsBound(rws!.subgroups)
    then return fail;
  fi;
  for i in [1..rws!.numSubgroups] do
    if rws!.subgroups[i]!.alphabet = subrws!.alphabet then
       return i;
    fi;
  od;
  return fail;
end;

#############################################################################
##
#F  SetOrderingRWS(<rws>,<ord>[,list]) 
##                          . . .  specify the ordering of a rewriting system
##
##  <rws> should be a rewriting system, and <ord> one of the strings that
##  defines an ordering on the words in the alphabet of <rws>.
##  These are "shortlex", "recursive", rt_recursive", "wtlex" and "wreathprod".
##  In the case of "wtlex" and "wreathprod", the extra parameter <list> is
##  required, and it should be a list of ng (= number of alphabet of <rws>)
##  non-negative integers, specifying the weights or the levels of the
##  alphabet, respectively, for this ordering.
##  Public function.
SetOrderingRWS := function ( arg )
    local rws, ord, list, ng, go, i;
    if Length(arg)<2 or Length(arg)>3 then
       Error("SetOrderingRWS has 2 or 3 arguments");
    fi;
    rws:=arg[1];
    ord:=arg[2];
    if Length(arg)=3 then
      list:=arg[3];
    else
      list:=[];
    fi;
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not an KBMAG rewriting system.");
    fi;
    if not IsString(ord) then
       Error("Second argument is not a string.");
    fi;

    ng := Length(rws!.alphabet);
    if Length(arg)=3 then
      if not IsList(list) or Length(list)<>ng then
         Error("Third argument is not a list of length <ng>.");
      fi;
      for i in [1..ng] do
        if not IsInt(list[i]) or list[i]<0 then
          Error("Third argument is not a list of non-negative integers.");
        fi;
      od;
    fi;
    
    if ord="shortlex" or ord="recursive" or ord="rt_recursive" or
       ord="wtlex" or ord="wreathprod" then
      rws!.ordering:=ord;
    else
      Error("Unknown ordering",ord);
    fi;
    if (ord="wtlex" or ord="wreathprod") and list=[] then
      Error("Third argument required for ordering",ord);
    fi;
    if ord="wtlex" then rws!.weight:=list; fi;
    if ord="wreathprod" then rws!.level:=list; fi;
end;

#############################################################################
##
#F  ReorderGeneratorsRWS(<rws>,<p>) . reorder alphabet of a rewriting system
##
##  <rws> should be a rewriting system, and <p>  a permutation of the set
##  [1..ng], where <rws> has <ng> = length of alphabet.
##  The alphabet of <rws> is reordered by applying the permutation <p> to
##  its existing order.
##  Public function.
ReorderGeneratorsRWS := function ( rws, p )
    local ng, list, i, eqn;
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not an KBMAG rewriting system.");
    fi;
    if not IsPerm(p) then
       Error("Second argument is not a permutation.");
    fi;
    ng := Length(rws!.alphabet);
    if LargestMovedPointPerm(p) > ng then
       Error("Permutation is on more points than there are alphabet!");
    fi;
    
    list:=[];
    for i in [1..ng] do list[i^p]:=rws!.alphabet[i]; od;
    rws!.alphabet:=list;

    list:=[];
    for i in [1..ng] do 
      if IsInt(rws!.invAlphabet[i]) then
        list[i^p]:=rws!.invAlphabet[i]^p;
      else list[i^p] := false;
      fi;
    od;
    rws!.invAlphabet:=list;

    for eqn in rws!.equations do
      list := List(eqn[1],i->i^p);
      eqn[1]:=list;
      list := List(eqn[2],i->i^p);
      eqn[2]:=list;
    od;

    if IsBound(rws!.originalEquations) then
      for eqn in rws!.originalEquations do
        list := List(eqn[1],i->i^p);
        eqn[1]:=list;
        list := List(eqn[2],i->i^p);
        eqn[2]:=list;
      od;
    fi;

    if IsBound(rws!.weight) then
      list:=[];
      for i in [1..ng] do list[i^p]:=rws!.weight[i]; od;
      rws!.weight:=list;
    fi;

    if IsBound(rws!.level) then
      list:=[];
      for i in [1..ng] do list[i^p]:=rws!.level[i]; od;
      rws!.level:=list;
    fi;
end;

#############################################################################
##
#F  ReadRWS(<filename>, [semigp])  . . . .read and convert a rewriting system
##
##  ReadRWS reads a rewriting system, which must be declared with the
##  external variable name "_RWS" from the file <filename>, and converts it
##  to internal format. First it creates and reads the GAP preprocessor file
##  <filename>.gap, for the declarations of variable names.
##  This is created using the external program "ppgap".
##  The rewriting system is returned.
##  If the optional second argument is true, then the rewriting system is
##  regarded as being for a semigroup rather than for a monoid (default).
##  This means that the empty word is not part of the language.
##  For this to be the case there must be no inverses, or an error will result.
##  Public function.
ReadRWS := function ( arg )
    local i, rgm, rfgm, rws, ng, p, ig, ri,
          eqn, filename, semigp, mnames, fam, isgp, l, s, gtom, igtom;
    
    filename:=arg[1];
    if Length(arg)>1 then
      semigp := arg[2];
    else
      semigp := false;
    fi;
    Exec(Concatenation(Filename(_KBExtDir,"ppgap4")," ",filename));
    Read(Concatenation(filename,".gap4"));
    Exec(Concatenation("/bin/rm -f ",filename,".gap4")); 
 
    rfgm := _RWS.FreeGpMonSgp;
                  #This is about to get overwritten, so we remember it! 

    if not READ(filename) then Error("Could not open file for reading"); fi;

    rws := _RWS; _RWS := rec(); #reset _RWS for next time
    
    rws.FreeGpMonSgp := rfgm;
    isgp := IsGroup(rfgm);
    rws.hasOne := not semigp;
    rws.options := rec();

    #Several of the fields of the rewriting system are stored differently
    #or have different names in the internal storage, than the way they
    #appear in the file.
    ng := Length(rws.generatorOrder);

    #Internally, inverses are not stored as a list of alphabet, but as
    #a list of integers (in the field invAlphabet), giving the position
    #of the inverse generator in the generator list.
    ri := rws.inverses;
    ig := []; rws.invAlphabet := ig;
    for i in [1..ng] do
      if IsBound(ri[i]) then
        ig[i] := Position(rws.generatorOrder,ri[i]);
        if semigp then
          Error("There can be no inverse in a semigroup.");
        fi;
      else
        ig[i] := false;
      fi;
    od;
    Unbind(rws.inverses);


    #The left- and right-hand sides of the equations are not stored
    #internally as words, but as lists of integers, giving the numbers of
    #the alphabet appearing in the list.
    for eqn in rws.equations do
        eqn[1] := WordToListRWS(eqn[1],rws.generatorOrder);
        eqn[2] := WordToListRWS(eqn[2],rws.generatorOrder);
    od;

    mnames := [];
    for i in [1..ng] do
      if isgp then mnames[i] := Concatenation("_g",String(i));
      else mnames[i] := Concatenation("_m",String(i));
      fi;
    od;
    rws.WordMonoid := FreeMonoid(mnames);
    rws.alphabet := GeneratorsOfMonoid(rws.WordMonoid);

    #Now we have to set up the Ext/Int correspondence.
    #This is tricky for groups, because some of the names in the
    #external file might have form "x^-1".
    if isgp then
      gtom := []; igtom :=[];
      for i in [1..ng] do
        s:=String(rws.generatorOrder[i]);
        l:=Length(s);
        if l<=3 or s{[l-2..l]} <> "^-1" then
          Add(gtom,i);
          Add(igtom,rws.invAlphabet[i]);
        fi;
      od;
      rws.ExtIntCorr :=
         CorrespondenceGroupMonoid(rfgm,rws.WordMonoid,gtom,igtom);
      rws.ExtToInt := FreeGroup2FreeMonoid;
      rws.IntToExt := FreeMonoid2FreeGroup;
    else
      rws.ExtIntCorr :=
         CorrespondenceGroupMonoid(rfgm,rws.WordMonoid);
      rws.ExtToInt := FreeMS2FreeMonoid;
      rws.IntToExt := FreeMonoid2FreeMS;
    fi;
    Unbind(rws.generatorOrder); #we no longer use this field.

    fam := NewFamily("Family of Knuth-Bendix Rewriting systems",
                IsKnuthBendixRewritingSystem);
    rws := Objectify(NewType(fam,
                IsMutable and IsKnuthBendixRewritingSystem
                and IsKBMAGRewritingSystemRep),
                rws);
    FpStructureRWS(rws);
    return rws;
end;

#############################################################################
##
#F  ExtVarHandlerRWS(<rws>, <filename>) . . write file to handle externals
##
## This is hopefully a temporary hack, for use until GAP V4, where should be
## a better solution. A GAP file is written to preserve any existing values
## of external variables corresponding to the generator names of the
## rewriting system <rws>, and then to declare these variables to be equal
## to the corresponding alphabet of <rws>. This is necessary for reading
## back in the output of KBRWS or AutRWS, which uses these names.
## This first file is called <rws>.gap1.
## A second file <rws>.gap2 is written for reading afterwards, which restores
## the values of any previously existing externals with those names.
## The files are read by the following two functions below.
##
ExtVarHandlerRWS  := function(rws, filename)
    local file1, file2, ng, names, line, i, ni, l;
    file1 := Concatenation(filename,".gap1");
    file2 := Concatenation(filename,".gap2");
    PrintTo(file1,"_RWS.oldNames:=false;\n");
    PrintTo(file2,"");
    
    ng := Length(rws!.alphabet);
    names := List(rws!.alphabet,x->String(x));
    _RWS.WordMonoid := rws!.WordMonoid;
    for i in [1..ng] do _RWS.(i) := rws!.alphabet[i]; od;

    for i in [1..ng] do
      ni := names[i]; l := Length(ni);
      if l <= 3 or ni{[l-2..l]} <> "^-1" then
        line := Concatenation("if IsBound(",ni,") and ",ni,
            " <> _RWS.WordMonoid.",String(i)," then _RWS.",String(i+ng),":=",
               ni,"; _RWS.oldNames:=true; fi;\n");
        line := Concatenation(line,ni,":=_RWS.WordMonoid.",String(i),";\n");
        AppendTo(file1,line);
        line := Concatenation("if IsBound(_RWS.",String(i+ng),") then ",
                ni,":=_RWS.",String(i+ng),"; fi;\n");
        AppendTo(file2,line);
      fi;
    od;
    line := Concatenation(
       "if IsBound(_) and _ <> One(_RWS.WordMonoid) then _RWS.",
       String(2*ng+1), ":=_;\n    _RWS.oldNames:=true; fi;\n");
    line := Concatenation(line,"_:=One(_RWS.WordMonoid);\n");
    AppendTo(file1,line);
    line := Concatenation("if IsBound(_RWS.",String(2*ng+1),
          ") then  _:=_RWS.",String(2*ng+1),"; fi;\n");
    AppendTo(file2,line);
    line := Concatenation(
    "if IsBound(IdWord) and IdWord <> One(_RWS.WordMonoid) then _RWS.",
          String(2*ng+2), ":=IdWord;\n     _RWS.oldNames:=true; fi;\n");
    line := Concatenation(line,"IdWord:=One(_RWS.WordMonoid);\n");
    AppendTo(file1,line);
    line := Concatenation("if IsBound(_RWS.",String(2*ng+2),
          ") then  IdWord:=_RWS.",String(2*ng+2),"; fi;\n");
    AppendTo(file2,line);
end;

#############################################################################
##
#F  StoreNamesRWS(<rws>, <filename>) 
##  Store existing variables before reading external file.
StoreNamesRWS := function(rws, filename)
    local i;
    ExtVarHandlerRWS(rws,filename);
    Read(Concatenation(filename,".gap1"));
    rws!.oldNames := _RWS.oldNames;
end;

#############################################################################
##
#F  RedefineNamesRWS(<rws>, <filename>) 
##  Redefine existing variables after reading external file.
##  Store existing variables.
RedefineNamesRWS := function(rws, filename)
    local i;
    if rws!.oldNames then
      Read(Concatenation(filename,".gap2"));
    fi;
    _RWS := rec();
    _RWS_Cos := rec();
end;

#############################################################################
##
#F  UpdateRWS(<rws>, <filename>, <kb>, [<cosets>])
##                              . . update rws, after run of external program
##
## This function is called after a run of one of the "documented" external
## programs (currently KBRWS and AutRWS) on the rewriting system <rws>.
## It updates <rws> being careful to reset any external variables that were
## used by the external program, but previously existed in the current GAP
## session.   <filename> should be the file in which the
## original rewriting-system was stored. <kb> should be true or false,
## according to whether the function is being called from a Knuth-Bendix
## application (KBRWS) or automatic groups (AutRWS).
## In the Knuth-Bendix case, <filename>.kbprog is read in, for the updated
## version of the equations. Then <filename>.reduce is read in
## for the reduction machine.
## In the automatic groups case, <filename>.wa is read in for the word-acceptor,
## and then <filename.diff2> and <filename>.diff1c for the word-difference
## machines used in word  reduction.
## 

UpdateRWS := function(arg)
	local rws, filename, kb, cosets, _RWSrec, x, i, j, k, l, eqn, twovar,
              fsa, fsa2, fsa3, newrow, ig, mg, alph, la, efilename;

    rws := arg[1];
    filename := arg[2];
    kb := arg[3];
    cosets := false;
    if Length(arg)>=4 then
      cosets := arg[4];
    fi;

    #Make preprocessing file
    StoreNamesRWS(rws, filename);
    if cosets then
      _RWS_Cos := _RWS;
    fi;

    mg := GeneratorsOfMonoid(rws!.WordMonoid);
    if cosets then
      alph := rws!.baseAlphabet;
    else
      alph := rws!.alphabet;
    fi;
    la := Length(alph);
    if kb then
      #Read in updated version of equations.
      if not READ(Concatenation(filename,".kbprog")) then
         Error("Could not open output of external Knuth-Bendix program.");
      fi;
      if cosets then _RWSrec := _RWS_Cos; else _RWSrec := _RWS; fi;
      rws!.equations := _RWSrec.equations;
      for eqn in rws!.equations do
        eqn[1] := WordToListRWS(eqn[1],mg);
        eqn[2] := WordToListRWS(eqn[2],mg);
      od;
      rws!.isConfluent := _RWSrec.isConfluent;
      if cosets then
        rws!.ordering := _RWSrec.ordering;
        rws!.level := _RWSrec.level;
      fi;
    fi;

    # read automata
    if kb then
      if not READ(Concatenation(filename,".reduce")) then
         Error("Could not open reduction machine file");
      fi;
      fsa:= _RWSrec.reductionFSA;
      rws!.reductionFSA := fsa;
      if not rws!.hasOne then # empty word should not be accepted.
        fsa.accepting := [2..fsa.states.size];
      fi;
      for i in [1..la] do
        fsa.alphabet.names[i] := alph[i];
        #They may got re-ordered!
      od;
    else
      if cosets then _RWSrec := _RWS_Cos; else _RWSrec := _RWS; fi;
      if not READ(Concatenation(filename,".wa")) then
         Error("Could not open word-acceptor file");
      fi;
      fsa := _RWSrec.wa;
      rws!.wa := fsa;
      for i in [1..la] do
        fsa.alphabet.names[i] := alph[i];
        #They may got re-ordered!
      od;
      if cosets then efilename:=Concatenation(filename,".midiff1");
      else efilename:=Concatenation(filename,".diff1c");
      fi;
      if not READ(efilename) then
         Error("Could not open word-difference file");
      fi;
      if cosets then fsa2 := _RWS.midiff1; else fsa2 := _RWS.diff1c; fi;
      if cosets then rws!.midiff1 := fsa2; else rws!.diff1 := fsa2; fi;
      if cosets then efilename:=Concatenation(filename,".midiff2");
      else efilename:=Concatenation(filename,".diff2");
      fi;
      if not READ(efilename) then
         Error("Could not open word-difference file");
      fi;
      if cosets then fsa3 := _RWS.midiff2; else fsa3 := _RWS.diff2; fi;
      if cosets then rws!.midiff2 := fsa3; else rws!.diff2:=fsa3; fi;
      #fsa2.alphabet.type := "simple";
      #fsa3.alphabet.type := "simple";
      for i in [1..la] do
        fsa2.states.alphabet[i] := alph[i];
        fsa3.states.alphabet[i] := alph[i];
        #They may got re-ordered!
      od;
    fi;

    #Reset any lost existing externals
    RedefineNamesRWS(rws, filename);
    
    InitializeFSA(fsa);
    #Make sure the table is stored densely
    DenseDTableFSA(fsa);
    fsa.table.format:="dense deterministic";
    fsa.table.transitions:=fsa.denseDTable;
    Unbind(fsa.sparseTable);
    fsa.alphabet.printingStrings:=List(rws!.alphabet,x->String(x));
    if not kb then
       InitializeFSA(fsa2);
       InitializeFSA(fsa3);
       #Make sure the table is stored densely
       DenseDTableFSA(fsa2);
       DenseDTableFSA(fsa3);
       #fsa2.alphabet.base.printingStrings:=List(rws!.alphabet,x->String(x));
       #fsa3.alphabet.base.printingStrings:=List(rws!.alphabet,x->String(x));
       fsa2.states.printingStrings:=List(rws!.alphabet,x->String(x));
       fsa3.states.printingStrings:=List(rws!.alphabet,x->String(x));
       fsa2.table.format:="dense deterministic";
       fsa3.table.format:="dense deterministic";
       fsa2.table.transitions:=fsa.denseDTable;
       fsa3.table.transitions:=fsa.denseDTable;
       Unbind(fsa2.sparseTable);
       Unbind(fsa3.sparseTable);
    fi;
end;

#############################################################################
##
#F  WriteRWS(<rws>, [<filename>], [<endsymbol>])
##           . . . . . . . . . . . .write an rws to a file in external format
##
##  WriteRWS prints the rws <rws> to the  file <filename> formatting nicely.
##  It works by building up the material to be printed line by line as strings,
##  and calling LinePrintRWS to print each individual line.
##  If <filename> is not present, or empty, then writing is to the terminal
##  and is simply of form rec(..).
##  Otherwise, printing takes form _RWS := rec(...)<endsymbol>
##  where <endsymbol> is a string which is ";" by default.
##  (_RWS is a global variable.)
##
##  Public function.
WriteRWS := function ( arg )
    local rws, name, filename, gapfilename, line, i, eqn, endsymbol,
          ng, en, gn, ls, ig;

    if Length(arg)<1 then
       Error("WriteRWS has 1, 2 or 3 arguments");
    fi;
    rws := arg[1];
    filename := "";
    if Length(arg)>=2 then filename := arg[2]; fi;
    if filename="" then endsymbol := ""; else endsymbol := ";"; fi;
    if Length(arg)>=3 then endsymbol := arg[3]; fi;
    
    if not IsKBMAGRewritingSystemRep(rws) then
      Error("First argument is not an KBMAG rewriting system.");
    fi;

    ng := Length(rws!.alphabet);
    en := List(rws!.alphabet,x->String(x));

    #Now print main file
    if filename="" then Print("rec(\n");
    else PrintTo(filename,"_RWS := rec (\n");
    fi;

    line := String("isRWS",16);
    line := Concatenation(line," := true,");
    LinePrintRWS(line,filename);

    if IsBound(rws!.isConfluent) then
      line := String("isConfluent",16);
      line := Concatenation(line," := ",String(rws!.isConfluent),",");
      LinePrintRWS(line,filename);
    fi;

#Now come all of the optional parameters
    if IsBound(rws!.options.tidyint) then
      line := String("tidyint",16);
      line := Concatenation(line," := ",String(rws!.options.tidyint),",");
      LinePrintRWS(line,filename);
    fi;
    if IsBound(rws!.options.maxeqns) then
      line := String("maxeqns",16);
      line := Concatenation(line," := ",String(rws!.options.maxeqns),",");
      LinePrintRWS(line,filename);
    fi;
    if IsBound(rws!.options.maxstates) then
      line := String("maxstates",16);
      line := Concatenation(line," := ",String(rws!.options.maxstates),",");
      LinePrintRWS(line,filename);
    fi;
    if IsBound(rws!.options.maxreducelen) then
      line := String("maxreducelen",16);
      line := Concatenation(line," := ",String(rws!.options.maxreducelen),",");
      LinePrintRWS(line,filename);
    fi;
    if IsBound(rws!.options.confnum) then
      line := String("confnum",16);
      line := Concatenation(line," := ",String(rws!.options.confnum),",");
      LinePrintRWS(line,filename);
    fi;
    if IsBound(rws!.options.maxwdiffs) then
      line := String("maxwdiffs",16);
      line := Concatenation(line," := ",String(rws!.options.maxwdiffs),",");
      LinePrintRWS(line,filename);
    fi;
    if IsBound(rws!.options.maxstoredlen) then
      line := String("maxstoredlen",16);
      line := Concatenation(line, " := [",
              String(rws!.options.maxstoredlen[1]),",",
                               String(rws!.options.maxstoredlen[2]),"],");
      LinePrintRWS(line,filename);
    fi;
    if IsBound(rws!.options.sorteqns) then
      line := String("sorteqns",16);
      line := Concatenation(line," := ",String(rws!.options.sorteqns),",");
      LinePrintRWS(line,filename);
    fi;
    if IsBound(rws!.options.maxoplen) then
      line := String("maxoplen",16);
      line := Concatenation(line," := ",String(rws!.options.maxoplen),",");
      LinePrintRWS(line,filename);
    fi;
    if InfoLevel(InfoRWS)=0 then
      line := String("silent",16);
      line := Concatenation(line," := true,");
      LinePrintRWS(line,filename);
    fi;
    if InfoLevel(InfoRWS)>1 then
      line := String("verbose",16);
      line := Concatenation(line," := true,");
      LinePrintRWS(line,filename);
    fi;
    if InfoLevel(InfoRWS)>2 then
      line := String("veryVerbose",16);
      line := Concatenation(line," := true,");
      LinePrintRWS(line,filename);
    fi;

    line := Concatenation(String("generatorOrder",16)," := [");
    for i in [1..ng] do
      if i > 1 then
        line := Concatenation(line,",");
      fi;
      if i=1 or Length(line)+Length(en[i]) <= 76 then
        line := Concatenation(line,en[i]);
      else
        LinePrintRWS(line,filename);
        line := String("",21);
        line := Concatenation(line,en[i]);
      fi;
    od;
    line := Concatenation(line,"],");
    LinePrintRWS(line,filename);

    ig := rws!.invAlphabet;
    line := Concatenation(String("inverses",16)," := [");
    for i in [1..ng] do
      if i > 1 then line := Concatenation(line,","); fi;
      if IsInt(ig[i]) and ig[i]>0 then
        if i=1 or Length(line)+Length(en[ig[i]]) <= 76 then
          line := Concatenation(line,en[ig[i]]);
        else
          LinePrintRWS(line,filename);
          line := String("",21);
          line := Concatenation(line,en[ig[i]]);
        fi;
      fi;
    od;
    line := Concatenation(line,"],");
    LinePrintRWS(line,filename);

    if not IsString(rws!.ordering) then
       Error("Can only output orderings that are strings");
    fi;
    line := String("ordering",16);
    line := Concatenation(line," := \"",rws!.ordering,"\",");
    LinePrintRWS(line,filename);

    if rws!.ordering="wtlex" and IsBound(rws!.weight) then
      line := Concatenation(String("weight",16)," := [");
      for i in [1..ng] do
        if i > 1 then
          line := Concatenation(line,",");
        fi;
        line := Concatenation(line,String(rws!.weight[i]));
      od;
      line := Concatenation(line,"],");
      LinePrintRWS(line,filename);
    fi;

    if rws!.ordering="wreathprod" and IsBound(rws!.level) then
      line := Concatenation(String("level",16)," := [");
      for i in [1..ng] do
        if i > 1 then
          line := Concatenation(line,",");
        fi;
        line := Concatenation(line,String(rws!.level[i]));
      od;
      line := Concatenation(line,"],");
      LinePrintRWS(line,filename);
    fi;

    line := Concatenation(String("equations",16)," := [");
    for i in [1..Length(rws!.equations)] do
      if i > 1 then line := Concatenation(line,","); fi;
      LinePrintRWS(line,filename);
      eqn := rws!.equations[i];
      line := Concatenation(String("[",10),
                          StringRWS(ListToWordRWS(eqn[1],rws!.alphabet)),",");
      if Length(line)>=40 then
        LinePrintRWS(line,filename);
        line := String("",10);
      fi;
      line :=Concatenation(line,
                  StringRWS(ListToWordRWS(eqn[2],rws!.alphabet)),"]");
    od;
    LinePrintRWS(line,filename);
    line := String("]",8);
    LinePrintRWS(line,filename);
    line := Concatenation(")",endsymbol);
    LinePrintRWS(line,filename);
end;

#############################################################################
##
#F  IsReducedWordRWS(<rws>,<w>) . . . . tests if a word is reduced
##
##  IsReducedWordRWS tests whether the word <w>
##  is reduced, using the  rewriting system <rws>.
##  <w> can be given either as a list of integers (internal format) or as
##  a word in the generators of the underlying group or monoid.
##  Either the word-acceptor (automatic group case) or the reduction FSA
##  must be defined.
##  It merely calls the corresponding FSA function.
##
##  Public function.
IsReducedWordRWS := function ( rws, w )
    local i, ng;
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not an KBMAG rewriting system.");
    fi;
    if not IsAvailableReductionRWS(rws) then
       Error(
   "Reduction algorithm unavailable. Run KnuthBendix or AutomaticStructure.");
    fi;
    if not IsList(w) and not IsWord(w) then
       Error("Second argument is not a word or list.");
    fi;
    ng := Length(rws!.alphabet);
    if IsWord(w) then
       w:=WordToListRWS(w,rws!.alphabet);
    fi;
    if IsBound(rws!.wa) then
    # Automatic group case - use word-acceptor
      return IsAcceptedWordDFA( rws!.wa,w );
    fi;
    if not IsBound(rws!.reductionFSA)  then
       Error("First argument does not have initialized dfa as field.");
    fi;
    return IsAcceptedWordDFA( rws!.reductionFSA,w );
end;
      
#############################################################################
##
#F  ReduceWordWD(<wd>,<w>)
##                   . . . . .reduces a word using word-difference automaton
##
##  ReduceWordWD calculates the reduction of the word <w> (list of integers)
##  using the word-difference automaton <wd>.
##  <wd> should be two-variable, where <w> is a list of integers in the range
##  [1..ng], where ng is the size of the base alphabet.
##  WARNING: No validity checks are carried out!
##
##  Private function.
ReduceWordWD := function ( wd, w)
    local  ndiff, ngens, ng1, identity, level, cf, gpref, gct, gptr,
           diff, newdiff, deqi, gen1, gen2, donesub, donediffs, subvert,dosub,
           g2ltg1, diffct, t, nlen, olen, i, l, table;
    if not IsInitializedFSA(wd) then
       Error("First argument is not an initialized dfa.");
    fi;

    ndiff := wd.states.size;
    ngens := wd.alphabet.base.size;
    ng1 := ngens+1;            
    identity := wd.initial[1];
    if Length(w) <= 0 then
      return w;
    fi;
    cf := [];
    # cf is used as a characteristic function, when constructing a subset of the
    # set  D  of word differences.
    gpref := []; gct := 0; gpref[1] := 0; gptr := [];
    # gpref[n]  is the number of "vertices" that have been defined after
    # reading the first n-1 elements of the word.
    # These vertices are gptr[1],...,gptr[gpref[n]].
    # A vertex is a record with 4 components, backptr, genno, diffno, sublen,
    # It represents a vertex in the graph of strings that may eventually
    # be used as substituted strings in the word w.
    # backptr is either undefined or another vertex.
    # gen is the generator at the vertex.
    # diffno is the word-difference number of the string at which the vertex
    #        is at the end - this string is reconstructed using backptr.
    # sublen is plus or minus the length of this string. sublen is positive
    #        iff the string lexicographically precedes the corresponding
    #        prefix of the word being reduced.

    # Now we start scanning the word.
    table := DenseDTableFSA(wd);
    level := 1;
    while level <= Length(w) do
      for i in [1..ndiff] do cf[i] := false; od;
      gen1 := w[level];
      # The next loop is over the identity, and the subset of the set of
      # word-differences (states of wd) defined at the previous level (level-1)

      diff := identity;
      donesub := false;
      donediffs := false;
      while not donesub and not donediffs do
        deqi := diff = identity;
      # First look for a possible substitution of a shorter string
        newdiff := table[diff][ng1*gen1];
        if newdiff=identity then
          #Make substitution  reducing length of word by 1
          SubstitutedListFSA(w,level,level,[]);
          i := level-1;
          if not deqi then
            subvert := gptr[diffct];
	    dosub := true;
            while dosub do
              w[i] := subvert.gen;
              i := i-1;
              if IsBound(subvert.backptr) then
	        subvert := subvert.backptr;
              else
                dosub := false;
              fi;
            od;
          fi;
          #Whenever we make a substitution, we have to go back one level more
          #than expected, because of our policy of looking ahead for
          #substitutions that reduce the length by 2.
          if i>0 then level:=i-1; else level:=i; fi;
          gct := gpref[level+1];
          donesub := true;
        elif newdiff>0 and level<Length(w) then
          #See if there is a substitution reducing length by 2.
          gen2 := w[level+1];
          t := table[newdiff][ng1*gen2];
          if t=identity then
            #Make substitution  reducing length of word by 2
            SubstitutedListFSA(w,level,level+1,[]);
            i := level-1;
            if not deqi then
              subvert := gptr[diffct];
  	      dosub := true;
              while dosub do
                w[i] := subvert.gen;
                i := i-1;
                if IsBound(subvert.backptr) then
  	          subvert := subvert.backptr;
                else
                  dosub := false;
                fi;
              od;
            fi;
            if i>0 then level:=i-1; else level:=i; fi;
            gct := gpref[level+1];
            donesub := true;
          fi;
        fi;

        if not donesub then
          #Now we loop over the generator that is a candidate for
          #substitution at this point.
          for gen2 in [1..ngens] do
            g2ltg1 := gen2 < gen1;
            newdiff := table[diff][ng1*(gen1-1)+gen2];
            if donesub then
              donesub := true;
              #i.e. do nothing - we really want to break from the for loop here.
            elif newdiff=identity then
              if deqi then #only occurs when gen2 and gen1 are equal in group
                if g2ltg1 then
                  w[level] := gen2;
                  if level>1 then level:=level-2; else level:=level-1; fi;
                  gct := gpref[level+1];
                  donesub := true;
                fi;
              elif gptr[diffct].sublen>0 then
                #Make a substitution by a string of equal length.
                w[level] := gen2;
                i := level-1;
                subvert := gptr[diffct];
    	        dosub := true;
                while dosub do
                  w[i] := subvert.gen;
                  i := i-1;
                  if IsBound(subvert.backptr) then
    	            subvert := subvert.backptr;
                  else
                    dosub := false;
                  fi;
                od;
                if i>0 then level:=i-1; else level:=i; fi;
                gct := gpref[level+1];
                donesub := true;
              fi;
            elif newdiff>0 then
              if cf[newdiff] then
                #We have this word difference stored already, but we will check
                #to see if the current string precedes the existing one.
                i := gpref[level];
                repeat
                  i := i+1;
                  subvert := gptr[i];
                until subvert.diffno=newdiff;
                olen := subvert.sublen;
                if deqi then 
                  if g2ltg1 then nlen:=1; else nlen:= -1; fi;
                else
                  l := gptr[diffct].sublen;
                  if l>0 then nlen:=l+1; else nlen:=l-1; fi;
                fi;
                if nlen > olen then # new string is better than existing one
                  subvert.gen := gen2;
                  subvert.sublen := nlen;
                  if deqi then Unbind(subvert.backptr);
                  else subvert.backptr := gptr[diffct];
                  fi;
                fi;
              else
               # this is a new word-difference at this level, so
               # we define a new vertex.
                gct := gct+1;
                gptr[gct] := rec();
                if deqi then 
                  if g2ltg1 then nlen:=1; else nlen:= -1; fi;
                else
                  l := gptr[diffct].sublen;
                  if l>0 then nlen:=l+1; else nlen:=l-1; fi;
                fi;
                subvert := gptr[gct];
                subvert.gen := gen2;
                subvert.diffno := newdiff;
                subvert.sublen := nlen;
                if not deqi then subvert.backptr := gptr[diffct]; fi;
                cf[newdiff] := true;
              fi;
            fi;
          od; # End of loop over gen2

          if not donesub then
            #Go on to next word-difference from the previous level
            if diff=identity then
              if level=1 then
                donediffs := true;
              else
                diffct := gpref[level-1] + 1;
              fi;
            else
              diffct := diffct+1;
            fi;
            if not donesub and not donediffs then
              if diffct > gpref[level] then
                donediffs := true;
              else
                diff := gptr[diffct].diffno;
              fi;
            fi;
          fi;
        fi;
      od; #end of loop over word-differences at previous level

      level := level+1;
      gpref[level] := gct;
    od;
    return w;
end;

#############################################################################
##
#F  ReduceWordRWS(<rws>,<w>) . . . . reduces a word using rewriting-system
##
##  ReduceWordRWS reduces the word <w>, using the rewriting-system <rws>.
##  <w> can be given either as a list of integers (internal format) or as
##  a word in the generators of the underlying group or monoid.
##  Either the reduction FSA, or one of the word-difference automata (in the
##  automatic group case) must be defined for <rws>.
##  In the latter case, the separate function ReduceWordWD is called.
##
##  Public function.
ReduceWordRWS := function ( rws, w )
    local fsa, pos, label, state, history, eqn, sublen, table, ng,  i, word;
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not an KBMAG rewriting system.");
    fi;
    if not IsAvailableReductionRWS(rws) then
       Error(
   "Reduction algorithm unavailable. Run KnuthBendix or AutomaticStructure.");
    fi;
    if not IsList(w) and not IsWord(w) then
       Error("Second argument is not a word or list.");
    fi;
    ng := Length(rws!.alphabet);
    if IsWord(w) then
       word :=true;
       w:=ShallowCopy(WordToListRWS(w,rws!.alphabet));
    else word := false;
    fi;
    if IsBound(rws!.warningOn) and rws!.warningOn then
      if IsBound(rws!.KBRun) and rws!.KBRun then
        Print(
 "#WARNING: system is not confluent, so reductions may not be to normal form.\n"
      );
      else
        Print(
 "#WARNING: word-difference reduction machine is not proven correct,\n",
 "          so reductions may not be to normal form.\n");
      fi;
      rws!.warningOn:=false;
           # only give the warning once, or it could become irritating!
    fi;
    if IsBound(rws!.diff2) then
     # automatic group case
       w := ReduceWordWD(rws!.diff2,w);
    elif IsBound(rws!.diff1c) then
     # automatic group case
       w := ReduceWordWD(rws!.diff1c,w);
    elif IsBound(rws!.diff1) then
     # automatic group case
       w := ReduceWordWD(rws!.diff1,w);
    elif IsBound(rws!.reductionFSA)  then
       fsa := rws!.reductionFSA;
       if not IsInitializedFSA(fsa) or IsDeterministicFSA(fsa)=false  then
          Error("First argument does not have initialized dfa as field.");
       fi;
   
       state := fsa.initial[1];
       pos := 1;
       history:= [];
       history[1] := state; # history[i] = state before reading i-th symbol.
       table := DenseDTableFSA(fsa);
       while pos <= Length(w) do
         state := table[state][w[pos]];
         if state>0 then
           pos := pos+1;
           history[pos] := state;
         else
           state := -state;
           eqn := rws!.equations[state];
           sublen := Length(eqn[1]);
           SubstitutedListFSA(w,pos-sublen+1,pos,eqn[2]);
           pos := pos-sublen+1;
           state := history[pos];
         fi;
       od;
    else
       Error("First argument does not have initialized dfa as field.");
    fi;

    if not rws!.hasOne and Length(w)=0 then
      Error("The empty word does not represent an element of a semigroup.");
    fi;
    if word then
       w := ListToWordRWS(w,rws!.alphabet);
    fi;
    return w;
end;
      
#############################################################################
##
#F  SizeRWS(<rws>>) . . . . . number of reduced words in a rewriting system
##
##  This merely calls the corresponding FSA function.
##
##  Public function.
SizeRWS := function ( rws )
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not a rewriting system.");
    fi;
    if not IsAvailableSizeRWS(rws) then
       Error(
   "Size algorithm unavailable. Run KnuthBendix or AutomaticStructure.");
    fi;
    if IsBound(rws!.warningOn) and rws!.warningOn then
      if rws!.KBRun then
        Print(
 "#WARNING: system is not confluent, so size returned may not be correct.\n"
      );
      else
        Print(
 "#WARNING: word-difference reduction machine is not proven correct,\n",
 "          so size returned may not be correct.\n");
      fi;
      rws!.warningOn:=false;
           # only give the warning once, or it could become irritating!
    fi;
    if IsBound(rws!.wa) then
     # automatic group case
      return LSizeDFA( rws!.wa );
    fi;
    return LSizeDFA( rws!.reductionFSA );
end;

#############################################################################
##
#F  EnumerateRWS(<rws>, <min>, <max>) . . . enumerate reduced words in a rws
##
##  This merely calls the corresponding FSA function.
##  Words are converted to words in generators of underlying group or monoid
##  before returning.
##
##  Public function.
EnumerateRWS := function ( rws, min, max )
    local ret, x, i;
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not a rewriting system.");
    fi;
    if not IsAvailableSizeRWS(rws) then
       Error(
   "Enumeration algorithm unavailable. Run KnuthBendix or AutomaticStructure.");
    fi;
    if IsBound(rws!.wa) then
     # automatic group case
      ret := LEnumerateDFA( rws!.wa,min,max );
    else
      ret := LEnumerateDFA( rws!.reductionFSA,min,max );
    fi;
    return ret;
end;

#############################################################################
##
#F  SortEnumerateRWS(<rws>, <min>, <max>)  . . enumerate reduced words and sort
##
##  This merely calls the corresponding FSA function.
##  Words are converted to words in generators of underlying group or monoid
##  before returning.
##
##  Public function.
SortEnumerateRWS := function ( rws, min, max )
    local ret, x, i;
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not a rewriting system.");
    fi;
    if not IsAvailableSizeRWS(rws) then
       Error(
   "Enumeration algorithm unavailable. Run KnuthBendix or AutomaticStructure.");
    fi;
    if IsBound(rws!.wa) then
     # automatic group case
      ret := SortLEnumerateDFA( rws!.wa,min,max );
    else
      ret := SortLEnumerateDFA( rws!.reductionFSA,min,max );
    fi;
    return ret;
end;

#############################################################################
##
#F  SizeEnumerateRWS(<rws>, <min>, <max>)  . . . . number of reduced words 
##
##  This merely calls the corresponding FSA function.
##
##  Public function.
SizeEnumerateRWS := function ( rws, min, max )
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not a rewriting system.");
    fi;
    if not IsAvailableSizeRWS(rws) then
       Error(
   "Enumeration algorithm unavailable. Run KnuthBendix or AutomaticStructure.");
    fi;
    if IsBound(rws!.wa) then
     # automatic group case
      return SizeLEnumerateDFA( rws!.wa,min,max );
    fi;
    return SizeLEnumerateDFA( rws!.reductionFSA,min,max );
end;

#############################################################################
##
#F  OrderRWS(<rws>,<w>) . . . . order of word <w> in group or monoid
##
##  OrderRWS tries to calculate the order of the element represented by the
##  word <w> in the group  or monoid of the rewriting system <rws>.
##  Either the word-acceptor (automatic group case) or the reduction FSA
##  must be defined.
##  It could conceivably not terminate, but I have never known that happen!
##
##  Public function.
OrderRWS := function ( rws, w )
    local i, ng, fsa, prefix, preford, pt, t, targets, sufford, tracing, x,
          z, cr, l;
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not an KBMAG rewriting system.");
    fi;
    if not rws!.hasOne then
       Error("Order algorithm is only possible in a monoid or group");
    fi;
    if not IsAvailableReductionRWS(rws) then
       Error(
   "Reduction algorithm unavailable. Run KnuthBendix or AutomaticStructure.");
    fi;
    if not IsList(w) and not IsWord(w) then
       Error("Second argument is not a word or list.");
    fi;
    ng := Length(rws!.alphabet);
    if IsWord(w) then
       w:=ShallowCopy(WordToListRWS(w,rws!.alphabet));
    fi;
    w := ReduceWordRWS(rws, w);
    if Length(w)=0 then
       return 1;
    fi;
    if IsBound(rws!.wa) then
    # Automatic group case - use word-acceptor
      fsa := rws!.wa;
    else
      fsa := rws!.reductionFSA;
    fi;
    prefix := w;
    preford := 1;
    while true do
      #Check prefix is cyclically reduced
      cr := true;
      while cr do
        l := Length(prefix);
        if l>1 and rws!.invAlphabet[prefix[1]]=prefix[l] then
          #remove first and last terms of prefix, but we must also
          #perform the same conjugation operation on w.
          w:=Concatenation([prefix[l]],w,[prefix[1]]);
          w := ReduceWordRWS(rws,w);
          prefix := prefix{[2..l-1]};
        else
          cr := false;
        fi;
      od;
      #First see if all powers of prefix are reduced - if so, then a
      #state of fsa will eventually repeat on tracing w^n, and w will have
      #infinite order.
      pt := WordTargetDFA(fsa, prefix);
      t := pt;
      targets := Set([t]);
      tracing:=true;
      while tracing do
        for x in prefix do
          t := TargetDFA(fsa, x, t);
          if t<=0 then
            break;
          fi;
        od; #for x in prefix
        if t<=0 then
          tracing := false;
        elif t in targets then
          return infinity;
        else
          AddSet(targets,t);
        fi;
      od; # while tracing
      #not all powers of prefix are reduced, so we need to replace prefix
      #by reduced word for a higher power.
      sufford := 0;
      tracing := true;
      t := pt;
      while tracing do
        sufford := sufford+1;
        for x in w do
          t := TargetDFA(fsa, x, t);
          if t<=0 then
            tracing := false;
            for i in [1..sufford] do
              prefix := Concatenation(prefix,w);
            od;
            prefix := ReduceWordRWS(rws, prefix);
            preford := preford + sufford;
            if Length(prefix)=0 then
              return preford;
            fi;
            #To improve chance of proving order infinite, we replace
            #el and w by cyclic conjugates.
            z := rws!.invAlphabet[prefix[1]];
            if  z <> false then
              w:=Concatenation([z],w,[prefix[1]]);
              w := ReduceWordRWS(rws,w);
              prefix:=Concatenation([z],prefix,[prefix[1]]);
              prefix := ReduceWordRWS(rws,prefix);
            fi;
            break;
          fi;
        od; #for x in w
      od; #while tracing
    od; #while true
end;

#############################################################################
##
#F  AddOriginalEqnsRWS(<rws>).
##           . . . . add original equations to rws after a call of KBRWS.
##
##  This appends the original equations to the list of equations, after a
##  call of KBRWS. Useful for a re-check, if the external program may have
##  deleted some equations.
##  After this function, rewriting is no longer possible.
##  Public function.
AddOriginalEqnsRWS := function ( rws )
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not a rewriting system.");
    fi;
    Unbind(rws!.reductionFSA);
    Unbind(rws!.isConfluent);
    if IsBound(rws!.originalEquations) then
      Append(rws!.equations,rws!.originalEquations);
    fi;
end;

#############################################################################
##
#F  KBRWS(<rws>)  . . . . call external Knuth-Bendix program on rws
##
##  This returns true if a confluent rewriting system results - otherwise
##  false. In the latter case, words can still be rewritten with respect to
##  the current equations, but they are not guaranteed to reduce to the unique
##  representative of the group element.
##  An error message results if the external program aborts without outputting.
##  Public function.
KBRWS := function ( rws )
    local O, callstring;
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("First argument is not a rewriting system.");
    fi;
    if IsConfluentRWS(rws) then
       Print("#The rewriting system is already confluent.\n");
       Print("#Call - ResetRWS(<rws>) to restart.\n");
       return fail;
    fi;
    #If we have already run KBRWS then the original equations will
    #have been kept and should be re-inserted.
    AddOriginalEqnsRWS(rws);
    #Keep the original equations, in case we want them again.
    if not IsBound(rws!.originalEquations) then
      rws!.originalEquations := StructuralCopy(rws!.equations);
    fi;
    WriteRWS(rws,_KBTmpFileName);
    callstring := Concatenation(Filename(_KBExtDir,"kbprog")," ",_KBTmpFileName);
    Info(InfoRWS,1,"Calling external Knuth-Bendix program.");
    Info(InfoRWS,3,"  ", callstring);
    Exec(callstring);
    UpdateRWS(rws,_KBTmpFileName,true);
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
    Info(InfoRWS,1,"External Knuth-Bendix program complete.");
    
    if rws!.isConfluent then
      O := rws!.options;
      if IsBound(O.maxstoredlen) or IsBound(O.maxoplen) then
        Print(
 "#WARNING: Because of the control parameters you set, the system may\n");
        Print(
 "#         not be confluent. Unbind the parameters and re-run KnuthBendix\n");
        Print(
 "#         to check!\n");
        rws!.isConfluent:=false;
      fi;
    fi;
    if rws!.isConfluent then
      Info(InfoRWS,1,"System computed is confluent.");
      rws!.isAvailableNormalForm := true;
      rws!.warningOn := false;
    else
      Info(InfoRWS,1,"System computed is NOT confluent.");
      rws!.isAvailableNormalForm := false;
      rws!.warningOn := true;
    fi;
    rws!.KBRun := true;
    rws!.isAvailableReduction := true;
    rws!.isAvailableSize := true;
    return rws!.isConfluent;
end;

#############################################################################
##
#F  AutRWS(<rws>, [<large>], [<filestore>], [<diff1>]) 
##                      . . . . call external automatic group program on rws
##
##  This returns true if the automatic group programs succeed - otherwise
##  false.
##  The optional parameters are all boolean, and false by default.
##  <large> means problem is large - the external programs use bigger tables.
##  <filestore> means external programs use less core memory and more external
##         files - they run a little slower.
##  <diff1> is necessary on some examples - see manual for information.
##  Public function.
AutRWS := function ( arg )
    local  narg, rws, large, filestore, diff1, callstring, optstring;
    narg := Number(arg);
    if narg<1  or  not IsKBMAGRewritingSystemRep(arg[1]) then
       Error("First argument is not a rewriting system.");
    fi;
    rws := arg[1];
    if not IsGroupRWS(rws) then
      Error("AutRWS can only be applied when all generators have inverses.");
    fi;
    if IsBound(rws!.KBRun) and rws!.KBRun then
      Print("Knuth-Bendix has already been run on this rewriting system.\n");
      Print("Call - ResetRWS( <rws> ) before proceeding.\n");
      return;
    fi;
    if not rws!.ordering = "shortlex" then
       Error("AutRWS only works for shortlex ordering");
    fi;
    large:=false; filestore:=false; diff1:=false;
    if narg>=2 and arg[2]=true then large:=true; fi;
    if narg>=3 and arg[3]=true then filestore:=true; fi;
    if narg>=4 and arg[4]=true then diff1:=true; fi;
    WriteRWS(rws,_KBTmpFileName);
    callstring := Filename(_KBExtDir,"autgroup");
    optstring := " ";
    if large then optstring := Concatenation(optstring," -l "); fi;
    if filestore then optstring := Concatenation(optstring," -f "); fi;
    if diff1 then optstring := Concatenation(optstring," -d "); fi;
    if InfoLevel(InfoRWS)=0 then
                      optstring := Concatenation(optstring," -s "); fi;
    if InfoLevel(InfoRWS)>1 then
                      optstring := Concatenation(optstring," -v "); fi;
    if InfoLevel(InfoRWS)>2 then
                      optstring := Concatenation(optstring," -vv "); fi;
    callstring := Concatenation(callstring,optstring,_KBTmpFileName);
    Info(InfoRWS,1,"Calling external automatic groups program.");
    Info(InfoRWS,3,"  ", callstring);
    Exec(callstring);
    callstring := Filename(_KBExtDir,"gpminkb");
    optstring := " ";
    if InfoLevel(InfoRWS)=0 then
                      optstring := Concatenation(optstring," -s "); fi;
    if InfoLevel(InfoRWS)>1 then
                      optstring := Concatenation(optstring," -v "); fi;
    if InfoLevel(InfoRWS)>2 then
                      optstring := Concatenation(optstring," -vv "); fi;
    callstring := Concatenation(callstring,optstring,_KBTmpFileName);
    if READ(Concatenation(_KBTmpFileName,".success")) then
     Info(InfoRWS,1,
         "Computation was successful - automatic structure computed.");
      Info(InfoRWS,3,"  ", callstring);
      Exec(callstring);
      UpdateRWS(rws,_KBTmpFileName,false);
      Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
      rws!.isAvailableNormalForm := true;
      rws!.isAvailableReduction := true;
      rws!.isAvailableSize := true;
      rws!.warningOn := false;
      return true;
    else
      Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
      Info(InfoRWS,1,"Computation was not successful.");
      return false;
    fi;
end;

#############################################################################
## The remaining functions in the file enable the user to to call the
## different parts of the automata program individually.
## They are experimental and less well supported than KBRUN and AutRWS.
#############################################################################
##
#F  KBWD(<rws>, [<haltingfactor>], [<large>]) 
##                . . . . call external Knuth-Bendix program with -wd on rws
##
##  Runs KBRUN, computes word differences, and sets the diff1 and diff2 flags 
##  of rws to be the appropriate difference machines.
##  An error message results if the external program aborts without outputting.
##  Public function.
KBWD := function ( arg )
    local narg,rws, haltingfactor,large, callstring, optstring, mg, IdWord;
    narg := Number(arg);
    if narg<1  or  not IsKBMAGRewritingSystemRep(arg[1]) then
       Error("First argument is not a rewriting system.");
    fi;
    large:=false; haltingfactor:=100;
    rws := arg[1];
    if not IsGroupRWS(rws) then
      Error("KBWD can only be applied when all generators have inverses.");
    fi;
    if IsBound(rws!.KBRun) and rws!.KBRun then
      Print("Knuth-Bendix has already been run on this rewriting system.\n");
      Print("Call - ResetRWS( <rws> ) before proceeding.\n");
    fi;
    if narg>1 then haltingfactor := arg[2]; fi;
    if narg>2 then large := arg[3]; fi;
    WriteRWS(rws,_KBTmpFileName);
    callstring := Concatenation(Filename(_KBExtDir,"kbprog")," -wd -hf ");
    callstring := Concatenation(callstring,String(haltingfactor)," ");
    optstring := "";
    if large then 
       optstring := Concatenation(optstring," -cn 0 -me 262144 -t 500 "); 
    fi;
    if InfoLevel(InfoRWS)=0 then
                      optstring := Concatenation(optstring," -silent "); fi;
    if InfoLevel(InfoRWS)>1 then
                      optstring := Concatenation(optstring," -v "); fi;
    if InfoLevel(InfoRWS)>2 then
                      optstring := Concatenation(optstring," -vv "); fi;
    callstring := Concatenation(callstring,optstring,_KBTmpFileName);
    Info(InfoRWS,1,
        "Calling external Knuth-Bendix program for word-differences.");
    Info(InfoRWS,3,"  ", callstring);
    Exec(callstring);
    Info(InfoRWS,1,"External Knuth-Bendix program complete.");

    StoreNamesRWS(rws,_KBTmpFileName);
    if not READ(Concatenation(_KBTmpFileName,".diff1")) then
       Error("Could not open diff1 file");
    fi;
    if not READ(Concatenation(_KBTmpFileName,".diff2")) then
       Error("Could not open diff2 file");
    fi;
    if not READ(Concatenation(_KBTmpFileName,".kbprog.ec")) then
       Error("Could not open exit-code file");
    fi;
    rws!.diff1 := _RWS.diff1;
    rws!.diff2 := _RWS.diff2;
    RedefineNamesRWS(rws,_KBTmpFileName);

    InitializeFSA(rws!.diff1);
    rws!.diff1.alphabet.base.printingStrings:=List(rws!.alphabet,x->String(x));
    rws!.diff1.states.printingStrings:=List(rws!.alphabet,x->String(x));

    DenseDTableFSA(rws!.diff1);
    rws!.diff1.table.format:="dense deterministic";
    rws!.diff1.table.transitions:=rws!.diff1.denseDTable;
    Unbind(rws!.diff1.sparseTable);
    InitializeFSA(rws!.diff2);
    rws!.diff2.alphabet.base.printingStrings:=List(rws!.alphabet,x->String(x));
    rws!.diff2.states.printingStrings:=List(rws!.alphabet,x->String(x));
    DenseDTableFSA(rws!.diff2);
    rws!.diff2.table.format:="dense deterministic";
    rws!.diff2.table.transitions:=rws!.diff2.denseDTable;
    Unbind(rws!.diff2.sparseTable);
    if _ExitCode=2 then
      Print(
  "#WARNING: Knuth-Bendix program terminated with halting factor condition\n");
      Print("         not satisfied.\n");
      return false;
    fi;
    rws!.isAvailableReduction := true;
    rws!.warningOn := true;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
    return true;
end;

#############################################################################
##
#F  GpWA(<rws>, [<large>], [<filestore>], [<diff1>]) 
##                      . . . . call external word-acceptor program on rws
##
##  This assumes that KBWD has already been called on rws
##  Public function.
GpWA := function ( arg )
    local  narg, rws, large, filestore, diff1, callstring, optstring;
    narg := Number(arg);
    if narg<1  or  not IsKBMAGRewritingSystemRep(arg[1]) then
       Error("First argument is not a rewriting system.");
    fi;
    rws := arg[1];
    if not rws!.ordering = "shortlex"  then
       Error("Ordering must be shortlex for external word-acceptor program");
    fi;
    large:=false; filestore:=false; diff1:=false;
    if narg>=2 and arg[2]=true then large:=true; fi;
    if narg>=3 and arg[3]=true then filestore:=true; fi;
    if narg>=4 and arg[4]=true then diff1:=true; fi;
    if diff1 then
      WriteFSA(
          rws!.diff1,"_RWS.diff1",Concatenation(_KBTmpFileName,".diff1"),";");
    else
      WriteFSA(
          rws!.diff2,"_RWS.diff2",Concatenation(_KBTmpFileName,".diff2"),";");
    fi;
    callstring := Filename(_KBExtDir,"gpwa");
    optstring := " ";
    if large then optstring := Concatenation(optstring," -l "); fi;
    if filestore then optstring := Concatenation(optstring," -f "); fi;
    if diff1 then optstring := Concatenation(optstring," -d "); fi;
    if InfoLevel(InfoRWS)=0 then
      optstring := Concatenation(optstring," -silent ");
    fi;
    if InfoLevel(InfoRWS)>1 then
      optstring := Concatenation(optstring," -v ");
    fi;
    if InfoLevel(InfoRWS)>2 then
      optstring := Concatenation(optstring," -vv ");
    fi;
    callstring := Concatenation(callstring,optstring,_KBTmpFileName);
    Info(InfoRWS,1,"Calling external word-acceptor program.");
    Info(InfoRWS,3,"  ", callstring);
    Exec(callstring);
    Info(InfoRWS,1,"External word-acceptor program complete.");

    StoreNamesRWS(rws,_KBTmpFileName);
    if not READ(Concatenation(_KBTmpFileName,".wa")) then
       Error("Could not open wa file");
    fi;
    rws!.wa := _RWS.wa;
    RedefineNamesRWS(rws,_KBTmpFileName);

    InitializeFSA(rws!.wa);
    rws!.wa.alphabet.printingStrings:=List(rws!.alphabet,x->String(x));
    rws!.isAvailableSize := true;
    rws!.warningOn := true;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
end;

#############################################################################
##
#F  GpGenMult(<rws>, [<large>], [<filestore>], [<diff1>] ) 
##                 . . . . call external generalised multiplier program on rws
##
##  This assumes that KBWD and GpWA have already been called on rws
##  Public function.
GpGenMult := function ( arg )
    local  narg, rws, large, filestore, diff1, callstring, optstring;
    narg := Number(arg);
    if narg<1  or  not IsKBMAGRewritingSystemRep(arg[1]) then
       Error("First argument is not a rewriting system.");
    fi;
    rws := arg[1];
    large:=false; filestore:=false; diff1:=false;
    if narg>=2 and arg[2]=true then large:=true; fi;
    if narg>=3 and arg[3]=true then filestore:=true; fi;
    if diff1 then
      WriteFSA(
      rws!.("diff1)"),"_RWS.diff1",Concatenation(_KBTmpFileName,".diff1"),";");
    fi;
    WriteFSA(
        rws!.wa,"_RWS.wa",Concatenation(_KBTmpFileName,".wa"),";");
    WriteFSA(
        rws!.diff2,"_RWS.diff2",Concatenation(_KBTmpFileName,".diff2"),";");
    callstring := Filename(_KBExtDir,"gpgenmult");
    optstring := " ";
    if large then optstring := Concatenation(optstring," -l "); fi;
    if filestore then optstring := Concatenation(optstring," -f "); fi;
    if diff1 then optstring := Concatenation(optstring," -c "); fi;
    if InfoLevel(InfoRWS)=0 then
                      optstring := Concatenation(optstring," -silent "); fi;
    if InfoLevel(InfoRWS)>1 then
                      optstring := Concatenation(optstring," -v "); fi;
    if InfoLevel(InfoRWS)>2 then
                      optstring := Concatenation(optstring," -vv "); fi;
    callstring := Concatenation(callstring,optstring,_KBTmpFileName);
    Info(InfoRWS,1,"Calling external generalised multiplier program.");
    Info(InfoRWS,3,"  ", callstring);
    Exec(callstring);
    Info(InfoRWS,1,"External generalised-multiplier program complete.");

    StoreNamesRWS(rws,_KBTmpFileName);
    if not READ(Concatenation(_KBTmpFileName,".gm")) then
       if diff1 then
         if not READ(Concatenation(_KBTmpFileName,".diff1")) then
           Error("Cannot read modified diff1 file.");
         fi;
         rws!.diff1 := _RWS.diff1;
         RedefineNamesRWS(rws,_KBTmpFileName);
         InitializeFSA(rws!.diff1);
         rws!.diff1.alphabet.base.printingStrings:=
                                  List(rws!.alphabet,x->String(x));
         rws!.diff1.states.printingStrings:=List(rws!.alphabet,x->String(x));
         DenseDTableFSA(rws!.diff1);
         rws!.diff1.table.format:="dense deterministic";
         rws!.diff1.table.transitions:=rws!.diff1.denseDTable;
         Unbind(rws!.diff1.sparseTable);
       fi;
       Print("Could not open gm file - try re-running GpWA.\n");
       Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
       return false;
    fi;
    rws!.gm := _RWS.gm;
    RedefineNamesRWS(rws,_KBTmpFileName);

    InitializeFSA(rws!.gm);
    rws!.gm.alphabet.base.printingStrings:=List(rws!.alphabet,x->String(x));
    rws!.gm.states.labels.printingStrings:=List(rws!.alphabet,x->String(x));
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
    return true;
end;

#############################################################################
##
#F  GpCheckMult(<rws>, [<large>], [<filestore>] ) 
##                 . . . . call external generalised multiplier program on rws
##
##  This assumes that KBWD, GpWA and GpGenMult have already been called on rws
##  Public function.
GpCheckMult := function ( arg )
    local  narg, rws, large, filestore, callstring, optstring;
    narg := Number(arg);
    if narg<1  or  not IsKBMAGRewritingSystemRep(arg[1]) then
       Error("First argument is not a rewriting system.");
    fi;
    rws := arg[1];
    large:=false; filestore:=false;
    if narg>=2 and arg[2]=true then large:=true; fi;
    if narg>=3 and arg[3]=true then filestore:=true; fi;
    WriteRWS(rws,_KBTmpFileName);
    WriteFSA(
        rws!.diff2,"_RWS.diff2",Concatenation(_KBTmpFileName,".diff2"),";");
    WriteFSA(
        rws!.gm,"_RWS.gm",Concatenation(_KBTmpFileName,".gm"),";");
    WriteFSA(
        rws!.wa,"_RWS.wa",Concatenation(_KBTmpFileName,".wa"),";");
    callstring := Filename(_KBExtDir,"gpcheckmult");
    optstring := " ";
    if large then optstring := Concatenation(optstring," -l "); fi;
    if filestore then optstring := Concatenation(optstring," -f "); fi;
    if rws!.ordering="wtlex" then
       optstring := Concatenation(optstring," -wtlex ");
    fi;
    if IsBound(rws!.options.outputWords) and rws!.options.outputWords then
      optstring := Concatenation(optstring," -ow ");
    fi; 
    if InfoLevel(InfoRWS)=0 then
                      optstring := Concatenation(optstring," -silent "); fi;
    if InfoLevel(InfoRWS)>1 then
                      optstring := Concatenation(optstring," -v "); fi;
    if InfoLevel(InfoRWS)>2 then
                      optstring := Concatenation(optstring," -vv "); fi;
    callstring := Concatenation(callstring,optstring,_KBTmpFileName);
    Info(InfoRWS,1,"Calling external multiplier checking program.");
    Info(InfoRWS,3,"  ", callstring);
    Exec(callstring);
    Info(InfoRWS,1,"External multiplier checking program complete.");
    if not READ(Concatenation(_KBTmpFileName,".cm.ec")) then
       Error("Could not open exit-code file");
    fi;
    if _ExitCode=2 then
      StoreNamesRWS(rws,_KBTmpFileName);
      if IsBound(rws!.options.outputWords) and rws!.options.outputWords then
        Print(
 "#Validity test on generalised multiplier failed. Reading offending words.\n");
        if not READ(Concatenation(_KBTmpFileName,".wg")) then
          Error("Could not open wg file");
        fi;
        rws!.wg := _RWS.wg;
        RedefineNamesRWS(rws,_KBTmpFileName);
        Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
        return false;
      fi;
      Print(
       "#Validity test on generalised multiplier failed. Re-run GpGenMult.\n");
      if not READ(Concatenation(_KBTmpFileName,".diff2")) then
         Error("Could not open diff2 file");
      fi;
      rws!.diff2 := _RWS.diff2;
      RedefineNamesRWS(rws,_KBTmpFileName);
      InitializeFSA(rws!.diff2);
      rws!.diff2.alphabet.base.printingStrings:=List(rws!.alphabet,x->String(x));
      rws!.diff2.states.printingStrings:=List(rws!.alphabet,x->String(x));
      DenseDTableFSA(rws!.diff2);
      rws!.diff2.table.format:="dense deterministic";
      rws!.diff2.table.transitions:=rws!.diff2.denseDTable;
      Unbind(rws!.diff2.sparseTable);
      Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
      return false;
    fi;
    Print(
       "#Validity test on generalised multiplier passed.\n");
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
    return true;
end;

#############################################################################
##
#F  ElimGenRWS(<rws>, <gen>, <w> ) 
##                 . . . . eliminate a generator in an rws
##
##  This is for the case when a generator in an rws reduces to a word of
##  length greater than one in the ordering being used.
##  The generator is marked as having no inverse (to prevent the inverse
##  relations being processed), and in all other relations in the rws it is
##  eliminated by substituting w for it.
##  Public function.
ElimGenRWS := function ( rws, gen, w )
    local rwsc, gens, genno, wl, ig, igenno, eqn, i, side;
    rwsc := ShallowCopy(rws);
    rwsc!.invAlphabet := ShallowCopy(rws!.invAlphabet);
    rwsc!.equations := StructuralCopy(rws!.equations);
    gens := rwsc!.alphabet;
    genno := Position(gens,gen);
    if genno=fail then
       Error("Invalid generator");
    fi;
    wl := ShallowCopy(WordToListRWS(w,rwsc!.alphabet));
    eqn:=[];
    ig := rwsc!.invAlphabet;
    igenno := ig[genno];
    if igenno <> 0 then
      #Add relations that say that these two generators are mutually
      #inverse.
      if genno=igenno then
        ig[genno] := 0;
        eqn[1]:=Concatenation(wl,wl); eqn[2]:=[];
        Add(rwsc!.equations,eqn);
      else
        ig[genno] := 0;
        ig[igenno] := 0;
        eqn[1]:=Concatenation([igenno],wl); eqn[2]:=[];
        Add(rwsc!.equations,eqn);
        eqn:=[];
        eqn[1]:=Concatenation(wl,[igenno]); eqn[2]:=[];
        Add(rwsc!.equations,eqn);
      fi;
    fi;
    #Now do the substitutions in the other equations
    for eqn in rwsc!.equations do
      i:=1;
      while i<=Length(eqn[1]) do
        if eqn[1][i]=genno then
          SubstitutedListFSA(eqn[1],i,i,wl);
        fi;
        i := i+1;
      od;
      i:=1;
      while i<=Length(eqn[2]) do
        if eqn[2][i]=genno then
          SubstitutedListFSA(eqn[2],i,i,wl);
        fi;
        i := i+1;
      od;
      #Now do free reduction
      for side in [eqn[1],eqn[2]] do
        i:=1;
        while i < Length(side) do
          if side[i+1]=ig[side[i]] then
            SubstitutedListFSA(side,i,i+1,[]);
            if i>1 then i:=i-1; fi;
          else i:=i+1;
          fi;
        od;
      od;
    od;
    #finally eliminate any repetitions
    rwsc!.equations := Set(rwsc!.equations);
    for eqn in rwsc!.equations do
      if eqn[1]=eqn[2] then
        RemoveSet(rwsc!.equations,eqn);
      fi;
    od;
    return rwsc;
end;

#############################################################################
##
#F  GpAxioms(<rws>, [<large>], [<filestore>] ) 
##                 . . . . call external axiom checking program on rws
##
##  This assumes that KBWD, GpWA, GpGenMult and GpCheckMult have already
##  been called on rws
##  Public function.
GpAxioms := function ( arg )
    local  narg, rws, large, filestore, callstring, optstring;
    narg := Number(arg);
    if narg<1  or  not IsKBMAGRewritingSystemRep(arg[1]) then
       Error("First argument is not a rewriting system.");
    fi;
    rws := arg[1];
    large:=false; filestore:=false;
    if narg>=2 and arg[2]=true then large:=true; fi;
    if narg>=3 and arg[3]=true then filestore:=true; fi;
    WriteRWS(rws,_KBTmpFileName);
    WriteFSA(
          rws!.gm,"_RWS.gm",Concatenation(_KBTmpFileName,".gm"),";");
    callstring := Filename(_KBExtDir,"gpaxioms");
    optstring := " ";
    if IsBound(rws!.sub) then
      WriteRWS(rws!.sub,Concatenation(_KBTmpFileName,"_x"));
      optstring := Concatenation(optstring," -x ");
    fi;
    if large then optstring := Concatenation(optstring," -l "); fi;
    if filestore then optstring := Concatenation(optstring," -f "); fi;
    #gpaxioms no longer needs a -wtlex flag, so omit following 3 lines.
    #if rws!.ordering="wtlex" then
    #   optstring := Concatenation(optstring," -wtlex ");
    #fi;
    if InfoLevel(InfoRWS)=0 then
                      optstring := Concatenation(optstring," -silent "); fi;
    if InfoLevel(InfoRWS)>1 then
                      optstring := Concatenation(optstring," -v "); fi;
    if InfoLevel(InfoRWS)>2 then
                      optstring := Concatenation(optstring," -vv "); fi;
    callstring := Concatenation(callstring,optstring,_KBTmpFileName);
    Info(InfoRWS,1,"Calling external axiom checking program.");
    Info(InfoRWS,3,"  ", callstring);
    Exec(callstring);
    Info(InfoRWS,1,"External axiom checking program complete.");
    if not READ(Concatenation(_KBTmpFileName,".axioms.ec")) then
       Error("Could not open exit-code file");
    fi;
    if _ExitCode=2 then
      Print(
       "#Axiom checking failed.\n");
      return false;
    fi;
    Print(
       "#Axiom checking succeeded.\n");
    rws!.warningOn:=false;
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
    return true;
end;

#############################################################################
##
#F  CommutativeRWS(<rws>) 
##                 . . . . add extra equations to an RWS to make commutative
##
##  This procedure simply adds relations to the rewriting system <rws> to
##  make each pair of generators commute. 
##  Public function.
CommutativeRWS := function(rws)
    local ng, i, j;
    if not IsKBMAGRewritingSystemRep(rws)  then
       Error("Argument is not an internal rewriting system.");
    fi;
    ng := Length(rws!.alphabet);
    for i in [1..ng] do for j in [1..i-1] do
      Add(rws!.equations,[[i,j],[j,i]]);
    od; od;
end;
