#############################################################################
##
#A  rwssub4.g                  GAP library                  Derek Holt
##
## Created 21/3/00. New to GAP4.
##
## This file contains GAP4 interface functions to the subgroup functionality
## of the KBMAG standalone package.
##
#V  _xg          external variable - a free group for a subgroup presentation
#V  _x_relators  external variable - relators for a subgroup presentations
_xg := FreeGroup(1);
_x_relators:=[];

#############################################################################
##
#F  SubgroupRWS(<rws>,<H>) . . . . . . . create a subgroup of an <rws>
##
##  <rws> should be a rewriting system and <H> a subgroup of G or a list
##  of generators of G defining a subgroup, where G = rws!.GpMonSgp.
##  G must be a group (i.e. all inverses defined) for this to work.
##
##  Public function.
SubgroupRWS := function ( rws, H )
  local G, invH, g, ng, ns, subrec, mnames, i, l, fam;

  if not IsGroupRWS(rws) then
     Error("SubgroupRWS only applies to rewriting systems from groups.");
  fi;
  G := rws!.GpMonSgp;
  if IsGroup(H) then
    H := GeneratorsOfGroup(H);
  fi;

  for g in H do if not g in G and not g in rws!.FreeGpMonSgp then
     Error ("Second argument of SubgroupRWS should define a subgroup.");
  fi; od;
  ## We want to store H as words in the word monoid.
  H := List(H,i->UnderlyingElement(i));
  H := List(H,i->rws!.ExtToInt(rws!.ExtIntCorr,i));
  ## and we need the inverses of these generators.
  invH:=[];
  for g in H do
    l := WordToListRWS(g,rws!.alphabet);
    l := List(Reversed(l),i->rws!.invAlphabet[i]);
    Add(invH,ListToWordRWS(l,rws!.alphabet));
  od;
  ng := Length(H);

  if IsBound(rws!.subgroups) then
    ns := rws!.numSubgroups+1;
    rws!.numSubgroups := ns;
  else
    rws!.subgroups := [];
    rws!.cosrws := [];
    rws!.subrws := [];
    ns :=  1;
    rws!.numSubgroups := ns;
  fi;
  rws!.subgroups[ns] := rec();
  rws!.cosrws[ns] := rec();
  subrec := rws!.subgroups[ns];
  subrec.GpMonSgp := rws!.GpMonSgp;
  subrec.FreeGpMonSgp := rws!.FreeGpMonSgp;
  subrec.ordering := rws!.ordering;
  mnames := [];
  subrec.generatingWords := [];
  subrec.invAlphabet := [];
  for i in [1..ng] do
    subrec.generatingWords[2*i-1] := H[i];
    subrec.generatingWords[2*i] := invH[i];
    mnames[2*i-1] := Concatenation("_x",String(i));
    mnames[2*i] := Concatenation("_X",String(i));
    subrec.invAlphabet[2*i-1] := 2*i;
    subrec.invAlphabet[2*i] := 2*i-1;
  od;
  subrec.equations:=[];
  subrec.options:=rec();
  subrec.WordMonoid := FreeMonoid(mnames);
  subrec.alphabet := GeneratorsOfMonoid(subrec.WordMonoid);

  fam := NewFamily("Family of Knuth-Bendix Rewriting systems",
                IsKnuthBendixRewritingSystem);
  subrec := Objectify(NewType(fam,
                IsMutable and IsKnuthBendixRewritingSystem
                and IsKBMAGRewritingSystemRep),
                subrec);
  rws!.cosrws[ns] := Objectify(NewType(fam,
                IsMutable and IsKnuthBendixRewritingSystem
                and IsKBMAGRewritingSystemRep),
                rws!.cosrws[ns]);
  return subrec;
end;

#############################################################################
##
#F  IsConfluentCosetsRWS(<rws>, <subrws>)
##  .  .  test whether <subrws> has a confluent coset system in <rws>.
##
##  Public function.
IsConfluentCosetsRWS := function ( rws, subrws )
  local ns, cosrws;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error("Second argument of IsConfluentCosetsRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  return IsBound(cosrws!.isConfluent) and cosrws!.isConfluent=true;
end;

#############################################################################
##
#F  IsAvailableNormalFormCosetsRWS(<rws>, <subrws>) 
##    . . test whether <rws> has a cosets normal form in <subrws>
##
##  Public function.
IsAvailableNormalFormCosetsRWS := function (  rws, subrws )
  local ns, cosrws;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error(
 "Second argument of IsAvailableNormalFormCosetsRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  return IsBound(cosrws!.isAvailableNormalForm) and
                 cosrws!.isAvailableNormalForm=true;
end;

#############################################################################
##
#F  IsAvailableReductionCosetsRWS(<rws>, <subrws>)
##      . . test whether <rws> has a cosets reduction algorithm in <subrws>
##
##  Public function.
IsAvailableReductionCosetsRWS := function (  rws, subrws )
  local ns, cosrws;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error(
 "Second argument of IsAvailableReductionCosetsRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  return IsBound(cosrws!.isAvailableReduction)
                 and cosrws!.isAvailableReduction=true;
end;

#############################################################################
##
#F  IsAvailableIndexRWS(<rws>, <subrws>)
##      . . test whether <rws> has a index algorithm in <subrws>
##
##  Public function.
IsAvailableIndexRWS := function (  rws, subrws )
  local ns, cosrws;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error("Second argument of IsAvailableIndexRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  return IsBound(cosrws!.isAvailableIndex)
                 and cosrws!.isAvailableIndex=true;
end;

#############################################################################
##
#F  WriteSubgroupRWS(<rws>, <subrws>, [<filename>], [<endsymbol>])
##       . . . . . .write an rws and a subgroup to files in external format
##
##  WriteSubgroupRWS prints the rws <rws> and its subgroup <subrws> to the
##  files <filename> and <filename>.sub (where <subrws> is subgroup)
## 
##  This is an extension of WriteRWS, but it is the original equations
##  of rws that are written, and the control parameters are not needed.
##
##  Public function.
WriteSubgroupRWS := function ( arg )
  local ns, filename, endsymbol, ng, nsg, rwsgennames, subrwsgens,
        subrwsigens, ig, line,
        geni, genstring,i, rws, subrws, subgens, eqn, eqns;

  if Length(arg) < 2 then
    Error("WriteSubgroupRWS needs at least two arguments.");
  fi;
  rws := arg[1];
  subrws := arg[2];
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error("Second argument of WriteSubgroupRWS is not a subRWS of first.");
  fi;

  filename := "";
  if Length(arg)>=3 then filename := arg[3]; fi;
  if filename="" then endsymbol := ""; else endsymbol := ";"; fi;
  if Length(arg)>=4 then endsymbol := arg[4]; fi;

  ng := Length(rws!.alphabet);
  rwsgennames := List(rws!.alphabet,x->String(x));

  #Now print main <rws> file
  if filename="" then Print("rec(\n");
  else PrintTo(filename,"_RWS := rec (\n");
  fi;

  line := String("isRWS",16);
  line := Concatenation(line," := true,");
  LinePrintRWS(line,filename);

  line := Concatenation(String("generatorOrder",16)," := [");
  for i in [1..ng] do
    if i > 1 then
      line := Concatenation(line,",");
    fi;
    if i=1 or Length(line)+Length(rwsgennames[i]) <= 76 then
      line := Concatenation(line,rwsgennames[i]);
    else
      LinePrintRWS(line,filename);
      line := String("",21);
      line := Concatenation(line,rwsgennames[i]);
    fi;
  od;
  line := Concatenation(line,"],");
  LinePrintRWS(line,filename);

  ig := rws!.invAlphabet;
  line := Concatenation(String("inverses",16)," := [");
  for i in [1..ng] do
    if i > 1 then line := Concatenation(line,","); fi;
    if IsInt(ig[i]) and ig[i]>0 then
      if i=1 or Length(line)+Length(rwsgennames[ig[i]]) <= 76 then
        line := Concatenation(line,rwsgennames[ig[i]]);
      else
        LinePrintRWS(line,filename);
        line := String("",21);
        line := Concatenation(line,rwsgennames[ig[i]]);
      fi;
    fi;
  od;
  line := Concatenation(line,"],");
  LinePrintRWS(line,filename);

  line := String("ordering",16);
  line := Concatenation(line," := \"",rws!.ordering,"\",");
  LinePrintRWS(line,filename);
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

  if IsBound(rws!.originalEquations) then
    eqns := rws!.originalEquations;
  else
    eqns := rws!.equations;
  fi;
  line := Concatenation(String("equations",16)," := [");
  for i in [1..Length(eqns)] do
    if i > 1 then line := Concatenation(line,","); fi;
    LinePrintRWS(line,filename);
    eqn := eqns[i];
    line := Concatenation(String("[",10),
                  StringRWS(ListToWordRWS(eqn[1],rws!.alphabet)),",");
    if Length(line)>=40 then
      LinePrintRWS(line,filename);
      line := String("",10);
    fi;
    line :=Concatenation( line,
               StringRWS(ListToWordRWS(eqn[2],rws!.alphabet)),"]");
  od;
  LinePrintRWS(line,filename);
  line := String("]",8);
  LinePrintRWS(line,filename);
  line := Concatenation(")",endsymbol);
  LinePrintRWS(line,filename);

  # That ends output of rws - now we do the subgroup

  if filename <> "" then
    filename := Concatenation(filename,".sub");
  fi;
  subgens := rws!.subgroups[ns]!.generatingWords;
  nsg := Length(rws!.subgroups[ns]!.alphabet);
  subrwsgens := rws!.subgroups[ns]!.alphabet;
  ig := rws!.subgroups[ns]!.invAlphabet;
  subrwsigens := [];
  for i in [1..nsg] do
    subrwsigens[i]:= subrwsgens[ig[i]];
  od;

  if filename="" then Print("rec(\n");
  else PrintTo(filename,"_RWS_Sub := rec (\n");
  fi;

  line := Concatenation(String("subGenerators",26)," := [");
  for i in [1..nsg] do
    if i > 1 then
      line := Concatenation(line,",");
    fi;
    genstring := String(subgens[i]);
    if i=1 or Length(line)+Length(genstring) <= 76 then
      line := Concatenation(line,genstring);
    else
      LinePrintRWS(line,filename);
      line := String("",21);
      line := Concatenation(line,genstring);
    fi;
  od;
  line := Concatenation(line,"],");
  LinePrintRWS(line,filename);

  line := Concatenation(String("subGeneratorNames",26)," := [");
  for i in [1..nsg] do
    if i > 1 then
      line := Concatenation(line,",");
    fi;
    genstring := String(subrwsgens[i]);
    if i=1 or Length(line)+Length(genstring) <= 76 then
      line := Concatenation(line,genstring);
    else
      LinePrintRWS(line,filename);
      line := String("",21);
      line := Concatenation(line,genstring);
    fi;
  od;
  line := Concatenation(line,"],");
  LinePrintRWS(line,filename);

  line := Concatenation(String("subGeneratorInverseNames",26)," := [");
  for i in [1..nsg] do
    if i > 1 then
      line := Concatenation(line,",");
    fi;
    genstring := String(subrwsigens[i]);
    if i=1 or Length(line)+Length(genstring) <= 76 then
      line := Concatenation(line,genstring);
    else
      LinePrintRWS(line,filename);
      line := String("",21);
      line := Concatenation(line,genstring);
    fi;
  od;
  line := Concatenation(line,"]");
  LinePrintRWS(line,filename);

  line := Concatenation(")",endsymbol);
  LinePrintRWS(line,filename);
end;


#############################################################################
##
#F  KBCosets(<rws>, <subrws> [,<subgens>]) 
##      . . . . call external Knuth-Bendix cosets program on rws, subrws!.
##
##  This returns true if a confluent coset rewriting system results - otherwise
##  false. In the latter case, words can still be rewritten with respect to
##  the current equations, but they are not guaranteed to reduce to the unique
##  representative of the group element.
##  If the optional third argument is set true then rewriting system generators
##  will be introduced for the subgroup generators, and so the final
##  confluent presentation will include a confluent presentation of the
##  subgroup.
##  If the third argument is missing or false, then these new generators
##  will not be introduced, and the Knuth-Bendix will operate only on
##  cosets.
##  An error message results if the external program aborts without outputting.
##  Public function.
KBCosets := function ( arg )
  local rws, subrws, subgens, ns, ng, nsg, callstring, filename, cosrws,
        M, subfreegp, is, nst, sr, nsgg, i, j, mnames, gf, eq, eqns,
        gtom, igtom, fam;

  if Length(arg) < 2 then
    Error("KBCosets needs at least two arguments.");
  fi;
  rws := arg[1];
  subrws := arg[2];

  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error("Second argument of WriteSubgroupRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  if IsBound(cosrws!.KBRun) and cosrws!.KBRun then
    Print(
      "KBCosets or AutCosets has already been run on <rws>, <subrws>.\n");
    Print("Call - ResetCosetsRWS( <rws>, <subrws> ) before proceeding.\n");
    return;
  fi;

  subgens := false;
  if Length(arg) >= 3 then
    subgens := arg[3];
  fi;

  ng := Length(rws!.alphabet);
  nsg := Length(subrws!.alphabet);

  #We need to set up a few fields in the cosets record.
  cosrws!.isRWS := true;
  cosrws!.isInternalRWS:=true;
  cosrws!.ordering := "wreathprod";
  cosrws!.hasOne := true;
  mnames := [];
  if subgens then
     mnames := Concatenation(List(rws!.alphabet,x->String(x)),["_H"],
                    List(rws!.subgroups[ns]!.alphabet,x->String(x)) );
  else
     mnames := Concatenation(List(rws!.alphabet,x->String(x)),["_H"] );
  fi;
  M := FreeMonoid(mnames);
  cosrws!.alphabet := GeneratorsOfMonoid(M);
  cosrws!.invAlphabet := ShallowCopy(rws!.invAlphabet);
  cosrws!.invAlphabet[ng+1] := false;
  if subgens then
    for i in [1..nsg] do
      cosrws!.invAlphabet[ng+1+i] :=rws!.subgroups[ns]!.invAlphabet[i]+ng+1;
    od;
  fi;
  cosrws!.FreeGpMonSgp := M;
  cosrws!.WordMonoid := M;
  cosrws!.baseAlphabet := rws!.alphabet;
  cosrws!.options := rec();
  
  WriteSubgroupRWS(rws,subrws,_KBTmpFileName);
  callstring := Filename(_KBExtDir,"makecosfile");
  if subgens then
     callstring := Concatenation(callstring," -sg ");
  fi;
  callstring := Concatenation(callstring," ",_KBTmpFileName," sub");
  Info(InfoRWS,3,"  ",callstring);
  Exec(callstring);

  callstring :=  Filename(_KBExtDir,"kbprogcos");
  callstring := Concatenation(callstring," ");
  #This time optional parameters will be added in the command-line.
  if IsBound(rws!.options.maxeqns) then
    callstring := Concatenation(callstring,"-me ",
                                  String(rws!.options.maxeqns)," ");
  fi;
  if IsBound(rws!.options.tidyint) then
    callstring := Concatenation(callstring,"-t ",
                                  String(rws!.options.tidyint)," ");
  fi;
  if IsBound(rws!.options.confnum) then
    callstring := Concatenation(callstring,"-cn ",
                                  String(rws!.options.confnum)," ");
  fi;
  if IsBound(rws!.options.maxstoredlen) then
    callstring := Concatenation(callstring,"-mlr ",
        String(rws!.options.maxstoredlen[1])," ",
                                  String(rws!.options.maxstoredlen[2])," ");
  fi;
  if IsBound(rws!.options.maxoverlaplen) then
  callstring := Concatenation(callstring,"-mo ",
                                  String(rws!.options.maxoverlaplen)," ");
  fi;
  if IsBound(rws!.options.maxreducelen) then
  callstring := Concatenation(callstring,"-mrl ",
                                  String(rws!.options.maxreducelen)," ");
  fi;
  if IsBound(rws!.options.maxstates) then
    callstring := Concatenation(callstring,"-ms ",
                           String(rws!.options.maxstates)," ");
  fi;
  if InfoLevel(InfoRWS)=0 then
    callstring := Concatenation(callstring,"-silent ");
  fi;
  if InfoLevel(InfoRWS)>1 then
    callstring := Concatenation(callstring,"-v ");
  fi;
  if InfoLevel(InfoRWS)>2 then
    callstring := Concatenation(callstring,"-vv ");
  fi;

  callstring := Concatenation(callstring,_KBTmpFileName," cos");
  Info(InfoRWS,1,"Calling external Knuth-Bendix cosets program.\n");
  Info(InfoRWS,3,"  ",callstring);
  Exec(callstring);
  filename := Concatenation(_KBTmpFileName,".cos");
  UpdateRWS(cosrws,filename,true,true);
  Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
  Info(InfoRWS,1,"External Knuth-Bendix cosets program complete.\n");

  if cosrws!.isConfluent then
    Info(InfoRWS,1,"System computed is confluent.\n");
    cosrws!.isAvailableNormalForm := true;
    cosrws!.warningOn := false;
  else
    Info(InfoRWS,1,"System computed is NOT confluent.\n");
    cosrws!.isAvailableNormalForm := false;
    cosrws!.warningOn := true;
  fi;
  cosrws!.KBRun := true;
  cosrws!.isAvailableReduction := true;
  cosrws!.isAvailableReductionPlus := subgens;
  cosrws!.isAvailableIndex := true;
  if subgens and cosrws!.isAvailableReduction then
  #We will make a new rewriting system for the subgroup.
    rws!.subrws[ns]:=rec();
    sr:=rws!.subrws[ns];
    sr.ordering := "shortlex";
    sr.hasOne := true;
    sr.invAlphabet := subrws!.invAlphabet;
    nsgg := 0;
    gtom:=[];
    igtom:=[];
    for i in [1..nsg] do
      if sr.invAlphabet[i] >= i then
        nsgg := nsgg+1;
        Add(gtom,i);
        Add(igtom,sr.invAlphabet[i]);
      fi;
    od;
    sr.FreeGpMonSgp := FreeGroup(nsgg);
    mnames := [];
    for i in [1..nsg] do
      mnames[i] := Concatenation("_g",String(i));
    od;
    sr.WordMonoid := FreeMonoid(mnames);
    sr.ExtIntCorr := CorrespondenceGroupMonoid(
                                sr.FreeGpMonSgp,sr.WordMonoid,gtom,igtom);
    sr.ExtToInt := FreeGroup2FreeMonoid;
    sr.IntToExt := FreeMonoid2FreeGroup;
    sr.alphabet := GeneratorsOfMonoid(sr.WordMonoid);

    sr.options := rec();
    sr.equations := [];
    ## pick up the required equations from cosrws!.eqauations
    eqns := cosrws!.equations;
    for eq in eqns do
      if eq[1][1] > ng+1 then
        Add(sr.equations, [List(eq[1],i->i-ng-1),List(eq[2],i->i-ng-1)] );
      fi;
    od;
    fam := NewFamily("Family of Knuth-Bendix Rewriting systems",
                IsKnuthBendixRewritingSystem);
    sr := Objectify(NewType(fam,
                IsMutable and IsKnuthBendixRewritingSystem
                and IsKBMAGRewritingSystemRep),
                sr);
    FpStructureRWS(sr);
    if cosrws!.isConfluent then
      Info(InfoRWS,1,"Running external program on subgroup presentation.\n");
      KBRWS(sr); #just to generate to reduction fsa.
    fi;
  fi;
  return cosrws!.isConfluent;
end;

#############################################################################
##
#F  RWSOfSubgroup(<rws>, <subrws>) 
##    . . The rewriting system of the subgroup as a separate entity.
##
##  This can be run after a run of KBCosets(<rws>,<subrws>,true);
##
##  Public function.
RWSOfSubgroup := function (  rws, subrws )
  local ns, cosrws;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error(
 "Second argument of RWSOfSubgroup is not a subRWS of first.");
  fi;
  if not IsBound(rws!.subrws[ns]) then
    Error("You did not call KnuthBendixOnCosetsWithSubgroupRewritingSystem.");
  fi;
  return rws!.subrws[ns];
end;

#############################################################################
##
#F  AutCosets(<rws>, <subrws>,
##                         [<subpres>, <large>], [<filestore>], [<diff1>])
##      . . . . call external automatic cosets program on <subrws> in <rws>.
##
##  This returns true if the automatic cosets programs succeed - otherwise
##  false.
##  If <subpres> is present and true, then a subgroup presentation
##  is also computed - but this not on the user generators. 
##
##  The other optional parameters are all boolean, and false by default.
##  <large> means problem is large - the external programs use bigger tables.
##  <filestore> means external programs use less core memory and more external
##         files - they run a little slower.
##  <diff1> is necessary on some examples - see manual for information.
##  Public function.
AutCosets := function ( arg )
  local  narg, rws, subrws, subpres, large, filestore, diff1, callstring,
         optstring, filename, cosrws, ns, ng, nsg, i;
  narg := Number(arg);
  if narg<2 then
     Error("AutCosets needs at least two arguments.");
  fi;
  rws := arg[1];
  if not IsGroupRWS(rws) then
    Error("AutCosets can only be applied to groups.");
  fi;
  subrws := arg[2];

  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error("Second argument of WriteSubgroupRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  if IsBound(cosrws!.KBRun) and cosrws!.KBRun then
    Print(
      "KBCosets or AutCosets has already been run on <rws>, <subrws>.\n");
    Print("Call - ResetCosetsRWS( <rws>, <subrws> ) before proceeding.\n");
    return;
  fi;

  if not rws!.ordering = "shortlex" then
     Error("Ordering must be shortlex for automatic group programs");
  fi;
  subpres := false; large:=false; filestore:=false; diff1:=false;
  if narg>=3 and arg[3]=true then subpres:=true; fi;
  if narg>=4 and arg[4]=true then large:=true; fi;
  if narg>=5 and arg[5]=true then filestore:=true; fi;
  if narg>=6 and arg[6]=true then diff1:=true; fi;

  ng := Length(rws!.alphabet);
  nsg := Length(subrws!.alphabet);

  #We need to set up a few fields in the cosets record.
  cosrws!.isRWS := true;
  cosrws!.isInternalRWS:=true;
  cosrws!.ordering := "wreathprod";
  cosrws!.hasOne := true;
  cosrws!.alphabet := rws!.alphabet;
  cosrws!.invAlphabet := rws!.invAlphabet;
  cosrws!.FreeGpMonSgp := rws!.WordMonoid;
  cosrws!.WordMonoid := rws!.WordMonoid;
  cosrws!.options:=rec();
  cosrws!.baseAlphabet := rws!.alphabet;
  cosrws!.equations := [];

  WriteSubgroupRWS(rws,subrws,_KBTmpFileName);
  callstring := Concatenation(Filename(_KBExtDir,"makecosfile"),"  -sg ");
  callstring := Concatenation(callstring,_KBTmpFileName," sub");
  Info(InfoRWS,3,"  ",callstring);
  Exec(callstring);

  callstring := Filename(_KBExtDir,"autcos");
  optstring := " ";
  if subpres then optstring := Concatenation(optstring," -p "); fi;
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
  Info(InfoRWS,1,"Calling external automatic cosets groups program.\n");
  Info(InfoRWS,3,"  ",callstring);
  Exec(callstring);
  if subpres then
  # read subgroup presentation
    if READ(Concatenation(_KBTmpFileName,".sub.pres")) then
      #Presentation is very redundant, so simplify.
      rws!.subgroups[ns]!.presentation :=
                                   SimplifiedFpGroup(_xg/_x_relators);
    fi;
  fi;
  filename := Concatenation(_KBTmpFileName,".cos");
  if READ(Concatenation(filename,".success")) then
   Info(InfoRWS,1,
      "Computation was successful - automatic coset structure computed.\n");
    UpdateRWS(cosrws,filename,false,true);
    #Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
    cosrws!.KBRun := true;
    cosrws!.isAvailableNormalForm := true;
    cosrws!.isAvailableNormalForm := true;
    cosrws!.isAvailableReduction := true;
    cosrws!.isAvailableReductionPlus := true;
    cosrws!.isAvailableIndex := true;
    cosrws!.warningOn := false;
    return true;
  else
    Exec(Concatenation("/bin/rm -f ",_KBTmpFileName,"*"));
    Info(InfoRWS,1,"Computation was not successful.\n");
    return false;
  fi;
end;

#############################################################################
##
#F  PresentationOfSubgroupRWS(<rws>, <subrws>) 
##    . . The presentation of the subgroup computed by AutCosets
##
##  This can be run after a run of AutCosets(<rws>,<subrws>,true);
##
##  Public function.
PresentationOfSubgroupRWS := function (  rws, subrws )
  local ns;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error(
 "Second argument of RWSOfSubgroup is not a subRWS of first.");
  fi;
  if not IsBound(rws!.subgroups[ns]!.presentation) then
    Error("RWS or subRWS unavailable. You must call AutCosets first.");
  fi;
  return rws!.subgroups[ns]!.presentation;
end;

#############################################################################
##
#F  IsReducedWordCosetsRWS(<rws>, <subrws>, <w>) 
##  . . tests if a <w> word represents a reduced coset of <subrws> in <rws>
##
##  IsReducedWordCosetsRWS tests whether the word <w>
##  is reduced as a coset of <subrws> in <rws>.
##  <w> can be given either as a list of integers (internal format) or as
##  a word in the generators of the underlying free group.
##  Either the word-acceptor (automatic group case) or the reduction FSA
##  must be defined.
##  It merely calls the corresponding FSA function.
##
##  Public function.
IsReducedWordCosetsRWS := function ( rws, subrws, w )
    local i, ng, ns, cosrws;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
  Error("Second argument of IsReducedWordCosetsRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  if not IsAvailableReductionCosetsRWS(rws,subrws) then
     Error(
    "Reduction algorithm unavailable. You must run KBCosets or AutomataCosets");
  fi;

  if not IsList(w) and not IsWord(w) then
     Error("Third argument is not a word or list.");
  fi;
  ng := Length(rws!.alphabet);
  if IsWord(w) then
     w:=WordToListRWS(w,rws!.alphabet);
  fi;
  for i in w do
    if not i in [1..ng] then Error("Invalid entry in word or list");fi;
  od;
  if IsBound(cosrws!.wa) then
  # Coset automatic group case - use word-acceptor
    return IsAcceptedWordDFA( cosrws!.wa,w );
  fi;
  if not IsBound(cosrws!.reductionFSA) then
     Error("Coset rewriting system  does not have initialized dfa as field.");
  fi;
  ##Put the subgroup symbol at the beginning of w
  w := Concatenation([ng+1],w);
  return IsAcceptedWordDFA( cosrws!.reductionFSA,w );
end;

#############################################################################
##
#F  ReduceWordCosetsWD(<wd>, <w>, <subgpword>)
##       . . . . reduces a word for a coset using word-difference automaton
##
##  ReduceWordCosetsWD calculates the reduction of the word <w> (list of
##  integers)  using the MIDFA word-difference automaton <wd>.
##  <wd> should be two-variable, where <w> is a list of integers in the range
##  [1..ng], where ng is the size of the base alphabet.
##  The first letter of w should always be ng+1 where ng is the number
##  of generators of the group - this represents the subgroup _H.
##  WARNING: No validity checks are carried out!
##
##  A list of two words [w1,w] is returned, where w is the reduce representative
##  of the coset of w, and, if subgpword is true,  w1 represents the element
##  in the subgroup such that  the original w = w1 * w in the group, or
##  w1 is the empty list if  subgpword is false. Note that w1 is a word in
## the group generators (not any user-supplied subgroup generators).
##
##  Private function.
ReduceWordCosetsWD := function ( wd, w, subgpword )
    local  ndiff, ngens, ng1, identity, level, cf, gpref, gct, gptr,
           diff, newdiff, deqi, gen1, gen2, donesub, donediffs, subvert,dosub,
           g2ltg1, diffct, t, nlen, olen, i, l, table, w1;
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
    #        prefix of the word being reduced. sublen is zero if the
    #        substitution starts at the beginning of the word and both strings
    #        are equal up to that point.
    # We put in some immediate vertices at level 1 for the non-identity
    # initial states of the word-difference machine.
    gct := 0;
    for i in [2..Length(wd.initial)] do
      gct := gct+1;
      gptr[gct] := rec();
      gptr[gct].genno := 0;
      gptr[gct].diffno := wd.initial[i];
      gptr[gct].sublen := 0;
    od;
    gpref[2] := gct;
    w1 := [];

    # Now we start scanning the word.
    table := DenseDTableFSA(wd);
    level := 2;
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
            while dosub and i>1 do
              w[i] := subvert.gen;
              i := i-1;
              if IsBound(subvert.backptr) then
	        subvert := subvert.backptr;
              else
                dosub := false;
              fi;
            od;
            if dosub and i=1 and subgpword then
              #We have a prefix
               w1 := Concatenation(w1, ShallowCopy(WordToListRWS(
                         wd.states.names[subvert.diffno],wd.states.alphabet)));
               ReduceWordWD( wd, w1);
            fi;
          fi;
          #Whenever we make a substitution, we have to go back one level more
          #than expected, because of our policy of looking ahead for
          #substitutions that reduce the length by 2.
          if i>1 then level:=i-1; else level:=i; fi;
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
              while dosub and i>1  do
                w[i] := subvert.gen;
                i := i-1;
                if IsBound(subvert.backptr) then
  	          subvert := subvert.backptr;
                else
                  dosub := false;
                fi;
              od;
              if dosub and i=1 and subgpword then
                #We have a prefix
               w1 := Concatenation(w1, ShallowCopy(WordToListRWS(
                         wd.states.names[subvert.diffno],wd.states.alphabet)));
                 ReduceWordWD( wd, w1);
              fi;
            fi;
            if i>1 then level:=i-1; else level:=i; fi;
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
              if deqi then 
                if g2ltg1 then
                  w[level] := gen2;
                  if level>2 then level:=level-2; else level:=level-1; fi;
                  gct := gpref[level+1];
                  donesub := true;
                fi;
              elif gptr[diffct].sublen>0 or
                                (gptr[diffct].sublen=0 and g2ltg1) then
                #Make a substitution by a string of equal length.
                w[level] := gen2;
                i := level-1;
                subvert := gptr[diffct];
    	        dosub := true;
                while dosub and i>1 do
                  w[i] := subvert.gen;
                  i := i-1;
                  if IsBound(subvert.backptr) then
    	            subvert := subvert.backptr;
                  else
                    dosub := false;
                  fi;
                od;
                if dosub and i=1 and subgpword then
                  #We have a prefix
                   w1 := Concatenation(w1, ShallowCopy(WordToListRWS(
                        wd.states.names[subvert.diffno],wd.states.alphabet)));
                   ReduceWordWD( wd, w1);
                fi;
                if i>1 then level:=i-1; else level:=i; fi;
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
                if not deqi then
                  l := gptr[diffct].sublen;
                fi;
                if deqi or l=0 then 
                  if g2ltg1 then nlen:=1;
                  elif gen2=gen1 then nlen:=0;
                  else  nlen:= -1;
                  fi;
                else
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
                if not deqi then
                  l := gptr[diffct].sublen;
                fi;
                if deqi or l=0 then 
                  if g2ltg1 then nlen:=1;
                  elif gen2=gen1 then nlen:=0;
                  else  nlen:= -1;
                  fi;
                else
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
              diffct := gpref[level-1] + 1;
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
    w := w{[2..Length(w)]}; #remove subgroup symbol!
    return [w1,w];
end;

#############################################################################
##
#F  ReduceWordCosetsRWS(<rws>, <subrws>, <w> [,<subgpword>])
##   .  .  . reduce a word  as a coset of <subrws> in <rws>
##
##  ReduceWordCosetsRWS reduces the word <w>, as a coset representatibe of
##  <subrws> in <rws>.
##  <w> can be given either as a list of integers (internal format) or as
##  a word in the generators of the underlying group or monoid.
##  Either the reduction FSA, or one of the word-difference automata (in the
##  automatic group case) must be defined for <rws>.
##  In the latter case, the separate function ReduceWordWD is called.
## 
##  If the optional fourth argument is 'true', then a pair of words
##  [w1,w2] is returned, where w = w1*w2 in the group, w2 is the
##  coset reduction of w, and w1 is an element of the subgroup.
##
##  Public function.
ReduceWordCosetsRWS := function ( arg )
  local rws, subrws, w, subgpword, fsa, pos, label, state, history, eqn,
        sublen, table, ng,  i, word, IdWord, ns, cosrws, p, w1, wp, kb, wd;
  if Length(arg)<3 then
     Error("ReduceWordCosetsRWS must have at least 3 arguments.");
  fi;
  rws:=arg[1]; subrws:=arg[2]; w:=arg[3];
  if Length(arg)>=4 then subgpword:=arg[4]; else subgpword:=false; fi;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error("Second argument of ReduceWordCosetsRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  if subgpword and not cosrws!.isAvailableReductionPlus then
    Error("Subgroup word reduction not available.");
  fi;
  if not IsAvailableReductionCosetsRWS(rws,subrws) then
     Error(
    "Reduction algorithm unavailable. You must run KBCosets or AutCosets");
  fi;
  if not IsList(w) and not IsWord(w) then
     Error("Third argument is not a word or list.");
  fi;
  ng := Length(rws!.alphabet);
  if IsWord(w) then
     word :=true;
     w:=ShallowCopy(WordToListRWS(w,rws!.alphabet));
  else word := false;
  fi;
  if IsBound(cosrws!.warningOn) and cosrws!.warningOn then
    if IsBound(cosrws!.KBRun) and cosrws!.KBRun then
        Print(
 "#WARNING: system is not confluent, so reductions may not be to normal form.\n"
      );
      else
        Print(
 "#WARNING: word-difference reduction machine is not proven correct,\n",
 "          so reductions may not be to normal form.\n");
      fi;
      cosrws!.warningOn:=false;
      # only give the warning once, or it could become irritating!
  fi;
  if IsBound(cosrws!.midiff2) then
   # automatic cosets case
    kb := false;
    wd := cosrws!.midiff2;
  elif IsBound(cosrws!.midiff1) then
   # automatic cosets case
    kb := false;
    wd := cosrws!.midiff1;
  else kb := true;
  fi;
  # put the subgroup symbol in front of w.
  w := Concatenation([ng+1],w);
  if kb then
    w := ReduceWordRWS(cosrws,w);
    #remove prefix up to subgroup symbol
    p := Position(w,ng+1);
    if subgpword then
      w1 := List(w{[1..p-1]},i->i-ng-1);
    fi;
    w := w{[p+1..Length(w)]};
  else
    wp := ReduceWordCosetsWD(wd,w,subgpword);
    w1 := wp[1]; w := wp[2];
  fi;

  if word then
     if subgpword then
       if kb then
         w1 := ListToWordRWS(w1,rws!.subrws[ns]!.alphabet);
       else
         w1 := ListToWordRWS(w1,rws!.alphabet);
       fi;
     fi;
     w := ListToWordRWS(w,rws!.alphabet);
  fi;

  if subgpword then
    return [w1,w];
  fi;
  return w;
end;

#############################################################################
##
#F  IndexRWS(<rws>, <subrws>)
##    . . number of reduced coset words of <subrws> in <rws>
##
##  This merely calls the corresponding FSA function.
##
##  Public function.
IndexRWS := function ( rws, subrws )
  local ns, cosrws, rfsa, ng;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error("Second argument of IndexRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  if not IsAvailableIndexRWS(rws,subrws) then
     Error(
 "Index algorithm unavailable. You must run KBCosets or AutCosets first.");
  fi;
  if IsBound(cosrws!.warningOn) and cosrws!.warningOn then
  if cosrws!.KBRun then
        Print(
 "#WARNING: system is not confluent, so index returned may not be correct.\n"
      );
      else
        Print(
 "#WARNING: word-difference reduction machine is not proven correct,\n",
 "          so index returned may not be correct.\n");
      fi;
  cosrws!.warningOn:=false;
     # only give the warning once, or it could become irritating!
  fi;
  if IsBound(cosrws!.wa) then
     # automatic group case
      return LSizeDFA( cosrws!.wa );
  fi;
  rfsa := cosrws!.reductionFSA;
  ng := Length(rws!.alphabet);
  return LSizeDFA(rfsa,TargetDFA(rfsa,ng+1,rfsa.initial[1]));
end;

#############################################################################
##
#F  EnumerateCosetsRWS(<rws>, <subrws>, <min>, <max>)
##         . . enumerate reduced cosets words of <subrws> in <rws>
##
##  This merely calls the corresponding FSA function.
##  Words are converted to words in generators of underlying group
##  before returning.
##
##  Public function.
EnumerateCosetsRWS := function ( rws, subrws, min, max )
  local ret, x, i, ns, cosrws, rfsa, ng;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error("Second argument of EnumerateCosetsRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  if not IsAvailableIndexRWS(rws,subrws) then
     Error(
  "Enumeration algorithm unavailable. You must run KBCosets or AutCosets");
  fi;
  if IsBound(cosrws!.wa) then
   # automatic group case
    ret := LEnumerateDFA( cosrws!.wa, min, max );
  else
    rfsa := cosrws!.reductionFSA;
    ng := Length(rws!.alphabet);
    ret := LEnumerateDFA(
                rfsa, min, max, TargetDFA(rfsa,ng+1,rfsa.initial[1]));
  fi;
  return ret;
end;

#############################################################################
##
#F  SortEnumerateCosetsRWS(<rws>, <subrws>, <min>, <max>)
##         . . enumerate reduced cosets words of <subrws> in <rws> and sort
##
##  This merely calls the corresponding FSA function.
##  Words are converted to words in generators of underlying group
##  before returning.
##
##  Public function.
SortEnumerateCosetsRWS := function ( rws, subrws, min, max )
  local ret, x, i, ns, cosrws, rfsa, ng;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
  Error("Second argument of SortEnumerateCosetsRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  if not IsAvailableIndexRWS(rws,subrws) then
     Error(
  "Enumeration algorithm unavailable. You must run KBCosets or AutCosets");
  fi;
  if IsBound(cosrws!.wa) then
   # automatic group case
    ret := SortLEnumerateDFA( cosrws!.wa,min,max );
  else
    rfsa := cosrws!.reductionFSA;
    ng := Length(rws!.alphabet);
    ret := SortLEnumerateDFA(
                rfsa, min, max, TargetDFA(rfsa,ng+1,rfsa.initial[1]));
  fi;
  return ret;
end;

#############################################################################
##
#F  SizeEnumerateCosetsRWS(<rws>, <subrws>, <min>, <max>)
##         . . number of reduced cosets words of <subrws> in <rws>
##
##  This merely calls the corresponding FSA function.
##  Words are converted to words in generators of underlying group
##  before returning.
##
##  Public function.
SizeEnumerateCosetsRWS := function ( rws, subrws, min, max )
  local ret, x, i, IdWord, ns, cosrws, rfsa, ng;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
  Error("Second argument of SizeEnumerateCosetsRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];
  if not IsAvailableIndexRWS(rws,subrws) then
     Error(
  "Enumeration algorithm unavailable. You must run KBCosets or AutCosets");
  fi;
  if IsBound(cosrws!.wa) then
   # automatic group case
    return SizeLEnumerateDFA( cosrws!.wa,min,max );
  else
    rfsa := cosrws!.reductionFSA;
    ng := Length(rws!.alphabet);
    return SizeLEnumerateDFA(
                rfsa, min, max, TargetDFA(rfsa,ng+1,rfsa.initial[1]));
  fi;
end;


#############################################################################
##
#F  ResetCosetsRWS(<rws>,<subrws>)  .  reset coset rws after a call of KBCosets.
##
##  Public function.
##  This resets a coset rewriting system back to the original, after a
##  call of KBCosets or AutCosets.
##  Perhaps useful if order of alphabet is to be changed.
ResetCosetsRWS := function ( rws, subrws )
  local ns, cosrws;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error("Second argument of ResetCosetsRWS is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];

  Unbind(cosrws!.KBRun);
  Unbind(cosrws!.isConfluent);
  Unbind(cosrws!.isAvailableNormalForm);
  Unbind(cosrws!.isAvailableReduction);
  Unbind(cosrws!.isAvailableIndex);
  Unbind(cosrws!.warningOn);
  Unbind(cosrws!.reductionFSA);
  Unbind(cosrws!.wa);
  Unbind(cosrws!.midiff1);
  Unbind(cosrws!.midiff2);
  Unbind(cosrws!.migm);
  Unbind(cosrws!.equations);
end;
