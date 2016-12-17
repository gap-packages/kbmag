#############################################################################
##
#W  kbsmg.gi           GAP library                        Derek Holt
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains code for the Knuth-Bendix rewriting system for semigroups
##

############################################################################
##
#R  IsKBMAGRewritingSystemRep(<obj>)
## 
##  reduced - is the system known to be reduced
##  lessthanorequal(a, b) - is <a> less than or equal<b> in the word order
##
DeclareRepresentation("IsKBMAGRewritingSystemRep", 
IsComponentObjectRep,
 ["GpMonSgp","FreeGpMonSgp","hasOne","ordering","alphabet",
  "invAlphabet", "WordMonoid", "equations","isConfluent","options",
   "ExtToInt", "IntToExt", "ExtIntCorr",
  "weight","level","KBRun","warningOn","reductionFSA","wa","diff1",
  "diff1c","diff2","gm","isAvailableNormalForm","isAvailableReduction",
   "isAvailableSize","originalEquations","outputWords","wg","sub",
   "subgroups","numSubgroups","cosrws","subrws","namesInverseGenerators",
   "IsAvailableIndex","presentation","generatingWords"]
);


#############################################################################
##
#F  CreateKBMAGRewritingSystemOfFpSemigroup (<S>)
##  
InstallGlobalFunction(CreateKBMAGRewritingSystemOfFpSemigroup,
function(S)
 	local r,kbrws,fam;

	fam := NewFamily("Family of Knuth-Bendix Rewriting systems", 
		IsKnuthBendixRewritingSystem);

	r := FpSemigroupToRWS(S);

	kbrws := Objectify(NewType(fam, 
		IsMutable and IsKnuthBendixRewritingSystem
		and IsKBMAGRewritingSystemRep), 
		r);

	return kbrws;

end);

#############################################################################
## 
#M  KBMAGRewritingSystem(<S>,<lteq>)
##
##  creates the Knuth Bendix rewriting system for the semigroup S
##
InstallMethod(KBMAGRewritingSystem, "for an fp semigroup", true,
[IsFpSemigroup], 0,
function(S)
	local kbrws;

	kbrws := CreateKBMAGRewritingSystemOfFpSemigroup(S);
  return kbrws; 
end);

#############################################################################
##
#F  CreateKBMAGRewritingSystemOfFpMonoid (<S>)
##  
InstallGlobalFunction(CreateKBMAGRewritingSystemOfFpMonoid,
function(S)
 	local r,kbrws,fam;

	fam := NewFamily("Family of Knuth-Bendix Rewriting systems", 
		IsKnuthBendixRewritingSystem);

	r := FpMonoidToRWS(S);

	kbrws := Objectify(NewType(fam, 
		IsMutable and IsKnuthBendixRewritingSystem
		and IsKBMAGRewritingSystemRep), 
		r);

	return kbrws;

end);

#############################################################################
## 
#M  KBMAGRewritingSystem(<S>,<lteq>)
##
##  creates the Knuth Bendix rewriting system for the semigroup S
##
InstallMethod(KBMAGRewritingSystem, "for an fp Monoid", true,
[IsFpMonoid], 0,
function(S)
	local kbrws;

	kbrws := CreateKBMAGRewritingSystemOfFpMonoid(S);
  return kbrws; 
end);

#############################################################################
##
#F  CreateKBMAGRewritingSystemOfFpGroup (<S>)
##  
InstallGlobalFunction(CreateKBMAGRewritingSystemOfFpGroup,
function(S)
 	local r,kbrws,fam;

	fam := NewFamily("Family of Knuth-Bendix Rewriting systems", 
		IsKnuthBendixRewritingSystem);

	r := FpGroupToRWS(S);

	kbrws := Objectify(NewType(fam, 
		IsMutable and IsKnuthBendixRewritingSystem
		and IsKBMAGRewritingSystemRep), 
		r);

	return kbrws;

end);

#############################################################################
## 
#M  KBMAGRewritingSystem(<S>)
##
##  creates the Knuth Bendix rewriting system for the  fp-group S
##
InstallMethod(KBMAGRewritingSystem, "for an fp group", true, [IsFpGroup], 0,
function(S)
	local kbrws;

	kbrws := CreateKBMAGRewritingSystemOfFpGroup(S);
  return kbrws; 
end);

#############################################################################
##
#F  KBMAG_REW.MakeKnuthBendixRewritingSystemConfluent
##  
##  using the external KB. This method will replace the library KB by a call
##  to the external KB.
KBMAG_REW.MakeKnuthBendixRewritingSystemConfluent:=
function(kbrws)
local rws,M,F,gens,ng,wnames,mnames,i,fam,rels;
  rws := rec();
  M:=CollectionsFamily(kbrws!.family)!.wholeMonoid;
  rws.GpMonSgp := M;
  rws.hasOne := true;
  F:=FreeMonoidOfFpMonoid(M);
  rws.FreeGpMonSgp := F;
  rws.options := rec();

  if IsShortLexOrdering(kbrws!.ordering) then
    rws.ordering := "shortlex";
  else
    Error("KBMAG for library rewriting systems so far only works for shortlex",
      "You might want to use `CreateKBMAGRewritingSystemOfFpMonoid' instead");
  fi;
  ng := Length(GeneratorsOfMonoid(F));

  mnames := [];
  for i in [1..ng] do
    mnames[i] := Concatenation("_m",String(i));
  od;
  rws.WordMonoid := FreeMonoid(mnames);

  rws.ExtIntCorr := CorrespondenceMSMonoid(F,rws.WordMonoid);
  rws.ExtToInt := FreeMS2FreeMonoid;
  rws.IntToExt := FreeMonoid2FreeMS;

  gens := GeneratorsOfMonoid(rws.WordMonoid);
  rws.alphabet := gens;
  rws.invAlphabet := List([1..ng],i->false);

  rws.equations := ShallowCopy(TzRules(kbrws));

  fam := NewFamily("Family of Knuth-Bendix Rewriting systems",
		  IsKnuthBendixRewritingSystem);

  rws := Objectify(NewType(fam,
           IsMutable and IsKnuthBendixRewritingSystem 
	   and IsKBMAGRewritingSystemRep), rws);
  MakeConfluent(rws);
  if IsBound(rws!.isConfluent) and rws!.isConfluent=true then
    kbrws!.tzrules:=rws!.equations;
    kbrws!.pairs2check:=[];
    kbrws!.reduced:=true;
  else
    Error("did not terminate");
  fi;
end;

#############################################################################
##
#E

