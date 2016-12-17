#############################################################################
##
#W  kbsmg2.gi           GAP library                                 Derek Holt
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains more implementations for Knuth Bendix Rewriting Systems
##
############################################################################
##
#M  ViewObj(<rws>)
##
##
InstallMethod(ViewObj, "for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 6, 
function(rws) 
	WriteRWS(rws);
end);

############################################################################
##
#M  SemigroupOfRewritingSystem(<rws>)
##
##
InstallMethod(SemigroupOfRewritingSystem,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
  return FpStructureRWS(rws);
end);

############################################################################
##
#M  FreeStructureOfRewritingSystem(<rws>)
##
##
InstallMethod(FreeStructureOfRewritingSystem,"for a KBMAG rewriting system",
         true, [IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
  return rws!.FreeGpMonSgp;
end);

############################################################################
##
#M  WordMonoidOfRewritingSystem(<rws>)
##
##
InstallMethod(WordMonoidOfRewritingSystem,"for a KBMAG rewriting system",
         true, [IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
  return rws!.WordMonoid;
end);

############################################################################
##
#F  ExternalWordToInternalWordOfRewritingSystem(<R>,<w>)
## 
## Convert a word in the external free structure of a rewriting system
## to its corresponding word in the internal word monoid.
##
InstallGlobalFunction(ExternalWordToInternalWordOfRewritingSystem,
function(R,w) return R!.ExtToInt(R!.ExtIntCorr,w); end);

############################################################################
##
#F  InternalWordToExternalWordOfRewritingSystem(<R>,<w>)
## 
## Convert a word in the external free structure of a rewriting system
## to its corresponding word in the internal word monoid.
##
InstallGlobalFunction(InternalWordToExternalWordOfRewritingSystem,
  function(R,w) return R!.IntToExt(R!.ExtIntCorr,w); end);


############################################################################
##
#F  OptionsRecordOfKBMAGRewritingSystem(<rws>)
##
##
InstallGlobalFunction(OptionsRecordOfKBMAGRewritingSystem,
  function(rws) return rws!.options;
end);

############################################################################
##
#M  Alphabet(<rws>)
##
##
InstallMethod(Alphabet,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
  return rws!.alphabet;
end);

############################################################################
##
#M  Rules(<rws>)
##
##
InstallMethod(Rules,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
  return List(rws!.equations,e->
   [ListToWordRWS(e[1],rws!.alphabet),ListToWordRWS(e[2],rws!.alphabet)]);
end);

############################################################################
##
#F  ReorderAlphabetOfKBMAGRewritingSystem(<rws>,<perm>)
## 
## <perm> should be a permutation of [1..Size of Alphabet of <rws>].
## The order of the alphabet is part of the definition of the
## ordering of the rewriting-system.
##
InstallGlobalFunction(ReorderAlphabetOfKBMAGRewritingSystem,
function(rws,perm)
   local i;
   ##To be on the safe side, we reset everything before changing the
   ## ordering.
   ResetRWS(rws);
   if IsBound(rws!.numSubgroups) then
     for i in [1..rws!.numSubgroups] do
       ResetCosetsRWS(rws,rws!.subrws[i]);
     od;
   fi;
   ReorderGeneratorsRWS(rws,perm);
end );

############################################################################
##
#F  SetOrderingOfKBMAGRewritingSystem(<rws>,<ordering-string>[,list])
##  
## This sets the ordering of words that will be used by the Knuth-Bendix
## program. Remember that the ordering also depends on the ordering of
## the alphabet, which can be changed by the preceding function.
## The permitted ordering strings are:
## "shortlex", "wtlex", "wreathprod", "recursive".
## In the "wtlex" and "recursive" cases, the third parameter giving a
## list of the (positive integral) weights or levels of the alphabet
## is mandatory.
##
InstallGlobalFunction(SetOrderingOfKBMAGRewritingSystem,
function(arg)
   ##To be on the safe side, we reset everything before changing the
   ##ordering.
   local i, rws;
   rws := arg[1];
   ResetRWS(rws);
   if IsBound(rws!.numSubgroups) then
     for i in [1..rws!.numSubgroups] do
       ResetCosetsRWS(rws,rws!.subrws[i]);
     od;
   fi;
   CallFuncList(SetOrderingRWS,arg);
end);

############################################################################
##
#F OrderingOfKBMAGRewritingSystem(<rws>)
## 
## Prints out a description of the ordering.
##
InstallGlobalFunction(OrderingOfKBMAGRewritingSystem,
function(rws)
  local ord;
  ord := rws!.ordering;
  Print("            Ordering: ",ord,"\n");
  Print("   Order of alphabet: ",rws!.alphabet,"\n");
  if ord="wtlex" then
    Print(" Weights of alphabet: ",rws!.weight,"\n");
  fi;
  if ord="wreathprod" then
    Print("  Levels of alphabet: ",rws!.level,"\n");
  fi;
end);

#############################################################################
##
#A  OrderingOfRewritingSystem(<rws>)
##
##  for a rewriting system rws
##  returns the order used by the rewriting system
##  DO NOT CONFUSE with OrderingOfKBMAGRewritingSystem, which returns
##  a description of the ordering.
##
InstallMethod(OrderingOfRewritingSystem,
"for a Knuth Bendix rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
        local M, alph, ord;
        M := WordMonoidOfRewritingSystem(rws);
        alph := Alphabet(rws);
        ord := rws!.ordering;
        if ord = "shortlex" then
           return ShortLexOrdering(M,alph);
        elif ord = "wtlex" then
           return WeightLexOrdering(M,alph,rws!.weight);
        elif ord = "recursive" then
           return BasicWreathProductOrdering(M,alph);
        elif ord = "wreathprod" then
           return WreathProductOrdering(M,alph,rws!.level);
        fi;
end);

############################################################################
##
#M  IsConfluent(<rws>)
##
##
InstallMethod(IsConfluent,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
  return IsConfluentRWS(rws);
end);
 
############################################################################
##
#M  KnuthBendix(<rws>)
##
##
InstallMethod(KnuthBendix,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
  return KBRWS(rws);
end);
 
############################################################################
##
#M  MakeConfluent(<rws>)
##
## Same as KnuthBendix
##
InstallOtherMethod(MakeConfluent,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
  return KBRWS(rws);
end);
 
############################################################################
##
#F  AutomaticStructure(<rws>[,<large>,<filestore>,<diff1>])
##
##
InstallGlobalFunction(AutomaticStructure,
function(arg)
  if arg[1]!.ordering <> "shortlex" then
       Info(InfoRWS,1,
                   "Ordering is not shortlex - trying alternative procedure.");
       return CallFuncList(TestAutomatic,arg);
  fi;
  return CallFuncList(AutRWS,arg);
end);

############################################################################
##
#M  Size(<rws>)
##
##  Number of irreducible words in the rewriting system
##
InstallOtherMethod(Size,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
  return SizeRWS(rws);
end);

############################################################################
##
#M  ReducedForm(<rws>,<w>)
##
##  Reduce a word in the free structure of the rewriting system
##
InstallMethod(ReducedForm,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,IsAssocWord], 0,
function(rws,w)
  w := ExternalWordToInternalWordOfRewritingSystem(rws,w);
  if IsBound(rws!.diff2) and rws!.ordering <> "shortlex" then
    ##use Sarah's code
    w := DiffReducedWord(rws!.diff2,WordOrder(rws),w);
  else 
    w := ReduceWordRWS(rws,w);
  fi;
  return InternalWordToExternalWordOfRewritingSystem(rws,w);
end);

############################################################################
##
#M  ReducedWord(<rws>,<w>)
##
##  Same as ReducedForm
##
InstallMethod(ReducedWord,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,IsAssocWord], 0,
function(rws,w)
  w := ExternalWordToInternalWordOfRewritingSystem(rws,w);
  if IsBound(rws!.diff2) and rws!.ordering <> "shortlex" then
    ##use Sarah's code
    w := DiffReducedWord(rws!.diff2,WordOrder(rws),w);
  else 
    w := ReduceWordRWS(rws,w);
  fi;
  return InternalWordToExternalWordOfRewritingSystem(rws,w);
end);

############################################################################
##
#A  IsReducedWord(<rws>,<w>)
##
##
InstallMethod(IsReducedWord,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,IsAssocWord], 0,
function(rws,w)
  local wi;
  wi := ExternalWordToInternalWordOfRewritingSystem(rws,w);
  if w <> InternalWordToExternalWordOfRewritingSystem(rws,wi) then
    return false; ## because w contains a non-reduced inverse of a generator.
  fi;
  return IsReducedWordRWS(rws,wi);
end);

############################################################################
##
#A  IsReducedForm(<rws>,<w>)
##
## Same as IsReducedWord
##
InstallMethod(IsReducedForm,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,IsAssocWord], 0,
function(rws,w)
  local wi;
  wi := ExternalWordToInternalWordOfRewritingSystem(rws,w);
  if w <> InternalWordToExternalWordOfRewritingSystem(rws,wi) then
    return false; ## because w contains a non-reduced inverse of a generator.
  fi;
  return IsReducedWordRWS(rws,wi);
end);

############################################################################
##
#M  EnumerateReducedWords(<rws>,<minlength>,<maxlength>)
##
##
InstallMethod(EnumerateReducedWords,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,IsInt,IsInt], 0,
function(rws,n,m)
  return List(EnumerateRWS(rws,n,m),
      w -> InternalWordToExternalWordOfRewritingSystem(rws,w) );
end);

############################################################################
##
#M  Order(<rws>,<w>)
##
##  <w> should be an element of the free structure of <rws>, which must
##  be a monoid or group.
##  The order of the element of the group/monoid of <rws> represented by
##  <w> is returned. 
##  This is not guaranteed to succeed in all cases when the order is
##  infinite, but it usually does.
##
InstallOtherMethod(Order,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,IsAssocWord], 0,
function(rws,w)
  w := ExternalWordToInternalWordOfRewritingSystem(rws,w);
  return OrderRWS(rws,w);
end);

############################################################################
##
#F GrowthFunction(<rws>)
## 
## The growth function of the irreducible words of <rws>.
##
InstallGlobalFunction(GrowthFunction,
function(rws)
  if IsBound(rws!.reductionFSA) then
     return GrowthFSA(rws!.reductionFSA);
  fi;
  if IsBound(rws!.wa) then
     return GrowthFSA(rws!.wa);
  fi;
  
  Error("Growth function not available.");
end); 

############################################################################
##
#F ReductionAutomaton(<rws>)
## 
## The reduction automaton of <rws> if available.
##
InstallGlobalFunction(ReductionAutomaton,
function(rws)
  if not IsBound(rws!.reductionFSA) then
    Error("Reduction automaton not available.");
  fi;
  return rws!.reductionFSA;
end); 

############################################################################
##
#F WordAcceptor(<rws>)
## 
##
InstallGlobalFunction(WordAcceptor,
function(rws)
  if not IsBound(rws!.wa) then
    Error("Word acceptor not available.");
  fi;
  return rws!.wa;
end); 

############################################################################
##
#F FirstWordDifferenceAutomaton(<rws>)
## 
##
InstallGlobalFunction(FirstWordDifferenceAutomaton,
function(rws)
  if not IsBound(rws!.diff1c) and not IsBound(rws!.diff1) then
    Error("First word difference automaton not available.");
  fi;
  if IsBound(rws!.diff1c) then
    return rws!.diff1c;
  fi;
  return rws!.diff1;
end); 

############################################################################
##
#F SecondWordDifferenceAutomaton(<rws>)
## 
##
InstallGlobalFunction(SecondWordDifferenceAutomaton,
function(rws)
  if not IsBound(rws!.diff2) then
    Error("Second word difference automaton not available.");
  fi;
  return rws!.diff2;
end); 

############################################################################
##
#F GeneralMultiplier(<rws>)
## 
##
InstallGlobalFunction(GeneralMultiplier,
function(rws)
  if not IsBound(rws!.wa) or not IsBound(rws!.diff2) then
    Error("General multiplier automaton not available.");
  fi;
  if not IsBound(rws!.gm) then
    GpGenMult(rws);
  fi;
  return rws!.gm;
end); 

############################################################################
##
#M  MakeConfluent(<rws>)
##
## Same as KnuthBendix
##
InstallOtherMethod(MakeConfluent,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws)
  return KBRWS(rws);
end);

############################################################################
##
#F  ResetRewritingSystem(<rws>)
##
##
InstallGlobalFunction(ResetRewritingSystem,
function(rws)
  ResetRWS(rws);
end);

############################################################################
##
#F  SubgroupOfKBMAGRewritingSystem(<rws>,<H>)
##
##
InstallGlobalFunction(SubgroupOfKBMAGRewritingSystem,
  function(rws,H) return SubgroupRWS(rws,H);
end);

############################################################################
##
#A  IsConfluentOnCosets(<rws>,<subrws>)
##
##
InstallMethod(IsConfluentOnCosets,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,
 IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws,subrws)
  return IsConfluentCosetsRWS(rws,subrws);
end);

############################################################################
##
#M  KnuthBendixOnCosets(<rws>,<subrws>)
##
##
InstallMethod(KnuthBendixOnCosets,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,
 IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws,subrws)
  return KBCosets(rws,subrws);
end);

############################################################################
##
#M  KnuthBendixOnCosetsWithSubgroupRewritingSystem(<rws>,<subrws>)
##
##
InstallMethod(KnuthBendixOnCosetsWithSubgroupRewritingSystem,
 "for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,
 IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws,subrws)
  return KBCosets(rws,subrws,true);
end);

############################################################################
##
#F  RewritingSystemOfSubgroupOfKBMAGRewritingSystem(<rws>,<subrws>)
##
##
InstallGlobalFunction(RewritingSystemOfSubgroupOfKBMAGRewritingSystem,
  function(rws,subrws) return RWSOfSubgroup(rws,subrws);
end);

############################################################################
##
#F  AutomaticStructureOnCosets(<rws>,<subrws>[,<large>,<filestore>,<diff1>])
##
##
InstallGlobalFunction(AutomaticStructureOnCosets,
function(arg)
  return CallFuncList(AutCosets,arg);
end);

#############################################################################
##
#F  AutomaticStructureOnCosetsWithSubgroupPresentation(<rws>,<subrws>,
##                                        [large,filestore,diff1])
##
InstallGlobalFunction(AutomaticStructureOnCosetsWithSubgroupPresentation,
function(arg)
  local l;
  if Length(arg)<2 then
    Error("AutomaticStructureOnCosets needs at least two arguments.");
  fi;
  l := Concatenation([arg[1],arg[2]],[true],arg{[3..Length(arg)]});
  return CallFuncList(AutCosets,l);
end);

#############################################################################
##
#F  PresentationOfSubgroupOfKBMAGRewritingSystem(<rws>,<subrws>)
##
InstallGlobalFunction(PresentationOfSubgroupOfKBMAGRewritingSystem,
function(rws,subrws) return PresentationOfSubgroupRWS(rws,subrws);
end);

############################################################################
##
#M  Index(<rws>,<subrws>)
##
##
InstallOtherMethod(Index,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,
 IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep], 0,
function(rws,subrws)
  return IndexRWS(rws,subrws);
end);

############################################################################
##
#M  ReducedFormOfCosetRepresentative(<rws>,<subrws>,<w>)
##
##
InstallMethod(ReducedFormOfCosetRepresentative,
  "for a KBMAG rewriting system", true,
 [IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,
  IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,IsAssocWord], 0,
function(rws,subrws,w)
  w := ExternalWordToInternalWordOfRewritingSystem(rws,w);
  w := ReduceWordCosetsRWS(rws,subrws,w);
  return InternalWordToExternalWordOfRewritingSystem(rws,w);
end);

############################################################################
##
#M  ReducedCosetRepresentative(<rws>,<subrws>,<w>)
##
## same as ReducedFormOfCosetRepresentative
##
InstallMethod(ReducedCosetRepresentative,
  "for a KBMAG rewriting system", true,
 [IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,
  IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,IsAssocWord], 0,
function(rws,subrws,w)
  w := ExternalWordToInternalWordOfRewritingSystem(rws,w);
  w := ReduceWordCosetsRWS(rws,subrws,w);
  return InternalWordToExternalWordOfRewritingSystem(rws,w);
end);

############################################################################
##
#A  IsReducedCosetRepresentative(<rws>,<subrws>,<w>)
##
##
InstallMethod(IsReducedCosetRepresentative,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,
 IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,IsAssocWord], 0,
function(rws,subrws,w)
  local wi;
  wi := ExternalWordToInternalWordOfRewritingSystem(rws,w);
  if w <> InternalWordToExternalWordOfRewritingSystem(rws,wi) then
    return false; ## because w contains a non-reduced inverse of a generator.
  fi;
  return IsReducedWordCosetsRWS(rws,subrws,wi);
end);

############################################################################
##
#M EnumerateReducedCosetRepresentatives(<rws>,<subrws>,<minlength>,<maxlength>)
##
##
InstallMethod(EnumerateReducedCosetRepresentatives
 ,"for a KBMAG rewriting system", true,
[IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,
 IsKnuthBendixRewritingSystem and IsKBMAGRewritingSystemRep,IsInt,IsInt], 0,
function(rws,subrws,n,m)
  return List(EnumerateCosetsRWS(rws,subrws,n,m),
      w -> InternalWordToExternalWordOfRewritingSystem(rws,w) );
end);

############################################################################
##
#F GrowthFunctionOfCosetRepresentatives(<rws>,<subrws>)
##
## The growth function of the irreducible words of <subrws> in <rws>.
##
InstallGlobalFunction(GrowthFunctionOfCosetRepresentatives,
function(rws,subrws)
  local ns, cosrws, fsa, is, gf;
  ns := NumberSubgroupRWS(rws,subrws);
  if ns = fail then
    Error("Second argument of GrowthFunctionOn... is not a subRWS of first.");
  fi;
  cosrws := rws!.cosrws[ns];

  if IsBound(cosrws!.reductionFSA) then
     fsa := cosrws!.reductionFSA;
     #We need to change initial state to get the growth correct
     is := fsa.initial[1];
     fsa.initial[1] := TargetDFA(fsa,Length(rws!.alphabet)+1,is);
     gf := GrowthFSA(fsa);
     fsa.initial[1] := is;
     return gf;
  fi;
  if IsBound(cosrws!.wa) then
     return GrowthFSA(cosrws!.wa);
  fi;

  Error("Growth function not available.");
end);

############################################################################
##
#F  ResetRewritingSystemOnCosets(<rws>,<subrws>)
##
##
InstallGlobalFunction(ResetRewritingSystemOnCosets,
function(rws,subrws)
  ResetCosetsRWS(rws,subrws);
end);
