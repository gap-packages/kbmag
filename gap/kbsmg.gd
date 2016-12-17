#############################################################################
##
#W  kbsmg.gd           GAP library                                 Derek Holt
##
#Y  Copyright (C)  1997,  Lehrstuhl D fuer Mathematik,  RWTH Aachen,  Germany
#Y  (C) 1998 School Math and Comp. Sci., University of St.  Andrews, Scotland
##
##  This file contains the declarations for Knuth Bendix Rewriting Systems
##


############################################################################
##
#C  IsKnuthBendixRewritingSystem(<obj>)
## 
##  This is the category of Knuth Bendix rewriting systems.	
##  DO WE NEED A NEW CATEGORY OF KBMAG REWRITING SYSTEMS???
##
##DeclareCategory("IsKnuthBendixRewritingSystem", IsRewritingSystem);

############################################################################
##
#F  CreateKBMAGRewritingSystemOfFpSemigroup(<S>,<lt>)
##  
##
DeclareGlobalFunction("CreateKBMAGRewritingSystemOfFpSemigroup");

############################################################################
##
#F  CreateKBMAGRewritingSystemOfFpMonoid(<S>,<lt>)
##  
##
DeclareGlobalFunction("CreateKBMAGRewritingSystemOfFpMonoid");

############################################################################
##
#F  CreateKBMAGRewritingSystemOfFpGroup(<S>,<lt>)
##  
##
DeclareGlobalFunction("CreateKBMAGRewritingSystemOfFpGroup");

#############################################################################
##
#O  KBMAGRewritingSystem(<rws>)
##
##
DeclareOperation("KBMAGRewritingSystem",[IsSemigroup]);

#############################################################################
##
#O  WordMonoidOfRewritingSystem(<rws>)
##
##
DeclareOperation("WordMonoidOfRewritingSystem",[IsKnuthBendixRewritingSystem]);

############################################################################
##
#F  ExternalWordToInternalWordOfRewritingSystem(<R>,<w>)
##  
## Convert a word in the external free structure of a rewriting system
## to its corresponding word in the internal word monoid.
##
DeclareGlobalFunction("ExternalWordToInternalWordOfRewritingSystem");

############################################################################
##
#F  InternalWordToExternalWordOfRewritingSystem(<R>,<w>)
##  
## Convert a word in the external free structure of a rewriting system
## to its corresponding word in the internal word monoid.
##
DeclareGlobalFunction("InternalWordToExternalWordOfRewritingSystem");

############################################################################
##
#O  Alphabet(<rws>)
##
##
DeclareAttribute("Alphabet",IsKnuthBendixRewritingSystem);

############################################################################
##
#F  OptionsRecordOfKBMAGRewritingSystem(<R>)
##  
##  This is a record whose components are optional parameters controlling
##  the Knuth-Bendix completion process, and can be set by the user.
##
DeclareGlobalFunction("OptionsRecordOfKBMAGRewritingSystem");

############################################################################
##
#F  ReorderAlphabetOfKBMAGRewritingSystem(<R>,<perm>)
##  
## <perm> should be a permutation of [1..Size of Alphabet of <rws>].
## The order of the alphabet is part of the definition of the
## ordering of the rewriting-system.
##
DeclareGlobalFunction("ReorderAlphabetOfKBMAGRewritingSystem");

############################################################################
##
#F  SetOrderingOfKBMAGRewritingSystem(<R>,<ordering-string>[,list])
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
DeclareGlobalFunction("SetOrderingOfKBMAGRewritingSystem");

############################################################################
##
#F OrderingOfKBMAGRewritingSystem(<R>)
##  
## Prints out a description of the ordering.
##
DeclareGlobalFunction("OrderingOfKBMAGRewritingSystem");

#############################################################################
##
#O  KnuthBendix(<rws>)
##
##  Apply the Knuth-Bendix completion algorithm to <rws>
##
DeclareOperation("KnuthBendix",[IsKnuthBendixRewritingSystem]);

#############################################################################
##
#F  AutomaticStructure(<rws>[,<large>,<filestore>,<diff1>])
##
##  Attempt to compute a shortlex automatix structure for <rws>
##  <large>,<filestore>and<diff1> are optional boolean parameters.
##  <large> is the most useful and should be used for difficult examples.
##
DeclareGlobalFunction("AutomaticStructure");

#############################################################################
##
#O  EnumerateReducedWords(<rws>,<minlength>,<maxlength>)
##
##  return a list of the reduced words in the rewriting system having lengths
##  between <minlength> and <maxlength> 
##
DeclareOperation("EnumerateReducedWords",
                           [IsKnuthBendixRewritingSystem,IsInt,IsInt]);

#############################################################################
##
#A  IsReducedWord(<rws>,<w>)
##
##  is w in reduced form?
##
DeclareOperation("IsReducedWord",
                           [IsKnuthBendixRewritingSystem,IsAssocWord]);

#############################################################################
##
#A  ReducedWord(<rws>,<w>)
##
##  reduced form of w - same as ReducedForm
##
DeclareOperation("ReducedWord",
                           [IsKnuthBendixRewritingSystem,IsAssocWord]);

############################################################################
##
#F GrowthFunction(<rws>)
##
## The growth function of <rws> if available (a rational function).
##
DeclareGlobalFunction("GrowthFunction");

############################################################################
##
#F ReductionAutomaton(<rws>)
##
## The reduction automaton of <rws> if available.
##
DeclareGlobalFunction("ReductionAutomaton");

############################################################################
##
#F WordAcceptor(<rws>)
##
##
DeclareGlobalFunction("WordAcceptor");

############################################################################
##
#F FirstWordDifferenceAutomaton(<rws>)
##
##
DeclareGlobalFunction("FirstWordDifferenceAutomaton");

############################################################################
##
#F SecondWordDifferenceAutomaton(<rws>)
##
##
DeclareGlobalFunction("SecondWordDifferenceAutomaton");

############################################################################
##
#F GeneralMultiplier(<rws>)
##
##
DeclareGlobalFunction("GeneralMultiplier");

############################################################################
##
#F  ResetRewritingSystem(<rws>)
##
##  Reset after an earlier run of KnuthBendix or AutomaticStructure
##
DeclareGlobalFunction("ResetRewritingSystem");

#############################################################################
##
#F  SubgroupOfKBMAGRewritingSystem(<rws>,<H>)
##
## Defines a subgroup of a KBMAGRewritingSystem <rws>, which will itself
## be a KBMAG rewriting system, but initially without rules.
## This is only applicable if <rws> is defined from a group.
## <H> needs to define a subgroup of the underlying free group of <rws>,
##  either as a subgroup or a s a list of generators.
##
DeclareGlobalFunction("SubgroupOfKBMAGRewritingSystem");

#############################################################################
##
#A  IsConfluentOnCosets(<rws>,<subrws>)
##
##
DeclareOperation("IsConfluentOnCosets",
        [IsKnuthBendixRewritingSystem,IsKnuthBendixRewritingSystem]);

#############################################################################
##
#O  KnuthBendixOnCosets(<rws>,<subrws>,)
##
##  Apply the Knuth-Bendix completion algorithm on a cosets rewriting
##  system of <rws> with respect to the subgroup corresponding to <subrws>
##  (<subrws> should be the result returned by a call of
##  SubgroupOfKBMAGRewritingSystem. If the optional <subgens> is 'true',
## then in addition a confluent rewriting system for <subrws> is
## computed.
##
DeclareOperation("KnuthBendixOnCosets",
    [IsKnuthBendixRewritingSystem,IsKnuthBendixRewritingSystem]);

#############################################################################
##
#O  KnuthBendixOnCosetsWithSubgroupRewritingSystem(<rws>,<subrws>)
##
## Same as KnuthBendixOnCosets but
## in addition a confluent rewriting system for <subrws> is computed.
##
DeclareOperation("KnuthBendixOnCosetsWithSubgroupRewritingSystem",
    [IsKnuthBendixRewritingSystem,IsKnuthBendixRewritingSystem]);

#############################################################################
##
#F  RewritingSystemOfSubgroupOfKBMAGRewritingSystem(<rws>,<subrws>)
##
##  Returns the rewriting system computed by 
##  KnuthBendixOnCosetsWithSubgroupRewritingSystem
##
DeclareGlobalFunction("RewritingSystemOfSubgroupOfKBMAGRewritingSystem");

#############################################################################
##
#F  AutomaticStructureOnCosets(<rws>,<subrws>,[large,filestore,diff1])
##
##  Attempt to compute a shortlex coset automatix structure for <rws>
##  <large>,<filestore>and<diff1> are optional boolean parameters.
##  <large> is the most useful and should be used for difficult examples.
##
DeclareGlobalFunction("AutomaticStructureOnCosets");

#############################################################################
##
#F  AutomaticStructureOnCosetsWithSubgroupPresentation(<rws>,<subrws>,
##                                        [large,filestore,diff1])
##
##  Same as AutomaticStructureOnCosets but compute subgroup
##  presentation in addition.
##
DeclareGlobalFunction("AutomaticStructureOnCosetsWithSubgroupPresentation");

#############################################################################
##
#F  PresentationOfSubgroupOfKBMAGRewritingSystem(<rws>,<subrws>)
##
##  Returns the subgroup presentation computed by 
##  AutomaticStructureOnCosetsWithSubgroupPresentation
##
DeclareGlobalFunction("PresentationOfSubgroupOfKBMAGRewritingSystem");

#############################################################################
##
#O  ReducedFormOfCosetRepresentative(<rws>,<subrws>,<w>)
##
## Reduce coset representative of word w - cosets of <subrws> in <rws>.
##
DeclareOperation("ReducedFormOfCosetRepresentative",
    [IsKnuthBendixRewritingSystem,IsKnuthBendixRewritingSystem,IsAssocWord]);

#############################################################################
##
#O  ReducedCosetRepresentative(<rws>,<subrws>,<w>)
##
## Same as ReducedFormOfCosetRepresentative
##
DeclareOperation("ReducedCosetRepresentative",
    [IsKnuthBendixRewritingSystem,IsKnuthBendixRewritingSystem,IsAssocWord]);

#############################################################################
##
#A  IsReducedCosetRepresentative(<rws>,<subrws>,<w>)
##
##  is w in reduced form as a coset representative?
##
DeclareOperation("IsReducedCosetRepresentative",
    [IsKnuthBendixRewritingSystem,IsKnuthBendixRewritingSystem,IsAssocWord]);

#############################################################################
##
#O  EnumerateReducedCosetRepresentatives(<rws>,<subrws>,<minlength>,<maxlength>)
##
##  return a list of the reduced words for coset representatives in the
##  subgroup rewriting system <subrws> in <rws> having lengths
##  between <minlength> and <maxlength> 
##
DeclareOperation("EnumerateReducedCosetRepresentatives",
     [IsKnuthBendixRewritingSystem,IsKnuthBendixRewritingSystem,IsInt,IsInt]);

############################################################################
##
#F GrowthFunctionOfCosetRepresentatives(<rws>,<subrws>)
##
## The growth function of the reduced words for coset representatives in
## the subgroup rewriting system <subrws> in <rws> (a rational function).
##
DeclareGlobalFunction("GrowthFunctionOfCosetRepresentatives");


############################################################################
##
#F  ResetRewritingSystemOnCosets(<rws>,<subrws>)
##
##  Reset after an earlier run of KnuthBendix or AutomaticStructure
##  On Cosets
##
DeclareGlobalFunction("ResetRewritingSystemOnCosets");

#############################################################################
##
#V  KBMAG_REW
##
##  `KBMAG_REW', contains the KB functions for library level rewriting
##  systems provided using KBMAG.
BindGlobal("KBMAG_REW",rec(name:="KBMAG Knuth-Bendix"));


#############################################################################
##
#E

