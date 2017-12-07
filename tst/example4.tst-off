##############################################################################
##
#W  example4.tst                 KBMag Package                      Derek Holt
##
gap> START_TEST( "KBMag package: example4.tst" );
gap> fsa_infolevel_saved := InfoLevel( InfoFSA );; 
gap> SetInfoLevel( InfoFSA, 0 );; 
gap> rws_infolevel_saved := InfoLevel( InfoRWS );; 
gap> SetInfoLevel( InfoRWS, 0 );; 

gap> ## SubSection 1.9, Example 4 
gap> ## This is an example of the use of the Knuth-Bendix algorithm 
gap> ## to prove the nilpotence of a finitely presented group. 
gap> ## (The method is due to Sims, described in Chapter 11.8 of [Sim94].) 
gap> ## This example is of intermediate difficulty, and demonstrates the 
gap> ## necessity of using the maxstoredlen control parameter.
gap> ## The group is ⟨a,b|[b,a,b],[b,a,a,a,a],[b,a,a,a,b,a,a]⟩ 
gap> ## with left-normed commutators. The first step in the method is to 
gap> ## check that there is a maximal nilpotent quotient of the group, 
gap> ## for which we could use, for example, the GAP NilpotentQuotient command, 
gap> ## from the package “nq”. We find that there is a maximal such quotient, 
gap> ## and it has class 7, and the layers going down the lower central series 
gap> ## have the abelian structures [0,0], [0], [0], [0], [0], [2], [2]. 
gap> ## By using the stand-alone C nilpotent quotient program, it is possible 
gap> ## to find a power-commutator presentation of this maximal quotient. 
gap> ## We now construct a new presentation of the same group, by introducing 
gap> ## the generators in this power-commutator presentation, together with 
gap> ## their definitions as powers or commutators of earlier generators. 
gap> ## This new presentation that we use as input for the Knuth-Bendix program. 
gap> ## Again we use the recursive ordering, but this time we will be careful 
gap> ## to introduce the generators in the correct order in the first place!
gap> ## 
gap> F := FreeGroup( "h", "g", "f", "e", "d", "c", "b", "a" );;
gap> h:=F.1;;  g:=F.2;;  f:=F.3;;  e:=F.4;; 
gap> d:=F.5;;  c:=F.6;;  b:=F.7;;  a:=F.8;;
gap> G := F/[Comm(b,a)*c^-1, Comm(c,a)*d^-1, Comm(d,a)*e^-1,
>            Comm(e,b)*f^-1, Comm(f,a)*g^-1, Comm(g,b)*h^-1,
>            Comm(g,a), Comm(c,b), Comm(e,a)];;
gap> R := KBMAGRewritingSystem( G );
rec(
           isRWS := true,
  generatorOrder := [_g1,_g2,_g3,_g4,_g5,_g6,_g7,_g8,_g9,_g10,_g11,_g12,_g13,
                     _g14,_g15,_g16],
        inverses := [_g2,_g1,_g4,_g3,_g6,_g5,_g8,_g7,_g10,_g9,_g12,_g11,_g14,
                     _g13,_g16,_g15],
        ordering := "shortlex",
       equations := [
         [_g14*_g16*_g13,_g11*_g16],
         [_g12*_g16*_g11,_g9*_g16],
         [_g10*_g16*_g9,_g7*_g16],
         [_g8*_g14*_g7,_g5*_g14],
         [_g6*_g16*_g5,_g3*_g16],
         [_g4*_g14*_g3,_g1*_g14],
         [_g4*_g16,_g16*_g4],
         [_g12*_g14,_g14*_g12],
         [_g8*_g16,_g16*_g8]
       ]
)
gap> SetOrderingOfKBMAGRewritingSystem( R, "recursive" );
gap> ## A little experimentation reveals that this example works best 
gap> ## when only those equations with left and right hand sides of 
gap> ## lengths at most 10 are kept.
gap> O := OptionsRecordOfKBMAGRewritingSystem( R );;
gap> O.maxstoredlen := [10,10];;
gap> SetInfoLevel( InfoRWS, 2 );
gap> KnuthBendix( R );
false 
gap> ## Now it is essential to re-run with the ‘maxstoredlen’ limit removed 
gap> ## to check that the system really is confluent.
gap> Unbind( O.maxstoredlen );
gap> KnuthBendix( R );
#I  External Knuth-Bendix program complete.
#I  System computed is confluent.
true
gap> ## #In fact, in this case, we did have a confluent set already. 
gap> ## Inspection of the confluent set now reveals it to be precisely 
gap> ## a power-commutator presentation of a nilpotent group, and so we 
gap> ## have proved that the group we started with really is nilpotent. 
gap> ## Of course, this means also that it is equal to its largest 
gap> ## nilpotent quotient, of which we already know the structure.

gap> ## SetInfoLevel( InfoFSA, fsa_infolevel_saved );; 
gap> ## SetInfoLevel( InfoRWS, rws_infolevel_saved );; 
gap> STOP_TEST( "example4.tst", 10000 );
