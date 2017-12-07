##############################################################################
##
#W  example3.tst                 KBMag Package                      Derek Holt
##
gap> START_TEST( "KBMag package: example3.tst" );
gap> fsa_infolevel_saved := InfoLevel( InfoFSA );; 
gap> SetInfoLevel( InfoFSA, 0 );; 
gap> rws_infolevel_saved := InfoLevel( InfoRWS );; 
gap> SetInfoLevel( InfoRWS, 0 );; 
gap> ## SubSection 1.9, Example 3 
gap> ## The Heisenberg group - that is, the free 2-generator nilpotent 
gap> ## group of class 2. For this to complete, we need to use the recursive 
gap> ## ordering, and reverse our initial order of generators. 
gap> ## (Alternatively, we could avoid this reversal, by using a “wreathprod” 
gap> ## ordering, and setting the levels of the generators to be 6,5,4,3,2,1.) 
gap> F := FreeGroup( "x", "y", "z" );;
gap> x:=F.1;;  y:=F.2;;  z:=F.3;;
gap> G := F/[Comm(y,x)*z^-1, Comm(z,x), Comm(z,y)];;
gap> R := KBMAGRewritingSystem( G );
rec(
           isRWS := true,
          silent := true,
  generatorOrder := [_g1,_g2,_g3,_g4,_g5,_g6],
        inverses := [_g2,_g1,_g4,_g3,_g6,_g5],
        ordering := "shortlex",
       equations := [
         [_g4*_g2*_g3,_g5*_g2],
         [_g6*_g2,_g2*_g6],
         [_g6*_g4,_g4*_g6]
       ]
)

gap> SetOrderingOfKBMAGRewritingSystem( R, "recursive" );
gap> ReorderAlphabetOfKBMAGRewritingSystem( R, (1,6)(2,5)(3,4) );
gap> R;
rec(
           isRWS := true,
          silent := true,
  generatorOrder := [_g6,_g5,_g4,_g3,_g2,_g1],
        inverses := [_g5,_g6,_g3,_g4,_g1,_g2],
        ordering := "recursive",
       equations := [
         [_g4*_g2*_g3,_g5*_g2],
         [_g6*_g2,_g2*_g6],
         [_g6*_g4,_g4*_g6]
       ]
)

gap> SetInfoLevel( InfoRWS, 1 );
gap> KnuthBendix( R );
#I  Calling external Knuth-Bendix program.
#I  External Knuth-Bendix program complete.
#I  System computed is confluent.
true
gap> R;
rec(
           isRWS := true,
     isConfluent := true,
  generatorOrder := [_g6,_g5,_g4,_g3,_g2,_g1],
        inverses := [_g5,_g6,_g3,_g4,_g1,_g2],
        ordering := "recursive",
       equations := [
         [_g6*_g5,IdWord],
         [_g5*_g6,IdWord],
         [_g4*_g3,IdWord],
         [_g3*_g4,IdWord],
         [_g2*_g1,IdWord],
         [_g1*_g2,IdWord],
         [_g6*_g2,_g2*_g6],
         [_g6*_g4,_g4*_g6],
         [_g4*_g2,_g2*_g4*_g5],
         [_g5*_g2,_g2*_g5],
         [_g6*_g1,_g1*_g6],
         [_g5*_g4,_g4*_g5],
         [_g6*_g3,_g3*_g6],
         [_g3*_g1,_g1*_g3*_g5],
         [_g4*_g1,_g1*_g4*_g6],
         [_g3*_g2,_g2*_g3*_g6],
         [_g5*_g1,_g1*_g5],
         [_g5*_g3,_g3*_g5]
       ]
)

gap> Size( R );
infinity
gap> IsReducedWord( R, z*y*x );
false
gap> ReducedForm( R, z*y*x );
x*y*z^2
gap> IsReducedForm( R, x*y*z^2 );
true
gap> ## SetInfoLevel( InfoFSA, fsa_infolevel_saved );; 
gap> ## SetInfoLevel( InfoRWS, rws_infolevel_saved );; 
gap> STOP_TEST( "example3.tst", 10000 );
