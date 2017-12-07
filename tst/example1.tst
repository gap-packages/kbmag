##############################################################################
##
#W  example1.tst                 KBMag Package                      Derek Holt
##
gap> START_TEST( "KBMag package: example1.tst" );
gap> fsa_infolevel_saved := InfoLevel( InfoFSA );; 
gap> SetInfoLevel( InfoFSA, 0 );; 
gap> rws_infolevel_saved := InfoLevel( InfoRWS );; 
gap> SetInfoLevel( InfoRWS, 0 );; 
gap> ## SubSection 1.9, Example 1  
gap> ## We start with a easy example - the alternating group A4.
gap> F := FreeGroup( "a", "b" );;
gap> a := F.1;; b := F.2;;
gap> G := F/[ a^2, b^3, (a*b)^3 ];;
gap> R := KBMAGRewritingSystem( G );
rec(
           isRWS := true,
          silent := true,
  generatorOrder := [_g1,_g2,_g3],
        inverses := [_g1,_g3,_g2],
        ordering := "shortlex",
       equations := [
         [_g2^2,_g3],
         [_g1*_g2*_g1,_g3*_g1*_g3]
       ]
)

gap> ## Notice that monoid generators printed as _g1, _g2, _g3 are used
gap> ## internally. These correspond to the group generators a, b, b^-1.
gap> KnuthBendix( R );
true
gap> R;
rec(
           isRWS := true,
     isConfluent := true,
          silent := true,
  generatorOrder := [_g1,_g2,_g3],
        inverses := [_g1,_g3,_g2],
        ordering := "shortlex",
       equations := [
         [_g1^2,IdWord],
         [_g2*_g3,IdWord],
         [_g3*_g2,IdWord],
         [_g2^2,_g3],
         [_g3*_g1*_g3,_g1*_g2*_g1],
         [_g3^2,_g2],
         [_g2*_g1*_g2,_g1*_g3*_g1],
         [_g3*_g1*_g2*_g1,_g2*_g1*_g3],
         [_g1*_g2*_g1*_g3,_g3*_g1*_g2],
         [_g2*_g1*_g3*_g1,_g3*_g1*_g2],
         [_g1*_g3*_g1*_g2,_g2*_g1*_g3]
       ]
)

gap> ## The ‘equations’ field of <R> is now a complete system of rewriting rules
gap> Size(R);
12
gap> EnumerateReducedWords(R,0,12);
[ <identity ...>, a, a*b, a*b*a, a*b^-1, a*b^-1*a, b, b*a, b*a*b^-1, b^-1, 
  b^-1*a, b^-1*a*b ]
gap> ## We have enumerated all of the elements of the group - 
gap> ## note that they are returned as words in the free group F.
gap> ## SetInfoLevel( InfoFSA, fsa_infolevel_saved );; 
gap> ## SetInfoLevel( InfoRWS, rws_infolevel_saved );; 
gap> STOP_TEST( "example1.tst", 10000 );
