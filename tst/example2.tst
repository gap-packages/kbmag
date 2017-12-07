##############################################################################
##
#W  example2.tst                 KBMag Package                      Derek Holt
##
gap> START_TEST( "KBMag package: example2.tst" );
gap> fsa_infolevel_saved := InfoLevel( InfoFSA );; 
gap> SetInfoLevel( InfoFSA, 0 );; 
gap> rws_infolevel_saved := InfoLevel( InfoRWS );; 
gap> SetInfoLevel( InfoRWS, 0 );; 
gap> ## SubSection 1.9, Example 2 
gap> ## The Fibonacci group F(2, 5) defined by a semigroup rather than a 
gap> ## group presentation. Interestingly this defines the same structure 
gap> ## (although it would not do so for F(2, r) with r even).
gap> S := FreeSemigroup( 5 );; 
gap> a:=S.1;;  b:=S.2;;  c:=S.3;;  d:=S.4;;  e:=S.5;;
gap> Q := S/[ [a*b,c], [b*c,d], [c*d,e], [d*e,a], [e*a,b] ];
<fp semigroup on the generators [ s1, s2, s3, s4, s5 ]>
gap> R:=KBMAGRewritingSystem(Q);
rec(
           isRWS := true,
          silent := true,
  generatorOrder := [_s1,_s2,_s3,_s4,_s5],
        inverses := [,,,,],
        ordering := "shortlex",
       equations := [
         [_s1*_s2,_s3],
         [_s2*_s3,_s4],
         [_s3*_s4,_s5],
         [_s4*_s5,_s1],
         [_s5*_s1,_s2]
       ]
)

gap> KnuthBendix( R );
true
gap> Size( R );
11
gap> EnumerateReducedWords( R, 0, 4 );
[ s1, s1^2, s1^2*s4, s1*s3, s1*s4, s2, s2^2, s2*s5, s3, s4, s5 ]
gap> ## Let’s do the same thing using the "recursive" ordering.
gap> SetOrderingOfKBMAGRewritingSystem( R, "recursive" );
gap> KnuthBendix( R );
true
gap> Size( R );
11
gap> EnumerateReducedWords( R, 0, 11 );
[ s1, s1^2, s1^3, s1^4, s1^5, s1^6, s1^7, s1^8, s1^9, s1^10, s1^11 ]
gap> ## SetInfoLevel( InfoFSA, fsa_infolevel_saved );; 
gap> ## SetInfoLevel( InfoRWS, rws_infolevel_saved );; 
gap> STOP_TEST( "example2.tst", 10000 );
