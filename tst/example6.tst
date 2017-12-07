##############################################################################
##
#W  example6.tst                 KBMag Package                      Derek Holt
##
gap> START_TEST( "KBMag package: example6.tst" );
gap> fsa_infolevel_saved := InfoLevel( InfoFSA );; 
gap> SetInfoLevel( InfoFSA, 0 );; 
gap> rws_infolevel_saved := InfoLevel( InfoRWS );; 
gap> SetInfoLevel( InfoRWS, 0 );; 
gap> ## SubSection 1.15, Example 1  
gap> F := FreeGroup( "a", "b", "c" );;
gap> a:=F.1;;  b:=F.2;;  c:=F.3;;
gap> G := F/[b^3,c^3,(b*c)^4,(b*c^-1)^5,a^-1*b^-1*c*b*c*b^-1*c*b*c^-1];
<fp group on the generators [ a, b, c ]>
gap> R := KBMAGRewritingSystem( G );
rec(
           isRWS := true,
          silent := true,
  generatorOrder := [_g1,_g2,_g3,_g4,_g5,_g6],
        inverses := [_g2,_g1,_g4,_g3,_g6,_g5],
        ordering := "shortlex",
       equations := [
         [_g3^2,_g4],
         [_g5^2,_g6],
         [(_g3*_g5)^2,(_g6*_g4)^2],
         [(_g3*_g6)^2*_g3,(_g5*_g4)^2*_g5],
         [_g2*_g4*_g5*_g3*_g5,_g5*_g4*_g6*_g3]
       ]
)

gap> S := SubgroupOfKBMAGRewritingSystem( R, [ a^3, c*a^2 ] );
rec(
           isRWS := true,
          silent := true,
  generatorOrder := [_x1,_X1,_x2,_X2],
        inverses := [_X1,_x1,_X2,_x2],
        ordering := "shortlex",
       equations := [
       ]
)

gap> KnuthBendixOnCosetsWithSubgroupRewritingSystem( R, S );
true
gap> Index( R, S );
18
gap> IsReducedCosetRepresentative( R, S, b*a*b*a );
false
gap> ReducedFormOfCosetRepresentative( R, S, b*a*b*a );
b^-1*a^-1
gap> EnumerateReducedCosetRepresentatives( R, S, 0, 4 );
[ <identity ...>, a, a*b, a*b*c, a*b^-1, a^-1, a^-1*b, a^-1*b*c, a^-1*b^-1, 
  b, b*c, b*c*a, b*c*a^-1, b*c^-1, b^-1, b^-1*a, b^-1*a^-1, b^-1*a^-1*b ]
gap> SS := RewritingSystemOfSubgroupOfKBMAGRewritingSystem( R, S );;
gap> Size( SS );
60
gap> ## SetInfoLevel( InfoFSA, fsa_infolevel_saved );; 
gap> ## SetInfoLevel( InfoRWS, rws_infolevel_saved );; 
gap> STOP_TEST( "example6.tst", 10000 );
