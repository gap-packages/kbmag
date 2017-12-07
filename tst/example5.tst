##############################################################################
##
#W  example5.tst                 KBMag Package                      Derek Holt
##
gap> START_TEST( "KBMag package: example5.tst" );
gap> fsa_infolevel_saved := InfoLevel( InfoFSA );; 
gap> SetInfoLevel( InfoFSA, 0 );; 
gap> rws_infolevel_saved := InfoLevel( InfoRWS );; 
gap> SetInfoLevel( InfoRWS, 0 );; 
gap> ## SubSection 1.9, Example 5 
gap> ## Our final example illustrates the use of the AutomaticStructure 
gap> ## command, which runs the automatic groups programs. The group has a 
gap> ## balanced symmetrical presentation with 3 generators and 3 relators, 
gap> ## and was originally pro- posed by Heineken as a possible example of 
gap> ## a finite group with such a presentation. 
gap> ## In fact, the AutomaticStructure command proves it to be infinite.
gap> ## 
gap> F := FreeGroup( "a", "b", "c" );;
gap> a:=F.1;;  b:=F.2;;  c:=F.3;;
gap> G := F/[ Comm(a,Comm(a,b))*c^-1, Comm(b,Comm(b,c))*a^-1,
>             Comm(c,Comm(c,a))*b^-1 ];;
gap> R := KBMAGRewritingSystem( G );
rec(
           isRWS := true,
          silent := true,
  generatorOrder := [_g1,_g2,_g3,_g4,_g5,_g6],
        inverses := [_g2,_g1,_g4,_g3,_g6,_g5],
        ordering := "shortlex",
       equations := [
         [_g2*_g4*_g2*_g3*_g1,_g5*_g4*_g2*_g3],
         [_g4*_g6*_g4*_g5*_g3,_g1*_g6*_g4*_g5],
         [_g6*_g2*_g6*_g1*_g5,_g3*_g2*_g6*_g1]
       ]
)

gap> ## SetInfoLevel( InfoRWS, 1 );
gap> AutomaticStructure( R, true );
true
gap> Size( R );
infinity
gap> Order( R, a );
infinity
gap> Order( R, Comm(a,b) );
infinity
gap> #
gap> ## SetInfoLevel( InfoFSA, fsa_infolevel_saved );; 
gap> ## SetInfoLevel( InfoRWS, rws_infolevel_saved );; 
gap> STOP_TEST( "example5.tst", 10000 );
