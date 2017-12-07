##############################################################################
##
#W  example7.tst                 KBMag Package                      Derek Holt
##
gap> START_TEST( "KBMag package: example7.tst" );
gap> fsa_infolevel_saved := InfoLevel( InfoFSA );; 
gap> SetInfoLevel( InfoFSA, 0 );; 
gap> rws_infolevel_saved := InfoLevel( InfoRWS );; 
gap> SetInfoLevel( InfoRWS, 0 );; 

gap> ## SubSection 1.15, Example 2  
gap> ## We find a free subgroup of the Fibonacci group F(2, 8). 
gap> ## This example may take about 20 minutes to run on a typical WorkStation.
gap> F := FreeGroup( 8 );;
gap> a:=F.1;; b:=F.2;; c:=F.3;; d:=F.4;; e:=F.5;; f:=F.6;; g:=F.7;; h:=F.8;;
gap> G := F/[ a*b*c^-1, b*c*d^-1, c*d*e^-1, d*e*f^-1,
>             e*f*g^-1, f*g*h^-1, g*h*a^-1, h*a*b^-1 ];;
gap> R := KBMAGRewritingSystem( G );;
gap> S := SubgroupOfKBMAGRewritingSystem( R, [a,e] );;
gap> AutomaticStructureOnCosetsWithSubgroupPresentation( R, S );
gap> P := PresentationOfSubgroupOfKBMAGRewritingSystem( R, S );
<fp group on the generators [ f1, f3 ]>
gap> RelatorsOfFpGroup( P );
[]
gap> Index( R, S );
infinity

gap> ## SetInfoLevel( InfoFSA, fsa_infolevel_saved );; 
gap> ## SetInfoLevel( InfoRWS, rws_infolevel_saved );; 
gap> STOP_TEST( "example7.tst", 10000 );
