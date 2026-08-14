##############################################################################
##
#W  cosets.tst                    KBMag Package
##
gap> START_TEST( "KBMag package: cosets.tst" );
gap> rws_infolevel_saved := InfoLevel( InfoRWS );;
gap> SetInfoLevel( InfoRWS, 0 );

# Leftover temporary files made a failing computation look like a successful
# one, because success is decided by the presence of a `.success' file that
# an earlier run had created - see issue #30.
gap> LeftoverTmpFiles := function()
>      local pos, dir, base;
>      pos := Length( _KBTmpFileName );
>      while _KBTmpFileName[pos] <> '/' do pos := pos - 1; od;
>      dir := _KBTmpFileName{[1..pos]};
>      base := _KBTmpFileName{[pos+1..Length( _KBTmpFileName )]};
>      return Filtered( DirectoryContents( dir ),
>               f -> Length( f ) >= Length( base )
>                    and f{[1..Length( base )]} = base );
>    end;;
gap> F := FreeGroup( "a", "b" );;
gap> a := F.1;;  b := F.2;;
gap> G := F/[ a^2, b^3 ];;
gap> R := KBMAGRewritingSystem( G );;
gap> S := SubgroupOfKBMAGRewritingSystem( R, [ a ] );;
gap> AutomaticStructureOnCosetsWithSubgroupPresentation( R, S );
true
gap> Index( R, S );
infinity
gap> LeftoverTmpFiles();
[  ]

#
gap> SetInfoLevel( InfoRWS, rws_infolevel_saved );
gap> STOP_TEST( "cosets.tst", 10000 );
