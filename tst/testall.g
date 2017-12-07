##############################################################################
##
#W  testall.g                     KBMag Package                    Derek Holt
##

LoadPackage( "kbmag" ); 
dir := DirectoriesPackageLibrary("kbmag","tst");
TestDirectory(dir, rec(exitGAP := true));
FORCE_QUIT_GAP(1);
