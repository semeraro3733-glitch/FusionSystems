#############################################################################
##
##  testall.g              FusionSystems package
##
##  Run all tests:  gap -A -l ";<root>" tst/testall.g   or
##  Read( Filename( DirectoriesPackageLibrary( "FusionSystems", "tst" ), "testall.g" ) );
##
LoadPackage( "FusionSystems" );
TestDirectory( DirectoriesPackageLibrary( "FusionSystems", "tst" ),
               rec( exitGAP := true, testOptions := rec( compareFunction := "uptowhitespace" ) ) );
FORCE_QUIT_GAP( 1 );
