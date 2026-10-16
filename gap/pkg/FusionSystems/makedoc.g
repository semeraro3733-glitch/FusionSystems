LoadPackage( "GAPDoc" );
SetGapDocLaTeXOptions( "utf8" );
MakeGAPDocDoc( "doc", "manual", [ "../PackageInfo.g" ], "FusionSystems" );
CopyHTMLStyleFiles( "doc" );
GAPDocManualLab( "FusionSystems" );
QUIT;
