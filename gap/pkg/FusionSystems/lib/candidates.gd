#############################################################################
##
##  candidates.gd          FusionSystems package
##
##  Candidates for the automizers Aut_F(P) of proto-essential subgroups.
##
DeclareGlobalFunction( "FS_OutData" );
DeclareAttribute( "FSSylowNormalizer", IsGroup, "mutable" );
DeclareGlobalFunction( "FS_SubgroupClassesWithPPart" );
DeclareGlobalFunction( "FS_LatticeFeasible" );
DeclareGlobalFunction( "ProtoEssentialAutomizerCandidates" );
DeclareGlobalFunction( "FS_FrameCandidates" );
DeclareGlobalFunction( "FS_AutBGenerators" );
DeclareGlobalFunction( "FS_BorelCompatibleCandidates" );
DeclareGlobalFunction( "FS_CoreCompatible" );
DeclareGlobalFunction( "FS_TransportCandidate" );

BindGlobal( "FS_Options", rec( latticeBound := 500000, solvableLatticeBound := 10^9, perfectBound := 10^11, tupleBound := 200000 ) );
