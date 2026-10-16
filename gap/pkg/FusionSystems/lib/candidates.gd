#############################################################################
##
##  candidates.gd          FusionSystems package
##
##  Candidates for the automizers Aut_F(P) of proto-essential subgroups.
##
DeclareGlobalFunction( "FS_OutData" );
DeclareGlobalFunction( "FS_SubgroupClassesWithPPart" );
DeclareGlobalFunction( "FS_LatticeFeasible" );
DeclareGlobalFunction( "ProtoEssentialAutomizerCandidates" );
DeclareGlobalFunction( "FS_FrameCandidates" );
DeclareGlobalFunction( "FS_AutBGenerators" );
DeclareGlobalFunction( "FS_BorelCompatibleCandidates" );
DeclareGlobalFunction( "FS_CoreCompatible" );
DeclareGlobalFunction( "FS_TransportCandidate" );

BindGlobal( "FS_Options", rec( latticeBound := 20000000, tupleBound := 200000 ) );
