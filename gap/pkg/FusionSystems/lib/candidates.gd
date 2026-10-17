#############################################################################
##
##  candidates.gd          FusionSystems package
##
##  Candidates for the automizers Aut_F(P) of proto-essential subgroups.
##
DeclareGlobalFunction( "FS_OutData" );
DeclareGlobalFunction( "FS_CandCount" );
DeclareAttribute( "FSSylowNormalizer", IsGroup, "mutable" );
DeclareGlobalFunction( "FS_SubgroupClassesWithPPart" );
DeclareGlobalFunction( "FS_LatticeFeasible" );
DeclareGlobalFunction( "ProtoEssentialAutomizerCandidates" );
DeclareGlobalFunction( "FS_FrameCandidates" );
DeclareGlobalFunction( "FS_AutBGenerators" );
DeclareGlobalFunction( "FS_BorelCompatibleCandidates" );
DeclareGlobalFunction( "FS_CoreCompatible" );
DeclareGlobalFunction( "FS_TransportCandidate" );

BindGlobal( "FS_Options", rec( latticeBound := 500000, solvableLatticeBound := 10^6, perfectBound := 10^11, tupleBound := 200000,
                               radicalLatticeBound := 500000, hallLatticeBound := 10^6, conjugateBound := 10^5, smallNormalizerBound := 2*10^5 ) );
## FS_Diagnostics.incomplete is set to true whenever an enumeration of
## automizer candidates is known to be incomplete (see FS_CandidatesInGroup);
## callers may reset it before and inspect it after a computation.
BindGlobal( "FS_Diagnostics", rec( incomplete := false, messages := [] ) );
DeclareGlobalFunction( "FS_PSolubleCyclicCandidates" );
