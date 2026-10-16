#############################################################################
##
##  util.gd                FusionSystems package
##
##  Low level helpers: restriction and transport of automorphisms,
##  automizers, conjugacy class bookkeeping and the cheap Parker-Semeraro
##  tests on p-groups.
##
DeclareInfoClass( "InfoFusionSystems" );

DeclareGlobalFunction( "FS_PPart" );
DeclareGlobalFunction( "FS_PcgsOf" );
DeclareGlobalFunction( "FS_HomByImages" );
DeclareGlobalFunction( "FS_IdentityAut" );
DeclareGlobalFunction( "FS_ConjAut" );
DeclareGlobalFunction( "FS_RestrictAut" );
DeclareGlobalFunction( "FS_InducedAutOnQuotient" );
DeclareGlobalFunction( "FS_InverseIso" );
DeclareGlobalFunction( "FS_ComposeHoms" );
DeclareGlobalFunction( "FS_TransportAut" );
DeclareGlobalFunction( "FS_OnImage" );
DeclareGlobalFunction( "FS_AutGroupByGenerators" );
DeclareGlobalFunction( "FS_Automizer" );
DeclareGlobalFunction( "FS_AutomizerGenerators" );
DeclareGlobalFunction( "FS_InnerAutGenerators" );
DeclareGlobalFunction( "FS_IsCentricIn" );
DeclareGlobalFunction( "FS_SubgroupInvariants" );
DeclareGlobalFunction( "FS_ClassPosition" );
DeclareGlobalFunction( "FS_IsQuaternionOrCyclic" );
DeclareGlobalFunction( "FS_IsStronglypSylow" );
DeclareGlobalFunction( "FS_RadicalTest" );
DeclareGlobalFunction( "FS_CheapProtoEssentialTest" );
DeclareGlobalFunction( "FS_LargestInvariantSubgroup" );
DeclareGlobalFunction( "FS_SubgroupsContaining" );
DeclareGlobalFunction( "FS_IsSylowIn" );
