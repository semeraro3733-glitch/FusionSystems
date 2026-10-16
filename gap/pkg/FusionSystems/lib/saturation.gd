#############################################################################
##
##  saturation.gd          FusionSystems package
##
##  The saturation test, O_p(F) and the focal subgroup.
##
DeclareProperty( "IsSaturated", IsFusionSystem );
DeclareOperation( "IsReceptive", [ IsFusionSystem, IsGroup ] );
DeclareOperation( "HasSurjectivityProperty", [ IsFusionSystem, IsGroup ] );
DeclareAttribute( "OpF", IsFusionSystem );
DeclareAttribute( "FocalSubgroup", IsFusionSystem );
DeclareProperty( "IsOpFTrivial", IsFusionSystem );
DeclareProperty( "IsPPerfectFusionSystem", IsFusionSystem );
DeclareGlobalFunction( "FS_CentricClassesInEssentials" );
DeclareGlobalFunction( "FS_SaturationTest" );
DeclareGlobalFunction( "FS_IsSaturatedWithReason" );
DeclareGlobalFunction( "FS_CommutatorWithAutomorphisms" );
