#############################################################################
##
##  iso.gd                 FusionSystems package
##
##  Isomorphism of fusion systems.
##
DeclareOperation( "IsIsomorphicFusionSystems", [ IsFusionSystem, IsFusionSystem ] );
DeclareOperation( "IsomorphismFusionSystems", [ IsFusionSystem, IsFusionSystem ] );
DeclareGlobalFunction( "FS_IsContainedIn" );
DeclareGlobalFunction( "FS_TransportFusionSystem" );
DeclareGlobalFunction( "FS_IsomorphismFusionSystemsSameS" );
DeclareGlobalFunction( "FS_BClassOrbitStabilizer" );
