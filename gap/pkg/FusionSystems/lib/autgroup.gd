#############################################################################
##
##  autgroup.gd            FusionSystems package
##
##  A handle for the automorphism group of a p-group X.  All group
##  theoretic computations with subgroups of Aut(X) are done in a model
##  group: a pc group (via the autpgrp package) when Aut(X) is soluble, and
##  a permutation group otherwise.  Automorphisms are translated to and from
##  the model with the functions FS_AutToModel and FS_AutFromModel.
##
DeclareAttribute( "FSAutHandle", IsGroup, "mutable" );

DeclareGlobalFunction( "FS_AutHandle" );
DeclareGlobalFunction( "FS_AutToModel" );
DeclareGlobalFunction( "FS_AutFromModel" );
DeclareGlobalFunction( "FS_AutSubgroup" );
DeclareGlobalFunction( "FS_AutSubgroupGenerators" );
DeclareGlobalFunction( "FS_AutPCore" );
DeclareGlobalFunction( "FS_AutInn" );
DeclareGlobalFunction( "FS_AutOrbitStabilizer" );
DeclareGlobalFunction( "FS_AutStabilizer" );
DeclareGlobalFunction( "FS_AutRepresentativeAction" );
DeclareGlobalFunction( "FS_ExponentsAutPGroup" );
