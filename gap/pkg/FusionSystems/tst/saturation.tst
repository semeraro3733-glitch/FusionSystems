#############################################################################
##
##  saturation.tst         FusionSystems package
##
##  Saturated and non-saturated systems on 3^{1+2}_+, isomorphism tests.
##
gap> START_TEST( "saturation.tst" );
gap> LoadPackage( "FusionSystems", false );
true
gap> S := ExtraspecialGroup( 27, 3 );;
gap> Es := First( MaximalSubgroups( S ), M -> IsElementaryAbelian( M ) );;
gap> A := AutomorphismGroup( Es );;  n := NiceMonomorphism( A );;
gap> gl := List( GeneratorsOfGroup( Image( n ) ), x -> PreImagesRepresentative( n, x ) );;
gap> sl := List( GeneratorsOfGroup( DerivedSubgroup( Image( n ) ) ), x -> PreImagesRepresentative( n, x ) );;
gap> F1 := FusionSystem( S, [], [ Es ], [ sl ] );
<fusion system on a group of order 3^3 with 1 essential classes>
gap> IsSaturated( F1 );
false
gap> F2 := FusionSystem( S, [], [ Es ], [ gl ] );;
gap> FS_IsSaturatedWithReason( F2 );
[ false, "the surjectivity property fails at a subgroup of order 9" ]
gap> FL := GroupFusionSystem( PSL( 3, 3 ), 3 );;
gap> iso := IsomorphismGroups( UnderlyingGroup( FL ), S );;
gap> FLt := FS_TransportFusionSystem( FL, iso );;
gap> IsSaturated( FLt );
true
gap> IsIsomorphicFusionSystems( FL, FLt );
true
gap> F3 := FusionSystem( S, FLt!.autSgens, [ FLt!.ess[1] ], [ FLt!.essauts[1] ] );;
gap> IsSaturated( F3 ); IsOpFTrivial( F3 ); Size( OpF( F3 ) );
true
false
9
gap> IsIsomorphicFusionSystems( FLt, F3 );
false
gap> F4 := GroupFusionSystem( MathieuGroup( 12 ), 3 );;
gap> IsIsomorphicFusionSystems( FL, F4 );   # L3(3) and M12 have the same 3-fusion
true
gap> OutFSOrder( F4 ); OutFSOrder( FL );
4
4
gap> HasStronglyPEmbeddedSubgroup( SymmetricGroup( 5 ), 5 );
true
gap> HasStronglyPEmbeddedSubgroup( SymmetricGroup( 4 ), 2 );
false
gap> HasStronglyPEmbeddedSubgroup( GL( 2, 5 ), 5 );
true
gap> HasStronglyPEmbeddedSubgroup( AlternatingGroup( 6 ), 3 );
true
gap> STOP_TEST( "saturation.tst", 1 );
