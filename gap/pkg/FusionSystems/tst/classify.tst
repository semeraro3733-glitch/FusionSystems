#############################################################################
##
##  classify.tst           FusionSystems package
##
##  AllFusionSystems on small p-groups, compared with the known results
##  (Ruiz-Viruel for extraspecial groups of order p^3, Parker-Semeraro).
##
gap> START_TEST( "classify.tst" );
gap> LoadPackage( "FusionSystems", false );
true
gap> Summ := F -> [ OutFSOrder( F ), List( EssentialSubgroups( F ), Size ),
>      List( [ 1 .. Length( EssentialSubgroups( F ) ) ], i ->
>        Size( EssentialAutomizers( F )[i] ) / Index( EssentialSubgroups( F )[i], Center( EssentialSubgroups( F )[i] ) ) ) ];;
gap> D8 := Image( IsomorphismPcGroup( DihedralGroup( 8 ) ) );;
gap> L := AllFusionSystems( D8 );;  List( L, Summ );
[ [ 1, [ 4, 4 ], [ 6, 6 ] ] ]
gap> ForAny( L, F -> IsIsomorphicFusionSystems( F, GroupFusionSystem( PSL( 2, 7 ), 2 ) ) );
true
gap> L := AllFusionSystems( D8, rec( OpTriv := false, pPerfect := false ) );;  Length( L );
3
gap> E27 := ExtraspecialGroup( 27, 3 );;
gap> L := AllFusionSystems( E27 );;  SortedList( List( L, Summ ) );
[ [ 4, [ 9, 9 ], [ 48, 48 ] ], [ 8, [ 9 ], [ 48 ] ], [ 8, [ 9, 9 ], [ 48, 48 ] ],
  [ 16, [ 9 ], [ 48 ] ] ]
gap> ForAny( L, F -> IsIsomorphicFusionSystems( F, GroupFusionSystem( PSL( 3, 3 ), 3 ) ) );
true
gap> ForAny( L, F -> IsIsomorphicFusionSystems( F, GroupFusionSystem( MathieuGroup( 12 ), 3 ) ) );
true
gap> Length( AllFusionSystems( E27, rec( OpTriv := false, pPerfect := false ) ) );
15
gap> D16 := Image( IsomorphismPcGroup( DihedralGroup( 16 ) ) );;
gap> L := AllFusionSystems( D16 );;  List( L, Summ );
[ [ 1, [ 4, 4 ], [ 6, 6 ] ] ]
gap> SD16 := SmallGroup( 16, 8 );;
gap> L := AllFusionSystems( SD16 );;  List( L, Summ );
[ [ 1, [ 8, 4 ], [ 6, 6 ] ] ]
gap> ForAny( L, F -> IsIsomorphicFusionSystems( F, GroupFusionSystem( PSL( 3, 3 ), 2 ) ) );
true
gap> E125 := ExtraspecialGroup( 125, 5 );;
gap> L := AllFusionSystems( E125 );;  SortedList( List( L, Summ ) );
[ [ 16, [ 25, 25 ], [ 480, 480 ] ], [ 32, [ 25 ], [ 480 ] ], [ 96, [ 25 ], [ 480 ] ] ]
gap> ForAny( L, F -> IsIsomorphicFusionSystems( F, GroupFusionSystem( PSL( 3, 5 ), 5 ) ) );
true
gap> STOP_TEST( "classify.tst", 1 );
