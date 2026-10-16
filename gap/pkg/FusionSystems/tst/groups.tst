#############################################################################
##
##  groups.tst             FusionSystems package
##
##  Fusion systems of finite groups: saturation, automizers, F-conjugacy.
##
gap> START_TEST( "groups.tst" );
gap> LoadPackage( "FusionSystems", false );
true
gap> CheckGroup := function( G, p )
>   local F, S, iso, cls, P, P0, ok, i, j;
>   F := GroupFusionSystem( G, p );
>   S := UnderlyingGroup( F ); iso := F!.iso;
>   ok := FS_IsSaturatedWithReason( F )[1];
>   cls := Filtered( List( ConjugacyClassesSubgroups( S ), Representative ), P -> Size( P ) > 1 );
>   for P in cls do
>     P0 := PreImage( iso, P );
>     if Size( AutF( F, P ) ) <> Index( Normalizer( G, P0 ), Centralizer( G, P0 ) ) then ok := false; fi;
>   od;
>   for i in [ 1 .. Length( cls ) ] do for j in [ i + 1 .. Length( cls ) ] do
>     if Size( cls[i] ) = Size( cls[j] ) and
>        IsFConjugate( F, cls[i], cls[j] ) <> IsConjugate( G, PreImage( iso, cls[i] ), PreImage( iso, cls[j] ) ) then
>       ok := false;
>     fi;
>   od; od;
>   return [ ok, OutFSOrder( F ), List( EssentialSubgroups( F ), Size ) ];
> end;;
gap> CheckGroup( SymmetricGroup( 4 ), 2 );
[ true, 1, [ 4 ] ]
gap> CheckGroup( PSL( 3, 3 ), 3 );
[ true, 4, [ 9, 9 ] ]
gap> CheckGroup( AlternatingGroup( 6 ), 2 );
[ true, 1, [ 4, 4 ] ]
gap> CheckGroup( PSp( 4, 3 ), 3 );
[ true, 2, [ 27, 27 ] ]
gap> CheckGroup( AlternatingGroup( 9 ), 3 );
[ true, 2, [ 27, 9 ] ]
gap> CheckGroup( PSL( 3, 5 ), 5 );
[ true, 16, [ 25, 25 ] ]
gap> CheckGroup( MathieuGroup( 12 ), 3 );
[ true, 4, [ 9, 9 ] ]
gap> F := GroupFusionSystem( PSU( 4, 3 ), 3 );;
gap> [ OutFSOrder( F ), List( EssentialSubgroups( F ), Size ), List( EssentialAutomizers( F ), Size ) ];
[ 4, [ 243, 81 ], [ 3888, 29160 ] ]
gap> FS_IsSaturatedWithReason( F );
[ true ]
gap> IsOpFTrivial( F ); IsPPerfectFusionSystem( F );
true
true
gap> S := UnderlyingGroup( F );;
gap> Z := Center( S );;
gap> Size( AutF( F, Z ) );
2
gap> IsFCentric( F, Z );
false
gap> E := First( EssentialSubgroups( F ), E -> Size( E ) = 81 );;
gap> IsFCentric( F, E ); IsFullyNormalized( F, E ); IsFullyAutomized( F, E ); IsFRadical( F, E );
true
true
true
true
gap> HasSurjectivityProperty( F, E );
true
gap> STOP_TEST( "groups.tst", 1 );
