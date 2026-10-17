Read( "/home/user/FusionSystems/order38/scripts/stage2.g" );
SetInfoLevel( InfoFusionSystems, 0 );
LOGF := "/home/user/FusionSystems/order38/logs/reference_3d4.log";;
out := OutputTextFile( LOGF, false );; SetPrintFormattingStatus( out, false );;
Say := function( arg ) CallFuncList( AppendTo, Concatenation( [ out ], arg ) ); end;;
Read( "/home/user/FusionSystems/order38/data/d4_sylow_model.g" );
P := PcGroupCode( FS38_D4Model, 6561 );;
t := Runtime();;
iso := IsomorphismGroups( P, SmallGroup( 6561, 2221 ) );;
Say( "3D4 model (a = 3) isomorphic to SmallGroup(6561,2221): ", iso <> fail, " (", Runtime() - t, " ms)\n" );
# the small case a = 1: order 81
G := PrimitiveGroup( 819, 5 );;
S81 := SylowSubgroup( G, 3 );;
Say( "Syl_3(3D4(2)) = SmallGroup", IdGroup( S81 ), "\n" );
refs := [ [ "3D4(2)", G ], [ "3D4(2).3", PrimitiveGroup( 819, 6 ) ], [ "PSL3(19)", PSL( 3, 19 ) ], [ "PGL3(19)", PGL( 3, 19 ) ], [ "PSU3(17)", PSU( 3, 17 ) ], [ "PGU3(17)", PGU( 3, 17 ) ] ];;
REF := [];;
for r in refs do
    t := Runtime();
    Sr := SylowSubgroup( r[2], 3 );
    Say( r[1], ": |G| = ", Size( r[2] ), ", |S| = ", Size( Sr ), ", S = SmallGroup", IdGroup( Sr ), "\n" );
    if Size( Sr ) <> 81 then continue; fi;
    F := GroupFusionSystem( r[2], 3 );
    Say( "    ", FS38_DescLine( FS38_Describe( F ) ), "; O_3 = 1: ", IsOpFTrivial( F ), ", O^3 = F: ", IsPPerfectFusionSystem( F ), " (", Runtime() - t, " ms)\n" );
    Add( REF, [ r[1], F ] );
od;
S := SmallGroup( 81, 9 );;
L := AllFusionSystems( S );;
Say( Length( L ), " fusion systems on SmallGroup(81,9) with O_3 = 1 = O^3:\n" );
for i in [ 1 .. Length( L ) ] do
    Say( "F", i, ": ", FS38_DescLine( FS38_Describe( L[i] ) ), "\n" );
    for r in REF do
        if IsIsomorphicFusionSystems( L[i], r[2] ) then Say( "    = F_S(", r[1], ")\n" ); fi;
    od;
od;
Say( "DONE\n" );
CloseStream( out );
QUIT;
