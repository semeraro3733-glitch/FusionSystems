#############################################################################
##
##  examples/run_examples.g        FusionSystems package
##
##  The classification runs reported in the README:
##    * the Sylow 3-subgroup of PSU(4,3) (order 3^6),
##    * the extraspecial group 7^{1+2}_+ (Ruiz-Viruel),
##    * the Sylow 5-subgroup of Alt(30) (order 5^7),
##  each followed by the check that the fusion system of the starting
##  group is recovered (IsIsomorphicFusionSystems).
##
##  Usage:  gap -l ";<root>" examples/run_examples.g   (writes to examples.log)
##
LoadPackage( "FusionSystems" );
SetInfoLevel( InfoFusionSystems, 1 );

LOG := "examples.log";
PrintTo( LOG, "" );
Say := function( arg ) CallFuncList( AppendTo, Concatenation( [ LOG ], arg ) ); CallFuncList( Print, arg ); end;

Summary := function( F )
    return rec( OutFS := OutFSOrder( F ), essentials := List( EssentialSubgroups( F ), Size ),
                OutFE := List( [ 1 .. Length( EssentialSubgroups( F ) ) ], i ->
                    Size( EssentialAutomizers( F )[i] ) / Index( EssentialSubgroups( F )[i], Center( EssentialSubgroups( F )[i] ) ) ) );
end;

RunExample := function( name, G, p )
    local t, FG, S, L, F;
    t := Runtime();
    FG := GroupFusionSystem( G, p );
    S := UnderlyingGroup( FG );
    Say( "\n=== ", name, ": |S| = ", p, "^", LogInt( Size( S ), p ), " ===\n" );
    Say( "F_S(G): ", Summary( FG ), "  (", Runtime() - t, " ms)\n" );
    t := Runtime();
    L := AllFusionSystems( S );
    Say( Length( L ), " saturated fusion systems with O_p(F) = 1 and O^p(F) = F  (", Runtime() - t, " ms)\n" );
    for F in L do Say( "   ", Summary( F ), "\n" ); od;
    t := Runtime();
    Say( "F_S(G) recovered: ", ForAny( L, F -> IsIsomorphicFusionSystems( F, FG ) ), "  (", Runtime() - t, " ms)\n" );
    return L;
end;

RunExample( "PSU(4,3), p = 3", PSU( 4, 3 ), 3 );
RunExample( "PSL(3,7), p = 7 (S = 7^{1+2}_+)", PSL( 3, 7 ), 7 );
RunExample( "Alt(30), p = 5", AlternatingGroup( 30 ), 5 );
Say( "\nDONE\n" );
