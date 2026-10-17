# Stage 2 for the Sylow 3-subgroups of Alt(18) and PSp4(9) followed by the
# identification of the systems found with the fusion systems of the
# alternating/symmetric groups of degree 18, 19, 20 and of PSp4(9), PGSp4(9).
#   gap -c 'Read("reference_known_ident.g"); FS38_KnownIdent();'
Read( "/home/user/FusionSystems/order38/scripts/stage2.g" );
FS38_KnownIdent := function()
    local K, i, r, name, logf, out, Say, refs, R, L, j, F, t, d, hit;
    K := FS_KnownGroups38();
    out := OutputTextFile( "/home/user/FusionSystems/order38/logs/reference_known_ident.log", false ); SetPrintFormattingStatus( out, false );
    Say := function( arg ) CallFuncList( AppendTo, Concatenation( [ out ], arg ) ); end;
    for i in [ 1, 2 ] do
        name := K[i].name;
        logf := Concatenation( "/home/user/FusionSystems/order38/logs/stage2_known_", String( i ), ".log" );
        t := Runtime();
        r := FS38_Stage2( K[i].group, name, logf, rec() );
        L := r.systems;
        Say( name, ": ", Length( L ), " fusion systems (", Runtime() - t, " ms), incomplete = ", r.incomplete, "\n" );
        for j in [ 1 .. Length( L ) ] do Say( "  F", j, ": ", FS38_DescLine( r.descriptions[j] ), "\n" ); od;
        if i = 1 then
            refs := [ [ "Alt(18)", AlternatingGroup( 18 ) ], [ "Sym(18)", SymmetricGroup( 18 ) ], [ "Alt(19)", AlternatingGroup( 19 ) ],
                      [ "Sym(19)", SymmetricGroup( 19 ) ], [ "Alt(20)", AlternatingGroup( 20 ) ], [ "Sym(20)", SymmetricGroup( 20 ) ] ];
        else
            refs := [ [ "PSp4(9)", PSp( 4, 9 ) ], [ "PGSp4(9)", PGO( 5, 9 ) ] ];
        fi;
        for R in refs do
            t := Runtime();
            F := GroupFusionSystem( R[2], 3 );
            hit := Filtered( [ 1 .. Length( L ) ], j -> IsIsomorphicFusionSystems( L[j], F ) );
            Say( "  F_S(", R[1], ") = ", List( hit, j -> Concatenation( "F", String( j ) ) ), " (", Runtime() - t, " ms); ",
                 FS38_DescLine( FS38_Describe( F ) ), "\n" );
        od;
    od;
    Say( "DONE\n" );
    CloseStream( out );
end;
