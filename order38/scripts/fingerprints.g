# Fingerprints (isomorphism invariants) of the groups of order 3^k,
# 3 <= k <= 7, whose automorphism group is not a 3-group, from aut3table.g.
# A candidate essential subgroup E of order <= 3^7 which is not elementary
# abelian must be isomorphic to one of them, so a candidate whose
# fingerprint does not occur in the table is discarded.
LoadPackage( "FusionSystems", false );
Read( "/home/user/FusionSystems/order38/data/aut3table.g" );

FS38_Fingerprint := function( E )
    local Z;
    Z := Center( E );
    return [ Size( E ), Size( Z ), Size( FrattiniSubgroup( E ) ), Size( DerivedSubgroup( E ) ), Exponent( E ),
             NilpotencyClassOfGroup( E ), AbelianInvariants( E ), List( LowerCentralSeriesOfGroup( E ), Size ),
             List( UpperCentralSeriesOfGroup( E ), Size ), Size( Agemo( E, 3 ) ), Size( Omega( Z, 3 ) ),
             Collected( List( ConjugacyClasses( E ), c -> [ Order( Representative( c ) ), Size( c ) ] ) ) ];
end;

FS38_MakeFingerprintTable := function( file )
    local out, k, i, E, fp, gl, tab;
    out := OutputTextFile( file, false ); SetPrintFormattingStatus( out, false );
    AppendTo( out, "# FINGERPRINTS[k] = list of [ fingerprint, id, glOrder, |Aut| ] for the groups of order 3^k with Aut not a 3-group\n" );
    AppendTo( out, "FINGERPRINTS := [ , , " );
    for k in [ 3 .. 7 ] do
        AppendTo( out, "[\n" );
        for i in [ 1 .. NumberSmallGroups( 3^k ) ] do
            gl := AUT3TABLE[k][i][1];
            if gl = 1 or SmallestRootInt( gl ) = 3 then continue; fi;
            E := SmallGroup( 3^k, i );
            fp := FS38_Fingerprint( E );
            AppendTo( out, "[ ", fp, ", ", i, ", ", gl, ", ", AUT3TABLE[k][i][2], " ],\n" );
        od;
        AppendTo( out, "]" );
        if k < 7 then AppendTo( out, ",\n" ); fi;
    od;
    AppendTo( out, " ];\n" );
    CloseStream( out );
end;
