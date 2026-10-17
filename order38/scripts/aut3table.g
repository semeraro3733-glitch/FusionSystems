# For every group E of order 3^k, 3 <= k <= 7 (SmallGroups library ids):
# the order of the image of Aut(E) in GL(E/Phi(E)) (autpgrp's glOrder) and
# |Aut(E)|.  A candidate essential subgroup E with Aut(E) a 3-group
# (glOrder a power of 3) can be discarded at once.
LoadPackage( "FusionSystems", false );
FS38_MakeAut3Table := function( file )
    local out, k, n, i, E, a, gl;
    out := OutputTextFile( file, false ); SetPrintFormattingStatus( out, false );
    AppendTo( out, "# AUT3TABLE[k][i] = [ glOrder, |Aut(E)| ] for E = SmallGroup( 3^k, i ), k = 3..7\n" );
    AppendTo( out, "AUT3TABLE := [ , , " );
    for k in [ 3 .. 7 ] do
        n := NumberSmallGroups( 3^k );
        AppendTo( out, "[\n" );
        for i in [ 1 .. n ] do
            E := SmallGroup( 3^k, i );
            if IsAbelian( E ) then
                gl := Size( GL( RankPGroup( E ), 3 ) ); a := Size( AutomorphismGroup( E ) );
            else
                a := AutomorphismGroupPGroup( E );
                gl := a.glOrder; a := a.size;
            fi;
            AppendTo( out, "[", gl, ",", a, "]" );
            if i < n then AppendTo( out, "," ); fi;
            if i mod 20 = 0 then AppendTo( out, "\n" ); fi;
        od;
        AppendTo( out, "]" );
        if k < 7 then AppendTo( out, ",\n" ); fi;
    od;
    AppendTo( out, " ];\n" );
    AppendTo( out, "FS38_AutIs3Group := function( E ) local id, gl; id := IdGroup( E ); gl := AUT3TABLE[ LogInt( id[1], 3 ) ][ id[2] ][1]; return gl = 1 or SmallestRootInt( gl ) = 3; end;\n" );
    CloseStream( out );
end;
