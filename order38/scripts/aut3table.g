# For every group E of order 3^k, 3 <= k <= 7 (SmallGroups library ids):
# |Aut(E)|, with autpgrp's glOrder.  A candidate essential subgroup E with
# Aut(E) a 3-group (|Aut(E)| a power of 3) can be discarded at once.
# (autpgrp's glOrder is 1 whenever the action on the Frattini quotient is
# soluble, so it must not be used for this purpose.)
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
    AppendTo( out, "FS38_IsPowerOf3 := n -> n = 3^LogInt( n, 3 );\n" );
    CloseStream( out );
end;
