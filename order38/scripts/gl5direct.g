#############################################################################
##
##  gl5direct.g   The look-up table for GL_5(3) and T = 3^2 by direct
##                construction.  A subgroup H <= GL_5(3) with Sylow
##                3-subgroup T = 3^2 and a strongly 3-embedded subgroup has
##                O^{3'}(H/O_{3'}(H)) in { A6, L3(4), M11 }; 7 does not divide
##                |GL_5(3)|, so the perfect residuum Y of H is A6, SL2(9) or
##                M11 (M11 has trivial Schur multiplier) and H lies between Y
##                and N(Y) [Frattini argument, as in FS_PerfectCandidates].
##                A6 and SL2(9) act on F_3^5 as 4+1 (their only faithful
##                F_3-modules of dimension <= 5), M11 irreducibly (two dual
##                classes).
##
Read( "/home/user/FusionSystems/order38/scripts/gltables.g" );

FS38_GL5Direct3x3 := function()
    local G, iso, Gp, Ys, tab, Y, N, T, ints, H, cands, r, mats, module, M11, pm, cf, rep, m, embed, d, gens, NT, res, T0, found, Tp, L, W;
    Read( "/home/user/FusionSystems/order38/data/gl4_table.g" );
    G := GL( 5, 3 );
    iso := IsomorphismPermGroup( G );
    Gp := Image( iso );
    embed := function( m4 )   # 4x4 matrix -> 5x5 block diagonal with 1
        local m;
        m := IdentityMat( 5, GF( 3 ) );
        m{[ 1 .. 4 ]}{[ 1 .. 4 ]} := m4;
        return ImmutableMatrix( GF( 3 ), m );
    end;
    Ys := [];
    # A6 and SL2(9) from the GL4(3) table (the candidates of orders 360 and 720 with simple/quasisimple structure)
    for r in GLTABLE_4 do
        for d in r.cands do
            if d.size in [ 360, 720 ] and PositionSublist( d.desc, "A6" ) <> fail or d.desc = "SL(2,9)" then
                mats := List( d.gens, m -> embed( m * One( GF( 3 ) ) ) );
                Y := Image( iso, Group( mats ) );
                if ( Size( Y ) = 360 or Size( Y ) = 720 ) and IsPerfectGroup( Y ) then
                    Add( Ys, rec( name := d.desc, grp := Y ) );
                fi;
            fi;
        od;
    od;
    # M11 on its two 5-dimensional modules over GF(3): they are constituents
    # of the module induced from a 5-dimensional constituent of the
    # permutation module of PSL(2,11) < M11 on 11 points
    M11 := MathieuGroup( 11 );
    L := First( List( ConjugacyClassesMaximalSubgroups( M11 ), Representative ), K -> Size( K ) = 660 );
    cf := MTX.CollectedFactors( PermutationGModule( L, GF( 3 ) ) );
    W := First( cf, m -> m[1].dimension = 5 )[1];
    cf := MTX.CollectedFactors( InducedGModule( M11, L, W ) );
    for m in cf do
        if m[1].dimension = 5 then
            mats := List( m[1].generators, x -> ImmutableMatrix( GF( 3 ), x ) );
            Y := Image( iso, Group( mats ) );
            if Size( Y ) = 7920 then Add( Ys, rec( name := "M11", grp := Y ) ); fi;
            mats := List( m[1].generators, x -> ImmutableMatrix( GF( 3 ), TransposedMat( x^-1 ) ) );
            Y := Image( iso, Group( mats ) );
            if Size( Y ) = 7920 then Add( Ys, rec( name := "M11 (dual)", grp := Y ) ); fi;
        fi;
    od;
    Info( InfoFusionSystems, 1, "perfect residua: ", List( Ys, y -> [ y.name, Size( y.grp ) ] ) );
    # remove conjugate duplicates
    res := [];
    for Y in Ys do
        if ForAll( res, Z -> Size( Z.grp ) <> Size( Y.grp ) or RepresentativeAction( Gp, Z.grp, Y.grp ) = fail ) then Add( res, Y ); fi;
    od;
    Ys := res;
    Info( InfoFusionSystems, 1, Length( Ys ), " classes of perfect residua" );
    # candidates: subgroups between Y and N(Y) with 3-part 9 and a strongly 3-embedded subgroup, by their Sylow 3-subgroup
    tab := [];
    for Y in Ys do
        N := Normalizer( Gp, Y.grp );
        T := SylowSubgroup( Y.grp, 3 );
        ints := Concatenation( [ Y.grp, N ], IntermediateSubgroups( N, Y.grp ).subgroups );
        for H in ints do
            if FS_PPart( Size( H ), 3 ) <> 9 then continue; fi;
            if not HasStronglyPEmbeddedSubgroup( H, 3 ) then continue; fi;
            # the Sylow of H containing T is T itself (|H|_3 = 9)
            found := false;
            for r in tab do
                if RepresentativeAction( Gp, r.T, T ) <> fail then
                    Tp := RepresentativeAction( Gp, T, r.T );
                    H := ConjugateSubgroup( H, Tp );
                    if ForAll( r.cands, K -> Size( K ) <> Size( H ) or RepresentativeAction( r.NT, K, H ) = fail ) then Add( r.cands, H ); fi;
                    found := true; break;
                fi;
            od;
            if not found then
                Add( tab, rec( T := T, NT := Normalizer( Gp, T ), cands := [ H ] ) );
            fi;
        od;
    od;
    # the records in the format of FS38_GLTable
    res := [];
    for r in tab do
        Add( res, rec( n := 5, T := r.T, Tmats := List( GeneratorsOfGroup( r.T ), x -> PreImagesRepresentative( iso, x ) ),
                       Ttype := "3^2", NT := Size( r.NT ),
                       cands := List( r.cands, function( H ) local mats, module;
                           mats := List( GeneratorsOfGroup( H ), x -> PreImagesRepresentative( iso, x ) );
                           module := GModuleByMats( mats, GF( 3 ) );
                           return rec( size := Size( H ), gens := mats, desc := FS38_Describe( H ), NHT := Size( Normalizer( H, r.T ) ),
                                       soluble := false, O3prime := FS38_OpPrime( H, 3 ), irreducible := MTX.IsIrreducible( module ),
                                       composition := List( MTX.CompositionFactors( module ), m -> m.dimension ) );
                       end ) ) );
    od;
    return res;
end;
