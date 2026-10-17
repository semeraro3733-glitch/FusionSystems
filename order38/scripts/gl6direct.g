#############################################################################
##
##  gl6direct.g   The look-up table for GL_6(3) and T = 3^2 by direct
##                construction.
##
##  A subgroup H <= GL_6(3) with Sylow 3-subgroup T = 3^2 and a strongly
##  3-embedded subgroup has H/O_{3'}(H) with O^{3'} in { A6, L3(4), M11 }.
##  Its perfect residuum Y = H^(oo) satisfies Y/O_{3'}(Y) in that list; the
##  argument of report.tex (Section on look-up tables) shows that
##  Q = O_{3'}(Y) is a 2-group which is either central (so Y is one of
##  A6, SL2(9), M11, or a cover 2.L3(4), 4.L3(4), ... with a faithful
##  6-dimensional module over GF(3)) or Q = 2^5 with Y = 2^5:A6 the
##  perfect subgroup of the monomial group 2^6:S6 (A6 permuting the six
##  weight spaces of Q).  H lies between Y and N(Y) (Frattini argument).
##
##  The faithful 6-dimensional GF(3)-modules: for A6 the modules with
##  composition factors 4,1,1 (4+1+1, (4/1)+1, (1/4)+1, the uniserial
##  permutation module 1/4/1; Ext^1(1,4) is one-dimensional, so these are
##  all) and the irreducible 6 (3 + 3^sigma over GF(9), the symmetric
##  square of the natural module of SL2(9)); for SL2(9) only 4+1+1; for
##  M11 the modules 5+1, 5*+1 and the two non-split extensions (H^1 of
##  one of the two dual 5-dimensional modules is one-dimensional; they
##  occur as the 6-dimensional submodule and quotient of the permutation
##  module on 12 points); for the covers of L3(4) the irreducible
##  6-dimensional modules found by IrreducibleModules (the perfect groups
##  library is used for the covers).
##
Read( "/home/user/FusionSystems/order38/scripts/gltables.g" );

FS38_GL6Residua := function( iso )
    local F3, blockdiag, Ys, addY, A6, pm, subs, one, aug, N5, Q5, H4, sl, sym2, sym2mats, nat, M11, L, cf, W, M5s, i, act12, pm12, s12,
          U6, S6, F6, ord, j, Y, q, mods, m, mats, signs, k, d, res, t, Gp;
    F3 := GF( 3 );
    Gp := Image( iso );
    blockdiag := function( A, B )
        local n, mm, a, b, r;
        n := Length( A ); mm := Length( B );
        r := NullMat( n + mm, n + mm, F3 );
        for a in [ 1 .. n ] do for b in [ 1 .. n ] do r[a][b] := A[a][b]; od; od;
        for a in [ 1 .. mm ] do for b in [ 1 .. mm ] do r[n+a][n+b] := B[a][b]; od; od;
        return ImmutableMatrix( F3, r );
    end;
    Ys := [];
    addY := function( name, mats, expected )
        local Y;
        mats := List( mats, x -> ImmutableMatrix( F3, x ) );
        Y := Group( mats );
        if Size( Y ) <> expected then Error( name, ": wrong order ", Size( Y ) ); fi;
        Add( Ys, rec( name := name, grp := Image( iso, Y ) ) );
    end;
    # A6
    A6 := AlternatingGroup( 6 );
    pm := PermutationGModule( A6, F3 );
    subs := MTX.BasesSubmodules( pm );
    one := First( subs, b -> Length( b ) = 1 );
    aug := First( subs, b -> Length( b ) = 5 );
    N5 := MTX.InducedActionSubmodule( pm, aug );
    Q5 := MTX.InducedActionFactorModule( pm, one );
    H4 := MTX.InducedActionFactorModule( N5, First( MTX.BasesSubmodules( N5 ), b -> Length( b ) = 1 ) );
    addY( "A6 (4+1+1)", List( H4.generators, x -> blockdiag( x, IdentityMat( 2, F3 ) ) ), 360 );
    addY( "A6 (4/1+1)", List( N5.generators, x -> blockdiag( x, IdentityMat( 1, F3 ) ) ), 360 );
    addY( "A6 (1/4+1)", List( Q5.generators, x -> blockdiag( x, IdentityMat( 1, F3 ) ) ), 360 );
    addY( "A6 (1/4/1)", pm.generators, 360 );
    sl := SL( 2, 9 );
    sym2 := function( x )
        local b, r, X, Y2;
        b := [ [ [ 1, 0 ], [ 0, 0 ] ], [ [ 0, 1 ], [ 1, 0 ] ], [ [ 0, 0 ], [ 0, 1 ] ] ] * One( GF( 9 ) );
        r := [];
        for X in b do
            Y2 := TransposedMat( x ) * X * x;
            Add( r, [ Y2[1][1], Y2[1][2], Y2[2][2] ] );
        od;
        return r;
    end;
    sym2mats := List( GeneratorsOfGroup( sl ), x -> BlownUpMat( Basis( GF( 9 ) ), sym2( x ) ) );
    addY( "A6 (6)", sym2mats, 360 );
    # SL2(9)
    nat := List( GeneratorsOfGroup( sl ), x -> BlownUpMat( Basis( GF( 9 ) ), x ) );
    addY( "SL(2,9) (4+1+1)", List( nat, x -> blockdiag( x, IdentityMat( 2, F3 ) ) ), 720 );
    # M11
    M11 := MathieuGroup( 11 );
    L := First( List( ConjugacyClassesMaximalSubgroups( M11 ), Representative ), K -> Size( K ) = 660 );
    cf := MTX.CollectedFactors( PermutationGModule( L, F3 ) );
    W := First( cf, x -> x[1].dimension = 5 )[1];
    cf := MTX.CollectedFactors( InducedGModule( M11, L, W ) );
    M5s := List( Filtered( cf, x -> x[1].dimension = 5 ), x -> x[1] );
    for i in [ 1 .. Length( M5s ) ] do
        addY( Concatenation( "M11 (5+1) #", String( i ) ), List( M5s[i].generators, x -> blockdiag( x, IdentityMat( 1, F3 ) ) ), 7920 );
    od;
    act12 := Action( M11, RightCosets( M11, L ), OnRight );
    pm12 := PermutationGModule( act12, F3 );
    s12 := MTX.BasesSubmodules( pm12 );
    U6 := First( s12, b -> Length( b ) = 6 );
    S6 := MTX.InducedActionSubmodule( pm12, U6 );
    F6 := MTX.InducedActionFactorModule( pm12, U6 );
    addY( "M11 (1/5 non-split)", S6.generators, 7920 );
    addY( "M11 (5/1 non-split)", F6.generators, 7920 );
    # covers of L3(4) (and of A8, which has the same order; the A8 covers
    # have no faithful module of dimension <= 6 and are harmless anyway:
    # they are excluded below by the strongly 3-embedded test)
    for ord in [ 20160, 40320, 80640, 161280, 322560 ] do
        for j in [ 1 .. NumberPerfectGroups( ord ) ] do
            Y := PerfectGroup( IsPermGroup, ord, j );
            q := NaturalHomomorphismByNormalSubgroup( Y, Centre( Y ) );
            if Size( Image( q ) ) <> 20160 then continue; fi;
            t := Runtime();
            mods := IrreducibleModules( Y, F3, 6 );
            Info( InfoFusionSystems, 1, "perfect group ", ord, "#", j, ": irreducible GF(3)-modules of dimension <= 6: ",
                  List( mods[2], x -> x.dimension ), " (", Runtime() - t, " ms)" );
            for m in mods[2] do
                if m.dimension in [ 5, 6 ] and Size( Group( m.generators ) ) = ord then
                    mats := m.generators;
                    if m.dimension = 5 then mats := List( mats, x -> blockdiag( x, IdentityMat( 1, F3 ) ) ); fi;
                    addY( Concatenation( "perfect ", String( ord ), "#", String( j ), " dim ", String( m.dimension ) ), mats, ord );
                fi;
            od;
        od;
    od;
    # 2^5 : A6 (monomial)
    signs := [];
    for k in [ 2 .. 6 ] do
        d := IdentityMat( 6, F3 ); d := List( d, ShallowCopy ); d[1][1] := -One( F3 ); d[k][k] := -One( F3 );
        Add( signs, ImmutableMatrix( F3, d ) );
    od;
    addY( "2^5:A6", Concatenation( pm.generators, signs ), 32 * 360 );
    Info( InfoFusionSystems, 1, "perfect residua: ", List( Ys, y -> [ y.name, Size( y.grp ) ] ) );
    res := [];
    for Y in Ys do
        if ForAll( res, Z -> Size( Z.grp ) <> Size( Y.grp ) or RepresentativeAction( Gp, Z.grp, Y.grp ) = fail ) then
            Add( res, Y );
        else
            Info( InfoFusionSystems, 1, Y.name, " is conjugate to an earlier residuum" );
        fi;
    od;
    Info( InfoFusionSystems, 1, Length( res ), " classes of perfect residua: ", List( res, r -> r.name ) );
    return res;
end;

# conjugacy of two subgroups T1, T2 = 3^2 of GL_6(3) (given as permutation
# groups, iso the isomorphism from the matrix group) through the module
# structure: T1^g = T2 iff for some generating pair (c1,c2) of T2 the
# GF(3)T-modules given by the generators of T1 and by (c1,c2) are isomorphic;
# returns the conjugating matrix or fail
FS38_GL6ConjugateT := function( iso, T1, T2 )
    local a, M1, els, c1, c2, M2, X, g;
    a := List( GeneratorsOfGroup( T1 ), x -> PreImagesRepresentative( iso, x ) );
    if Length( a ) <> 2 then a := List( MinimalGeneratingSet( T1 ), x -> PreImagesRepresentative( iso, x ) ); fi;
    M1 := GModuleByMats( a, GF( 3 ) );
    els := Filtered( Elements( T2 ), x -> not IsOne( x ) );
    for c1 in els do
        for c2 in els do
            if c2 in Group( c1 ) then continue; fi;
            M2 := GModuleByMats( List( [ c1, c2 ], x -> PreImagesRepresentative( iso, x ) ), GF( 3 ) );
            X := MTX.IsomorphismModules( M1, M2 );
            if X <> fail then
                # find the convention: g with g^-1 a g = c
                if ForAll( [ 1, 2 ], i -> X^-1 * M1.generators[i] * X = M2.generators[i] ) then g := X;
                elif ForAll( [ 1, 2 ], i -> X * M1.generators[i] * X^-1 = M2.generators[i] ) then g := X^-1;
                else Error( "unexpected convention of MTX.IsomorphismModules" ); fi;
                return ImmutableMatrix( GF( 3 ), g );
            fi;
        od;
    od;
    return fail;
end;

FS38_GL6Direct3x3 := function()
    local G, iso, Gp, Ys, tab, Y, N, T, ints, H, r, pos, g, candsY, res, t, K;
    G := GL( 6, 3 );
    iso := IsomorphismPermGroup( G );
    Gp := Image( iso );
    Ys := FS38_GL6Residua( iso );
    tab := [];
    for Y in Ys do
        t := Runtime();
        N := Normalizer( Gp, Y.grp );
        Info( InfoFusionSystems, 1, Y.name, ": |N(Y)/Y| = ", Size( N ) / Size( Y.grp ), " (", Runtime() - t, " ms)" );
        T := SylowSubgroup( Y.grp, 3 );
        if Size( T ) <> 9 then Error( "Sylow 3-subgroup of the residuum is not of order 9" ); fi;
        ints := Concatenation( [ Y.grp, N ], IntermediateSubgroups( N, Y.grp ).subgroups );
        # the candidates between Y and N(Y), one per N(Y)-class (candidates
        # with different residua are never conjugate)
        candsY := [];
        for H in ints do
            if FS_PPart( Size( H ), 3 ) <> 9 then continue; fi;
            if not HasStronglyPEmbeddedSubgroup( H, 3 ) then continue; fi;
            if ForAny( candsY, K -> Size( K ) = Size( H ) and RepresentativeAction( N, K, H ) <> fail ) then continue; fi;
            Add( candsY, H );
        od;
        # the class of T among the classes found so far
        pos := fail;
        for r in [ 1 .. Length( tab ) ] do
            g := FS38_GL6ConjugateT( iso, T, tab[r].T );
            if g <> fail then pos := r; g := Image( iso, g ); break; fi;
        od;
        if pos = fail then
            Add( tab, rec( T := T, cands := [] ) );
            pos := Length( tab ); g := One( Gp );
        fi;
        for H in candsY do
            Add( tab[ pos ].cands, ConjugateSubgroup( H, g ) );
        od;
        Info( InfoFusionSystems, 1, "  ", Length( candsY ), " candidates from ", Y.name, "; ", Length( tab ), " classes of T so far with ",
              List( tab, r -> Length( r.cands ) ), " candidates (", Runtime() - t, " ms)" );
    od;
    res := [];
    for r in tab do
        Add( res, rec( n := 6, T := r.T, Tmats := List( GeneratorsOfGroup( r.T ), x -> PreImagesRepresentative( iso, x ) ),
                       Ttype := "3^2", NT := 0,
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
