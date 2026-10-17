# Known groups of order 3^8: Sylow 3-subgroups of simple groups.
# Returns a list of records rec( name, group (pc group), desc ).
LoadPackage( "FusionSystems", false );
FS_KnownGroups38 := function()
    local res, S, G, W, T, H, prodone, c, z, N, iso;
    res := [];
    # (i) Alt(18), Alt(19), Alt(20): (C3 wr C3) x (C3 wr C3)
    S := Image( IsomorphismPcGroup( SylowSubgroup( SymmetricGroup( 18 ), 3 ) ) );
    Add( res, rec( name := "Syl_3(A18)", group := S, desc := "(C3 wr C3) x (C3 wr C3), Sylow 3-subgroup of Alt(18), Alt(19), Alt(20)" ) );
    # (ii) PSp4(9): the Sylow 3-subgroup of Sp(4,9) (the centre has order 2)
    S := Image( IsomorphismPcGroup( SylowSubgroup( SP( 4, 9 ), 3 ) ) );
    Add( res, rec( name := "Syl_3(PSp4(9))", group := S, desc := "unipotent radical of Sp4(9), Sylow 3-subgroup of PSp4(9)" ) );
    # (iii) PSL3(q), q = 1 mod 81 (not mod 243), and PSU3(q), q = -1 mod 81:
    #       { (x,y,z) in C81^3 : xyz = 1 } : C3 (cyclic permutation) modulo the diagonal C3
    W := WreathProduct( CyclicGroup( IsPermGroup, 81 ), CyclicGroup( IsPermGroup, 3 ) );
    T := Image( Embedding( W, 1 ) );
    prodone := Subgroup( W, Concatenation( List( [ 1, 2 ], i -> [ GeneratorsOfGroup( Image( Embedding( W, i ) ) )[1] * GeneratorsOfGroup( Image( Embedding( W, i+1 ) ) )[1]^-1 ] ) ) );
    H := ClosureGroup( prodone, Image( Embedding( W, 4 ) ) );   # order 81^2 * 3
    z := Product( List( [ 1 .. 3 ], i -> GeneratorsOfGroup( Image( Embedding( W, i ) ) )[1]^27 ) );  # (w,w,w), w of order 3
    N := Subgroup( H, [ z ] );
    S := Image( IsomorphismPcGroup( H / N ) );
    Add( res, rec( name := "Syl_3(PSL3(q)), q = 1 mod 81", group := S, desc := "((C81 x C81) : C3)/C3, Sylow 3-subgroup of PSL3(q) for 3^4 || q-1 and of PSU3(q) for 3^4 || q+1" ) );
    # (iv) 3D4(q), 3^3 || q^2-1: the model (C27 x C81) : C3 inside C81 wr C3 of
    #      scripts/d4model.g (validated against 3D4(2)); it is isomorphic to (iii)
    if IsExistingFile( "/home/user/FusionSystems/order38/data/d4_sylow_model.g" ) then
        Read( "/home/user/FusionSystems/order38/data/d4_sylow_model.g" );
        S := PcGroupCode( ValueGlobal( "FS38_D4Model" ), 6561 );
        Add( res, rec( name := "Syl_3(3D4(q)), 27 || q^2-1", group := S, desc := "(C27 x C81) : C3, Sylow 3-subgroup of 3D4(q) for 3^3 || q^2-1 (isomorphic to (iii))" ) );
    fi;
    return res;
end;
FS_GroupInvariants38 := function( S )
    local r;
    r := rec( order := Size( S ), centre := Size( Center( S ) ), class := NilpotencyClassOfGroup( S ),
              rank := RankPGroup( S ), exponent := Exponent( S ), derived := Size( DerivedSubgroup( S ) ),
              frattini := Size( FrattiniSubgroup( S ) ), abelianinv := AbelianInvariants( S ),
              elementorders := Collected( List( ConjugacyClasses( S ), c -> [ Order( Representative( c ) ), Size( c ) ] ) ),
              maxabelianrank := Maximum( List( ConjugacyClassesMaximalSubgroups( S ), c -> 0 ) ) );
    Unbind( r.maxabelianrank );
    r.nclasses := Length( ConjugacyClasses( S ) );
    r.upper := List( UpperCentralSeriesOfGroup( S ), Size );
    r.lower := List( LowerCentralSeriesOfGroup( S ), Size );
    return r;
end;
