#############################################################################
##
##  reduce.g      Stage 1a of the search on groups of order 3^8:
##                the cheap necessary conditions (no automorphism groups).
##
##  A group S of order 3^8 can carry a saturated fusion system F with
##  O_3(F) = 1 and O^3(F) = F only if
##   (R1) |S : Z(S)| > 9                              [Parker-Semeraro, Lemma 7.1]
##   (R2) S has a "cheap proto-essential" subgroup E: by [Gautam, Thm 3.6]
##        every essential subgroup is S-conjugate to some C_S(xA/A), A a term
##        of a central series refining the lower central series with A <= S',
##        xA of order 3 in S/A; and an essential E is S-centric, E < N_S(E),
##        Out_S(E) = N_S(E)/E is a Sylow 3-subgroup of a group with a strongly
##        3-embedded subgroup (so cyclic, elementary abelian, 3^{1+2}_+ or
##        Syl_3(U3(9))), |E/Phi(E)| >= |Out_S(E)|^2, and (F-radical) no
##        element of N_S(E) \ E acts trivially on all factors of a chain of
##        characteristic subgroups of E (the stability group of such a chain
##        is a normal 3-subgroup of Aut(E), which meets Out_F(E) trivially),
##        Aut(E) is not a 3-group (autpgrp), Aut_S(E) meets O_3(Aut(E)) in
##        Inn(E), and Aut(E) is insoluble unless Out_S(E) is cyclic.
##   (R3) no nontrivial subgroup W of S which is "visibly characteristic" in S
##        and in every candidate E (so W is normal in F, W <= O_3(F)).
##
LoadPackage( "FusionSystems", false );
LoadPackage( "sglppow", false );

# characteristic subgroups of a p-group X built from standard ones, closed
# once under intersections and products
FS38_CharList := function( X )
    local base, L, i, j, U, add;
    base := [ Center( X ), FrattiniSubgroup( X ), DerivedSubgroup( X ), Agemo( X, 3 ) ];
    L := LowerCentralSeriesOfGroup( X );
    if Length( L ) > 2 then Add( base, L[3] ); fi;
    L := UpperCentralSeriesOfGroup( X );
    if Length( L ) > 2 then Add( base, L[2] ); fi;
    Add( base, Omega( Center( X ), 3 ) );
    Add( base, Center( FrattiniSubgroup( X ) ) );
    Add( base, Centralizer( X, DerivedSubgroup( X ) ) );
    base := DuplicateFreeList( Filtered( base, U -> Size( U ) > 1 and Size( U ) < Size( X ) ) );
    add := function( U ) if Size( U ) > 1 and Size( U ) < Size( X ) and not U in base then Add( base, U ); fi; end;
    for i in [ 1 .. Length( base ) ] do
        for j in [ i + 1 .. Length( base ) ] do
            add( Intersection( base[i], base[j] ) );
            add( ClosureGroup( base[i], base[j] ) );
        od;
    od;
    return base;
end;

# the covering pairs [ D, D' ] (D < D', nothing of the list strictly between)
# of the set { 1 } u chars u { X }
FS38_CoveringPairs := function( X, chars )
    local L, pairs, i, j, k, between;
    L := Concatenation( [ TrivialSubgroup( X ) ], chars, [ X ] );
    L := DuplicateFreeList( L );
    SortBy( L, Size );
    pairs := [];
    for i in [ 1 .. Length( L ) ] do
        for j in [ i + 1 .. Length( L ) ] do
            if not IsSubset( L[j], L[i] ) then continue; fi;
            between := false;
            for k in [ i + 1 .. j - 1 ] do
                if Size( L[k] ) > Size( L[i] ) and Size( L[k] ) < Size( L[j] )
                   and IsSubset( L[k], L[i] ) and IsSubset( L[j], L[k] ) then between := true; break; fi;
            od;
            if not between then Add( pairs, [ L[i], L[j] ] ); fi;
        od;
    od;
    return pairs;
end;

# the elements of N acting trivially on D'/D for every covering pair
FS38_StabilityKernel := function( N, pairs )
    local C, pr, q, Q;
    C := N;
    for pr in pairs do
        q := NaturalHomomorphismByNormalSubgroup( C, pr[1] );
        Q := Image( q );
        C := PreImage( q, Centralizer( Q, Image( q, pr[2] ) ) );
        if Size( C ) = Size( pr[1] ) then break; fi;
    od;
    return C;
end;

# the type of Q = N_S(E)/E, or fail if Q cannot be a Sylow 3-subgroup of a
# group with a strongly 3-embedded subgroup
FS38_SylowType := function( Q )
    local n;
    n := Size( Q );
    if n = 1 then return fail; fi;
    if IsCyclic( Q ) then return Concatenation( "C", String( n ) ); fi;
    if IsElementaryAbelian( Q ) then return Concatenation( "3^", String( LogInt( n, 3 ) ) ); fi;
    if n = 27 and Exponent( Q ) = 3 then return "3^{1+2}_+"; fi;
    if n = 729 and IsomorphismGroups( Q, FS38_SylU39 ) <> fail then return "Syl_3(U3(9))"; fi;
    return fail;
end;
FS38_SylU39 := Image( IsomorphismPcGroup( SylowSubgroup( SU( 3, 9 ), 3 ) ) );

# invariants used to distinguish S-classes of subgroups
FS38_Inv := function( S, E )
    return [ Size( E ), Size( Normalizer( S, E ) ), Size( Center( E ) ), Size( FrattiniSubgroup( E ) ), Size( DerivedSubgroup( E ) ) ];
end;

# The candidates C_S(xA/A) of Gautam's theorem, one for each distinct
# subgroup: the centralizers are taken from the conjugacy classes of the
# quotients S/A (where they are stored by the class computation) and
# duplicates are removed inside the quotient before the preimage is formed.
FS38_Candidates := function( S )
    local p, ser, k, cands, i, q, Q, c, C, seenQ, x;
    p := PrimePGroup( S );
    ser := RefinedLowerCentralSeries( S );
    k := Position( ser, DerivedSubgroup( S ) );
    cands := [];
    for i in [ k + 1 .. Length( ser ) ] do          # A = S' only gives C = S
        if i = Length( ser ) then
            Q := S; q := fail;
        else
            q := NaturalHomomorphismByNormalSubgroup( S, ser[i] );
            Q := Image( q );
        fi;
        seenQ := [];
        for c in ConjugacyClasses( Q ) do
            x := Representative( c );
            if Order( x ) <> p then continue; fi;
            C := Centralizer( c );                  # stored by the class computation
            if Size( C ) = Size( Q ) then continue; fi;
            if C in seenQ then continue; fi;
            Add( seenQ, C );
            if q = fail then
                Add( cands, C );
            else
                Add( cands, PreImage( q, C ) );
            fi;
        od;
    od;
    return cands;
end;

# Stage 1a for one group.  Returns a record with components
#   status  "reject" or "survive",  reason (for rejects),
#   cands   list of records ( order, index (|N_S(E):E|), type, elab, abelian, rank, chars )
#   inv     [ |Z(S)|, class, rank, exponent, |S'|, |Phi(S)| ]
FS38_Cheap := function( S )
    local Z, cands, seen, seeninv, E, inv, N, q, Q, type, Phi, pairs, C, res, charsE,
          charS, W, result, pre, a;
    Z := Center( S );
    if Index( S, Z ) <= 9 then return rec( status := "reject", reason := "|S:Z(S)| <= 9" ); fi;
    cands := FS38_Candidates( S );
    # cheap tests first (normalizer, centric), then the S-class test
    pre := [];
    for E in cands do
        N := Normalizer( S, E );
        if N = E then continue; fi;
        if not IsSubset( E, Centralizer( S, E ) ) then continue; fi;
        Add( pre, [ E, N ] );
    od;
    seen := []; seeninv := []; res := [];
    for C in pre do
        E := C[1]; N := C[2];
        inv := [ Size( E ), Size( N ), Size( Center( E ) ), Size( FrattiniSubgroup( E ) ), Size( DerivedSubgroup( E ) ) ];
        if FS_ClassPosition( S, seen, seeninv, E ) <> fail then continue; fi;
        Add( seen, E ); Add( seeninv, inv );
        q := NaturalHomomorphismByNormalSubgroup( N, E );
        Q := Image( q );
        type := FS38_SylowType( Q );
        if type = fail then continue; fi;
        Phi := FrattiniSubgroup( E );
        if Index( E, Phi ) < Size( Q )^2 then continue; fi;
        # the Frattini quotient test, then the finer chain of characteristic subgroups
        C := FS38_StabilityKernel( N, [ [ Phi, E ] ] );
        if not IsSubset( E, C ) then continue; fi;
        charsE := FS38_CharList( E );
        pairs := FS38_CoveringPairs( E, charsE );
        C := FS38_StabilityKernel( N, pairs );
        if not IsSubset( E, C ) then continue; fi;
        # (R2e) an essential subgroup has a 3'-automorphism (Out_S(E) is not
        # normal in Out_F(E)): Aut(E) must not be a 3-group
        a := AutomorphismGroupPGroup( E );
        if a.glOrder = 1 or SmallestRootInt( a.glOrder ) = 3 then continue; fi;
        # the exact radical test Aut_S(E) meet O_3(Aut(E)) = Inn(E), and
        # Aut(E) insoluble unless Out_S(E) is cyclic [Parker-Semeraro]
        if not FS_RadicalTest( S, E ) then continue; fi;
        if not IsCyclic( Q ) and IsSolvableGroup( FS_AutHandle( E ).model ) then continue; fi;
        Add( res, rec( E := E, order := Size( E ), index := Size( Q ), type := type, autorder := a.size,
                       elab := IsElementaryAbelian( E ), abelian := IsAbelian( E ), rank := RankPGroup( E ), chars := charsE ) );
    od;
    if Length( res ) = 0 then return rec( status := "reject", reason := "no candidate essential subgroup" ); fi;
    # (R3) visibly characteristic subgroups
    charS := FS38_CharList( S );
    for W in charS do
        if ForAll( res, r -> IsSubset( r.E, W ) and W in r.chars ) then
            return rec( status := "reject", reason := Concatenation( "characteristic subgroup of order ", String( Size( W ) ), " in all candidates" ),
                        cands := res );
        fi;
    od;
    result := rec( status := "survive", cands := res,
                   inv := [ Size( Z ), NilpotencyClassOfGroup( S ), RankPGroup( S ), Exponent( S ),
                            Size( DerivedSubgroup( S ) ), Size( FrattiniSubgroup( S ) ) ] );
    return result;
end;

# one line of output per group
FS38_Line := function( id, r )
    local s, c;
    s := Concatenation( String( id ), ";", r.status, ";" );
    if r.status = "reject" then
        return Concatenation( s, r.reason );
    fi;
    s := Concatenation( s, String( r.inv ), ";" );
    for c in r.cands do
        s := Concatenation( s, "[", String( c.order ), ",", String( c.index ), ",", c.type, ",",
                            String( c.elab ), ",", String( c.abelian ), ",", String( c.rank ), ",", String( c.autorder ), "]" );
    od;
    return s;
end;

# process the ids  a, a+step, a+2*step, ... <= b  and append to file
FS38_Run := function( a, step, b, file, progressfile )
    local id, S, r, t, line, t0, n;
    t0 := Runtime(); n := 0;
    for id in [ a, a + step .. b ] do
        S := SmallGroup( 6561, id );
        t := Runtime();
        r := FS38_Cheap( S );
        line := FS38_Line( id, r );
        AppendTo( file, line, ";", Runtime() - t, "\n" );
        n := n + 1;
        if n mod 500 = 0 then
            PrintTo( progressfile, id, " ", Runtime() - t0, "\n" );
        fi;
    od;
    PrintTo( progressfile, "DONE ", b, " ", Runtime() - t0, "\n" );
end;
