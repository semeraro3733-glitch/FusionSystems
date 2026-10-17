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

FS38_SylU39 := Image( IsomorphismPcGroup( SylowSubgroup( SU( 3, 9 ), 3 ) ) );

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

# For non-cyclic T = Out_S(E), O^{3'}(Out_F(E)/O_{3'}(Out_F(E))) is a simple
# group determined by T up to finitely many choices, and its order divides
# |Aut(E)|.  The product of the primes dividing the order of every choice:
#   3^2: L2(9), L3(4), M11 -> 5;   3^3: L2(27) -> 7*13;   3^{1+2}_+: U3(3) -> 7;
#   3^4: L2(81) -> 5*41;  3^5: L2(243) -> 11*61;  3^6: L2(729), U3(9) -> 5*73.
FS38_RequiredDivisor := function( type )
    if type = "3^2" then return 5;
    elif type = "3^3" then return 91;
    elif type = "3^{1+2}_+" then return 7;
    elif type = "3^4" then return 205;
    elif type = "3^5" then return 671;
    elif type = "3^6" or type = "Syl_3(U3(9))" then return 365;
    fi;
    return 1;
end;

# The look-up tables for GL_n(3), n <= 4 (gltables.g): the classes of
# admissible T with at least one candidate automizer.  For an elementary
# abelian candidate E of rank n <= 4 the group Aut_S(E) <= GL_n(3) must be
# conjugate to one of them.
FS38_GLAdmissible := [];
FS38_GLGroups := [];
for n in [ 2 .. 4 ] do
    if IsExistingFile( Concatenation( "/home/user/FusionSystems/order38/data/gl", String( n ), "_table.g" ) ) then
        Read( Concatenation( "/home/user/FusionSystems/order38/data/gl", String( n ), "_table.g" ) );
        FS38_GLGroups[n] := GL( n, 3 );
        FS38_GLAdmissible[n] := List( Filtered( ValueGlobal( Concatenation( "GLTABLE_", String( n ) ) ), r -> Length( r.cands ) > 0 ),
                                      r -> Group( List( r.Tmats, m -> m * One( GF( 3 ) ) ) ) );
    fi;
od;

# Aut_S(E) as a matrix group on the elementary abelian group E
FS38_AutSMatrices := function( S, E, N )
    local pcgs, mats, g;
    pcgs := Pcgs( E );
    mats := [];
    for g in GeneratorsOfGroup( N ) do
        Add( mats, List( pcgs, x -> ExponentsOfPcElement( pcgs, x^g ) ) * One( GF( 3 ) ) );
    od;
    return Group( mats, IdentityMat( Length( pcgs ), GF( 3 ) ) );
end;

# counters: candidates entering each stage
FS38_Counts := rec( cands := 0, pre := 0, classes := 0, type := 0, frattini := 0, chain := 0, elab := 0, aut := 0, radical := 0, kept := 0 );

# timers for the stages of FS38_Cheap (ms)
FS38_Timers := rec( cands := 0, pre := 0, classes := 0, type := 0, frattini := 0, chain := 0, aut := 0, radical := 0, charS := 0 );
FS38_ResetTimers := function() local n; for n in RecNames( FS38_Timers ) do FS38_Timers.( n ) := 0; od; for n in RecNames( FS38_Counts ) do FS38_Counts.( n ) := 0; od; end;

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
          charS, W, result, pre, a, t, elab, n, T;
    Z := Center( S );
    if Index( S, Z ) <= 9 then return rec( status := "reject", reason := "|S:Z(S)| <= 9" ); fi;
    t := Runtime();
    cands := FS38_Candidates( S );
    FS38_Timers.cands := FS38_Timers.cands + Runtime() - t; t := Runtime();
    # cheap tests first (normalizer, centric), then the S-class test
    pre := [];
    FS38_Counts.cands := FS38_Counts.cands + Length( cands );
    for E in cands do
        if not IsSubset( E, Centralizer( S, E ) ) then continue; fi;
        N := Normalizer( S, E );
        if N = E then continue; fi;
        Add( pre, [ E, N ] );
    od;
    FS38_Timers.pre := FS38_Timers.pre + Runtime() - t;
    FS38_Counts.pre := FS38_Counts.pre + Length( pre );
    seen := []; seeninv := []; res := [];
    for C in pre do
        E := C[1]; N := C[2];
        t := Runtime();
        inv := [ Size( E ), Size( N ), Size( Center( E ) ), Size( FrattiniSubgroup( E ) ), Size( DerivedSubgroup( E ) ) ];
        if FS_ClassPosition( S, seen, seeninv, E ) <> fail then FS38_Timers.classes := FS38_Timers.classes + Runtime() - t; continue; fi;
        Add( seen, E ); Add( seeninv, inv );
        FS38_Timers.classes := FS38_Timers.classes + Runtime() - t; t := Runtime();
        FS38_Counts.classes := FS38_Counts.classes + 1;
        q := NaturalHomomorphismByNormalSubgroup( N, E );
        Q := Image( q );
        type := FS38_SylowType( Q );
        FS38_Timers.type := FS38_Timers.type + Runtime() - t; t := Runtime();
        if type = fail then continue; fi;
        FS38_Counts.type := FS38_Counts.type + 1;
        Phi := FrattiniSubgroup( E );
        if Index( E, Phi ) < Size( Q )^2 then continue; fi;
        elab := Size( Phi ) = 1;
        if elab then
            # Aut(E) = GL_n(3) is known; the table test for n <= 4
            FS38_Counts.elab := FS38_Counts.elab + 1;
            n := RankPGroup( E );
            if IsBound( FS38_GLAdmissible[n] ) then
                T := FS38_AutSMatrices( S, E, N );
                if not ForAny( FS38_GLAdmissible[n], T0 -> Size( T0 ) = Size( T ) and IsConjugate( FS38_GLGroups[n], T0, T ) ) then
                    FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t; continue;
                fi;
            elif Size( GL( n, 3 ) ) mod FS38_RequiredDivisor( type ) <> 0 then
                continue;
            fi;
            FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t;
            FS38_Counts.kept := FS38_Counts.kept + 1;
            Add( res, rec( E := E, order := Size( E ), index := Size( Q ), type := type, autorder := Size( GL( n, 3 ) ),
                           elab := true, abelian := true, rank := n, chars := [ E ] ) );
            continue;
        fi;
        # the Frattini quotient test, then the finer chain of characteristic subgroups
        C := FS38_StabilityKernel( N, [ [ Phi, E ] ] );
        FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t; t := Runtime();
        if not IsSubset( E, C ) then continue; fi;
        FS38_Counts.frattini := FS38_Counts.frattini + 1;
        charsE := FS38_CharList( E );
        pairs := FS38_CoveringPairs( E, charsE );
        C := FS38_StabilityKernel( N, pairs );
        FS38_Timers.chain := FS38_Timers.chain + Runtime() - t; t := Runtime();
        if not IsSubset( E, C ) then continue; fi;
        FS38_Counts.chain := FS38_Counts.chain + 1;
        # (R2e) an essential subgroup has a 3'-automorphism (Out_S(E) is not
        # normal in Out_F(E)): Aut(E) must not be a 3-group, and the simple
        # section forced by a non-cyclic Out_S(E) must fit into Out(E)
        a := AutomorphismGroupPGroup( E );
        FS38_Timers.aut := FS38_Timers.aut + Runtime() - t; t := Runtime();
        if a.glOrder = 1 or SmallestRootInt( a.glOrder ) = 3 then continue; fi;
        if a.size mod FS38_RequiredDivisor( type ) <> 0 then continue; fi;
        FS38_Counts.aut := FS38_Counts.aut + 1;
        # the exact radical test Aut_S(E) meet O_3(Aut(E)) = Inn(E), and
        # Aut(E) insoluble unless Out_S(E) is cyclic [Parker-Semeraro]
        if not FS_RadicalTest( S, E ) then FS38_Timers.radical := FS38_Timers.radical + Runtime() - t; continue; fi;
        if not IsCyclic( Q ) and IsSolvableGroup( FS_AutHandle( E ).model ) then FS38_Timers.radical := FS38_Timers.radical + Runtime() - t; continue; fi;
        FS38_Timers.radical := FS38_Timers.radical + Runtime() - t;
        FS38_Counts.kept := FS38_Counts.kept + 1;
        Add( res, rec( E := E, order := Size( E ), index := Size( Q ), type := type, autorder := a.size,
                       elab := false, abelian := IsAbelian( E ), rank := RankPGroup( E ), chars := charsE ) );
    od;
    if Length( res ) = 0 then return rec( status := "reject", reason := "no candidate essential subgroup" ); fi;
    # (R3) visibly characteristic subgroups
    t := Runtime();
    charS := FS38_CharList( S );
    for W in charS do
        if ForAll( res, r -> IsSubset( r.E, W ) and W in r.chars ) then
            FS38_Timers.charS := FS38_Timers.charS + Runtime() - t;
            return rec( status := "reject", reason := Concatenation( "characteristic subgroup of order ", String( Size( W ) ), " in all candidates" ),
                        cands := res );
        fi;
    od;
    FS38_Timers.charS := FS38_Timers.charS + Runtime() - t;
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
        r := CALL_WITH_CATCH( FS38_Cheap, [ S ] );
        if r[1] then
            line := FS38_Line( id, r[2] );
        else
            line := Concatenation( String( id ), ";error;", String( r[2] ) );
        fi;
        AppendTo( file, line, ";", Runtime() - t, "\n" );
        n := n + 1;
        if n mod 500 = 0 then
            PrintTo( progressfile, id, " ", Runtime() - t0, "\n" );
        fi;
    od;
    PrintTo( progressfile, "DONE ", b, " ", Runtime() - t0, "\n" );
end;
