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
##        Aut(E) is not a 3-group (fingerprint tables of the few groups of
##        order <= 3^7 with this property, then autpgrp), Aut_S(E) meets
##        O_3(Aut(E)) in Inn(E), Aut(E) is insoluble unless Out_S(E) is
##        cyclic, a prime divisor condition for non-cyclic Out_S(E), and for
##        elementary abelian E of rank <= 4 the class of Aut_S(E) in GL(E)
##        must carry a candidate automizer (look-up tables).
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

# does N/E act faithfully on E/Phi(E)?  (the action factors through N/E as
# [E,E] <= Phi(E)); checked on the coset representatives of E in N
FS38_FaithfulOnFrattiniQuotient := function( N, E, Phi )
    local pcgs, n;
    pcgs := Pcgs( E );
    for n in RightTransversal( N, E ) do
        if n in E then continue; fi;
        if ForAll( pcgs, x -> x^-1 * x^n in Phi ) then return false; fi;
    od;
    return true;
end;

# the elements of N acting trivially on D'/D for every covering pair
FS38_StabilityKernel := function( N, pairs )
    local C, pr, q, Q, H;
    C := N;
    for pr in pairs do
        # the elements of C centralising D'/D (D = pr[1] < D' = pr[2], both
        # normal in N); computed in <C, D'> since C need not contain D'
        H := ClosureGroup( C, pr[2] );
        q := NaturalHomomorphismByNormalSubgroup( H, pr[1] );
        Q := Image( q );
        C := Intersection( C, PreImage( q, Centralizer( Image( q, C ), Image( q, pr[2] ) ) ) );
        if Size( C ) = 1 then break; fi;
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
FS38_GLAdmissible := [];     # admissible T as subgroups of the permutation image
FS38_GLGroups := [];         # the permutation image of GL(n,3)
FS38_GLIso := [];            # the isomorphism GL(n,3) -> permutation group
FS38_GLTables := [];         # the table records with T (perm image) and cands (matrices)
FS38_GLTableTypes := [];     # the T-types covered by the table of GL(n,3)
for n in [ 2 .. 5 ] do
    if n <= 4 then
        f := Concatenation( "/home/user/FusionSystems/order38/data/gl", String( n ), "_table.g" );
    else
        f := "/home/user/FusionSystems/order38/data/gl5_3x3_table.g";
    fi;
    if IsExistingFile( f ) then
        Read( f );
        FS38_GLIso[n] := IsomorphismPermGroup( GL( n, 3 ) );
        FS38_GLGroups[n] := Image( FS38_GLIso[n] );
        FS38_GLTables[n] := List( ValueGlobal( Concatenation( "GLTABLE_", String( n ) ) ), r -> rec( Ttype := r.Ttype,
            T := Image( FS38_GLIso[n], Group( List( r.Tmats, m -> ImmutableMatrix( GF( 3 ), m * One( GF( 3 ) ) ) ) ) ),
            cands := List( r.cands, c -> List( c.gens, m -> ImmutableMatrix( GF( 3 ), m * One( GF( 3 ) ) ) ) ) ) );
        FS38_GLAdmissible[n] := List( Filtered( FS38_GLTables[n], r -> Length( r.cands ) > 0 ), r -> r.T );
        if n <= 4 then
            FS38_GLTableTypes[n] := fail;        # complete for all admissible types
        else
            FS38_GLTableTypes[n] := Set( List( FS38_GLTables[n], r -> r.Ttype ) );
        fi;
    fi;
od;

# Aut_S(E) as a matrix group on the elementary abelian group E
FS38_AutSMatrices := function( S, E, N )
    local pcgs, mats, g;
    pcgs := Pcgs( E );
    mats := [];
    for g in GeneratorsOfGroup( N ) do
        Add( mats, ImmutableMatrix( GF( 3 ), List( pcgs, x -> ExponentsOfPcElement( pcgs, x^g ) ) * One( GF( 3 ) ) ) );
    od;
    return Group( mats, IdentityMat( Length( pcgs ), GF( 3 ) ) );
end;

# The candidate automizers of an elementary abelian subgroup P of S from the
# tables, as lists of automorphisms of P (conjugated so that Aut_S(P) is
# their Sylow 3-subgroup); fail if the tables do not cover (rank, type).
FS38_TableCandidates := function( S, P )
    local n, N, Tmat, Tp, r, g, gmat, pcgs, res, H, mats, type;
    if not IsElementaryAbelian( P ) then return fail; fi;
    n := RankPGroup( P );
    if not IsBound( FS38_GLTables[n] ) then return fail; fi;
    N := Normalizer( S, P );
    type := FS38_SylowType( N / P );
    if type = fail then return []; fi;
    if FS38_GLTableTypes[n] <> fail and not type in FS38_GLTableTypes[n] then return fail; fi;
    Tmat := FS38_AutSMatrices( S, P, N );
    Tp := Image( FS38_GLIso[n], Tmat );
    for r in FS38_GLTables[n] do
        if Size( r.T ) <> Size( Tp ) then continue; fi;
        g := RepresentativeAction( FS38_GLGroups[n], r.T, Tp );
        if g = fail then continue; fi;
        gmat := PreImagesRepresentative( FS38_GLIso[n], g );
        pcgs := Pcgs( P );
        res := [];
        for H in r.cands do
            mats := List( H, m -> gmat^-1 * m * gmat );
            Add( res, List( mats, m -> GroupHomomorphismByImagesNC( P, P, pcgs, List( [ 1 .. n ], i -> PcElementByExponentsNC( pcgs, List( m[i], IntFFE ) ) ) ) ) );
        od;
        return res;
    od;
    return [];      # T is not conjugate to an admissible class
end;

# the fingerprints of the groups of order 3^3..3^7 whose automorphism group
# is not a 3-group (fingerprints.g); a candidate of such an order which is
# not elementary abelian must have one of these fingerprints
if IsExistingFile( "/home/user/FusionSystems/order38/data/fingerprints.g" ) then
    Read( "/home/user/FusionSystems/order38/data/fingerprints.g" );
    FS38_FingerprintSets := List( [ 1 .. 7 ], k -> fail );
    FS38_FingerprintSets1 := List( [ 1 .. 7 ], k -> fail );
    FS38_FingerprintSets2 := List( [ 1 .. 7 ], k -> fail );
    FS38_FingerprintSetsB := List( [ 1 .. 7 ], k -> fail );
    for n in [ 3 .. 7 ] do
        FS38_FingerprintSets[n] := Set( List( FINGERPRINTS[n], x -> x[1]{[ 1 .. 12 ]} ) );
        FS38_FingerprintSets1[n] := Set( List( FINGERPRINTS[n], x -> x[1]{[ 1, 2, 3, 4, 6 ]} ) );
        FS38_FingerprintSets2[n] := Set( List( FINGERPRINTS[n], x -> x[1]{[ 1 .. 11 ]} ) );
        FS38_FingerprintSetsB[n] := Set( List( FINGERPRINTS[n], x -> Concatenation( x[1]{[ 1 .. 11 ]}, [ x[1][13] ] ) ) );
    od;
else
    FS38_FingerprintSets := fail;
fi;
# the fingerprint in three levels: level 1 = [ |E|, |Z|, |Phi|, |E'|, class ],
# level 2 adds exponent, abelian invariants, lower and upper central series,
# |Agemo|, |Omega(Z)|, level 3 adds the class sizes by element order
FS38_Fingerprint1 := function( E )
    return [ Size( E ), Size( Center( E ) ), Size( FrattiniSubgroup( E ) ), Size( DerivedSubgroup( E ) ), NilpotencyClassOfGroup( E ) ];
end;
FS38_Fingerprint2 := function( E, fp1 )
    return [ fp1[1], fp1[2], fp1[3], fp1[4], Exponent( E ), fp1[5], AbelianInvariants( E ), List( LowerCentralSeriesOfGroup( E ), Size ),
             List( UpperCentralSeriesOfGroup( E ), Size ), Size( Agemo( E, 3 ) ), Size( Omega( Center( E ), 3 ) ) ];
end;
# For a group E of class 2 with |E/Z(E)| <= 3^4: the distribution of the
# ranks of the commutator maps y -> [x,y], i.e. of the class sizes (fail
# for other groups); much cheaper than the conjugacy classes
FS38_Breadth := function( E )
    local Z, q, Q, gens, pcZ, res, y, x, vecs;
    if NilpotencyClassOfGroup( E ) <> 2 then return fail; fi;
    Z := Center( E );
    if Index( E, Z ) > 81 then return fail; fi;
    q := NaturalHomomorphismByNormalSubgroup( E, Z ); Q := Image( q );
    gens := GeneratorsOfGroup( E );
    pcZ := Pcgs( DerivedSubgroup( E ) );
    res := [];
    for y in Q do
        if IsOne( y ) then continue; fi;
        x := PreImagesRepresentative( q, y );
        vecs := List( gens, g -> ExponentsOfPcElement( pcZ, Comm( x, g ) ) ) * One( GF( 3 ) );
        Add( res, RankMat( vecs ) );
    od;
    return Collected( res );
end;
FS38_Fingerprint := function( E )
    local fp;
    fp := FS38_Fingerprint2( E, FS38_Fingerprint1( E ) );
    Add( fp, Collected( List( ConjugacyClasses( E ), c -> [ Order( Representative( c ) ), Size( c ) ] ) ) );
    Add( fp, FS38_Breadth( E ) );
    return fp;
end;
# the (order-independent) test: does E have the fingerprint of a group with Aut(E) not a 3-group?
FS38_FingerprintTest := function( E )
    local k, fp1, fp2, br;
    k := LogInt( Size( E ), 3 );
    if FS38_FingerprintSets = fail or k < 3 then return true; fi;
    fp1 := FS38_Fingerprint1( E );
    if not fp1 in FS38_FingerprintSets1[k] then return false; fi;
    fp2 := FS38_Fingerprint2( E, fp1 );
    if not fp2 in FS38_FingerprintSets2[k] then return false; fi;
    if fp1[5] = 2 and Size( E ) / fp1[2] <= 81 then
        br := FS38_Breadth( E );
        if not Concatenation( fp2, [ br ] ) in FS38_FingerprintSetsB[k] then return false; fi;
    fi;
    Add( fp2, Collected( List( ConjugacyClasses( E ), c -> [ Order( Representative( c ) ), Size( c ) ] ) ) );
    return fp2 in FS38_FingerprintSets[k];
end;

# counters: candidates entering each stage
FS38_Counts := rec( cands := 0, pre := 0, classes := 0, type := 0, fingerprint := 0, frattini := 0, chain := 0, elab := 0, aut := 0, radical := 0, kept := 0 );

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
            if q <> fail then C := PreImage( q, C ); fi;
            if not C in cands then Add( cands, C ); fi;
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
          charS, W, result, pre, a, t, elab, n, T, idx;
    Z := Center( S );
    if Index( S, Z ) <= 9 then return rec( status := "reject", reason := "|S:Z(S)| <= 9" ); fi;
    t := Runtime();
    cands := FS38_Candidates( S );
    FS38_Timers.cands := FS38_Timers.cands + Runtime() - t;
    FS38_Counts.cands := FS38_Counts.cands + Length( cands );
    seen := []; seeninv := []; res := [];
    for E in cands do
        t := Runtime();
        if Size( E ) <= 3 or IsCyclic( E ) then continue; fi;
        elab := IsElementaryAbelian( E );
        FS38_Timers.pre := FS38_Timers.pre + Runtime() - t; t := Runtime();
        FS38_Counts.pre := FS38_Counts.pre + 1;
        N := Normalizer( S, E );
        if N = E then FS38_Timers.type := FS38_Timers.type + Runtime() - t; continue; fi;
        idx := Index( N, E );
        # the Sylow type of N/E: for |N:E| <= 9 every type is admissible
        # (C3, C9, 3^2), so the quotient is only formed for larger index
        if idx = 3 then
            type := "C3"; Q := fail;
        else
            q := NaturalHomomorphismByNormalSubgroup( N, E );
            Q := Image( q );
            type := FS38_SylowType( Q );
        fi;
        FS38_Timers.type := FS38_Timers.type + Runtime() - t; t := Runtime();
        if type = fail then continue; fi;
        FS38_Counts.type := FS38_Counts.type + 1;
        Phi := FrattiniSubgroup( E );
        if Index( E, Phi ) < idx^2 then FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t; continue; fi;
        if not IsSubset( E, Centralizer( S, E ) ) then FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t; continue; fi;
        if not elab then
            # the Frattini quotient test before the class test (cheap, selective)
            if not FS38_FaithfulOnFrattiniQuotient( N, E, Phi ) then FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t; continue; fi;
        fi;
        FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t; t := Runtime();
        # one representative per S-class from here on
        inv := [ Size( E ), Size( N ), Size( Center( E ) ), Size( Phi ), Size( DerivedSubgroup( E ) ) ];
        if FS_ClassPosition( S, seen, seeninv, E ) <> fail then FS38_Timers.classes := FS38_Timers.classes + Runtime() - t; continue; fi;
        Add( seen, E ); Add( seeninv, inv );
        FS38_Timers.classes := FS38_Timers.classes + Runtime() - t; t := Runtime();
        FS38_Counts.classes := FS38_Counts.classes + 1;
        if elab then
            # Aut(E) = GL_n(3) is known; the table test for n <= 4
            FS38_Counts.elab := FS38_Counts.elab + 1;
            n := RankPGroup( E );
            if IsBound( FS38_GLAdmissible[n] ) and ( FS38_GLTableTypes[n] = fail or type in FS38_GLTableTypes[n] ) then
                T := Image( FS38_GLIso[n], FS38_AutSMatrices( S, E, N ) );
                if not ForAny( FS38_GLAdmissible[n], T0 -> Size( T0 ) = Size( T ) and IsConjugate( FS38_GLGroups[n], T0, T ) ) then
                    FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t; continue;
                fi;
            elif n = 5 and type = "C9" then
                # no subgroup of GL_5(3) has a cyclic Sylow 3-subgroup of
                # order 9 and a strongly 3-embedded subgroup: a 3-soluble one
                # would need a faithful action of C9 on a {2,5,11,13}-group
                # inside GL_5(3), and the only simple group with cyclic Sylow
                # 3-subgroup of order 9 whose order divides |GL_5(3)| is
                # L2(8), whose smallest faithful module over GF(3) has
                # dimension 7 (see report.tex, Section on look-up tables)
                FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t; continue;
            elif Size( GL( n, 3 ) ) mod FS38_RequiredDivisor( type ) <> 0 then
                FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t; continue;
            fi;
            FS38_Timers.frattini := FS38_Timers.frattini + Runtime() - t;
            FS38_Counts.kept := FS38_Counts.kept + 1;
            Add( res, rec( E := E, order := Size( E ), index := idx, type := type, autorder := Size( GL( n, 3 ) ),
                           elab := true, abelian := true, rank := n, chars := [ E ] ) );
            continue;
        fi;
        FS38_Counts.frattini := FS38_Counts.frattini + 1;
        # the finer chain of characteristic subgroups
        charsE := FS38_CharList( E );
        pairs := FS38_CoveringPairs( E, charsE );
        C := FS38_StabilityKernel( N, pairs );
        FS38_Timers.chain := FS38_Timers.chain + Runtime() - t; t := Runtime();
        if not IsSubset( E, C ) then continue; fi;
        FS38_Counts.chain := FS38_Counts.chain + 1;
        # (R2e) Aut(E) is not a 3-group (autpgrp), and the simple section
        # forced by a non-cyclic Out_S(E) must fit into Out(E)
        a := AutomorphismGroupPGroup( E );
        FS38_Timers.aut := FS38_Timers.aut + Runtime() - t; t := Runtime();
        if a.size = 3^LogInt( a.size, 3 ) then continue; fi;     # Aut(E) is a 3-group
        if a.size mod FS38_RequiredDivisor( type ) <> 0 then continue; fi;
        FS38_Counts.aut := FS38_Counts.aut + 1;
        # the exact radical test Aut_S(E) meet O_3(Aut(E)) = Inn(E), and
        # Aut(E) insoluble unless Out_S(E) is cyclic [Parker-Semeraro]
        if not FS_RadicalTest( S, E ) then FS38_Timers.radical := FS38_Timers.radical + Runtime() - t; continue; fi;
        if type <> "C3" and not IsCyclic( Q ) and IsSolvableGroup( FS_AutHandle( E ).model ) then FS38_Timers.radical := FS38_Timers.radical + Runtime() - t; continue; fi;
        FS38_Timers.radical := FS38_Timers.radical + Runtime() - t;
        FS38_Counts.kept := FS38_Counts.kept + 1;
        Add( res, rec( E := E, order := Size( E ), index := idx, type := type, autorder := a.size,
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
    local id, S, r, t, line, t0, n, out;
    t0 := Runtime(); n := 0;
    b := b - ( ( b - a ) mod step );      # GAP ranges need (b - a) divisible by step
    for id in [ a, a + step .. b ] do
        S := SmallGroup( 6561, id );
        t := Runtime();
        r := CALL_WITH_CATCH( FS38_Cheap, [ S ] );
        if r[1] then
            line := FS38_Line( id, r[2] );
        else
            line := Concatenation( String( id ), ";error;", String( r[2] ) );
        fi;
        # unformatted output (no line wrapping), one line per group
        out := OutputTextFile( file, true ); SetPrintFormattingStatus( out, false );
        AppendTo( out, line, ";", Runtime() - t, "\n" );
        CloseStream( out );
        n := n + 1;
        if n mod 500 = 0 then
            PrintTo( progressfile, id, " ", Runtime() - t0, "\n" );
        fi;
    od;
    PrintTo( progressfile, "DONE ", b, " ", Runtime() - t0, "\n" );
end;
