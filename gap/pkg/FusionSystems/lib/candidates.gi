#############################################################################
##
##  candidates.gi          FusionSystems package
##
##  Let P be a proto-essential subgroup of S, T = Aut_S(P) and write
##  Out(P) = Aut(P)/Inn(P), Tbar = T/Inn(P).  If P is an essential subgroup
##  of a saturated fusion system F on S then A = Aut_F(P) satisfies
##     (a) T is a Sylow p-subgroup of A,
##     (b) A/Inn(P) has a strongly p-embedded subgroup,
##     (c) N_A(T) contains Aut_{N_B(P)}(P) where B = Aut_F(S) x| S, with
##         equality if N_S(P) is contained in no B-conjugate of an
##         essential subgroup (then every element of N_{Aut_F(P)}(T) extends
##         to N_S(P) and further to S by the extension axiom and Alperin's
##         theorem).
##
##  ProtoEssentialAutomizerCandidates(S, P) returns the subgroups A of
##  Aut(P) satisfying (a) and (b), one for each Aut(P)-conjugacy class: if
##  H <= Out(P) has a Sylow p-subgroup conjugate to Tbar then all conjugates
##  of H containing Tbar as a Sylow p-subgroup are conjugate under
##  W = N_{Out(P)}(Tbar) (Sylow's theorem in H).  The conjugates under W
##  compatible with a given Borel subgroup are produced later by
##  FS_BorelCompatibleCandidates.
##
##  The enumeration of the subgroups of Out(P) with p-part |Tbar| uses the
##  cyclic extension method with the hereditary bound |H|_p <= |Tbar|.
##

InstallGlobalFunction( FS_OutData, function( P )
    local h, q;
    h := FS_AutHandle( P );
    if not IsBound( h.out ) then
        q := NaturalHomomorphismByNormalSubgroup( h.model, h.inn );
        h.out := rec( q := q, Mbar := Image( q ) );
    fi;
    return h.out;
end );

InstallGlobalFunction( FS_LatticeFeasible, function( G, p, pp )
    if IsSolvableGroup( G ) then return Size( G ) <= FS_Options.solvableLatticeBound; fi;
    return Size( G ) <= FS_Options.latticeBound;
end );

#############################################################################
##
#F  FS_SubgroupClassesWithPPart( <G>, <p>, <pp> )
##
##  Representatives of the conjugacy classes of subgroups H of G with
##  |H|_p = pp.
##
InstallGlobalFunction( FS_SubgroupClassesWithPPart, function( G, p, pp )
    local cls, lat;
    if Size( G ) = 1 then return []; fi;
    if IsSolvableGroup( G ) or not IsBound( FS_Options.cyclicExtension ) or not FS_Options.cyclicExtension then
        cls := List( ConjugacyClassesSubgroups( G ), Representative );
    else
        lat := LatticeByCyclicExtension( G, function( H ) return FS_PPart( Size( H ), p ) <= pp; end );
        cls := List( ConjugacyClassesSubgroups( lat ), Representative );
    fi;
    return Filtered( cls, H -> FS_PPart( Size( H ), p ) = pp );
end );

#############################################################################
##
#F  FS_PerfectCandidates( <G>, <p>, <T> )
##
##  The subgroups H of G which are not p-soluble, have T as a Sylow
##  p-subgroup and have a strongly p-embedded subgroup, one for each
##  conjugacy class (conjugated so that T <= H).
##
##  Let H be such a group and Y = H^(infinity) its perfect residuum.  Then
##  Y is perfect and normal in H, T_0 = T meet Y is a Sylow p-subgroup of
##  Y and, by the Frattini argument, H = Y N_H(T_0) with
##  T <= N_H(T_0) <= R := N_G(Y) meet N_G(T_0).  Hence H = Y M for a
##  subgroup M of R containing T, and T normalizes Y.  So we run through
##  the perfect subgroups Y of G (up to conjugacy) with p | |Y| and
##  |Y|_p <= |T|, their conjugates whose Sylow p-subgroup lies in T and
##  which are normalized by T, and the subgroups M of R containing T.
##
BindGlobal( "FS_PerfectCandidates", function( G, p, T )
    local perf, res, W, Y0, TY, subsU, U, g, Y, NU, NY, tr, n, Yn, NYn, R0, ints, M, H, pp;
    pp := Size( T );
    perf := Filtered( RepresentativesPerfectSubgroups( G ), Y -> Size( Y ) mod p = 0 and FS_PPart( Size( Y ), p ) <= pp );
    W := Normalizer( G, T );
    res := [];
    for Y0 in perf do
        TY := SylowSubgroup( Y0, p );
        subsU := Filtered( List( ConjugacyClassesSubgroups( T ), Representative ), U -> Size( U ) = Size( TY ) );
        subsU := Concatenation( List( subsU, U -> AsList( ConjugacyClassSubgroups( T, U ) ) ) );
        for U in subsU do
            g := RepresentativeAction( G, TY, U );
            if g = fail then continue; fi;
            Y := ConjugateSubgroup( Y0, g );
            NY := Normalizer( G, Y );
            NU := Normalizer( G, U );
            if Size( U ) = pp then
                tr := [ One( G ) ];
            else
                tr := RightTransversal( NU, Intersection( NU, NY ) );
            fi;
            for n in tr do
                # T must normalize Y^n, i.e. T^(n^-1) <= N(Y)
                if not IsSubset( NY, ConjugateSubgroup( T, n^-1 ) ) then continue; fi;
                Yn := ConjugateSubgroup( Y, n );
                R0 := ConjugateSubgroup( Intersection( NY, NU ), n );
                if not IsSubset( R0, T ) then continue; fi;
                if Size( R0 ) = Size( T ) then
                    ints := [ T ];
                else
                    ints := Concatenation( [ T, R0 ], IntermediateSubgroups( R0, T ).subgroups );
                fi;
                for M in ints do
                    H := ClosureGroup( Yn, M );
                    if FS_PPart( Size( H ), p ) <> pp then continue; fi;
                    if ForAny( res, K -> Size( K ) = Size( H ) and RepresentativeAction( W, K, H ) <> fail ) then continue; fi;
                    if HasStronglyPEmbeddedSubgroup( H, p ) then Add( res, H ); fi;
                od;
            od;
        od;
    od;
    return res;
end );

#############################################################################
##
#F  FS_CandidatesInGroup( <G>, <p>, <T>, <elab>, <opts> )
##
##  The subgroups H of G with T as Sylow p-subgroup and a strongly
##  p-embedded subgroup, one for each G-class (conjugated so that T <= H),
##  by the method appropriate for the size of G:
##   - the subgroup lattice of G if G is small enough (complete);
##   - otherwise the perfect subgroup method FS_PerfectCandidates, which is
##     complete when T is neither cyclic nor quaternion (then no candidate
##     is p-soluble), supplemented, if T is cyclic or quaternion, by the
##     p-soluble candidates inside the monomial groups of the T-invariant
##     frames when elab = true (G = GL(n,p)); in this last case the
##     enumeration of p-soluble candidates is not complete, which is
##     reported through InfoFusionSystems.
##
BindGlobal( "FS_CandidatesInGroup", function( G, p, T, elab, opts )
    local pp, res, cls, H, Tsyl, g, r, cyc;
    pp := Size( T );
    cyc := FS_IsQuaternionOrCyclic( T );
    if FS_LatticeFeasible( G, p, pp ) then
        cls := FS_SubgroupClassesWithPPart( G, p, pp );
        res := [];
        for H in cls do
            Tsyl := SylowSubgroup( H, p );
            if IsNormal( H, Tsyl ) then continue; fi;
            g := RepresentativeAction( G, Tsyl, T );
            if g = fail then continue; fi;
            H := ConjugateSubgroup( H, g );
            if HasStronglyPEmbeddedSubgroup( H, p ) then Add( res, H ); fi;
        od;
        return res;
    fi;
    if Size( G ) > FS_Options.perfectBound then
        Info( InfoFusionSystems, 1, "|G| = ", Size( G ), " is too large for the enumeration of automizer candidates" );
        return [];
    fi;
    r := CALL_WITH_CATCH( FS_PerfectCandidates, [ G, p, T ] );
    if r[1] then
        res := r[2];
        if not cyc then return res; fi;
        Info( InfoFusionSystems, 1, "|G| = ", Size( G ), ": the p-soluble automizer candidates are not enumerated completely" );
    else
        Info( InfoFusionSystems, 1, "|G| = ", Size( G ), ": perfect subgroups could not be computed" );
        res := [];
    fi;
    return res;
end );

#############################################################################
##
#F  ProtoEssentialAutomizerCandidates( <S>, <P>[, <opts>] )
##
##  Returns a list of subgroups of the automorphism group model of P (see
##  FS_AutHandle) containing Inn(P), with Aut_S(P) as a Sylow p-subgroup
##  and with Out having a strongly p-embedded subgroup, one for each
##  Aut(P)-class.  Options: opts.candidates, a function (S, P) returning
##  either lists of automorphisms of P or subgroups of the model, used
##  instead of the enumeration; opts.allowFrames (default true): use the
##  frame method for elementary abelian P with a huge Out(P).
##
InstallGlobalFunction( ProtoEssentialAutomizerCandidates, function( arg )
    local S, P, opts, p, h, outd, Mbar, T, Tbar, pp, cls, res, H, g, Tsyl, user, t, W;
    S := arg[1]; P := arg[2];
    opts := rec();
    if Length( arg ) > 2 then opts := arg[3]; fi;
    p := PrimePGroup( S );
    h := FS_AutHandle( P );
    outd := FS_OutData( P );
    Mbar := outd.Mbar;
    T := FS_AutSubgroup( h, FS_AutomizerGenerators( S, P ) );
    Tbar := Image( outd.q, T );
    pp := Size( Tbar );
    if pp = 1 then return []; fi;
    t := Runtime();
    if IsBound( opts.candidates ) then
        user := opts.candidates( S, P );
        res := [];
        for H in user do
            if IsGroup( H ) and IsSubset( h.model, H ) then
                H := Image( outd.q, H );
            else
                if IsGroup( H ) then H := GeneratorsOfGroup( H ); fi;
                H := Image( outd.q, FS_AutSubgroup( h, H ) );
            fi;
            if FS_PPart( Size( H ), p ) = pp and IsSubset( H, Tbar ) and HasStronglyPEmbeddedSubgroup( H, p ) then
                Add( res, H );
            fi;
        od;
    else
        res := FS_CandidatesInGroup( Mbar, p, Tbar, IsElementaryAbelian( P ), opts );
        if IsElementaryAbelian( P ) and FS_IsQuaternionOrCyclic( Tbar ) and not FS_LatticeFeasible( Mbar, p, pp )
           and ( not IsBound( opts.allowFrames ) or opts.allowFrames ) then
            Info( InfoFusionSystems, 1, "|Out(P)| = ", Size( Mbar ), " for |P| = ", Size( P ),
                  ": adding the candidates from the monomial groups of the Aut_S(P)-invariant frames" );
            W := Normalizer( Mbar, Tbar );
            for H in FS_FrameCandidates( S, P, Tbar, opts ) do
                if ForAny( res, K -> Size( K ) = Size( H ) and RepresentativeAction( W, K, H ) <> fail ) then continue; fi;
                Add( res, H );
            od;
        fi;
        Info( InfoFusionSystems, 2, "automizer candidates for |P| = ", Size( P ), ": |Out(P)| = ", Size( Mbar ),
              ", ", Length( res ), " candidates (", Runtime() - t, " ms)" );
    fi;
    return List( res, H -> PreImage( outd.q, H ) );
end );

#############################################################################
##
#F  FS_FrameCandidates( <S>, <P>, <Tbar>, <opts> )
##
##  P elementary abelian of rank n, considered as a vector space V over
##  GF(p), T = Aut_S(P).  A frame is a set of n one-dimensional subspaces
##  of V spanning V; its stabilizer in GL(V) is a monomial group
##  GL(1,p) wr Sym(n).  A T-invariant frame is a union of T-orbits of
##  lines, i.e. a decomposition of V into transitive permutation modules
##  for T with chosen base lines; two T-invariant frames of the same type
##  (multiset of orbit lengths, with the same stabilizers) are conjugate
##  under C_{GL(V)}(T) (map base lines to base lines and extend
##  T-equivariantly).  We therefore take one frame of each type and return
##  the subgroups H of the corresponding monomial groups with Tbar as Sylow
##  p-subgroup and a strongly p-embedded subgroup, one for each class.
##  This covers the "imprimitive" automizers of abelian essential subgroups
##  (e.g. in alternating groups) but it is not a complete enumeration of
##  all automizer candidates.
##
InstallGlobalFunction( FS_FrameCandidates, function( S, P, Tbar, opts )
    local p, h, outd, Mbar, q, n, pcgs, lines, Tgens, Tgrp, orbs, frames, types, res, i, mon, cls, H,
          frame, Dgens, Pgens, sigma, img, W, candfr, typ, stabsize, D, NT, Ks, K, X, ints, N, L, pts, act, red, monS, TS;
    p := PrimePGroup( P );
    h := FS_AutHandle( P );
    outd := FS_OutData( P );
    Mbar := outd.Mbar; q := outd.q;
    pcgs := FS_PcgsOf( P );
    n := Length( pcgs );
    lines := DuplicateFreeList( List( Filtered( AsList( P ), x -> not IsOne( x ) ), x -> SubgroupNC( P, [ x ] ) ) );
    Tgens := List( GeneratorsOfGroup( Tbar ), x -> h.from( PreImagesRepresentative( q, x ) ) );
    Tgrp := Group( Tgens );
    orbs := OrbitsDomain( Tgrp, lines, FS_OnImage );
    # the type of an orbit: its length and the order of the stabilizer of a line
    stabsize := List( orbs, o -> Size( Tbar ) / Length( o ) );
    frames := []; types := [];
    candfr := function( chosen, start, size )
        local k, gens, t;
        if size = n then
            gens := Concatenation( List( chosen, k -> List( orbs[k], L -> GeneratorsOfGroup( L )[1] ) ) );
            if Size( SubgroupNC( P, gens ) ) = Size( P ) then
                t := SortedList( List( chosen, k -> [ Length( orbs[k] ), stabsize[k] ] ) );
                if not t in types then
                    Add( types, t );
                    Add( frames, Concatenation( List( chosen, k -> orbs[k] ) ) );
                fi;
            fi;
            return;
        fi;
        for k in [ start .. Length( orbs ) ] do
            if size + Length( orbs[k] ) <= n then
                candfr( Concatenation( chosen, [ k ] ), k + 1, size + Length( orbs[k] ) );
            fi;
        od;
    end;
    candfr( [], 1, 0 );
    Info( InfoFusionSystems, 2, Length( frames ), " types of T-invariant frames: ", types );
    if Length( frames ) = 0 then return []; fi;
    W := Normalizer( Mbar, Tbar );
    res := [];
    for frame in frames do
        # the monomial group of the frame
        Pgens := List( frame, L -> GeneratorsOfGroup( L )[1] );
        Dgens := [];
        for i in [ 1 .. n ] do
            img := ShallowCopy( Pgens );
            img[i] := Pgens[i] ^ PrimitiveRootMod( p );
            Add( Dgens, GroupHomomorphismByImagesNC( P, P, Pgens, img ) );
        od;
        for sigma in GeneratorsOfGroup( SymmetricGroup( n ) ) do
            img := List( [ 1 .. n ], i -> Pgens[ i ^ sigma ] );
            Add( Dgens, GroupHomomorphismByImagesNC( P, P, Pgens, img ) );
        od;
        mon := Image( q, FS_AutSubgroup( h, Dgens ) );
        if not IsSubset( mon, Tbar ) then continue; fi;
        # the monomial group acts faithfully on the (p-1)n non-trivial
        # multiples of the frame generators; all subgroup computations are
        # done in this small permutation representation
        pts := Concatenation( List( Pgens, g -> List( [ 1 .. p - 1 ], k -> g^k ) ) );
        act := function( pt, x ) return ImagesRepresentative( h.from( PreImagesRepresentative( q, x ) ), pt ); end;
        red := ActionHomomorphism( mon, pts, act );
        monS := Image( red, mon );
        TS := Image( red, Tbar );
        cls := FS_CandidatesInGroup( monS, p, TS, false, opts );
        if not FS_LatticeFeasible( monS, p, Size( TS ) ) and FS_IsQuaternionOrCyclic( TS ) then
            # the p-soluble candidates H = K N with K = O_{p'}(H) inside the
            # diagonal subgroup D of the monomial group and N <= N_mon(T)
            D := Image( red, Image( q, FS_AutSubgroup( h, Dgens{[ 1 .. n ]} ) ) );
            NT := Normalizer( monS, TS );
            Ks := SubgroupsSolvableGroup( D, rec( actions := List( GeneratorsOfGroup( TS ), x -> ConjugatorAutomorphismNC( D, x ) ) ) );
            for K in Ks do
                if Size( K ) = 1 then continue; fi;
                X := Normalizer( NT, K );
                if Size( X ) = Size( TS ) then
                    ints := [ TS ];
                else
                    ints := Concatenation( [ TS, X ], IntermediateSubgroups( X, TS ).subgroups );
                fi;
                for N in ints do
                    if FS_PPart( Size( N ), p ) <> Size( TS ) then continue; fi;
                    H := ClosureGroup( K, N );
                    if FS_PPart( Size( H ), p ) <> Size( TS ) then continue; fi;
                    if ForAny( cls, L -> Size( L ) = Size( H ) and RepresentativeAction( monS, L, H ) <> fail ) then continue; fi;
                    if HasStronglyPEmbeddedSubgroup( H, p ) then Add( cls, H ); fi;
                od;
            od;
        fi;
        Info( InfoFusionSystems, 2, "frame of type ", types[ Position( frames, frame ) ], ": ", Length( cls ),
              " candidates in the monomial group" );
        cls := List( cls, H -> PreImage( red, H ) );
        for H in cls do
            if Length( frames ) > 1 and ForAny( res, K -> Size( K ) = Size( H ) and RepresentativeAction( W, K, H ) <> fail ) then continue; fi;
            Add( res, H );
        od;
    od;
    return res;
end );

#############################################################################
##
#F  FS_AutBGenerators( <F>, <P> )
##
##  Generators of Aut_{N_B(P)}(P), the automorphisms of P induced by the
##  elements of B = Aut_F(S) x| S normalizing P: Aut_S(P) together with
##  (c followed by conjugation by s) for the elements c of the complement
##  with c(P) S-conjugate to P.
##
InstallGlobalFunction( FS_AutBGenerators, function( F, P )
    local S, gens, c, Y, s, pcP;
    S := F!.S;
    gens := FS_AutSGenerators( F, P );
    pcP := FS_PcgsOf( P );
    for c in FS_ComplementElements( F ) do
        if IsOne( c ) then continue; fi;
        Y := ImagesSet( c, P );
        if Y = P then s := One( S ); else s := RepresentativeAction( S, Y, P ); fi;
        if s <> fail then
            Add( gens, GroupHomomorphismByImagesNC( P, P, pcP, List( pcP, x -> ImagesRepresentative( c, x )^s ) ) );
        fi;
    od;
    return gens;
end );

#############################################################################
##
#F  FS_TransportCandidate( <A>, <hP>, <hQ>, <theta> )
##
##  A a subgroup of the model of Aut(P), theta: P -> Q an isomorphism;
##  returns theta^-1 A theta as a subgroup of the model of Aut(Q).
##
InstallGlobalFunction( FS_TransportCandidate, function( A, hP, hQ, theta )
    return SubgroupNC( hQ.model, List( GeneratorsOfGroup( A ), x -> hQ.to( FS_TransportAut( hP.from( x ), theta ) ) ) );
end );

#############################################################################
##
#F  FS_CoreCompatible( <F0>, <P>, <A> )
##
##  F0 a fusion system object carrying S and Aut_F(S) (the essential data
##  of F0 is ignored), A a subgroup of the model of Aut(P) with T = Aut_S(P)
##  as Sylow p-subgroup.  Let X be the largest subgroup of P normal in S and
##  invariant under Aut_F(S) and N_A(T).  In a saturated fusion system with
##  Aut_F(P) = A the group Y = < Aut_B(X), N_A(T)|_X > is contained in
##  Aut_F(X) and, as X is normal in S, N_{Aut_F(X)}(Aut_S(X)) = Aut_B(X).
##  We test this necessary condition.
##
InstallGlobalFunction( FS_CoreCompatible, function( F0, P, A )
    local S, h, T, NT, auts, X, hX, AutB, Y, AutS;
    S := F0!.S;
    h := FS_AutHandle( P );
    T := FS_AutSubgroup( h, FS_AutSGenerators( F0, P ) );
    NT := Normalizer( A, T );
    auts := Concatenation( FS_InnerAutGenerators( S ), F0!.autSgens, List( GeneratorsOfGroup( NT ), h.from ) );
    X := FS_LargestInvariantSubgroup( Core( S, P ), auts );
    if Size( X ) = 1 then return true; fi;
    hX := FS_AutHandle( X );
    AutB := FS_AutSubgroup( hX, FS_AutBGenerators( F0, X ) );
    AutS := FS_AutSubgroup( hX, FS_AutSGenerators( F0, X ) );
    Y := SubgroupNC( hX.model, Concatenation( GeneratorsOfGroup( AutB ),
             List( GeneratorsOfGroup( NT ), x -> hX.to( FS_RestrictAut( h.from( x ), X ) ) ) ) );
    return Size( Normalizer( Y, AutS ) ) = Size( AutB );
end );

#############################################################################
##
#F  FS_BorelCompatibleCandidates( <F0>, <P>, <classcands>, <maxenough> )
##
##  F0 a fusion system object carrying S and Aut_F(S); classcands the
##  output of ProtoEssentialAutomizerCandidates for P (or transported to
##  P); maxenough = true if N_S(P) is contained in no B-conjugate of a
##  proto-essential subgroup.  Returns all subgroups A of the model of
##  Aut(P) conjugate under W = N_{Aut(P)}(T) to a member of classcands with
##  N_A(T) >= Aut_B(P) (= if maxenough) which pass the core test.
##
InstallGlobalFunction( FS_BorelCompatibleCandidates, function( F0, P, classcands, maxenough )
    local S, p, h, M, T, W, AutB, res, A, NA, subs, sw, w, NW, n, cand, found, tr;
    S := F0!.S; p := F0!.p;
    h := FS_AutHandle( P );
    M := h.model;
    T := FS_AutSubgroup( h, FS_AutSGenerators( F0, P ) );
    AutB := FS_AutSubgroup( h, FS_AutBGenerators( F0, P ) );
    W := Normalizer( M, T );
    NW := Normalizer( W, AutB );
    res := [];
    for A in classcands do
        NA := Normalizer( A, T );
        if Size( NA ) mod Size( AutB ) <> 0 then continue; fi;
        if maxenough then
            if Size( NA ) <> Size( AutB ) then continue; fi;
            subs := [ NA ];
        else
            # the subgroups of NA of order |AutB| containing T
            subs := Filtered( List( ConjugacyClassesSubgroups( NA ), Representative ), U -> Size( U ) = Size( AutB ) );
            subs := Concatenation( List( subs, U -> AsList( ConjugacyClassSubgroups( NA, U ) ) ) );
            subs := Filtered( subs, U -> IsSubset( U, T ) );
        fi;
        for sw in subs do
            w := RepresentativeAction( W, sw, AutB );
            if w = fail then continue; fi;
            cand := ConjugateSubgroup( A, w );
            # all conjugates cand^n, n in NW, modulo the normalizer of cand
            tr := RightTransversal( NW, Intersection( NW, Normalizer( M, cand ) ) );
            for n in tr do
                found := ConjugateSubgroup( cand, n );
                if ForAny( res, K -> K = found ) then continue; fi;
                if FS_CoreCompatible( F0, P, found ) then Add( res, found ); fi;
            od;
        od;
    od;
    return res;
end );
