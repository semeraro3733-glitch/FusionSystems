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
    if IsSolvableGroup( G ) then return Size( G ) <= 50 * FS_Options.latticeBound; fi;
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
    if IsSolvableGroup( G ) then
        cls := List( ConjugacyClassesSubgroups( G ), Representative );
    else
        lat := LatticeByCyclicExtension( G, function( H ) return FS_PPart( Size( H ), p ) <= pp; end );
        cls := List( ConjugacyClassesSubgroups( lat ), Representative );
    fi;
    return Filtered( cls, H -> FS_PPart( Size( H ), p ) = pp );
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
    local S, P, opts, p, h, outd, Mbar, T, Tbar, pp, cls, res, H, g, Tsyl, user, t;
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
    elif FS_LatticeFeasible( Mbar, p, pp ) then
        cls := FS_SubgroupClassesWithPPart( Mbar, p, pp );
        res := [];
        for H in cls do
            Tsyl := SylowSubgroup( H, p );
            if IsNormal( H, Tsyl ) then continue; fi;
            g := RepresentativeAction( Mbar, Tsyl, Tbar );
            if g = fail then continue; fi;
            H := ConjugateSubgroup( H, g );
            if HasStronglyPEmbeddedSubgroup( H, p ) then Add( res, H ); fi;
        od;
        Info( InfoFusionSystems, 2, "automizer candidates for |P| = ", Size( P ), ": |Out(P)| = ", Size( Mbar ),
              ", ", Length( cls ), " subgroup classes with p-part ", pp, ", ", Length( res ), " candidates (",
              Runtime() - t, " ms)" );
    elif IsElementaryAbelian( P ) and ( not IsBound( opts.allowFrames ) or opts.allowFrames ) then
        Info( InfoFusionSystems, 1, "|Out(P)| = ", Size( Mbar ), " for |P| = ", Size( P ),
              " is too large for a complete enumeration; using monomial (frame) candidates only" );
        res := FS_FrameCandidates( S, P, Tbar );
    else
        Info( InfoFusionSystems, 1, "|Out(P)| = ", Size( Mbar ), " for |P| = ", Size( P ),
              " is too large for a complete enumeration of automizer candidates; attempting it anyway" );
        cls := FS_SubgroupClassesWithPPart( Mbar, p, pp );
        res := [];
        for H in cls do
            Tsyl := SylowSubgroup( H, p );
            if IsNormal( H, Tsyl ) then continue; fi;
            g := RepresentativeAction( Mbar, Tsyl, Tbar );
            if g = fail then continue; fi;
            H := ConjugateSubgroup( H, g );
            if HasStronglyPEmbeddedSubgroup( H, p ) then Add( res, H ); fi;
        od;
    fi;
    return List( res, H -> PreImage( outd.q, H ) );
end );

#############################################################################
##
#F  FS_FrameCandidates( <S>, <P>, <Tbar> )
##
##  P elementary abelian of rank n, considered as a vector space V over
##  GF(p), T = Aut_S(P).  A frame is a set of n one-dimensional subspaces
##  of V spanning V; its stabilizer in GL(V) is a monomial group
##  GL(1,p) wr Sym(n).  We consider the T-invariant frames up to the action
##  of N_{GL(V)}(T) and return the subgroups H of the corresponding monomial
##  groups with Tbar as Sylow p-subgroup and a strongly p-embedded subgroup
##  (one for each class).  This covers the automizers of abelian essential
##  subgroups which are "imprimitive" (e.g. in alternating groups) but it is
##  not a complete enumeration.
##
InstallGlobalFunction( FS_FrameCandidates, function( S, P, Tbar )
    local p, h, outd, Mbar, q, n, pcgs, lines, lineOf, Tgens, orbs, frames, res, gensP, i, j, mon, monsub, cls, H, Tsyl, g,
          frame, D, Dgens, Pgens, perm, sigma, vec, img, Hs, W, seen, pos, orbitsOfLines, blocks, fr, candfr, k, l, mat;
    p := PrimePGroup( P );
    h := FS_AutHandle( P );
    outd := FS_OutData( P );
    Mbar := outd.Mbar; q := outd.q;
    pcgs := FS_PcgsOf( P );
    n := Length( pcgs );
    # all one-dimensional subspaces as subgroups
    lines := List( Filtered( AsList( P ), x -> not IsOne( x ) ), x -> SubgroupNC( P, [ x ] ) );
    lines := DuplicateFreeList( lines );
    Tgens := List( GeneratorsOfGroup( Tbar ), x -> h.from( PreImagesRepresentative( q, x ) ) );
    # orbits of T on lines
    orbs := OrbitsDomain( Group( Tgens ), lines, FS_OnImage );
    # T-invariant frames: unions of T-orbits of total size n which are independent
    frames := [];
    candfr := function( chosen, start, size )
        local k, new, gens;
        if size = n then
            gens := Concatenation( List( chosen, o -> List( o, L -> GeneratorsOfGroup( L )[1] ) ) );
            if Size( SubgroupNC( P, gens ) ) = Size( P ) then Add( frames, Concatenation( chosen ) ); fi;
            return;
        fi;
        for k in [ start .. Length( orbs ) ] do
            if size + Length( orbs[k] ) <= n then
                candfr( Concatenation( chosen, [ orbs[k] ] ), k + 1, size + Length( orbs[k] ) );
            fi;
        od;
    end;
    candfr( [], 1, 0 );
    if Length( frames ) = 0 then return []; fi;
    # frames up to the action of W = N_{Out(P)}(Tbar)
    W := Normalizer( Mbar, Tbar );
    seen := []; res := [];
    for frame in frames do
        if ForAny( seen, fr -> RepresentativeAction( W, Set( fr ), Set( frame ),
                 function( fs, x ) local a; a := h.from( PreImagesRepresentative( q, x ) ); return Set( List( fs, L -> ImagesSet( a, L ) ) ); end ) <> fail ) then
            continue;
        fi;
        Add( seen, frame );
        # the monomial group of the frame: generated by scalings of one line and permutations of the lines
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
        cls := FS_SubgroupClassesWithPPart( mon, p, Size( Tbar ) );
        for H in cls do
            Tsyl := SylowSubgroup( H, p );
            if IsNormal( H, Tsyl ) then continue; fi;
            g := RepresentativeAction( Mbar, Tsyl, Tbar );
            if g = fail then continue; fi;
            H := ConjugateSubgroup( H, g );
            if not HasStronglyPEmbeddedSubgroup( H, p ) then continue; fi;
            if ForAny( res, K -> Size( K ) = Size( H ) and RepresentativeAction( Mbar, K, H ) <> fail ) then continue; fi;
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
