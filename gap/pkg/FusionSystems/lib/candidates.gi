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
#F  FS_PSolubleCyclicCandidates( <G>, <p>, <T> )
##
##  T a cyclic p-subgroup of G.  The p-soluble subgroups H of G with T as a
##  Sylow p-subgroup and O_p(H) = 1 (for cyclic T this is equivalent to H
##  having a strongly p-embedded subgroup), one for each G-class, conjugated
##  so that T <= H; or fail if the enumeration is not feasible.
##
##  Such an H has Q := O_{p'}(H) <> 1, T acts faithfully on Q, and H/Q has
##  the normal Sylow p-subgroup QT/Q (H/Q is p-soluble with O_{p'}(H/Q) = 1,
##  so it embeds into the automorphism group of its cyclic normal subgroup
##  O_p(H/Q) modulo that subgroup, which is abelian), so that H = QT'R with
##  T' a G-conjugate of T normalizing Q and R a p'-subgroup of N_G(QT').
##  The p'-subgroups Q are enumerated through the soluble radical: Q R/R
##  is a soluble p'-subgroup of G/Rad(G) (taken from the subgroup lattice of
##  G/Rad(G)), and inside its (soluble) preimage L every p'-subgroup lies
##  in a Hall p'-subgroup of L.  The conjugates T' of T normalizing Q are
##  found from the double cosets N_G(T) g N_G(Q).
##
InstallGlobalFunction( FS_PSolubleCyclicCandidates, function( G, p, T )
    local pp, R, nat, Gbar, lat, Qs, Qb, L, pr, K, Qc, Q, res, N, NT, dc, Tp, y, QT, M, nat2, Mb, Rbs, Kb, Rc, H, g, nT,
          Tps, tgens, t0, c, x, Qg, Qs2, tr, act, fixed, orb;
    pp := Size( T );
    if not IsCyclic( T ) then return fail; fi;
    t0 := First( GeneratorsOfGroup( T ), x -> Order( x ) = pp );
    if t0 = fail then t0 := First( T, x -> Order( x ) = pp ); fi;
    R := RadicalGroup( G );
    nat := NaturalHomomorphismByNormalSubgroup( G, R );
    Gbar := Image( nat );
    if Size( Gbar ) > FS_Options.radicalLatticeBound then
        Info( InfoFusionSystems, 2, "FS_PSolubleCyclicCandidates: |G/Rad(G)| = ", Size( Gbar ), " too large" );
        return fail;
    fi;
    # the p'-subgroups Q of G up to conjugacy, by the image in G/Rad(G)
    if Size( Gbar ) = 1 then
        lat := [ Gbar ];
    else
        lat := List( ConjugacyClassesSubgroups( Gbar ), Representative );
        lat := Filtered( lat, Y -> Size( Y ) mod p <> 0 and IsSolvableGroup( Y ) );
    fi;
    Qs := [];
    for Qb in lat do
        L := PreImage( nat, Qb );
        pr := Difference( PrimeDivisors( Size( L ) ), [ p ] );
        if Length( pr ) = 0 then continue; fi;
        K := HallSubgroup( L, pr );
        if Size( K ) > FS_Options.hallLatticeBound then
            Info( InfoFusionSystems, 2, "FS_PSolubleCyclicCandidates: Hall p'-subgroup of order ", Size( K ), " too large" );
            return fail;
        fi;
        # (subgroups of K which are G-conjugate but not K-conjugate are
        # both kept; the resulting duplicate candidates are removed below)
        for Qc in ConjugacyClassesSubgroups( K ) do
            Q := Representative( Qc );
            if Size( Q ) = 1 or Size( Image( nat, Q ) ) <> Size( Qb ) then continue; fi;
            Add( Qs, Q );
        od;
    od;
    Info( InfoFusionSystems, 3, "FS_PSolubleCyclicCandidates: ", Length( Qs ), " classes of p'-subgroups" );
    res := [];
    NT := Normalizer( G, T );
    nT := 0;
    tgens := Filtered( List( [ 1 .. pp ], k -> t0^k ), x -> Order( x ) = pp );
    for Q in Qs do
        # T must act faithfully on Q
        if Size( AutomorphismGroup( Q ) ) mod p <> 0 then continue; fi;
        N := Normalizer( G, Q );
        if Size( N ) mod pp <> 0 then continue; fi;
        Info( InfoFusionSystems, 4, "FS_PSolubleCyclicCandidates: |Q| = ", Size( Q ), ", |G:N(Q)| = ", Size( G ) / Size( N ), " (", Runtime(), " ms)" );
        # the pairs ( Q*, T* ) with Q* conjugate to Q, T* conjugate to T and
        # T* <= N_G(Q*), up to simultaneous conjugacy, as triples
        # [ Q*, T*, g ] with T*^g = T: when Q has few conjugates, the
        # T-invariant conjugates of Q (up to N_G(T)-conjugacy) with T* = T;
        # otherwise N is small and the conjugates of T inside N are found
        # from the conjugacy classes of elements of N
        Tps := [];
        if Size( N ) > FS_Options.smallNormalizerBound and Size( G ) / Size( N ) <= FS_Options.conjugateBound then
            # the T-invariant conjugates Q^g are the fixed points of T on the
            # cosets N g (Q^g is T-invariant iff T <= N^g iff N g t = N g);
            # N_G(T) permutes them, one representative per orbit is kept
            tr := RightTransversal( G, N );
            act := function( i, g ) return PositionCanonical( tr, tr[i] * g ); end;
            fixed := Filtered( [ 1 .. Length( tr ) ], i -> act( i, t0 ) = i );
            for orb in OrbitsDomain( NT, fixed, act ) do
                Add( Tps, [ ConjugateSubgroup( Q, tr[ orb[1] ] ), T, One( G ) ] );
            od;
        else
            for c in ConjugacyClasses( N ) do
                x := Representative( c );
                if Order( x ) <> pp then continue; fi;
                Tp := Subgroup( N, [ x ] );
                if ForAny( Tps, U -> IsConjugate( N, U[2], Tp ) ) then continue; fi;
                g := fail;
                for y in tgens do
                    g := RepresentativeAction( G, x, y );
                    if g <> fail then break; fi;
                od;
                if g = fail then continue; fi;
                Add( Tps, [ Q, Tp, g ] );
            od;
        fi;
        Info( InfoFusionSystems, 4, "FS_PSolubleCyclicCandidates: ", Length( Tps ), " pairs for this Q (", Runtime(), " ms)" );
        for dc in Tps do
            Qs2 := dc[1]; Tp := dc[2]; g := dc[3];
            y := GeneratorsOfGroup( Tp )[1]^( pp / p );
            if ForAll( GeneratorsOfGroup( Qs2 ), q -> q^y = q ) then continue; fi;   # T* must act faithfully on Q*
            nT := nT + 1;
            QT := ClosureGroup( Qs2, Tp );
            M := Normalizer( Normalizer( G, Qs2 ), QT );
            nat2 := NaturalHomomorphismByNormalSubgroup( M, QT );
            Mb := Image( nat2 );
            pr := Difference( PrimeDivisors( Size( Mb ) ), [ p ] );
            if Length( pr ) = 0 then
                Rbs := [ TrivialSubgroup( Mb ) ];
            elif IsSolvableGroup( Mb ) then
                Kb := HallSubgroup( Mb, pr );
                Rbs := List( ConjugacyClassesSubgroups( Kb ), Representative );
            elif Size( Mb ) <= FS_Options.radicalLatticeBound then
                Rbs := Filtered( List( ConjugacyClassesSubgroups( Mb ), Representative ), Y -> Size( Y ) mod p <> 0 );
            else
                Info( InfoFusionSystems, 2, "FS_PSolubleCyclicCandidates: N(QT)/QT of order ", Size( Mb ), " too large" );
                return fail;
            fi;
            for Rc in Rbs do
                H := ConjugateSubgroup( PreImage( nat2, Rc ), g );
                if ForAny( res, X -> Size( X ) = Size( H ) and RepresentativeAction( NT, X, H ) <> fail ) then continue; fi;
                if HasStronglyPEmbeddedSubgroup( H, p ) then Add( res, H ); fi;
            od;
        od;
    od;
    Info( InfoFusionSystems, 3, "FS_PSolubleCyclicCandidates: ", nT, " pairs (Q, T'), ", Length( res ), " candidates" );
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
    local pp, res, cls, H, Tsyl, g, r, cyc, psol, W, K;
    pp := Size( T );
    cyc := FS_IsQuaternionOrCyclic( T );
    if IsSolvableGroup( G ) then
        # every subgroup is p-soluble, and a p-soluble group with a strongly
        # p-embedded subgroup has cyclic or quaternion Sylow p-subgroups
        if not cyc then return []; fi;
        if IsCyclic( T ) and Size( G ) > FS_Options.solvableLatticeBound then
            psol := FS_PSolubleCyclicCandidates( G, p, T );
            if psol <> fail then
                Info( InfoFusionSystems, 2, "|G| = ", Size( G ), " soluble: ", Length( psol ), " automizer candidates (complete)" );
                return psol;
            fi;
        fi;
    fi;
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
        FS_Diagnostics.incomplete := true;
        Add( FS_Diagnostics.messages, Concatenation( "|G| = ", String( Size( G ) ), ": too large for the enumeration of automizer candidates" ) );
        return [];
    fi;
    r := CALL_WITH_CATCH( FS_PerfectCandidates, [ G, p, T ] );
    if r[1] then
        res := r[2];
        if not cyc then return res; fi;
        # the p-soluble candidates (only possible for cyclic or quaternion T)
        psol := fail;
        if IsCyclic( T ) then psol := FS_PSolubleCyclicCandidates( G, p, T ); fi;
        if psol <> fail then
            W := Normalizer( G, T );
            for H in psol do
                if not ForAny( res, K -> Size( K ) = Size( H ) and RepresentativeAction( W, K, H ) <> fail ) then Add( res, H ); fi;
            od;
            Info( InfoFusionSystems, 2, "|G| = ", Size( G ), ": ", Length( psol ), " p-soluble automizer candidates (complete)" );
            return res;
        fi;
        Info( InfoFusionSystems, 1, "|G| = ", Size( G ), ": the p-soluble automizer candidates are not enumerated completely" );
        FS_Diagnostics.incomplete := true;
        Add( FS_Diagnostics.messages, Concatenation( "|G| = ", String( Size( G ) ), ": p-soluble automizer candidates incomplete" ) );
    else
        Info( InfoFusionSystems, 1, "|G| = ", Size( G ), ": perfect subgroups could not be computed" );
        FS_Diagnostics.incomplete := true;
        Add( FS_Diagnostics.messages, Concatenation( "|G| = ", String( Size( G ) ), ": perfect subgroups could not be computed" ) );
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
    user := fail;
    if IsBound( opts.candidates ) then
        # a user function; it may return fail to ask for the default enumeration
        user := opts.candidates( S, P );
    fi;
    if user <> fail then
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
            user := FS_FrameCandidates( S, P, Tbar, opts );
            user.extra := List( res, H -> PreImage( outd.q, H ) );
            FS_Diagnostics.incomplete := true;
            Add( FS_Diagnostics.messages, Concatenation( "|P| = ", String( Size( P ) ), " elementary abelian, |Out(P)| = ", String( Size( Mbar ) ), ": frame method (incomplete)" ) );
            Info( InfoFusionSystems, 2, "automizer candidates for |P| = ", Size( P ), ": ", FS_CandCount( user ),
                  " candidates (", Runtime() - t, " ms)" );
            return user;
        fi;
        Info( InfoFusionSystems, 2, "automizer candidates for |P| = ", Size( P ), ": |Out(P)| = ", Size( Mbar ),
              ", ", Length( res ), " candidates (", Runtime() - t, " ms)" );
    fi;
    return List( res, H -> PreImage( outd.q, H ) );
end );

#############################################################################
##
##  The frame method for elementary abelian P with a huge Out(P) = GL(V).
##
##  Let T = Aut_S(P) = <u> be of order p.  A frame is a set of n lines of V
##  spanning V; its stabilizer in GL(V) is the monomial group
##  GL(1,p) wr Sym(n).  A u-invariant frame is a union of <u>-orbits of
##  lines (of length 1 or p), i.e. a decomposition of V into permutation
##  modules for <u> with chosen base lines.  Its type is the multiset of
##  orbit lengths.  Two u-invariant frames of the same type are conjugate
##  under C_{GL(V)}(u): the linear map sending base vectors to base vectors
##  and u^i(v) to u^i(v') commutes with u.  Ordering the lines of each orbit
##  as L, u(L), u^2(L), ... and choosing generators g, u(g), u^2(g), ... of
##  the lines, every frame of a given type is identified canonically with
##  the first one, the monomial groups being identified as permutation
##  groups on the (p-1)n non-trivial multiples of the generators ("index
##  permutations"); the identification differs from any other
##  C_{GL(V)}(u)-conjugation only by an element normalizing T inside the
##  monomial group.
##
##  FS_FrameCandidates returns a record (a "frame data" record) with the
##  u-invariant frames of each type and, for each type, the candidates
##  (subgroups of the monomial group with T as Sylow p-subgroup and a
##  strongly p-embedded subgroup, one for each class) as index permutation
##  groups.  FS_BorelCompatibleFrameCandidates runs the Borel
##  compatibility test for every frame invariant under Aut_{N_B(P)}(P),
##  entirely in the small permutation representation, and converts the
##  surviving candidates into subgroups of the model of Aut(P).  The method
##  covers the "imprimitive" automizers of abelian essential subgroups (as
##  in alternating groups) but it is not a complete enumeration of all
##  automizer candidates.
##

# the generators of the lines of a frame, ordered compatibly with u
BindGlobal( "FS_FrameGenerators", function( frame, u )
    local gens, orbit, g, i;
    gens := [];
    for orbit in frame do
        g := GeneratorsOfGroup( orbit[1] )[1];
        Add( gens, g );
        for i in [ 2 .. Length( orbit ) ] do
            g := ImagesRepresentative( u, g );
            Add( gens, g );
        od;
    od;
    return gens;
end );

BindGlobal( "FS_FramePoints", function( gens, p )
    return Concatenation( List( gens, g -> List( [ 1 .. p - 1 ], k -> g^k ) ) );
end );

# the index permutation of an automorphism a of P preserving the frame, or fail
BindGlobal( "FS_FrameToPerm", function( a, pts )
    local l, pt, pos;
    l := [];
    for pt in pts do
        pos := Position( pts, ImagesRepresentative( a, pt ) );
        if pos = fail then return fail; fi;
        Add( l, pos );
    od;
    return PermList( l );
end );

# the automorphism of P given by an index permutation
BindGlobal( "FS_FrameFromPerm", function( x, P, gens, pts )
    return GroupHomomorphismByImagesNC( P, P, gens, List( gens, g -> pts[ Position( pts, g ) ^ x ] ) );
end );

#############################################################################
##
#F  FS_MonomialCandidates( <monS>, <D>, <TS>, <p>, <n> )
##
##  monS = D x| Sym(n) a monomial group given as index permutations (D the
##  diagonal subgroup, acting on n blocks of p-1 points), TS a subgroup
##  of order p.  Returns the subgroups H of monS with TS as Sylow
##  p-subgroup and a strongly p-embedded subgroup, one for each class.  A
##  subgroup H is determined by X = HD/D, K = H meet D (an X-invariant
##  subgroup of the abelian group D) and a complement of D/K in (D X)/K;
##  this enumeration is complete and does not depend on the library of
##  perfect groups (which omits some orders, e.g. 368640 = |4^5:A6|).
##
BindGlobal( "FS_MonomialCandidates", function( monS, D, TS, p, n )
    local blocks, pi, SymS, ubar, Xs, X, g, Hhat, acts, Ks, K, nat, Q, DK, comps, C, H, Tsyl, res;
    blocks := List( [ 1 .. n ], i -> [ ( i - 1 ) * ( p - 1 ) + 1 .. i * ( p - 1 ) ] );
    pi := ActionHomomorphism( monS, blocks, OnSets );
    SymS := Image( pi, monS );
    ubar := Image( pi, TS );
    res := [];
    for X in List( ConjugacyClassesSubgroups( SymS ), Representative ) do
        if FS_PPart( Size( X ), p ) <> p then continue; fi;
        g := RepresentativeAction( SymS, SylowSubgroup( X, p ), ubar );
        if g = fail then continue; fi;
        X := ConjugateSubgroup( X, g );
        Hhat := PreImage( pi, X );
        acts := List( GeneratorsOfGroup( Hhat ), x -> ConjugatorAutomorphismNC( D, x ) );
        Ks := SubgroupsSolvableGroup( D, rec( actions := acts ) );
        Ks := Filtered( Ks, K -> ForAll( acts, a -> ImagesSet( a, K ) = K ) );
        for K in Ks do
            nat := NaturalHomomorphismByNormalSubgroup( Hhat, K );
            Q := Image( nat, Hhat );
            DK := Image( nat, D );
            if Size( DK ) = 1 then
                comps := [ Q ];
            else
                comps := ComplementClassesRepresentatives( Q, DK );
            fi;
            for C in comps do
                H := PreImage( nat, C );
                if FS_PPart( Size( H ), p ) <> p then continue; fi;
                Tsyl := SylowSubgroup( H, p );
                if IsNormal( H, Tsyl ) then continue; fi;
                g := RepresentativeAction( monS, Tsyl, TS );
                if g = fail then continue; fi;
                H := ConjugateSubgroup( H, g );
                if ForAny( res, L -> Size( L ) = Size( H ) and RepresentativeAction( monS, L, H ) <> fail ) then continue; fi;
                if HasStronglyPEmbeddedSubgroup( H, p ) then Add( res, H ); fi;
            od;
        od;
    od;
    return res;
end );

InstallGlobalFunction( FS_FrameCandidates, function( S, P, Tbar, opts )
    local p, h, outd, Mbar, q, n, lines, u, orbs, orb, orbit, img, types, frames, candfr, data, t, frame,
          gens, pts, monS, TS, r, i, k, l, perm, cls, D, NT, Ks, K, X, ints, N, H, L, sigma, ncomb, maxcomb;
    p := PrimePGroup( P );
    h := FS_AutHandle( P );
    outd := FS_OutData( P );
    Mbar := outd.Mbar; q := outd.q;
    n := Length( FS_PcgsOf( P ) );
    data := rec( isFrameData := true, P := P, p := p, n := n, types := [], frames := [], typedata := [], extra := [] );
    if Size( Tbar ) <> p then return data; fi;
    u := h.from( PreImagesRepresentative( q, First( GeneratorsOfGroup( Tbar ), x -> not IsOne( x ) ) ) );
    data.u := u;
    lines := DuplicateFreeList( List( Filtered( AsList( P ), x -> not IsOne( x ) ), x -> SubgroupNC( P, [ x ] ) ) );
    # the <u>-orbits of lines, each ordered as L, u(L), u^2(L), ...
    orbs := [];
    for orb in OrbitsDomain( Group( [ u ] ), lines, FS_OnImage ) do
        orbit := [ orb[1] ];
        img := ImagesSet( u, orb[1] );
        while Length( orbit ) < Length( orb ) do
            Add( orbit, img );
            img := ImagesSet( u, img );
        od;
        Add( orbs, orbit );
    od;
    # the u-invariant frames: unions of orbits of total size n spanning P
    types := []; frames := [];
    ncomb := 0; maxcomb := 200000;
    candfr := function( chosen, start, size )
        local k, gens, t, pos;
        ncomb := ncomb + 1;
        if ncomb > maxcomb then return; fi;
        if size = n then
            gens := Concatenation( List( chosen, k -> List( orbs[k], L -> GeneratorsOfGroup( L )[1] ) ) );
            if Size( SubgroupNC( P, gens ) ) = Size( P ) then
                t := SortedList( List( chosen, k -> Length( orbs[k] ) ) );
                pos := Position( types, t );
                if pos = fail then
                    Add( types, t ); Add( frames, [] ); pos := Length( types );
                fi;
                # the orbits in the order of the type (ascending lengths)
                Add( frames[ pos ], List( chosen, k -> orbs[k] ) );
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
    if ncomb > maxcomb then
        Info( InfoFusionSystems, 1, "too many unions of <u>-orbits of lines: the frame method is skipped" );
        return data;
    fi;
    for t in [ 1 .. Length( types ) ] do
        # order the orbits of every frame by length
        for frame in frames[t] do SortBy( frame, orbit -> Length( orbit ) ); od;
    od;
    Info( InfoFusionSystems, 2, Length( types ), " types of u-invariant frames: ", types,
          " with ", List( frames, Length ), " frames" );
    data.types := types; data.frames := frames;
    for t in [ 1 .. Length( types ) ] do
        frame := frames[t][1];
        gens := FS_FrameGenerators( frame, u );
        pts := FS_FramePoints( gens, p );
        # the monomial group as index permutations: scalings and permutations of the generators
        monS := [];
        r := PrimitiveRootMod( p );
        for i in [ 1 .. n ] do
            l := [ 1 .. Length( pts ) ];
            for k in [ 1 .. p - 1 ] do
                l[ ( i - 1 ) * ( p - 1 ) + k ] := ( i - 1 ) * ( p - 1 ) + ( ( r * k ) mod p );
            od;
            Add( monS, PermList( l ) );
        od;
        for sigma in GeneratorsOfGroup( SymmetricGroup( n ) ) do
            l := [];
            for i in [ 1 .. n ] do
                for k in [ 1 .. p - 1 ] do
                    l[ ( i - 1 ) * ( p - 1 ) + k ] := ( i ^ sigma - 1 ) * ( p - 1 ) + k;
                od;
            od;
            Add( monS, PermList( l ) );
        od;
        D := SubgroupNC( Group( monS ), monS{[ 1 .. n ]} );
        monS := Group( monS );
        TS := SubgroupNC( monS, [ FS_FrameToPerm( u, pts ) ] );
        cls := FS_MonomialCandidates( monS, D, TS, p, n );
        Info( InfoFusionSystems, 2, "frames of type ", types[t], ": ", Length( cls ), " candidates in the monomial group" );
        Add( data.typedata, rec( cands := cls, monS := monS, TS := TS, WS := Normalizer( monS, TS ) ) );
    od;
    return data;
end );

#############################################################################
##
#F  FS_TransportFrameData( <data>, <theta> ) . . . . . theta: P -> Q an isomorphism
##
BindGlobal( "FS_TransportFrameData", function( data, theta )
    local new;
    new := ShallowCopy( data );
    new.P := Range( theta );
    if IsBound( data.u ) then new.u := FS_TransportAut( data.u, theta ); fi;
    new.frames := List( data.frames, fl -> List( fl, frame -> List( frame, orbit -> List( orbit, L -> ImagesSet( theta, L ) ) ) ) );
    return new;
end );

#############################################################################
##
#F  FS_CandCount( <cands> ) . . . . . number of class candidates (list or frame data)
##
InstallGlobalFunction( FS_CandCount, function( cands )
    if IsRecord( cands ) then
        return Sum( List( cands.typedata, td -> Length( td.cands ) ) ) + Length( cands.extra );
    fi;
    return Length( cands );
end );

#############################################################################
##
#F  FS_BorelCompatibleFrameCandidates( <F0>, <P>, <data>, <maxenough> )
##
BindGlobal( "FS_BorelCompatibleFrameCandidates", function( F0, P, data, maxenough )
    local S, p, h, res, AutBgens, t, td, frame, gens, pts, AutBS, NWS, H, NH, subs, sw, c, cand, tr, nn,
          found, autgens, A, linesets, inv, g, L, Lg;
    S := F0!.S; p := F0!.p;
    h := FS_AutHandle( P );
    res := [];
    if Length( data.types ) = 0 then return res; fi;
    # a small generating set of Aut_B(P) (the frame invariance test is run
    # for every frame)
    AutBgens := FS_AutBGenerators( F0, P );
    AutBgens := List( SmallGeneratingSet( FS_AutSubgroup( h, AutBgens ) ), x -> FS_AsHom( h.from( x ), P ) );
    for t in [ 1 .. Length( data.types ) ] do
        td := data.typedata[t];
        if Length( td.cands ) = 0 then continue; fi;
        for frame in data.frames[t] do
            # is the frame invariant under Aut_B(P)?  (test on the lines first)
            linesets := Concatenation( frame );
            inv := true;
            for g in AutBgens do
                for L in linesets do
                    if not ImagesSet( g, L ) in linesets then inv := false; break; fi;
                od;
                if not inv then break; fi;
            od;
            if not inv then continue; fi;
            gens := FS_FrameGenerators( frame, data.u );
            pts := FS_FramePoints( gens, p );
            AutBS := List( AutBgens, g -> FS_FrameToPerm( g, pts ) );
            if fail in AutBS then continue; fi;
            AutBS := SubgroupNC( td.monS, AutBS );
            NWS := Normalizer( td.WS, AutBS );
            for H in td.cands do
                if HasFSSylowNormalizer( H ) then
                    NH := FSSylowNormalizer( H );
                else
                    NH := Normalizer( H, td.TS );
                    SetFSSylowNormalizer( H, NH );
                fi;
                if Size( NH ) mod Size( AutBS ) <> 0 then continue; fi;
                if maxenough then
                    if Size( NH ) <> Size( AutBS ) then continue; fi;
                    subs := [ NH ];
                else
                    subs := Filtered( List( ConjugacyClassesSubgroups( NH ), Representative ), U -> Size( U ) = Size( AutBS ) );
                    subs := Concatenation( List( subs, U -> AsList( ConjugacyClassSubgroups( NH, U ) ) ) );
                    subs := Filtered( subs, U -> IsSubset( U, td.TS ) );
                fi;
                for sw in subs do
                    c := RepresentativeAction( td.WS, sw, AutBS );
                    if c = fail then continue; fi;
                    cand := ConjugateSubgroup( H, c );
                    tr := RightTransversal( NWS, Normalizer( NWS, cand ) );
                    for nn in tr do
                        found := ConjugateSubgroup( cand, nn );
                        autgens := List( GeneratorsOfGroup( found ), x -> FS_FrameFromPerm( x, P, gens, pts ) );
                        A := FS_AutSubgroup( h, autgens );
                        if ForAny( res, K -> Size( K ) = Size( A ) and K = A ) then continue; fi;
                        if FS_CoreCompatible( F0, P, A ) then Add( res, A ); fi;
                    od;
                od;
            od;
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
    local S, p, h, M, T, W, AutB, res, A, NA, subs, sw, w, NW, n, cand, found, tr, fr;
    if IsRecord( classcands ) then
        fr := FS_BorelCompatibleFrameCandidates( F0, P, classcands, maxenough );
        if Length( classcands.extra ) > 0 then
            for A in FS_BorelCompatibleCandidates( F0, P, classcands.extra, maxenough ) do
                if not ForAny( fr, K -> Size( K ) = Size( A ) and K = A ) then Add( fr, A ); fi;
            od;
        fi;
        return fr;
    fi;
    S := F0!.S; p := F0!.p;
    h := FS_AutHandle( P );
    M := h.model;
    T := FS_AutSubgroup( h, FS_AutSGenerators( F0, P ) );
    AutB := FS_AutSubgroup( h, FS_AutBGenerators( F0, P ) );
    W := Normalizer( M, T );
    NW := Normalizer( W, AutB );
    res := [];
    for A in classcands do
        if HasFSSylowNormalizer( A ) then
            NA := FSSylowNormalizer( A );
        else
            NA := Normalizer( A, T );
            SetFSSylowNormalizer( A, NA );
        fi;
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
            tr := RightTransversal( NW, Normalizer( NW, cand ) );
            for n in tr do
                found := ConjugateSubgroup( cand, n );
                if ForAny( res, K -> K = found ) then continue; fi;
                if FS_CoreCompatible( F0, P, found ) then Add( res, found ); fi;
            od;
        od;
    od;
    return res;
end );
