#############################################################################
##
##  protoess.gi            FusionSystems package
##

#############################################################################
##
#F  RefinedLowerCentralSeries( <S> )
##
##  A central series S = L_1 > L_2 > ... > L_m = 1 of the p-group S with
##  all factors of order p which refines the lower central series.
##
InstallGlobalFunction( RefinedLowerCentralSeries, function( S )
    local lcs, ser, i, U, V, q, Q, cs, j, H, x;
    lcs := LowerCentralSeriesOfGroup( S );
    ser := [];
    for i in [ 1 .. Length( lcs ) - 1 ] do
        U := lcs[i]; V := lcs[i+1];
        # every subgroup between V and U is normal in S since [S,U] <= V
        q := NaturalHomomorphismByNormalSubgroup( U, V );
        Q := Image( q );
        cs := CompositionSeries( Q );          # Q > ... > 1, factors of order p
        for j in [ 1 .. Length( cs ) - 1 ] do
            Add( ser, PreImage( q, cs[j] ) );
        od;
    od;
    Add( ser, lcs[ Length( lcs ) ] );
    return ser;
end );

#############################################################################
##
#F  CentralSeriesCentralizers( <S> )
##
##  The subgroups C_S(xA/A) where A runs through the terms of
##  RefinedLowerCentralSeries(S) contained in [S,S] (including A = 1) and
##  xA through representatives of the conjugacy classes of elements of
##  order p of S/A, without repetitions and without S itself.  By [Gautam,
##  Theorem 3.6] every essential subgroup of a saturated fusion system on S
##  is S-conjugate to one of these.
##
InstallGlobalFunction( CentralSeriesCentralizers, function( S )
    local p, L, k, cands, i, q, Q, c, C, seenQ, x;
    p := PrimePGroup( S );
    L := RefinedLowerCentralSeries( S );
    k := Position( L, DerivedSubgroup( S ) );
    cands := [];
    # A = L[k] = S' only gives C_S(xA/A) = S; for the other terms the
    # centralizers are taken from the conjugacy classes of S/A (where the
    # class computation stores them) and duplicates are removed inside S/A
    for i in [ k + 1 .. Length( L ) ] do
        if Size( L[i] ) = 1 then
            Q := S; q := fail;
        else
            q := NaturalHomomorphismByNormalSubgroup( S, L[i] );
            Q := Image( q );
        fi;
        seenQ := [];
        for c in ConjugacyClasses( Q ) do
            x := Representative( c );
            if Order( x ) <> p then continue; fi;
            C := Centralizer( c );
            if Size( C ) = Size( Q ) or C in seenQ then continue; fi;
            Add( seenQ, C );
            if q = fail then Add( cands, C ); else Add( cands, PreImage( q, C ) ); fi;
        od;
    od;
    return cands;
end );

#############################################################################
##
#F  FS_AutOrbitsOnSubgroupClasses( <S>, <reps>, <invs>, <autgens> )
##
##  reps is a list of S-conjugacy class representatives of subgroups of S,
##  invs their invariants and autgens a list of automorphisms of S.
##  Returns a record with components
##    label  label[i] = number of the <autgens>-orbit containing reps[i],
##    dead   dead[k] = true if the k-th orbit contains subgroups not
##           S-conjugate to a member of reps,
##    reps   the positions of the orbit representatives,
##    path   path[i] = [ autos, s ]: an automorphism of S (a product of
##           members of autgens) and s in S with
##           reps[i] = Image( autos, reps[ orbitrep ] )^s.
##
InstallGlobalFunction( FS_AutOrbitsOnSubgroupClasses, function( S, reps, invs, autgens )
    local n, label, dead, orbreps, path, i, k, isdead, queue, j, a, img, pos, m, id;
    n := Length( reps );
    label := ListWithIdenticalEntries( n, 0 );
    dead := []; orbreps := []; path := [];
    id := IdentityMapping( S );
    for i in [ 1 .. n ] do
        if label[i] <> 0 then continue; fi;
        Add( orbreps, i ); k := Length( orbreps ); label[i] := k;
        path[i] := [ id, One( S ) ];
        isdead := false;
        queue := [ i ];
        while Length( queue ) > 0 do
            j := Remove( queue );
            for a in autgens do
                img := ImagesSet( a, reps[j] );
                pos := FS_ClassPosition( S, reps, invs, img );
                if pos = fail then
                    isdead := true;
                elif label[ pos[1] ] = 0 then
                    m := pos[1];
                    label[m] := k;
                    # reps[m] = Image(a, reps[j])^s = Image( path[j].autos * a, reps[i])^{path[j].s^a ...}
                    # we store the composite automorphism (path[j][1] then a) and the conjugator
                    path[m] := [ FS_ComposeHoms( [ path[j][1], a ] ),
                                 ImagesRepresentative( a, path[j][2] ) * pos[2] ];
                    Add( queue, m );
                fi;
            od;
        od;
        Add( dead, isdead );
    od;
    return rec( label := label, dead := dead, reps := orbreps, path := path );
end );

#############################################################################
##
#F  FS_CentricSubgroupClasses( <S> )
##
##  Representatives of the S-conjugacy classes of S-centric subgroups of S
##  (computed through the subgroup lattice of S/Z(S)).  Only used by the
##  exhaustive (slow) method.
##
InstallGlobalFunction( FS_CentricSubgroupClasses, function( S )
    local q, cls;
    q := NaturalHomomorphismByNormalSubgroup( S, Center( S ) );
    cls := List( ConjugacyClassesSubgroups( Image( q ) ), c -> PreImage( q, Representative( c ) ) );
    return Filtered( cls, P -> FS_IsCentricIn( S, P ) );
end );

#############################################################################
##
#F  ProtoEssentialSubgroups( <S>[, <options>] )
##
##  The proto-essential subgroups of the p-group S: the subgroups P which
##  pass all the Parker-Semeraro tests for being an essential subgroup of a
##  saturated fusion system on S (S-centric, non-cyclic, |P/Phi(P)| >=
##  |Out_S(P)|^2, C_{N_S(P)}(P/Phi(P)) <= P, Out_S(P) a possible Sylow
##  p-subgroup of a group with a strongly p-embedded subgroup, Aut_S(P) meet
##  O_p(Aut(P)) = Inn(P), and Aut(P) insoluble unless Out_S(P) is cyclic or
##  quaternion).  By default the candidates are the subgroups of
##  CentralSeriesCentralizers(S) (Gautam, Theorem 3.6); with the option
##  exhaustive := true all S-centric subgroups are examined, and with the
##  option candidates := list the given S-class representatives (which must
##  already pass the cheap tests) are used instead.
##
##  Every test is invariant under Aut(S), so the tests needing Aut(P) are
##  only applied once per Aut(S)-orbit of S-classes, and orbits which are
##  not closed under Aut(S) (i.e. which contain subgroups failing the cheap
##  tests) are discarded.
##
##  Returns a record with components
##    autreps   representatives of the Aut(S)-classes of proto-essentials,
##    sreps     representatives of the S-classes of proto-essentials,
##    label     label[i] = position in autreps of the Aut(S)-class of sreps[i],
##    path      path[i] = [ alpha, s ] with sreps[i] = Image( alpha, autreps[label[i]] )^s,
##    autgens   the generators of Aut(S) that were used.
##
InstallGlobalFunction( ProtoEssentialSubgroups, function( arg )
    local S, opts, p, exhaustive, cands, seen, seeninv, X, inv, x, pos, autgens, orb,
          autreps, sreps, label, path, k, i, keep, t, h, result, cheap;
    S := arg[1];
    opts := rec( exhaustive := false, autgens := fail, candidates := fail );
    if Length( arg ) > 1 then
        for x in RecNames( arg[2] ) do opts.( x ) := arg[2].( x ); od;
    fi;
    p := PrimePGroup( S );
    t := Runtime();
    if opts.candidates <> fail then
        # S-class representatives which already passed the cheap tests
        X := ShallowCopy( opts.candidates );
        inv := List( X, x -> FS_SubgroupInvariants( S, x ) );
    else
        if opts.exhaustive then
            cands := FS_CentricSubgroupClasses( S );
        else
            cands := CentralSeriesCentralizers( S );
        fi;
        Info( InfoFusionSystems, 2, Length( cands ), " candidate subgroups (", Runtime() - t, " ms)" );
        # S-classes of S-centric candidates passing the cheap tests
        seen := []; seeninv := []; X := []; inv := [];
        for x in cands do
            if x = S or IsCyclic( x ) or Normalizer( S, x ) = x or not FS_IsCentricIn( S, x ) then continue; fi;
            if FS_ClassPosition( S, seen, seeninv, x ) <> fail then continue; fi;
            Add( seen, x ); Add( seeninv, FS_SubgroupInvariants( S, x ) );
            if FS_CheapProtoEssentialTest( S, x ) then
                Add( X, x ); Add( inv, seeninv[ Length( seeninv ) ] );
            fi;
        od;
    fi;
    Info( InfoFusionSystems, 2, Length( seen ), " S-classes of S-centric candidates, ",
          Length( X ), " pass the tests not requiring Aut(P) (", Runtime() - t, " ms)" );
    if opts.autgens <> fail then
        autgens := opts.autgens;
    else
        autgens := GeneratorsOfGroup( FS_AutHandle( S ).group );
    fi;
    orb := FS_AutOrbitsOnSubgroupClasses( S, X, inv, autgens );
    Info( InfoFusionSystems, 2, Length( orb.reps ), " Aut(S)-classes, of which ",
          Number( orb.dead, d -> d ), " are not closed under Aut(S) (", Runtime() - t, " ms)" );
    autreps := []; sreps := []; label := []; path := [];
    for k in [ 1 .. Length( orb.reps ) ] do
        if orb.dead[k] then continue; fi;
        x := X[ orb.reps[k] ];
        if not FS_RadicalTest( S, x ) then continue; fi;
        if not FS_IsQuaternionOrCyclic( Normalizer( S, x ) / x ) then
            h := FS_AutHandle( x );
            if IsSolvableGroup( h.model ) then continue; fi;
        fi;
        Add( autreps, x );
        for i in [ 1 .. Length( X ) ] do
            if orb.label[i] = k then
                Add( sreps, X[i] ); Add( label, Length( autreps ) ); Add( path, orb.path[i] );
            fi;
        od;
    od;
    Info( InfoFusionSystems, 1, Length( autreps ), " Aut(S)-classes and ", Length( sreps ),
          " S-classes of proto-essential subgroups (", Runtime() - t, " ms)" );
    return rec( autreps := autreps, sreps := sreps, label := label, path := path, autgens := autgens );
end );
