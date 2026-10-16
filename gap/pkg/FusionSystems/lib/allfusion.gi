#############################################################################
##
##  allfusion.gi           FusionSystems package
##
##  AllFusionSystems( S [, opts ] ) follows the strategy of Parker and
##  Semeraro [arXiv:2003.01600, Section 4]:
##
##   1. find the proto-essential subgroups of S (fast method of Gautam),
##      up to Aut(S)-conjugacy, and the candidates for their automizers up
##      to Aut(P)-conjugacy;
##   2. for each "Borel subgroup" Aut_F(S) = Inn(S) x| K, K a p'-subgroup
##      of Aut(S) up to conjugacy:
##        - expand the proto-essentials to B-classes (B = Aut_F(S) x| S),
##        - determine the automizer candidates compatible with Aut_F(S),
##        - run through the subsets of proto-essentials up to the action of
##          N_{Aut(S)}(Aut_F(S)) and through the assignments of automizers
##          up to the action of the stabilizer of the subset,
##        - test O^p(F) = F and O_p(F) = 1 (if requested) and saturation,
##        - remove isomorphic systems.
##
##  Options (components of opts, all optional):
##    OpTriv      (default true)  only systems with O_p(F) = 1,
##    pPerfect    (default true)  only systems with O^p(F) = F,
##    OutFSOrders (default fail)  restrict |Out_F(S)| to this list,
##    exhaustive  (default false) examine all S-centric subgroups as
##                proto-essential candidates instead of Gautam's candidates,
##    candidates  a function (S, P) supplying automizer candidates.
##

InstallGlobalFunction( FS_AsHom, function( a, P )
    local gens;
    gens := FS_PcgsOf( P );
    return GroupHomomorphismByImagesNC( P, P, gens, List( gens, x -> ImagesRepresentative( a, x ) ) );
end );

InstallGlobalFunction( FS_IsCharacteristicIn, function( X, W )
    local h;
    if Size( W ) = Size( X ) or Size( W ) = 1 then return true; fi;
    h := FS_AutHandle( X );
    return ForAll( GeneratorsOfGroup( h.group ), a -> ImagesSet( a, W ) = W );
end );

#############################################################################
##
#F  FS_CharacteristicSubgroupTest( <protos>, <S> )
##
##  True if some non-trivial subgroup of the intersection of the members of
##  protos is characteristic in S and in every member of protos; then
##  O_p(F) <> 1 for every fusion system on S whose essential subgroups are
##  among (conjugates of) the protos.
##
InstallGlobalFunction( FS_CharacteristicSubgroupTest, function( protos, S )
    local Q, P, W;
    Q := S;
    for P in protos do Q := Intersection( Q, P ); od;
    if Size( Q ) = 1 then return false; fi;
    for W in NormalSubgroups( Q ) do
        if Size( W ) > 1 and FS_IsCharacteristicIn( S, W ) and ForAll( protos, P -> FS_IsCharacteristicIn( P, W ) ) then
            return true;
        fi;
    od;
    return false;
end );

#############################################################################
##
#F  FS_IsConjugateInto( <S>, <X>, <Y> ) . . . . is X S-conjugate to a subgroup of Y?
##
InstallGlobalFunction( FS_IsConjugateInto, function( S, X, Y )
    local s;
    if Size( X ) > Size( Y ) then return false; fi;
    for s in RightTransversal( S, Normalizer( S, X ) ) do
        if IsSubset( Y, ConjugateSubgroup( X, s ) ) then return true; fi;
    od;
    return false;
end );

#############################################################################
##
#F  BorelSubgroups( <S>[, <orders>] )
##
##  The p'-subgroups K of Aut(S) up to conjugacy (optionally only those
##  with |K| in orders), as records rec( model, gens ) where model is the
##  subgroup of the model of Aut(S) and gens its generators as
##  automorphisms.  Inn(S) x| K runs through the possibilities for Aut_F(S).
##
InstallGlobalFunction( BorelSubgroups, function( arg )
    local S, orders, p, h, M, pr, Hp, cls, keep, K, O, q, Q, lat, Kbar, Khat, res;
    S := arg[1];
    orders := fail;
    if Length( arg ) > 1 then orders := arg[2]; fi;
    p := PrimePGroup( S );
    h := FS_AutHandle( S );
    M := h.model;
    pr := Difference( PrimeDivisors( Size( M ) ), [ p ] );
    keep := [];
    if Length( pr ) = 0 then
        keep := [ TrivialSubgroup( M ) ];
    elif IsSolvableGroup( M ) then
        Hp := HallSubgroup( M, pr );
        cls := List( ConjugacyClassesSubgroups( Hp ), Representative );
        for K in cls do
            if orders <> fail and not Size( K ) in orders then continue; fi;
            if ForAny( keep, L -> Size( L ) = Size( K ) and RepresentativeAction( M, K, L ) <> fail ) then continue; fi;
            Add( keep, K );
        od;
    else
        O := PCore( M, p );
        q := NaturalHomomorphismByNormalSubgroup( M, O );
        Q := Image( q );
        if IsSolvableGroup( Q ) then
            cls := List( ConjugacyClassesSubgroups( Q ), Representative );
        else
            lat := LatticeByCyclicExtension( Q, function( H ) return Size( H ) mod p <> 0; end );
            cls := List( ConjugacyClassesSubgroups( lat ), Representative );
        fi;
        cls := Filtered( cls, H -> Size( H ) mod p <> 0 );
        for Kbar in cls do
            if orders <> fail and not Size( Kbar ) in orders then continue; fi;
            Khat := PreImage( q, Kbar );
            if Size( O ) = 1 then
                K := Khat;
            elif IsSolvableGroup( Khat ) then
                K := HallSubgroup( Khat, pr );
            else
                K := ComplementClassesRepresentatives( Khat, O )[1];
            fi;
            Add( keep, K );
        od;
    fi;
    res := List( keep, K -> rec( model := K, gens := List( GeneratorsOfGroup( K ), x -> FS_AsHom( h.from( x ), S ) ) ) );
    SortBy( res, r -> Size( r.model ) );
    return res;
end );

#############################################################################
##
#F  FS_FusionSystemsForBorel( <S>, <borel>, <proto>, <classcands>, <opts> )
##
InstallGlobalFunction( FS_FusionSystemsForBorel, function( S, borel, proto, classcands, opts )
    local p, F0, hS, cplElts, Pess, Pinv, Plabel, Ptheta, i, j, k, pos, P, cand, changed, maxenough, N, hP, hQ, theta,
          A0, Nrm, nrmauts, perms, perm, a, img, Pi, subsets, D, results, Ess, lists, stabgens, alpha, sig, act,
          tuples, nt, idx, t, orbrep, uf, find, union, tup, imgtup, c, s, Aimg, F, essauts, r, kept, iso, t0, total, nsat,
          prod, ok, SdS;
    p := PrimePGroup( S );
    hS := FS_AutHandle( S );
    F0 := FusionSystem( S, borel.gens, [], [] );
    A0 := FS_ComplementData( F0 ).autF;
    if p >= 5 and Size( borel.model ) = 1 and opts.pPerfect then
        Info( InfoFusionSystems, 1, "Borel with Aut_F(S) = Inn(S) skipped (p >= 5, O^p(F) < F)" );
        return [];
    fi;
    cplElts := FS_ComplementElements( F0 );
    # B-classes of the proto-essential S-classes
    Pess := []; Pinv := []; Plabel := []; Ptheta := [];
    for i in [ 1 .. Length( proto.sreps ) ] do
        P := proto.sreps[i];
        if FS_BClassPosition( F0, Pess, Pinv, P ) <> fail then continue; fi;
        Add( Pess, P ); Add( Pinv, FS_SubgroupInvariants( S, P ) ); Add( Plabel, proto.label[i] );
        # theta: autrep -> P, x -> alpha(x)^s
        a := proto.path[i][1]; s := proto.path[i][2];
        Add( Ptheta, GroupHomomorphismByImagesNC( proto.autreps[ proto.label[i] ], P, FS_PcgsOf( proto.autreps[ proto.label[i] ] ),
                 List( FS_PcgsOf( proto.autreps[ proto.label[i] ] ), x -> ImagesRepresentative( a, x )^s ) ) );
    od;
    Info( InfoFusionSystems, 1, "Borel with |Out_F(S)| = ", Size( borel.model ), ": ", Length( Pess ),
          " B-classes of proto-essential subgroups of orders ", List( Pess, Size ) );
    if opts.pPerfect then
        SdS := FS_CommutatorWithAutomorphisms( S, Concatenation( FS_InnerAutGenerators( S ), borel.gens ) );
        if Size( ClosureGroup( SdS, Concatenation( List( Pess, GeneratorsOfGroup ) ) ) ) < Size( S ) then
            Info( InfoFusionSystems, 1, "  focal subgroup cannot be S: Borel skipped" );
            return [];
        fi;
    fi;
    # transport the class candidates to the B-class representatives
    cand := [];
    for j in [ 1 .. Length( Pess ) ] do
        hP := FS_AutHandle( proto.autreps[ Plabel[j] ] );
        hQ := FS_AutHandle( Pess[j] );
        cand[j] := List( classcands[ Plabel[j] ], A -> FS_TransportCandidate( A, hP, hQ, Ptheta[j] ) );
    od;
    # Borel compatible candidates, iterated until stable
    changed := true;
    while changed do
        changed := false;
        for j in [ 1 .. Length( Pess ) ] do
            if Length( cand[j] ) = 0 then continue; fi;
            N := Normalizer( S, Pess[j] );
            maxenough := true;
            for k in [ 1 .. Length( Pess ) ] do
                if Length( cand[k] ) = 0 then continue; fi;
                if Size( Pess[k] ) < Size( N ) then continue; fi;
                for c in cplElts do
                    if FS_IsConjugateInto( S, ImagesSet( c, N ), Pess[k] ) then maxenough := false; break; fi;
                od;
                if not maxenough then break; fi;
            od;
            cand[j] := FS_BorelCompatibleCandidates( F0, Pess[j], cand[j], maxenough );
            Info( InfoFusionSystems, 2, "  proto-essential of order ", Size( Pess[j] ), ": ", Length( cand[j] ),
                  " compatible automizer candidates (maxenough = ", maxenough, ")" );
            if Length( cand[j] ) = 0 then changed := true; fi;
        od;
    od;
    idx := Filtered( [ 1 .. Length( Pess ) ], j -> Length( cand[j] ) > 0 );
    if Length( idx ) = 0 then return []; fi;
    Pess := Pess{ idx }; Pinv := Pinv{ idx }; cand := cand{ idx };
    if opts.OpTriv and Length( Pess ) = 1 and IsNormal( S, Pess[1] ) and ForAll( cplElts, c -> ImagesSet( c, Pess[1] ) = Pess[1] ) then
        return [];
    fi;
    # the normalizer of Aut_F(S) in Aut(S) acts on the B-classes
    Nrm := Normalizer( hS.model, A0 );
    nrmauts := List( GeneratorsOfGroup( Nrm ), x -> FS_AsHom( hS.from( x ), S ) );
    perms := []; ok := true;
    for a in nrmauts do
        perm := [];
        for j in [ 1 .. Length( Pess ) ] do
            pos := FS_BClassPosition( F0, Pess, Pinv, ImagesSet( a, Pess[j] ) );
            if pos = fail then ok := false; break; fi;
            perm[j] := pos[1];
        od;
        if not ok then break; fi;
        Add( perms, PermList( perm ) );
    od;
    if not ok then perms := []; nrmauts := []; fi;
    Pi := Group( perms, () );
    subsets := Filtered( Combinations( [ 1 .. Length( Pess ) ] ), D -> Length( D ) > 0 );
    subsets := List( Orbits( Pi, subsets, OnSets ), o -> o[1] );
    SortBy( subsets, D -> -Length( D ) );
    results := [];
    total := 0; nsat := 0;
    for D in subsets do
        if opts.OpTriv and Length( D ) = 1 and IsNormal( S, Pess[ D[1] ] )
           and ForAll( cplElts, c -> ImagesSet( c, Pess[ D[1] ] ) = Pess[ D[1] ] ) then
            continue;
        fi;
        Ess := Pess{ D };
        lists := cand{ D };
        prod := Product( List( lists, Length ) );
        # the stabilizer of D acts on the tuples of candidates
        stabgens := [];
        if Length( perms ) > 0 then
            for i in [ 1 .. Length( perms ) ] do
                if OnSets( D, perms[i] ) = D then Add( stabgens, i ); fi;
            od;
            if Length( stabgens ) = 0 and Size( Pi ) > 1 then
                # use generators of the set stabilizer and express them as words? simpler: take elements of Stabilizer
                stabgens := [];
            fi;
        fi;
        tuples := Cartesian( List( lists, l -> [ 1 .. Length( l ) ] ) );
        if prod <= FS_Options.tupleBound and Length( stabgens ) > 0 then
            # precompute the action of each stabilizing generator on candidate indices
            act := [];
            for i in stabgens do
                alpha := nrmauts[i]; sig := perms[i];
                act[i] := [];
                for j in [ 1 .. Length( D ) ] do
                    P := Ess[j];
                    k := Position( D, D[j]^sig );
                    pos := FS_BClassPosition( F0, Pess, Pinv, ImagesSet( alpha, P ) );
                    c := pos[2]; s := pos[3];
                    theta := GroupHomomorphismByImagesNC( P, Ess[k], FS_PcgsOf( P ),
                                 List( FS_PcgsOf( P ), x -> ImagesRepresentative( c, ImagesRepresentative( alpha, x ) )^s ) );
                    hP := FS_AutHandle( P ); hQ := FS_AutHandle( Ess[k] );
                    act[i][j] := List( lists[j], A -> Position( lists[k], FS_TransportCandidate( A, hP, hQ, theta ) ) );
                    if fail in act[i][j] then ok := false; fi;
                od;
            od;
            if ok then
                uf := [ 1 .. Length( tuples ) ];
                find := function( x ) while uf[x] <> x do uf[x] := uf[ uf[x] ]; x := uf[x]; od; return x; end;
                union := function( x, y ) x := find( x ); y := find( y ); if x <> y then uf[ Maximum( x, y ) ] := Minimum( x, y ); fi; end;
                for nt in [ 1 .. Length( tuples ) ] do
                    tup := tuples[ nt ];
                    for i in stabgens do
                        sig := perms[i];
                        imgtup := [];
                        for j in [ 1 .. Length( D ) ] do
                            k := Position( D, D[j]^sig );
                            imgtup[k] := act[i][j][ tup[j] ];
                        od;
                        union( nt, Position( tuples, imgtup ) );
                    od;
                od;
                tuples := Filtered( [ 1 .. Length( tuples ) ], nt -> find( nt ) = nt );
                tuples := List( tuples, nt -> Cartesian( List( lists, l -> [ 1 .. Length( l ) ] ) )[ nt ] );
            fi;
        fi;
        Info( InfoFusionSystems, 1, "  essentials of orders ", List( Ess, Size ), ": ", Length( tuples ),
              " automizer assignments (of ", prod, ")" );
        for tup in tuples do
            total := total + 1;
            essauts := List( [ 1 .. Length( D ) ], j -> List( GeneratorsOfGroup( lists[j][ tup[j] ] ),
                           x -> FS_AsHom( FS_AutHandle( Ess[j] ).from( x ), Ess[j] ) ) );
            F := FusionSystem( S, borel.gens, Ess, essauts );
            if opts.pPerfect and not IsPPerfectFusionSystem( F ) then continue; fi;
            if opts.OpTriv and not IsOpFTrivial( F ) then continue; fi;
            r := FS_IsSaturatedWithReason( F );
            if r[1] then
                nsat := nsat + 1;
                SetIsSaturated( F, true );
                Add( results, F );
            else
                Info( InfoFusionSystems, 3, "    not saturated: ", r[2] );
            fi;
        od;
    od;
    Info( InfoFusionSystems, 1, "  ", total, " candidate systems tested, ", nsat, " saturated" );
    # remove isomorphic systems
    kept := [];
    for F in results do
        if ForAny( kept, G -> IsIsomorphicFusionSystems( F, G ) ) then continue; fi;
        Add( kept, F );
    od;
    Info( InfoFusionSystems, 1, "  ", Length( kept ), " isomorphism classes" );
    return kept;
end );

#############################################################################
##
#F  AllFusionSystems( <S>[, <opts>] )
##
InstallGlobalFunction( AllFusionSystems, function( arg )
    local S, opts, p, h, proto, classcands, i, keep, borels, res, b, t0, x, copts;
    S := arg[1];
    opts := rec( OpTriv := true, pPerfect := true, OutFSOrders := fail, exhaustive := false );
    if Length( arg ) > 1 then
        for x in RecNames( arg[2] ) do opts.( x ) := arg[2].( x ); od;
    fi;
    if not IsPcGroup( S ) then
        Error( "<S> must be a pc group; use Image( IsomorphismPcGroup( S ) )" );
    fi;
    p := PrimePGroup( S );
    t0 := Runtime();
    borels := fail;
    if IsAbelian( S ) then
        if opts.OpTriv then return []; fi;
        borels := BorelSubgroups( S, opts.OutFSOrders );
        return List( borels, b -> FusionSystem( S, b.gens, [], [] ) );
    fi;
    # Parker-Semeraro Lemma 7.1: no saturated F with O_p(F) = 1 if |S:Z(S)| <= p^2 and |S| >= p^4
    if opts.OpTriv and Index( S, Center( S ) ) <= p^2 and Size( S ) >= p^4 then return []; fi;
    h := FS_AutHandle( S );
    # Diaz-Glesser-Mazza-Park, Corollary 6.2
    if opts.OpTriv and p >= 5 and IsPrimePowerInt( Size( h.model ) ) and PrimePGroup( h.model ) = p then
        return [];
    fi;
    copts := rec( exhaustive := opts.exhaustive );
    proto := ProtoEssentialSubgroups( S, copts );
    Info( InfoFusionSystems, 1, Length( proto.autreps ), " Aut(S)-classes of proto-essential subgroups of orders ",
          List( proto.autreps, Size ), " (", Runtime() - t0, " ms)" );
    if Length( proto.sreps ) = 0 then
        if opts.OpTriv then return []; fi;
        borels := BorelSubgroups( S, opts.OutFSOrders );
        return List( borels, b -> FusionSystem( S, b.gens, [], [] ) );
    fi;
    if opts.OpTriv and FS_CharacteristicSubgroupTest( proto.sreps, S ) then
        Info( InfoFusionSystems, 1, "a characteristic subgroup lies in all proto-essentials: O_p(F) <> 1 always" );
        return [];
    fi;
    if opts.pPerfect then
        x := ClosureGroup( FS_CommutatorWithAutomorphisms( S, GeneratorsOfGroup( h.group ) ),
                 Concatenation( List( proto.sreps, GeneratorsOfGroup ) ) );
        if Size( x ) < Size( S ) then
            Info( InfoFusionSystems, 1, "the proto-essentials and [S,Aut(S)] do not generate S: O^p(F) < F always" );
            return [];
        fi;
    fi;
    # automizer candidates for the Aut(S)-class representatives
    classcands := [];
    copts := rec();
    if IsBound( opts.candidates ) then copts.candidates := opts.candidates; fi;
    for i in [ 1 .. Length( proto.autreps ) ] do
        classcands[i] := ProtoEssentialAutomizerCandidates( S, proto.autreps[i], copts );
        Info( InfoFusionSystems, 1, "proto-essential of order ", Size( proto.autreps[i] ), ": ",
              Length( classcands[i] ), " classes of automizer candidates (", Runtime() - t0, " ms)" );
    od;
    keep := Filtered( [ 1 .. Length( proto.autreps ) ], i -> Length( classcands[i] ) > 0 );
    if Length( keep ) = 0 then
        if opts.OpTriv then return []; fi;
        borels := BorelSubgroups( S, opts.OutFSOrders );
        return List( borels, b -> FusionSystem( S, b.gens, [], [] ) );
    fi;
    if Length( keep ) < Length( proto.autreps ) then
        i := Filtered( [ 1 .. Length( proto.sreps ) ], j -> proto.label[j] in keep );
        proto := rec( autreps := proto.autreps{ keep }, sreps := proto.sreps{ i },
                      label := List( proto.label{ i }, l -> Position( keep, l ) ), path := proto.path{ i } );
        classcands := classcands{ keep };
        if opts.OpTriv and FS_CharacteristicSubgroupTest( proto.sreps, S ) then return []; fi;
    fi;
    borels := BorelSubgroups( S, opts.OutFSOrders );
    Info( InfoFusionSystems, 1, Length( borels ), " Borel subgroups, |Out_F(S)| in ", List( borels, b -> Size( b.model ) ),
          " (", Runtime() - t0, " ms)" );
    res := [];
    for b in borels do
        Append( res, FS_FusionSystemsForBorel( S, b, proto, classcands, opts ) );
        Info( InfoFusionSystems, 1, Length( res ), " fusion systems so far (", Runtime() - t0, " ms)" );
    od;
    if not opts.OpTriv then
        # the systems without essential subgroups
        Append( res, List( borels, b -> FusionSystem( S, b.gens, [], [] ) ) );
    fi;
    return res;
end );
