#############################################################################
##
##  iso.gi                 FusionSystems package
##
##  Two fusion systems F1 on S1 and F2 on S2 are isomorphic if there is an
##  isomorphism alpha: S1 -> S2 with  alpha Hom_{F1}(P,Q) alpha^-1 =
##  Hom_{F2}(alpha(P), alpha(Q))  for all P, Q <= S1, i.e. alpha carries
##  the generating data of F1 into F2 and vice versa.  Necessarily
##  alpha Aut_{F1}(S1) alpha^-1 = Aut_{F2}(S2).
##
##  Algorithm (S1 = S2 = S after transport):  let A := Aut(S) (through its
##  model), A1 := Aut_{F1}(S), A2 := Aut_{F2}(S).  Find alpha_0 in A with
##  A1^alpha_0 = A2 and let N := N_A(A2).  The candidates are the cosets of
##  A2 in alpha_0 N.  We prune them by requiring that alpha maps the
##  essential subgroups of F1 into the F2-classes of the essential subgroups
##  of F2 (backtrack over the essential subgroups, each time replacing N by
##  the stabilizer of the class), and finally test the two containments
##  alpha(F1) <= F2 and F2 <= alpha(F1) with the automizers computed in the
##  target fusion system.
##

#############################################################################
##
#F  FS_EssentialClassOrders( <F> )
##
##  The collected list of the orders of the F-conjugacy classes of essential
##  subgroups of F (an isomorphism invariant; the stored list F!.ess may
##  contain several S-class representatives of the same F-class).
##
InstallGlobalFunction( FS_EssentialClassOrders, function( F )
    local comps, E, c;
    comps := [];
    for E in F!.ess do
        c := Set( FS_ComponentOf( F, FS_NodeOf( F, E )[1] ) );
        if not c in comps then Add( comps, c ); fi;
    od;
    return Collected( List( comps, c -> Size( F!.nodes[ c[1] ].rep ) ) );
end );

#############################################################################
##
#F  FS_IsContainedIn( <F1>, <F2>, <alpha> )
##
##  alpha: S1 -> S2 an isomorphism; is alpha(F1) contained in F2 ?
##  I.e. alpha Aut_{F1}(S1) alpha^-1 <= Aut_{F2}(S2) and
##  alpha Aut_{F1}(E) alpha^-1 <= Aut_{F2}( alpha(E) ) for all essential E.
##
InstallGlobalFunction( FS_IsContainedIn, function( F1, F2, alpha )
    local S2, h, A2, i, E, theta, img, hR, AR, a, pos, node, R, s;
    S2 := F2!.S;
    h := FS_AutHandle( S2 );
    A2 := FS_ComplementData( F2 ).autF;
    for a in F1!.autSgens do
        if not h.to( FS_TransportAut( a, alpha ) ) in A2 then return false; fi;
    od;
    for i in [ 1 .. Length( F1!.ess ) ] do
        E := F1!.ess[i];
        img := ImagesSet( alpha, E );
        # work in the representative R of the S-class of img (cached data)
        pos := FS_NodeOf( F2, img );
        node := F2!.nodes[ pos[1] ];
        R := node.rep; s := pos[2];
        theta := GroupHomomorphismByImagesNC( E, R, FS_PcgsOf( E ), List( FS_PcgsOf( E ), x -> ImagesRepresentative( alpha, x )^s ) );
        hR := FS_AutHandle( R );
        if not IsBound( node.autFmodel ) then
            node.autFmodel := FS_AutSubgroup( hR, Concatenation( FS_AutSGenerators( F2, R ), FS_AutFGeneratorsOfNode( F2, pos[1] ) ) );
        fi;
        AR := node.autFmodel;
        for a in F1!.essauts[i] do
            if not hR.to( FS_TransportAut( a, theta ) ) in AR then return false; fi;
        od;
    od;
    return true;
end );

#############################################################################
##
#F  FS_TransportFusionSystem( <F>, <alpha> ) . . . . . . alpha(F) on Range(alpha)
##
InstallGlobalFunction( FS_TransportFusionSystem, function( F, alpha )
    local S2, ess, auts, i, E, img, theta;
    S2 := Range( alpha );
    ess := []; auts := [];
    for i in [ 1 .. Length( F!.ess ) ] do
        E := F!.ess[i];
        img := ImagesSet( alpha, E );
        theta := GroupHomomorphismByImagesNC( E, img, FS_PcgsOf( E ), List( FS_PcgsOf( E ), x -> ImagesRepresentative( alpha, x ) ) );
        Add( ess, img );
        Add( auts, List( F!.essauts[i], a -> FS_TransportAut( a, theta ) ) );
    od;
    return FusionSystem( S2, List( F!.autSgens, a -> FS_TransportAut( a, alpha ) ), ess, auts );
end );

#############################################################################
##
#F  FS_BClassOrbitStabilizer( <F>, <h>, <H>, <X> )
##
##  H a subgroup of the model of Aut(S) normalizing Aut_F(S), X a subgroup
##  of S.  Computes the orbit of the B-class of X under H (B = Aut_F(S) x| S)
##  by the orbit-stabilizer algorithm on classes.  Returns a record with
##  components reps (class representatives, reps[1] = X), invs, trans
##  (trans[i] an element of H mapping the class of X to the i-th class)
##  and stab (the stabilizer in H of the class of X).
##
InstallGlobalFunction( FS_BClassOrbitStabilizer, function( F, h, H, X )
    local gens, acts, reps, invs, trans, stabgens, i, j, g, Y, pos, t;
    gens := GeneratorsOfGroup( H );
    acts := List( gens, h.from );
    reps := [ X ]; invs := [ FS_SubgroupInvariants( F!.S, X ) ]; trans := [ One( H ) ];
    stabgens := [];
    i := 1;
    while i <= Length( reps ) do
        for j in [ 1 .. Length( gens ) ] do
            Y := ImagesSet( acts[j], reps[i] );
            pos := FS_BClassPosition( F, reps, invs, Y );
            if pos = fail then
                Add( reps, Y ); Add( invs, FS_SubgroupInvariants( F!.S, Y ) ); Add( trans, trans[i] * gens[j] );
            else
                t := trans[i] * gens[j] * trans[ pos[1] ]^-1;
                if not IsOne( t ) then Add( stabgens, t ); fi;
            fi;
        od;
        i := i + 1;
    od;
    return rec( reps := reps, invs := invs, trans := trans, stab := SubgroupNC( H, stabgens ) );
end );

#############################################################################
##
#F  FS_IsomorphismFusionSystemsSameS( <F1>, <F2> )
##
##  F1, F2 fusion systems on the same group S.  Returns an automorphism
##  alpha of S with alpha(F1) = F2, or fail.
##
InstallGlobalFunction( FS_IsomorphismFusionSystemsSameS, function( F1, F2 )
    local S, h, A1, A2, alpha0, N, ess1, ess2, k, targets, i, E, comp, j,
          search, result, inv2, reps2, alpha, test, classnodes;
    S := F1!.S;
    if not IsIdenticalObj( S, F2!.S ) then
        Error( "the fusion systems must be defined on the same group" );
    fi;
    # the orders of the F-classes of essential subgroups (the stored lists
    # may contain F-conjugate representatives)
    if FS_EssentialClassOrders( F1 ) <> FS_EssentialClassOrders( F2 ) then return fail; fi;
    h := FS_AutHandle( S );
    A1 := FS_ComplementData( F1 ).autF;
    A2 := FS_ComplementData( F2 ).autF;
    if Size( A1 ) <> Size( A2 ) then return fail; fi;
    alpha0 := RepresentativeAction( h.model, A1, A2 );
    if alpha0 = fail then return fail; fi;
    N := Normalizer( h.model, A2 );
    # the essential subgroups of F2, as nodes of F2, with their F2-classes
    ess2 := F2!.ess;
    classnodes := List( ess2, E -> FS_ComponentOf( F2, FS_NodeOf( F2, E )[1] ) );
    targets := [];
    for k in [ 1 .. Length( ess2 ) ] do
        for j in classnodes[k] do
            Add( targets, F2!.nodes[j].rep );
        od;
    od;
    targets := DuplicateFreeList( targets );
    # the images of the essential subgroups of F1 under alpha0
    ess1 := List( F1!.ess, E -> ImagesSet( h.from( alpha0 ), E ) );
    # backtrack: find n in N (modulo A2) with n( alpha0(E) ) in the F2-class of some essential, for all E
    test := function( alpha )
        return FS_IsContainedIn( F1, F2, alpha ) and FS_IsContainedIn( F2, F1, FS_InverseIso( alpha ) );
    end;
    search := function( i, H, n )
        # H <= N: the current group of allowed modifications, n the current element (product so far)
        local X, T, r, res, stab, c, os, idx, pos;
        if i > Length( ess1 ) then
            for c in RightTransversal( H, Intersection( H, A2 ) ) do
                alpha := h.from( alpha0 * n * c );
                if test( alpha ) then return alpha; fi;
            od;
            return fail;
        fi;
        X := ImagesSet( h.from( n ), ess1[i] );
        # the orbit of the B2-class of X under H (H normalizes A2, so it
        # permutes the B2-classes), with transversal and stabilizer
        os := FS_BClassOrbitStabilizer( F2, h, H, X );
        for T in targets do
            if Size( T ) <> Size( X ) then continue; fi;
            pos := FS_BClassPosition( F2, os.reps, os.invs, T );
            if pos = fail then continue; fi;
            idx := pos[1];
            r := os.trans[ idx ];
            stab := ConjugateSubgroup( os.stab, r );
            res := search( i + 1, stab, n * r );
            if res <> fail then return res; fi;
        od;
        return fail;
    end;
    # the F2-class of E'_j is a union of S-classes; alpha(E) must land in one of them
    # (as subgroups, not only up to S-conjugacy: S-conjugation is in A2 <= N, so we
    # may use the class representatives themselves as targets).
    result := search( 1, N, One( h.model ) );
    return result;
end );

#############################################################################
##
#M  IsomorphismFusionSystems( <F1>, <F2> )
##
InstallMethod( IsomorphismFusionSystems, [ IsFusionSystem, IsFusionSystem ], function( F1, F2 )
    local S1, S2, iso, G1, alpha;
    S1 := F1!.S; S2 := F2!.S;
    if F1!.p <> F2!.p or Size( S1 ) <> Size( S2 ) then return fail; fi;
    if Size( FS_ComplementData( F1 ).autF ) <> Size( FS_ComplementData( F2 ).autF ) then return fail; fi;
    if FS_EssentialClassOrders( F1 ) <> FS_EssentialClassOrders( F2 ) then return fail; fi;
    if IsIdenticalObj( S1, S2 ) then
        alpha := FS_IsomorphismFusionSystemsSameS( F1, F2 );
        if alpha = fail then return fail; fi;
        return alpha;
    fi;
    iso := IsomorphismGroups( S1, S2 );
    if iso = fail then return fail; fi;
    G1 := FS_TransportFusionSystem( F1, iso );
    alpha := FS_IsomorphismFusionSystemsSameS( G1, F2 );
    if alpha = fail then return fail; fi;
    return FS_ComposeHoms( [ iso, alpha ] );
end );

InstallMethod( IsIsomorphicFusionSystems, [ IsFusionSystem, IsFusionSystem ], function( F1, F2 )
    return IsomorphismFusionSystems( F1, F2 ) <> fail;
end );
