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
#F  FS_IsContainedIn( <F1>, <F2>, <alpha> )
##
##  alpha: S1 -> S2 an isomorphism; is alpha(F1) contained in F2 ?
##  I.e. alpha Aut_{F1}(S1) alpha^-1 <= Aut_{F2}(S2) and
##  alpha Aut_{F1}(E) alpha^-1 <= Aut_{F2}( alpha(E) ) for all essential E.
##
InstallGlobalFunction( FS_IsContainedIn, function( F1, F2, alpha )
    local S2, h, A2, i, E, theta, img, hE, AE, a;
    S2 := F2!.S;
    h := FS_AutHandle( S2 );
    A2 := FS_ComplementData( F2 ).autF;
    for a in F1!.autSgens do
        if not h.to( FS_TransportAut( a, alpha ) ) in A2 then return false; fi;
    od;
    for i in [ 1 .. Length( F1!.ess ) ] do
        E := F1!.ess[i];
        img := ImagesSet( alpha, E );
        theta := GroupHomomorphismByImagesNC( E, img, FS_PcgsOf( E ), List( FS_PcgsOf( E ), x -> ImagesRepresentative( alpha, x ) ) );
        hE := FS_AutHandle( img );
        AE := FS_AutSubgroup( hE, Concatenation( FS_AutSGenerators( F2, img ), FS_AutFGenerators( F2, img ) ) );
        for a in F1!.essauts[i] do
            if not hE.to( FS_TransportAut( a, theta ) ) in AE then return false; fi;
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
    if Length( F1!.ess ) <> Length( F2!.ess ) then
        # the numbers of essential classes could still agree if the lists
        # contain F-conjugate subgroups; we do not try to be clever here
        if Set( List( F1!.ess, Size ) ) <> Set( List( F2!.ess, Size ) ) then return fail; fi;
    fi;
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
        local X, T, r, res, stab, cos, c;
        if i > Length( ess1 ) then
            for c in RightTransversal( H, Intersection( H, A2 ) ) do
                alpha := h.from( alpha0 * n * c );
                if test( alpha ) then return alpha; fi;
            od;
            return fail;
        fi;
        X := ImagesSet( h.from( n ), ess1[i] );
        for T in targets do
            if Size( T ) <> Size( X ) then continue; fi;
            r := FS_AutRepresentativeAction( h, H, X, T );
            if r = fail then continue; fi;
            stab := FS_AutStabilizer( h, H, T );
            # the elements of H mapping X to T are r * stab
            cos := RightTransversal( stab, Intersection( stab, A2 ) );
            # we must keep the whole coset r*stab as search space, modulo A2
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
    if Collected( List( F1!.ess, Size ) ) <> Collected( List( F2!.ess, Size ) ) then return fail; fi;
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
