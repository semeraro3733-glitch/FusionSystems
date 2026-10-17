#############################################################################
##
##  autgroup.gi            FusionSystems package
##

#############################################################################
##
#F  FS_ExponentsAutPGroup( <B>, <auto> )
##
##  A copy of ExponentsAutPGroup from the autpgrp package which returns fail
##  instead of running into an error when the automorphism does not lie in
##  the group described by the record B.
##
InstallGlobalFunction( FS_ExponentsAutPGroup, function( B, auto )
    local exps, imgs, perm, news, tmpa, j, e, s, n, subs, base;
    exps := List( B.agAutos, x -> 0 );
    imgs := List( B.gens, x -> ExponentsOfPcElement( B.spec, x ^ auto ) );
    base := imgs{[ 1 .. B.rank ]}{[ 1 .. B.rank ]};
    if base <> IdentityMat( B.rank ) then
        # the action on the Frattini quotient: only available when autpgrp
        # has converted a (soluble) GL-part; if the GL-part is trivial
        # (agHomom unbound) a nontrivial action cannot be decomposed
        if not IsBound( B.agHomom ) then return fail; fi;
        base := base * One( B.field );
        if not base in Source( B.agHomom ) then return fail; fi;
        perm := Image( B.agHomom, base );
        news := ExponentsOfPcElement( B.agTopfc, perm );
        exps{[ 1 .. Length( news ) ]} := news;
        tmpa := MappedVector( news, B.agAutos{[ 1 .. Length( news ) ]} );
        auto := tmpa ^ -1 * auto;
    fi;
    imgs := List( B.gens, x -> ExponentsOfPcElement( B.spec, x ^ auto ) );
    for j in [ 1 .. B.rank ] do imgs[j][j] := 0; od;
    e := Minimum( List( imgs, PositionNonZero ) );
    while e <= Length( B.spec ) do
        j := LGLayers( B.spec )[e];
        s := LGFirst( B.spec )[j];
        n := LGFirst( B.spec )[j + 1];
        base := Concatenation( imgs{[ 1 .. B.rank ]}{[ s .. ( n - 1 ) ]} ) * One( B.field );
        s := PositionSorted( B.layer, j );
        n := PositionSorted( B.layer, j + 1 );
        subs := B.bases{[ s .. n - 1 ]};
        news := SolutionMat( subs, base );
        if news = fail then return fail; fi;
        news := IntVecFFE( news );
        exps{[ s .. n - 1 ]} := news;
        tmpa := MappedVector( news, B.agAutos{[ s .. n - 1 ]} );
        auto := tmpa ^ -1 * auto;
        imgs := List( B.gens, x -> ExponentsOfPcElement( B.spec, x ^ auto ) );
        for j in [ 1 .. B.rank ] do imgs[j][j] := 0; od;
        e := Minimum( List( imgs, PositionNonZero ) );
    od;
    return exps;
end );

#############################################################################
##
#F  FS_AutHandle( <X> )
##
##  Returns (and caches in X) a record with components
##    X       the group,
##    p       the prime,
##    autrec  the autpgrp record for Aut(X) (if used),
##    group   Aut(X) as a GAP group of automorphisms,
##    ispc    true if the model is a pc group,
##    model   the model group (pc group or permutation group),
##    to      a function mapping an automorphism of X to a model element,
##    from    a function mapping a model element to an automorphism of X,
##    inn     Inn(X) as a subgroup of the model.
##
InstallGlobalFunction( FS_AutHandle, function( X )
    local h, A, pcA, nice, P, autrec, gensX, imgs, ok, a, isom, pc, img;
    if HasFSAutHandle( X ) then return FSAutHandle( X ); fi;
    h := rec( X := X, p := PrimePGroup( X ) );
    if Size( X ) = 1 then
        h.group := Group( IdentityMapping( X ) );
        h.ispc := true;
        h.model := TrivialGroup( IsPcGroup );
        h.to := a -> One( h.model );
        h.from := x -> IdentityMapping( X );
        h.inn := h.model;
        SetFSAutHandle( X, h );
        return h;
    fi;
    autrec := AutomorphismGroupPGroup( X, "Over" );
    h.autrec := autrec;
    ok := false;
    if autrec.glOrder = 1 then
        # soluble: use the pc group model supplied by autpgrp
        pcA := PcGroupAutPGroup( autrec );
        pc := Pcgs( pcA );
        gensX := Pcgs( X );
        # autpgrp can only decompose its own PGAutomorphism objects, so we
        # convert a general automorphism first
        h.topg := a -> PGAutomorphism( X, gensX, List( gensX, y -> ImagesRepresentative( a, y ) ) );
        # test the translation on the inner automorphisms
        ok := ForAll( GeneratorsOfGroup( X ), g ->
                 FS_ExponentsAutPGroup( pcA!.autrec, h.topg( ConjugatorAutomorphismNC( X, g ) ) ) <> fail );
        if ok then
            h.ispc := true;
            h.model := pcA;
            h.to := function( a )
                local e;
                e := FS_ExponentsAutPGroup( pcA!.autrec, h.topg( a ) );
                if e = fail then Error( "automorphism not recognised by autpgrp model" ); fi;
                return PcElementByExponentsNC( pc, e );
            end;
            h.from := function( x )
                return MappedVector( ExponentsOfPcElement( pc, x ), pcA!.autrec.agAutos );
            end;
            h.group := ConvertHybridAutGroup( autrec );
        fi;
    fi;
    if not ok then
        A := ConvertHybridAutGroup( autrec );
        SetIsGroupOfAutomorphisms( A, true );
        AssignNiceMonomorphismAutomorphismGroup( A, X );
        nice := NiceMonomorphism( A );
        P := Image( nice, A );
        h.ispc := false;
        h.group := A;
        h.nice := nice;
        h.model := P;
        h.to := a -> ImagesRepresentative( nice, a );
        h.from := x -> PreImagesRepresentative( nice, x );
    fi;
    h.inn := SubgroupNC( h.model, List( GeneratorsOfGroup( X ), g -> h.to( ConjugatorAutomorphismNC( X, g ) ) ) );
    SetFSAutHandle( X, h );
    return h;
end );

InstallGlobalFunction( FS_AutToModel, function( h, a ) return h.to( a ); end );
InstallGlobalFunction( FS_AutFromModel, function( h, x ) return h.from( x ); end );

#############################################################################
##
#F  FS_AutSubgroup( <h>, <auts> ) . .  the subgroup of the model generated by auts
##
InstallGlobalFunction( FS_AutSubgroup, function( h, auts )
    return SubgroupNC( h.model, List( auts, h.to ) );
end );

#############################################################################
##
#F  FS_AutSubgroupGenerators( <h>, <H> ) . . generators of a model subgroup as automorphisms
##
InstallGlobalFunction( FS_AutSubgroupGenerators, function( h, H )
    return List( GeneratorsOfGroup( H ), h.from );
end );

#############################################################################
##
#F  FS_AutPCore( <h> ) . . . . . . . . . . . . . . . . O_p(Aut(X)) in the model
##
InstallGlobalFunction( FS_AutPCore, function( h )
    if not IsBound( h.pcore ) then h.pcore := PCore( h.model, h.p ); fi;
    return h.pcore;
end );

InstallGlobalFunction( FS_AutInn, function( h ) return h.inn; end );

#############################################################################
##
#F  FS_AutOrbitStabilizer( <h>, <H>, <Q> )
##
##  H a subgroup of the model, Q a subgroup of X.  Returns the record of
##  OrbitStabilizer for the action of H on Q by images: components orbit
##  (a list of subgroups of X) and stabilizer (a subgroup of the model).
##
InstallGlobalFunction( FS_AutOrbitStabilizer, function( h, H, Q )
    local gens, acts;
    gens := GeneratorsOfGroup( H );
    if Length( gens ) = 0 then
        return rec( orbit := [ Q ], stabilizer := H );
    fi;
    acts := List( gens, h.from );
    return OrbitStabilizer( H, Q, gens, acts, FS_OnImage );
end );

InstallGlobalFunction( FS_AutStabilizer, function( h, H, Q )
    return FS_AutOrbitStabilizer( h, H, Q ).stabilizer;
end );

#############################################################################
##
#F  FS_AutRepresentativeAction( <h>, <H>, <Q1>, <Q2> )
##
##  An element x of H with Image( h.from( x ), Q1 ) = Q2, or fail.
##
InstallGlobalFunction( FS_AutRepresentativeAction, function( h, H, Q1, Q2 )
    local gens, acts;
    if Q1 = Q2 then return One( H ); fi;
    gens := GeneratorsOfGroup( H );
    if Length( gens ) = 0 then return fail; fi;
    acts := List( gens, h.from );
    return RepresentativeAction( H, Q1, Q2, gens, acts, FS_OnImage );
end );
