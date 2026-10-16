#############################################################################
##
##  group.gi               FusionSystems package
##

#############################################################################
##
#F  FS_EssentialSubgroupsOfGroup( <G>, <S>, <iso>, <exhaustive> )
##
##  G a finite group, S a Sylow p-subgroup, iso: S -> Spc an isomorphism
##  onto a pc group.  Returns the list of pairs [ U, auts ] where U runs
##  through representatives of the Spc-classes of essential subgroups of
##  F_S(G) and auts generates Aut_G(U) (as automorphisms of U <= Spc).
##
InstallGlobalFunction( FS_EssentialSubgroupsOfGroup, function( G, S, iso, exhaustive )
    local Spc, p, cands, reps, invs, U, U0, N, K, res, gens, pcU, auts, x;
    Spc := Image( iso );
    p := PrimePGroup( Spc );
    if exhaustive then
        cands := FS_CentricSubgroupClasses( Spc );
    else
        cands := CentralSeriesCentralizers( Spc );
    fi;
    reps := []; invs := []; res := [];
    for U in cands do
        if U = Spc or not FS_IsCentricIn( Spc, U ) then continue; fi;
        if FS_ClassPosition( Spc, reps, invs, U ) <> fail then continue; fi;
        Add( reps, U ); Add( invs, FS_SubgroupInvariants( Spc, U ) );
        if not FS_CheapProtoEssentialTest( Spc, U ) then continue; fi;
        U0 := PreImage( iso, U );
        N := Normalizer( G, U0 );
        # fully normalized
        if FS_PPart( Size( N ), p ) <> Size( Normalizer( Spc, U ) ) then continue; fi;
        # p-centric
        K := Centralizer( G, U0 );
        if FS_PPart( Size( K ), p ) <> Size( Center( U0 ) ) then continue; fi;
        K := ClosureGroup( U0, K );
        if not FS_HasStronglyPEmbeddedSubgroupMod( N, K, p ) then continue; fi;
        pcU := FS_PcgsOf( U );
        gens := GeneratorsOfGroup( N );
        auts := List( gens, g -> GroupHomomorphismByImagesNC( U, U, pcU,
                    List( pcU, x -> ImagesRepresentative( iso, PreImagesRepresentative( iso, x )^g ) ) ) );
        Add( res, [ U, auts ] );
    od;
    return res;
end );

#############################################################################
##
#F  GroupFusionSystem( <G>, <p> )  or  GroupFusionSystem( <G>, <S> )
##
##  The fusion system F_S(G) on a Sylow p-subgroup S of G.  The result is
##  a fusion system on the pc group Image( IsomorphismPcGroup( S ) ); the
##  isomorphism is stored in the component F!.iso.  With a third argument
##  rec( exhaustive := true ) all S-centric subgroups are examined for being
##  essential; by default only the candidates of Gautam's Theorem 3.6 are
##  examined.
##
InstallGlobalFunction( GroupFusionSystem, function( arg )
    local G, S, p, iso, Spc, exhaustive, ess, N, pcS, autS, F, e;
    G := arg[1];
    if IsInt( arg[2] ) then
        p := arg[2];
        S := SylowSubgroup( G, p );
    else
        S := arg[2];
        p := PrimePGroup( S );
        if Size( G ) / Size( S ) mod p = 0 then
            Error( "<S> must be a Sylow p-subgroup of <G>" );
        fi;
    fi;
    exhaustive := Length( arg ) > 2 and IsBound( arg[3].exhaustive ) and arg[3].exhaustive;
    if IsPcGroup( S ) and IsPcGroup( G ) and ( Length( arg ) < 3 or not IsBound( arg[3].pcgroup ) ) then
        iso := IsomorphismPcGroup( S );
    else
        iso := IsomorphismPcGroup( S );
    fi;
    if Length( arg ) > 2 and IsBound( arg[3].pcgroup ) then
        # the user supplies the pc group and an isomorphism
        iso := arg[3].pcgroup;
    fi;
    Spc := Image( iso );
    N := Normalizer( G, S );
    pcS := FS_PcgsOf( Spc );
    autS := List( GeneratorsOfGroup( N ), g -> GroupHomomorphismByImagesNC( Spc, Spc, pcS,
                List( pcS, x -> ImagesRepresentative( iso, PreImagesRepresentative( iso, x )^g ) ) ) );
    ess := FS_EssentialSubgroupsOfGroup( G, S, iso, exhaustive );
    F := FusionSystem( Spc, autS, List( ess, e -> e[1] ), List( ess, e -> e[2] ) );
    F!.iso := iso;
    SetFusionSystemGroup( F, G );
    SetIsSaturated( F, true );
    return F;
end );
