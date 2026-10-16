#############################################################################
##
##  pembedded.gi           FusionSystems package
##
##  A finite group G with Sylow p-subgroup T <> 1 has a strongly p-embedded
##  subgroup if and only if  < N_G(T), N_G(Q) : Q <= T, |Q| = p > is a
##  proper subgroup of G  (see [GLS2, Proposition 17.11]).  In particular
##  G has no strongly p-embedded subgroup if T is normal in G or if O_p(G)
##  is non-trivial.
##

#############################################################################
##
#F  HasStronglyPEmbeddedSubgroup( <G>, <p> )
##
InstallGlobalFunction( HasStronglyPEmbeddedSubgroup, function( G, p )
    local T, H, c, x;
    if Size( G ) mod p <> 0 then return false; fi;
    T := SylowSubgroup( G, p );
    if IsNormal( G, T ) then return false; fi;
    H := Normalizer( G, T );
    if Size( H ) = Size( G ) then return false; fi;
    for c in ConjugacyClasses( T ) do
        x := Representative( c );
        if Order( x ) = p then
            H := ClosureGroup( H, Normalizer( G, SubgroupNC( G, [ x ] ) ) );
            if Size( H ) = Size( G ) then return false; fi;
        fi;
    od;
    return true;
end );

#############################################################################
##
#F  FS_HasStronglyPEmbeddedSubgroupMod( <G>, <K>, <p> ) . . . . for G/K
##
InstallGlobalFunction( FS_HasStronglyPEmbeddedSubgroupMod, function( G, K, p )
    local q;
    if Index( G, K ) mod p <> 0 then return false; fi;
    if Size( K ) = 1 then return HasStronglyPEmbeddedSubgroup( G, p ); fi;
    q := NaturalHomomorphismByNormalSubgroup( G, K );
    return HasStronglyPEmbeddedSubgroup( Image( q ), p );
end );
