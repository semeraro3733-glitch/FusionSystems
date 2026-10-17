LoadPackage( "FusionSystems" );;
# model of a Sylow 3-subgroup of 3D4(q), 3^a || q+1: inside C_{3^(a+1)} wr C3
D4Model := function( a )
    local n, K, z, g1, g, c, D, gens, S;
    n := 3^( a + 1 );
    K := CyclotomicField( n ); z := E( n );          # z of order 3^(a+1); g := z^3 of order 3^a
    g := z^3;
    c := PermutationMat( (1,2,3), 3, K );
    D := function( x, y, w ) return DiagonalMat( [ x, y, w ] ); end;
    gens := [ D( g, g^-1, 1 ), D( 1, g, g^-1 ), D( z, z, z^-2 ), c ];
    S := Group( gens );
    return S;
end;;
# 3D4(2): PrimitiveGroup( 819, 5 )
G := PrimitiveGroup( 819, 5 );;
Print( "|G| = ", Size( G ), " = |3D4(2)|: ", Size( G ) = 211341312, "\n" );
S2 := SylowSubgroup( G, 3 );;
Print( "Syl_3(3D4(2)): order ", Size( S2 ), ", IdGroup ", IdGroup( S2 ), ", abelian invariants of maximal abelian... Z = ", Size( Centre( S2 ) ), ", exponent ", Exponent( S2 ), ", class ", NilpotencyClassOfGroup( S2 ), "\n" );
M := Filtered( MaximalSubgroups( S2 ), IsAbelian );;
Print( "  abelian maximal subgroups: ", List( M, AbelianInvariants ), "\n" );
S2m := D4Model( 1 );;
Print( "model a=1: order ", Size( S2m ), ", IdGroup ", IdGroup( Image( IsomorphismPcGroup( S2m ) ) ), "\n" );
# the alternative with y^c = y (no twist) for comparison
S3m := D4Model( 3 );;
P := Image( IsomorphismPcGroup( S3m ) );;
Print( "model a=3: order ", Size( P ), ", |Z| = ", Size( Centre( P ) ), ", exponent ", Exponent( P ), ", class ", NilpotencyClassOfGroup( P ), ", rank ", RankPGroup( P ), ", |S'| = ", Size( DerivedSubgroup( P ) ), ", |Phi| = ", Size( FrattiniSubgroup( P ) ), ", classes ", Length( ConjugacyClasses( P ) ), "\n" );
Print( "  abelian maximal subgroups: ", List( Filtered( MaximalSubgroups( P ), IsAbelian ), AbelianInvariants ), "\n" );
# save the pc presentation
PrintTo( "/home/user/FusionSystems/order38/data/d4_sylow_model.g", "# model of Syl_3(3D4(q)), 3^3 || q+1, as a pc group (see scripts/known_groups.g)\nFS38_D4Model := ", CodePcGroup( P ), ";\n" );
QUIT;
