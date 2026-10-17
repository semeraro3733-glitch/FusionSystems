# GL(2,3) look-up table: for each admissible T, the candidates H (generators as matrices over GF(3))
GLTABLE_2 := [
rec( Ttype := "C3", Tmats := [ [ [ 1, 2 ], [ 0, 1 ] ] ], NT := 12,
   cands := [
     rec( size := 24, desc := "SL(2,3)", NHT := 6, soluble := true, O3prime := 8, irreducible := true, composition := [ 2 ], gens := [ [ [ 2, 0 ], [ 0, 2 ] ], [ [ 2, 1 ], [ 1, 1 ] ], [ [ 0, 1 ], [ 2, 0 ] ], [ [ 1, 2 ], [ 0, 1 ] ] ] ),
     rec( size := 48, desc := "GL(2,3)", NHT := 12, soluble := true, O3prime := 8, irreducible := true, composition := [ 2 ], gens := [ [ [ 2, 0 ], [ 0, 2 ] ], [ [ 2, 1 ], [ 1, 1 ] ], [ [ 0, 1 ], [ 2, 0 ] ], [ [ 1, 2 ], [ 0, 1 ] ], [ [ 2, 0 ], [ 0, 1 ] ] ] ),
   ] ),
];
