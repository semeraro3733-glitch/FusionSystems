# GL(3,3) look-up table: for each admissible T, the candidates H (generators as matrices over GF(3))
GLTABLE_3 := [
rec( Ttype := "C3", Tmats := [ [ [ 1, 0, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ] ], NT := 216,
   cands := [
     rec( size := 24, desc := "SL(2,3)", NHT := 6, soluble := true, O3prime := 8, irreducible := false, composition := [ 1, 2 ], gens := [ [ [ 1, 0, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], [ [ 2, 0, 2 ], [ 1, 1, 0 ], [ 2, 0, 1 ] ], [ [ 2, 0, 1 ], [ 2, 1, 0 ], [ 1, 0, 1 ] ], [ [ 2, 0, 0 ], [ 0, 1, 2 ], [ 0, 0, 2 ] ] ] ),
     rec( size := 48, desc := "GL(2,3)", NHT := 12, soluble := true, O3prime := 8, irreducible := false, composition := [ 2, 1 ], gens := [ [ [ 0, 0, 1 ], [ 1, 1, 1 ], [ 2, 0, 0 ] ], [ [ 2, 0, 0 ], [ 0, 1, 2 ], [ 0, 0, 2 ] ], [ [ 2, 0, 1 ], [ 2, 1, 0 ], [ 1, 0, 1 ] ], [ [ 2, 0, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], [ [ 1, 0, 1 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ] ] ),
     rec( size := 48, desc := "C2 x SL(2,3)", NHT := 12, soluble := true, O3prime := 16, irreducible := false, composition := [ 2, 1 ], gens := [ [ [ 2, 0, 0 ], [ 0, 2, 0 ], [ 0, 0, 2 ] ], [ [ 1, 0, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], [ [ 1, 0, 1 ], [ 2, 2, 0 ], [ 1, 0, 2 ] ] ] ),
     rec( size := 48, desc := "GL(2,3)", NHT := 12, soluble := true, O3prime := 8, irreducible := false, composition := [ 2, 1 ], gens := [ [ [ 0, 0, 2 ], [ 1, 1, 2 ], [ 1, 0, 0 ] ], [ [ 1, 0, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], [ [ 1, 0, 2 ], [ 0, 2, 0 ], [ 0, 0, 2 ] ] ] ),
     rec( size := 96, desc := "C2 x GL(2,3)", NHT := 24, soluble := true, O3prime := 16, irreducible := false, composition := [ 1, 2 ], gens := [ [ [ 2, 0, 0 ], [ 0, 2, 0 ], [ 0, 0, 2 ] ], [ [ 2, 0, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], [ [ 1, 0, 1 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], [ [ 0, 0, 1 ], [ 1, 1, 1 ], [ 2, 0, 0 ] ] ] ),
   ] ),
rec( Ttype := "C3", Tmats := [ [ [ 1, 1, 0 ], [ 0, 1, 1 ], [ 0, 0, 1 ] ] ], NT := 36,
   cands := [
     rec( size := 12, desc := "A4", NHT := 3, soluble := true, O3prime := 4, irreducible := true, composition := [ 3 ], gens := [ [ [ 1, 1, 0 ], [ 0, 1, 1 ], [ 0, 0, 1 ] ], [ [ 0, 0, 2 ], [ 1, 1, 1 ], [ 2, 1, 2 ] ] ] ),
     rec( size := 24, desc := "C2 x A4", NHT := 6, soluble := true, O3prime := 8, irreducible := true, composition := [ 3 ], gens := [ [ [ 2, 0, 0 ], [ 0, 2, 0 ], [ 0, 0, 2 ] ], [ [ 2, 1, 2 ], [ 0, 2, 1 ], [ 0, 0, 2 ] ], [ [ 0, 0, 2 ], [ 1, 0, 1 ], [ 2, 2, 0 ] ] ] ),
     rec( size := 24, desc := "S4", NHT := 6, soluble := true, O3prime := 4, irreducible := true, composition := [ 3 ], gens := [ [ [ 1, 0, 0 ], [ 0, 1, 0 ], [ 2, 1, 2 ] ], [ [ 0, 0, 2 ], [ 1, 1, 1 ], [ 2, 0, 0 ] ], [ [ 1, 1, 0 ], [ 0, 2, 0 ], [ 0, 0, 1 ] ] ] ),
     rec( size := 24, desc := "S4", NHT := 6, soluble := true, O3prime := 4, irreducible := true, composition := [ 3 ], gens := [ [ [ 2, 0, 0 ], [ 0, 2, 0 ], [ 1, 2, 1 ] ], [ [ 0, 0, 1 ], [ 2, 2, 2 ], [ 1, 0, 0 ] ], [ [ 2, 2, 0 ], [ 0, 1, 0 ], [ 0, 0, 2 ] ] ] ),
     rec( size := 39, desc := "C13 : C3", NHT := 3, soluble := true, O3prime := 13, irreducible := true, composition := [ 3 ], gens := [ [ [ 1, 1, 0 ], [ 0, 1, 1 ], [ 0, 0, 1 ] ], [ [ 0, 1, 2 ], [ 1, 2, 2 ], [ 1, 1, 2 ] ] ] ),
     rec( size := 48, desc := "C2 x S4", NHT := 12, soluble := true, O3prime := 8, irreducible := true, composition := [ 3 ], gens := [ [ [ 2, 0, 0 ], [ 0, 2, 0 ], [ 0, 0, 2 ] ], [ [ 1, 0, 0 ], [ 0, 1, 0 ], [ 2, 1, 2 ] ], [ [ 0, 0, 2 ], [ 1, 1, 1 ], [ 2, 0, 0 ] ], [ [ 1, 1, 0 ], [ 0, 2, 0 ], [ 0, 0, 1 ] ] ] ),
     rec( size := 78, desc := "C2 x (C13 : C3)", NHT := 6, soluble := true, O3prime := 26, irreducible := true, composition := [ 3 ], gens := [ [ [ 2, 0, 0 ], [ 0, 2, 0 ], [ 0, 0, 2 ] ], [ [ 1, 1, 0 ], [ 0, 1, 1 ], [ 0, 0, 1 ] ], [ [ 0, 1, 2 ], [ 1, 2, 2 ], [ 1, 1, 2 ] ] ] ),
   ] ),
rec( Ttype := "3^2", Tmats := [ [ [ 1, 0, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], [ [ 1, 0, 0 ], [ 0, 1, 1 ], [ 0, 0, 1 ] ] ], NT := 864,
   cands := [
   ] ),
rec( Ttype := "3^2", Tmats := [ [ [ 1, 0, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], [ [ 1, 1, 0 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ] ], NT := 864,
   cands := [
   ] ),
rec( Ttype := "3^2", Tmats := [ [ [ 1, 0, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], [ [ 1, 1, 0 ], [ 0, 1, 1 ], [ 0, 0, 1 ] ] ], NT := 108,
   cands := [
   ] ),
rec( Ttype := "3^{1+2}_+", Tmats := [ [ [ 1, 0, 2 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ], [ [ 1, 0, 0 ], [ 0, 1, 1 ], [ 0, 0, 1 ] ], [ [ 1, 1, 0 ], [ 0, 1, 0 ], [ 0, 0, 1 ] ] ], NT := 216,
   cands := [
   ] ),
];
