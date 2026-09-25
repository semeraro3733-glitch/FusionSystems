# Checks that the result for C3 wr C3 wr C3 does not depend on how the lower central series
# is refined (the MAGMA intrinsic RefinedLowerCentralSeries may choose differently from GAP).
# Tests the candidates from all subgroups between consecutive terms once, then reads off
# the result for each of the 16 refinements.
#   gap -q -o 6g validation/run_refinements.g
SizeScreen([4096,24]);;
Read("validation/fast_protoessentials.g");
RunAll := function()
  local W, S, p, L, segs, i, q, subs, As, tags, A, Cands, x, Seen, SeenInv, SeenTags, Xs, XTags, Inv, pos, c,
        AutGens, n, Label, Reps, k, Queue, j, a, m, dead, pass, choices, combos, combo, Aset, inR, orbitsR, res, t;
  t := Runtime();
  W := WreathProduct(WreathProduct(CyclicGroup(IsPermGroup,3), CyclicGroup(IsPermGroup,3)), CyclicGroup(IsPermGroup,3));
  S := Image(IsomorphismPcGroup(W)); p := 3;
  L := LowerCentralSeries(S);
  # As: all subgroups A with L[i+1] <= A <= L[i], i >= 2, A <> L[2]; choices[i]: the intermediate ones
  As := []; choices := [];
  for i in [2..Length(L)-1] do
    q := NaturalHomomorphismByNormalSubgroup(S, L[i+1]);
    subs := List(Filtered(AllSubgroups(Image(q, L[i])), U -> Size(U) > 1 and Size(U) < Index(L[i], L[i+1])), U -> PreImage(q, U));
    Add(choices, [Length(As)+1..Length(As)+Length(subs)]);
    Append(As, subs);
    if i > 2 then Add(As, L[i]); fi;
  od;
  Add(As, L[Length(L)]);
  Print("number of subgroups A: ", Length(As), "; intermediate choices per segment: ", List(choices, Length), "\n");
  # candidates with tags
  Seen := []; SeenInv := []; SeenTags := [];
  for i in [1..Length(As)] do
    q := NaturalHomomorphismByNormalSubgroup(S, As[i]);
    for c in Filtered(ConjugacyClasses(Image(q)), c -> Order(Representative(c)) = p) do
      x := PreImage(q, Centralizer(Image(q), Representative(c)));
      if x = S or IsCyclic(x) or not IsCentricIn(S, x) then continue; fi;
      pos := ClassPosition(S, Seen, SeenInv, x);
      if pos = 0 then Add(Seen, x); Add(SeenInv, SubgroupInvariants(S, x)); Add(SeenTags, [i]);
      else AddSet(SeenTags[pos], i); fi;
    od;
  od;
  Print("S-classes of S-centric candidates over all A: ", Length(Seen), " (", Runtime()-t, " ms)\n");
  Xs := []; XTags := []; Inv := [];
  for i in [1..Length(Seen)] do
    if CheapPS(S, Seen[i]) then Add(Xs, Seen[i]); Add(XTags, SeenTags[i]); Add(Inv, SeenInv[i]); fi;
  od;
  Print("cheap-passing S-classes over all A: ", Length(Xs), " (", Runtime()-t, " ms)\n");
  AutGens := GeneratorsOfGroup(AutomorphismGroup(S));
  n := Length(Xs); Label := List([1..n], i -> 0); Reps := []; dead := [];
  for i in [1..n] do
    if Label[i] <> 0 then continue; fi;
    Add(Reps, i); k := Length(Reps); Label[i] := k; Queue := [i]; Add(dead, false);
    while Length(Queue) > 0 do
      j := Remove(Queue);
      for a in AutGens do
        m := ClassPosition(S, Xs, Inv, Image(a, Xs[j]));
        if m = 0 then dead[k] := true; elif Label[m] = 0 then Label[m] := k; Add(Queue, m); fi;
      od;
    od;
  od;
  Print("Aut(S)-orbits over all A: ", Length(Reps), ", not closed: ", Number(dead, d -> d), " (", Runtime()-t, " ms)\n");
  pass := List(Reps, r -> ExpensivePS(S, Xs[r]));
  Print("orbits passing expensive tests: ", Number(pass, x -> x), " covering ",
        Number([1..n], i -> pass[Label[i]]), " S-classes (", Runtime()-t, " ms)\n");
  # each refinement: As in the refinement = fixed ones plus one choice per segment
  combos := Cartesian(Filtered(choices, ch -> Length(ch) > 0));
  res := [];
  for combo in combos do
    Aset := Difference([1..Length(As)], Difference(Union(choices), combo));
    inR := List([1..n], i -> Intersection(XTags[i], Aset) <> []);
    orbitsR := Filtered([1..Length(Reps)], k -> pass[k] and ForAll(Filtered([1..n], i -> Label[i] = k), i -> inR[i]));
    Add(res, [Length(orbitsR), Number([1..n], i -> Label[i] in orbitsR)]);
  od;
  Print("per refinement [Aut(S)-classes, S-classes]: ", res, "\n");
end;
RunAll();
QUIT;
