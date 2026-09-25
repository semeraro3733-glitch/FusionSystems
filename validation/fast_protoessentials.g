# GAP companion to FusionSystems.m (needs the packages autpgrp and smallgrp).
#
# This file contains
#  * CentralSeriesCandidates(S): the candidates C_S(xA/A) of Section 3 of
#    P. Gautam, arXiv:2607.24674 (same as CentralSeriesCentralizers in
#    FusionSystems.m),
#  * a line-by-line port of the Parker-Semeraro proto-essential tests and of
#    ProtoEssentialSubgroups(S : Fast:=true) from FusionSystems.m, used to
#    produce the expected output of tests/TestC3wrC3wrC3.m,
#  * ValidateSmallGroups(p, n, range): compares the fast candidates against an
#    exhaustive search through all subgroup classes of each small group,
#  * EssentialsOfGroupFound(G, p): checks that the essential subgroups of the
#    fusion system of a finite group G are among the fast candidates.
#
# Usage:  gap -q validation/fast_protoessentials.g validation/run_c3wrc3wrc3.g

LoadPackage("autpgrp");;
LoadPackage("smallgrp");;

# A central series of S with factors of order p refining the lower central series.
RefinedLowerCentralSeries := function(S)
  local L;
  L := CompositionSeriesThrough(S, LowerCentralSeries(S));
  return L{[1..Position(L, TrivialSubgroup(S))]};
end;

# The subgroups C_S(xA/A), A a term of the series inside [S,S], xA of order p.
CentralSeriesCandidates := function(S)
  local p, L, i, q, C;
  p := PrimePGroup(S);
  L := RefinedLowerCentralSeries(S);
  C := [];
  for i in [Position(L, DerivedSubgroup(S))+1..Length(L)] do
    q := NaturalHomomorphismByNormalSubgroup(S, L[i]);
    Append(C, List(Filtered(ConjugacyClasses(Image(q)), c -> Order(Representative(c)) = p),
                   c -> PreImage(q, Centralizer(Image(q), Representative(c)))));
  od;
  return C;
end;

IsCentricIn := function(S, E) return IsSubset(E, Centralizer(S, E)); end;

Automizer := function(G, H)
  local A;
  A := Group(List(GeneratorsOfGroup(Normalizer(G, H)), a -> ConjugatorAutomorphismNC(H, a)),
             IdentityMapping(H));
  SetIsGroupOfAutomorphisms(A, true);
  return A;
end;

# Aut_S(E) meet O_p(Aut(E)) = Inn(E)
IsRadicalAut := function(S, E)
  local p, A, n;
  p := PrimePGroup(S);
  A := AutomorphismGroup(E);
  if not HasNiceMonomorphism(A) then AssignNiceMonomorphismAutomorphismGroup(A, E); fi;
  n := NiceMonomorphism(A);
  return Size(Intersection(Image(n, Automizer(S, E)), PCore(Image(n, A), p))) = Index(E, Center(E));
end;

# C_{N_S(E)}(E/Phi(E)) <= E
FrattiniCentralizerTest := function(S, E)
  local N, q;
  N := Normalizer(S, E);
  q := NaturalHomomorphismByNormalSubgroup(N, FrattiniSubgroup(E));
  return IsSubset(E, PreImage(q, Centralizer(Image(q), Image(q, E))));
end;

# ---- port of IsQuaternionOrCyclic and IsStronglypSylow from FusionSystems.m ----
IsQuaternionOrCyclicPS := function(G)
  local p;
  if Size(G) = 1 then return true; fi;
  p := PrimePGroup(G);
  return Number(ConjugacyClasses(G), c -> Order(Representative(c)) = p) = p - 1;
end;

TestersCache := rec();
TestersPS := function(p)
  local X, Y, T, i;
  if IsBound(TestersCache.(String(p))) then return TestersCache.(String(p)); fi;
  X := CyclicGroup(IsPcGroup, p); Y := X; T := [];
  for i in [1..7] do Y := DirectProduct(Y, X); Add(T, Y); od;
  Add(T, SylowSubgroup(SU(3,p), p)); Add(T, SylowSubgroup(SU(3,p^2), p));
  if p = 3 then Add(T, SylowSubgroup(AutomorphismGroup(PSL(2,8)), 3)); fi;
  if p = 2 then Add(T, SylowSubgroup(SuzukiGroup(IsPermGroup, 8), 2)); fi;
  T := List(T, G -> Image(IsomorphismPcGroup(G)));
  TestersCache.(String(p)) := T;
  return T;
end;

IsStronglypSylowPS := function(Q)
  local p;
  p := PrimePGroup(Q);
  if not IsQuaternionOrCyclicPS(Q) and Size(Q) <= p^7 then
    return ForAny(TestersPS(p), T -> Size(T) = Size(Q) and IsomorphismGroups(T, Q) <> fail);
  fi;
  return true;
end;

# the tests of CheapProtoEssentialTest (for S-centric E)
CheapPS := function(S, E)
  local N;
  N := Normalizer(S, E);
  return Index(E, FrattiniSubgroup(E)) >= Index(N, E)^2
     and FrattiniCentralizerTest(S, E)
     and IsStronglypSylowPS(N/E);
end;

# RadicalTest and the solubility test
ExpensivePS := function(S, E)
  local p, A, n;
  p := PrimePGroup(S);
  A := AutomorphismGroup(E);
  if not HasNiceMonomorphism(A) then AssignNiceMonomorphismAutomorphismGroup(A, E); fi;
  n := NiceMonomorphism(A);
  if Size(Intersection(Image(n, Automizer(S, E)), PCore(Image(n, A), p))) <> Index(E, Center(E)) then
    return false;
  fi;
  return IsQuaternionOrCyclicPS(Normalizer(S, E)/E) or not IsSolvableGroup(Image(n, A));
end;

SubgroupInvariants := function(S, H)
  return [Size(H), Size(Normalizer(S, H)), Size(Center(H)), Size(FrattiniSubgroup(H)), Size(DerivedSubgroup(H))];
end;

ClassPosition := function(S, Xs, Inv, H)
  local j, iv;
  iv := SubgroupInvariants(S, H);
  for j in [1..Length(Xs)] do
    if Inv[j] = iv and IsConjugate(S, Xs[j], H) then return j; fi;
  od;
  return 0;
end;

# Port of the general (not maximal class) branch of
# ProtoEssentialSubgroups(S : Fast:=true) in FusionSystems.m.
# Returns [Aut(S)-class representatives, S-class representatives].
FastProtoEssentials := function(S)
  local p, t, C, Seen, SeenInv, Xs, Inv, x, AutGens, n, Label, Dead, Reps, i, k, dead, Queue, j, a, m,
        AutReps, SReps;
  p := PrimePGroup(S);
  t := Runtime();
  C := CentralSeriesCandidates(S);
  Print("#I ", Length(C), " candidates from the central series (", Runtime()-t, " ms)\n");
  Seen := []; SeenInv := []; Xs := []; Inv := [];
  for x in C do
    if x = S or IsCyclic(x) or not IsCentricIn(S, x) then continue; fi;
    if ClassPosition(S, Seen, SeenInv, x) <> 0 then continue; fi;
    Add(Seen, x); Add(SeenInv, SubgroupInvariants(S, x));
    if CheapPS(S, x) then Add(Xs, x); Add(Inv, SeenInv[Length(SeenInv)]); fi;
  od;
  Print("#I ", Length(Seen), " S-classes of S-centric candidates, ", Length(Xs),
        " pass the tests not requiring Aut(E) (", Runtime()-t, " ms)\n");
  AutGens := GeneratorsOfGroup(AutomorphismGroup(S));
  n := Length(Xs); Label := List([1..n], i -> 0); Dead := []; Reps := [];
  for i in [1..n] do
    if Label[i] <> 0 then continue; fi;
    Add(Reps, i); k := Length(Reps); Label[i] := k; dead := false; Queue := [i];
    while Length(Queue) > 0 do
      j := Remove(Queue);
      for a in AutGens do
        m := ClassPosition(S, Xs, Inv, Image(a, Xs[j]));
        if m = 0 then dead := true;
        elif Label[m] = 0 then Label[m] := k; Add(Queue, m); fi;
      od;
    od;
    Add(Dead, dead);
  od;
  Print("#I ", Length(Reps), " Aut(S)-classes, of which ", Number(Dead, d -> d),
        " are not closed under Aut(S) (", Runtime()-t, " ms)\n");
  AutReps := []; SReps := [];
  for k in [1..Length(Reps)] do
    if not Dead[k] and ExpensivePS(S, Xs[Reps[k]]) then
      Add(AutReps, Xs[Reps[k]]);
      Append(SReps, Xs{Filtered([1..n], i -> Label[i] = k)});
    fi;
  od;
  Print("#I ", Length(AutReps), " Aut(S)-classes and ", Length(SReps),
        " S-classes of proto-essential subgroups (", Runtime()-t, " ms)\n");
  return [AutReps, SReps];
end;

# The data printed by tests/TestC3wrC3wrC3.m for each Aut(S)-class representative:
# [log_p|E|, log_p|N_S(E):E|, |Z(E)|, |E:Phi(E)|, E normal in S]
ClassData := function(S, E)
  local p;
  p := PrimePGroup(S);
  return [Log(Size(E), p), Log(Index(Normalizer(S, E), E), p), Size(Center(E)),
          Index(E, FrattiniSubgroup(E)), IsNormal(S, E)];
end;

# ---- validation of the candidate reduction ----

# For all non-abelian SmallGroup(p^n, i), i in range: every subgroup class E which is proper,
# non-cyclic, S-centric, has |E/Phi(E)| >= |Out_S(E)|^2 and is radical
# (Aut_S(E) meet O_p(Aut(E)) = Inn(E)) is compared with the fast candidates.
# Returns the list of misses [i, IdGroup(E), |N_S(E):E|].
ValidateSmallGroups := function(p, n, range)
  local i, S, cls, Y, C, bad, E, totY, totcls, totC, t;
  bad := []; totY := 0; totcls := 0; totC := 0; t := Runtime();
  for i in range do
    S := SmallGroup(p^n, i);
    if IsAbelian(S) then continue; fi;
    cls := List(ConjugacyClassesSubgroups(S), Representative);
    totcls := totcls + Length(cls);
    Y := Filtered(cls, E -> E <> S and not IsCyclic(E) and IsCentricIn(S, E)
                  and Index(E, FrattiniSubgroup(E)) >= Index(Normalizer(S, E), E)^2);
    Y := Filtered(Y, E -> IsRadicalAut(S, E));
    C := CentralSeriesCandidates(S);
    totY := totY + Length(Y); totC := totC + Length(C);
    for E in Y do
      if not ForAny(C, D -> Size(D) = Size(E) and IsConjugate(S, D, E)) then
        Add(bad, [i, IdGroup(E), Index(Normalizer(S, E), E)]);
      fi;
    od;
  od;
  Print("p=", p, " n=", n, " groups ", range[1], "..", range[Length(range)],
        ": subgroup classes=", totcls, " candidates=", totC,
        " centric+radical+|E/Phi(E)|>=|Out_S(E)|^2 classes=", totY,
        " not among candidates=", Length(bad), " (", Runtime()-t, " ms)\n");
  return bad;
end;

# G has a strongly p-embedded subgroup iff <N_G(T), N_G(Q) : Q <= T, |Q| = p> <> G.
HasStronglyPEmbedded := function(G, p)
  local T, H, c;
  T := SylowSubgroup(G, p);
  if Size(T) = 1 or IsNormal(G, T) then return false; fi;
  H := Normalizer(G, T);
  for c in ConjugacyClasses(T) do
    if Order(Representative(c)) = p then
      H := ClosureGroup(H, Normalizer(G, Subgroup(G, [Representative(c)])));
      if Size(H) = Size(G) then return false; fi;
    fi;
  od;
  return true;
end;

# The essential subgroups of the fusion system of G on a Sylow p-subgroup S (up to
# S-conjugacy): [IdGroup(E), |Out_S(E)|, E is S-conjugate to a fast candidate].
EssentialsOfGroupFound := function(G0, p)
  local G, T, iso, S, C, cls, res, U, E0, nm, Q;
  G := Image(IsomorphismPermGroup(G0));
  T := SylowSubgroup(G, p); iso := IsomorphismPcGroup(T); S := Image(iso);
  C := CentralSeriesCandidates(S);
  cls := List(ConjugacyClassesSubgroups(S), Representative);
  res := [];
  for U in cls do
    if U = S or not IsCentricIn(S, U) then continue; fi;
    E0 := PreImage(iso, U); nm := Normalizer(G, E0);
    # fully normalised representative only
    if Size(SylowSubgroup(nm, p)) <> Size(Normalizer(S, U)) then continue; fi;
    Q := nm / ClosureGroup(E0, Centralizer(G, E0));
    if HasStronglyPEmbedded(Image(IsomorphismPermGroup(Q)), p) then
      Add(res, [IdGroup(U), Index(Normalizer(S, U), U),
                ForAny(C, D -> Size(D) = Size(U) and IsConjugate(S, D, U))]);
    fi;
  od;
  return res;
end;
