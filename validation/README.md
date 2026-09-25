# Validation (GAP)

The MAGMA code could not be run where it was written (no MAGMA licence), so the method was
checked in GAP 4.12.1 with the packages `autpgrp` and `smallgrp`.

* `fast_protoessentials.g` contains the candidates `C_S(xA/A)` and a line-by-line port of
  `ProtoEssentialSubgroups(S : Fast:=true)`, including the Parker–Semeraro tests
  `IsStronglypSylow`, `RadicalTest` and the solubility test. It also has the validation
  functions used below.
* `run_c3wrc3wrc3.g` produces the expected values in `tests/TestC3wrC3wrC3.m`.
* `run_validation.g` runs the checks below.

```
gap -q -o 6g validation/fast_protoessentials.g validation/run_c3wrc3wrc3.g
gap -q -o 6g validation/fast_protoessentials.g validation/run_validation.g
```

## 1. Are the candidates complete? (small groups, exhaustive)

`ValidateSmallGroups(p, n, range)` computes all conjugacy classes of subgroups of each
non-abelian `SmallGroup(p^n, i)`. It keeps those `E` which pass the necessary conditions used
by the original Parker–Semeraro code:
* `E < S` and `E` is not cyclic;
* `E` is `S`-centric;
* `|E/Phi(E)| >= |Out_S(E)|^2`;
* `Aut_S(E) ∩ O_p(Aut(E)) = Inn(E)`.

It then checks whether each such `E` is `S`-conjugate to one of the candidates.

| order | groups | subgroup classes | classes passing the conditions | not among the candidates |
|---|---|---|---|---|
| 2^3 | 5 | 14 | 2 | 0 |
| 2^4 | 14 | 136 | 9 | 0 |
| 2^5 | 51 | 1641 | 31 | 0 |
| 2^6 | 267 | 23802 | 198 | 12 |
| 3^3 | 5 | 19 | 5 | 0 |
| 3^4 | 15 | 242 | 17 | 0 |
| 3^5 | 67 | 4636 | 77 | 0 |
| 3^6 | 504 | 127061 | 802 | 62 |
| 5^3 | 5 | 25 | 7 | 0 |
| 5^4 | 15 | 452 | 24 | 0 |
| 7^3 | 5 | 31 | 9 | 0 |

At orders 2^6 and 3^6 the exceptions are all of the same kind:
* `E ≅ 2^4` with `Out_S(E) ≅ 2^2`, or `E ≅ 3^4` with `|Out_S(E)| = 9`;
* `E` is normal in `S`.

None of these can be essential in a saturated fusion system. If one were, the model of
`N_F(E)` would contain a perfect subgroup `E.L`, with `L ≅ SL_2(4)` (for p = 2) or
`L ≅ (P)SL_2(9)` (for p = 3), having `S` as a Sylow `p`-subgroup. The candidate groups are:

* for p = 2, `PerfectGroup(960, 1)` and `PerfectGroup(960, 2)`, with Sylow subgroups
  `SmallGroup(64, 242)` and `SmallGroup(64, 138)`;
* for p = 3, `PerfectGroup(29160, 4)`, `PerfectGroup(58320, 1)` and `PerfectGroup(58320, 2)`,
  with Sylow subgroups `SmallGroup(729, 321)` and `SmallGroup(729, 469)`.

None of these Sylow subgroups is among the exceptions, and in every one of these groups the
essential subgroup is among the candidates (section 2).

So the candidates contain every subgroup that can be essential, as Theorem 3.6 of
arXiv:2607.24674 asserts. However, they can be fewer than the subgroups accepted by the
original, weaker Parker–Semeraro tests. At orders `2^6` and `3^6`, `ProtoEssentialSubgroups`
with `Fast:=true` therefore returns fewer subgroups than with `Fast:=false`. The extra ones
cannot be essential, so the saturated fusion systems found by `AllFusionSystems` are the same.
For all the other orders in the table the two searches return exactly the same `S`-classes.

The zero-exception orders do not depend on the choice of central series. The candidate sets
depend on how the lower central series is refined, and the MAGMA intrinsic
`RefinedLowerCentralSeries` refines it differently from GAP's `CompositionSeriesThrough`. The
check was repeated with 5 random refinements of every non-abelian group of order `2^5`, `3^4`,
`3^5` and `5^4` (620 pairs), and there were no exceptions.

**End-to-end check of the pipeline.** For every non-abelian group of order `3^4`, `3^5`, `5^4`
and `2^5`, the GAP port of `ProtoEssentialSubgroups(S : Fast:=true)` returns exactly the
`S`-classes that pass the Parker–Semeraro tests in an exhaustive search: 17, 77, 24 and 31
classes in total. This covers the `Aut(S)`-orbit computation and the removal of orbits that
leave the candidate set. `tests/TestFastVsOriginal.m` makes the same comparison in MAGMA.

## 2. Essential subgroups of group fusion systems

`EssentialsOfGroupFound(G, p)` lists the essential subgroups of the fusion system of `G`,
up to `S`-conjugacy, and records whether each one is among the candidates.

| group | p | essential subgroups `[IdGroup(E), |Out_S(E)|]` | among the candidates |
|---|---|---|---|
| PSL(3,4) | 2 | `[16,14], 4` twice | yes |
| PSL(3,8) | 2 | `[64,267], 8` twice | yes |
| PSL(3,9) | 3 | `[81,15], 9` twice | yes |
| PSp(4,3) | 3 | `[27,5], 3` and `[27,3], 3` | yes |
| Alt(9) | 3 | `[9,2], 3` and `[27,5], 3` | yes |
| 3^4:PSL_2(9), 3^4.SL_2(9) (two groups) | 3 | `[81,15], 9` | yes |

PSL(3,8) shows why this code keeps the Parker–Semeraro bound `|E/Phi(E)| >= |Out_S(E)|^2`. The
GAP code accompanying arXiv:2607.24674 rejects `E` when `rank(E) < n^2`, where
`|Out_S(E)| = p^n`. That would discard the essential subgroups `2^6` of PSL(3,8) (`n = 3`,
rank 6).

## 3. C3 wr C3 wr C3

`run_c3wrc3wrc3.g` gives the following for `S = C3 wr C3 wr C3`, the Sylow 3-subgroup of
`Sym(27)`, of order `3^13`. Times are for GAP 4.12.1 on one core.

| step | result | time |
|---|---|---|
| candidates `C_S(xA/A)` (with GAP's `CompositionSeriesThrough`) | 2638 | 4 s |
| `S`-classes passing the tests not needing `Aut(E)` | 73 | 10 min |
| `Aut(S)`-orbits on these (Aut(S) has 20 generators) | 45, none leaving the candidate set | 1.5 min |
| after `RadicalTest` and the solubility test (one `Aut(E)` per orbit) | **16 `Aut(S)`-classes, 18 `S`-classes** | 17.5 min |

The 16 `Aut(S)`-classes, given as `[log_3|E|, log_3|N_S(E):E|, |Z(E)|, |E:Phi(E)|, E normal in S]`:

```
[12,1,27,729,true]
[11,1,243,2187,false]  [11,1,27,729,false]    [11,1,3,27,false]
[10,2,2187,6561,false] [10,2,243,2187,false]  [10,1,81,729,false]  [10,1,27,81,false]  [10,1,3,27,false]
[9,3,2187,6561,false]  [9,3,243,2187,false]   [9,2,729,2187,false]
[8,3,6561,6561,false]  [8,2,243,729,false]
[7,3,2187,2187,false]  [7,1,9,27,false]
```

The `S`-classes have orders `3^12` (1), `3^11` (3), `3^10` (6), `3^9` (4), `3^8` (2) and `3^7` (2).

For comparison, the old approach needs every subgroup class of `S` (or of `S/Z(S)`), plus
`Aut(E)` for every `S`-centric one. In GAP, `ConjugacyClassesSubgroups(S)` ran out of its 7 GB
memory limit before finishing.

Check that the result does not depend on the refinement of the lower central series: pending.

Comparison with the output of the GAP code accompanying arXiv:2607.24674: pending.
