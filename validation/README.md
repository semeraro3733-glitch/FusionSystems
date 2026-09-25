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

Pending: the GAP reference run (`run_c3wrc3wrc3.g`) is still in progress.

So far the port reports 2638 candidates from the central series (in 4 seconds), 73
`S`-classes passing the tests that do not need `Aut(E)`, and 45 `Aut(S)`-orbits on them,
none of which leaves the candidate set. The exhaustive approach (`ConjugacyClassesSubgroups(S)`)
ran out of its 7 GB memory limit.
