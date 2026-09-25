# FusionSystems.m with the fast proto-essential search

This is the Parker–Semeraro MAGMA package `FusionSystems.m`
(from [chris1961parker/Fusion-Systems](https://github.com/chris1961parker/Fusion-Systems),
described in *Algorithms for fusion systems with applications to p-groups of small order*).
It has been extended with the fast method for finding proto-essential subgroups from
Section 3 (Theorem 3.6 and Algorithms 3.7 and 3.9) of

> P. Gautam, *Fusion systems on Sylow 3-subgroups of Fischer and Monster sporadic groups II*,
> [arXiv:2607.24674](https://arxiv.org/abs/2607.24674).

The author's GAP implementation is in
[pete-g00/sporadics-code](https://github.com/pete-g00/sporadics-code) (`find-proto-essentials.g`).

Load the package as before with `Attach("FusionSystems.m");`.

## The method

Let `S = L_0 > L_1 > ... > L_n = 1` be a central series of `S` with all factors of order `p`
which refines the lower central series. The only subgroups considered as candidates for
essential subgroups are

    C_S(xA/A) = { s in S : [s,x] in A },

where `A = L_i` lies in `[S,S]` (including `A = 1`) and `xA` runs through the elements of
order `p` of `S/A`. These subgroups come from conjugacy classes of elements of the quotients
`S/A`. The subgroup lattice of `S` is never computed.

The original code computed every subgroup of `S/Z(S)` and the automorphism group of every
`S`-centric subgroup. That is not feasible once `|S|` is large; for example `S = C3 wr C3 wr C3`,
of order `3^13`.

## What changed in `FusionSystems.m`

New intrinsics:

| intrinsic | purpose |
|---|---|
| `RefinedLowerCentralSeries(S)` | a central series with factors of order `p` refining the lower central series |
| `CentralSeriesCentralizers(S)` | the candidates `C_S(xA/A)` described above |
| `ProtoEssentialSubgroups(S : Fast:=true, Printing:=false)` | returns the Aut(S)-class representatives and the S-class representatives of the proto-essential subgroups of the PC-group `S` |
| `ProtoEssentialAutomiserCandidates(S, P)` | the candidate automisers `Aut_F(P)` (stored in ``P`autF``). This code was duplicated in `AllProtoEssentials` and `AllFusionSystems`. |

`ProtoEssentialSubgroups` with `Fast:=true` (the default) works as follows.
1. It takes the candidates from `CentralSeriesCentralizers` and keeps the `S`-centric ones up to `S`-conjugacy.
2. It applies the Parker–Semeraro tests that do not need `Aut(E)`:
   * `|E/Phi(E)| >= |Out_S(E)|^2`;
   * `IsStronglypSylow(N_S(E)/E)`;
   * the cheap consequence `C_{N_S(E)}(E/Phi(E)) <= E` of the radical test.
3. It computes the orbits of `Aut(S)` on the surviving `S`-classes. All the tests are
   `Aut(S)`-invariant, so it then runs the expensive tests (`RadicalTest` and the
   solubility test, which need `Aut(E)`) once per orbit rather than once per `S`-class.
4. It discards any orbit containing a subgroup that is not a candidate. By Theorem 3.6, such a
   subgroup cannot be essential in any saturated fusion system on `S`, and neither can its
   `Aut(S)`-conjugates.

For maximal class groups of order at least `p^5`, the original special-purpose search is kept.
Its pearls (subgroups of order `p^2` containing `Z(S)` and of order `p^3` containing `Z_2(S)`)
are now read off from the elements of order `p` in `S/Z(S)` and `S/Z_2(S)`, instead of being
taken from the full subgroup lattice.

Changed intrinsics:
* `AllProtoEssentials(S : ..., Fast:=true)` and `AllFusionSystems(S : ..., Fast:=true)` use
  `ProtoEssentialSubgroups`. `Fast:=false` restores the original search.
* In the `pPerfect` test, `[S, Aut(S)]` is now computed from generators of `S` and `Aut(S)`
  rather than by applying every generator of `Aut(S)` to every element of `S`.
* A stray debugging `print "here";` in `AllProtoEssentials` has been removed.

Nothing else was changed. In particular, the Borel subgroup stage of `AllFusionSystems` and the
saturation test still use the subgroup lattice of `B/Z(S)`. So for `|S| = 3^13` only the
proto-essential stage (`ProtoEssentialSubgroups`) is expected to be practical.

## Tests

Run from the directory containing `FusionSystems.m`:

    magma tests/TestC3wrC3wrC3.m      # the fast search on C3 wr C3 wr C3 (order 3^13)
    magma tests/TestFastVsOriginal.m  # fast = original on C3 wr C3 and all groups of order 3^4, 3^5, 5^4

**The MAGMA code has not been run.** It was written in an environment without MAGMA. The
expected values in `tests/TestC3wrC3wrC3.m` come from a line-by-line GAP port of
`ProtoEssentialSubgroups` (`validation/fast_protoessentials.g`); see
[`validation/README.md`](validation/README.md).

## Results for C3 wr C3 wr C3 (GAP port)

See [`validation/README.md`](validation/README.md) for the full output and timings.
