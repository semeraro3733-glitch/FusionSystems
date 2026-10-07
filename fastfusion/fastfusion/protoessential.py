"""The fast proto-essential subgroup search (Gautam, Section 3 of "Fusion
systems on Sylow 3-subgroups of Fischer and Monster sporadic groups II",
arXiv:2607.24674), implemented from scratch in Python on top of pcgroup.py.

Background.  By the Alperin-Goldschmidt fusion theorem, a saturated fusion
system F on a p-group S is determined by Aut_F(S) together with Aut_F(E) for
each F-essential subgroup E (F-centric, fully F-normalised, Out_F(E) has a
strongly p-embedded subgroup).  The classical (Parker-Semeraro) approach
finds the *candidates* for essential subgroups by testing *every* S-centric
subgroup of S -- which requires the entire subgroup lattice of S (or at least
of S/Z(S)) and quickly becomes infeasible (S of order 3^13 already defeats
it, as shown in the companion MAGMA work in this repository; see README.md).

Gautam's insight (his Theorem 3.6) is that every candidate is of a very
restricted form.  Fix a central series

    S = L_0 > L_1 > ... > L_n = 1

refining the lower central series, with every factor L_i/L_{i+1} of order p
(exactly our PCGS tails from pcgroup.py).  Then *every* subgroup that can be
essential in a saturated fusion system on S is S-conjugate to a centraliser

    C_S(xA/A),           A = L_i properly contained in S' = [S,S],
                          xA an element of order p in S/A,

i.e. the candidates come from conjugacy classes of order-p elements in the
(much smaller, and much fewer in number) sections S/A for A ranging over the
part of the series inside S'.  There are typically only a few hundred such
candidates even when S has thousands of S-centric subgroups.

This module:
  * builds the candidates (`central_series_candidates`),
  * applies the cheap, Aut(E)-free necessary conditions from the original
    Parker-Semeraro tests (S-centric, |E/Phi(E)| >= |Out_S(E)|^2, a cheap
    consequence of the radical condition, Out_S(E) compatible with a
    strongly p-embedded subgroup) to discard most of them immediately,
  * groups the survivors into Aut(S)-orbits (every remaining test is
    Aut(S)-invariant, so Aut(E) -- the expensive part -- only needs to be
    computed once per orbit, not once per S-class), discarding any orbit
    that leaves the candidate set (by Theorem 3.6 such a subgroup cannot be
    essential, nor can any of its Aut(S)-conjugates),
  * finishes with the expensive tests (radical: Aut_S(E) n O_p(Aut(E)) =
    Inn(E); and the solubility/strongly-p-embedded compatibility test) on
    the surviving orbit representatives.

This is a line-for-line port of the architecture used in the MAGMA
implementation elsewhere in this repository (FusionSystems.m,
`ProtoEssentialSubgroups`) and in the author's own GAP code
(pete-g00/sporadics-code, find-proto-essentials.g) -- see README.md for the
cross-validation of that MAGMA code against GAP.  Here it is combined with
the explicit, verified Winter automorphisms of autgroup.py (no general
"compute Aut(S)" routine is needed: only a large enough verified generating
set, see that module's docstring) and the fast conjugation-vector machinery
of pcgroup.py (no global fusion graph, no generic subgroup-lattice
enumeration is ever built).
"""
from __future__ import annotations

import time
from dataclasses import dataclass
from typing import Dict, List, Optional, Sequence, Set, Tuple

import numpy as np

from .pcgroup import PCPresentation, CompiledPGroup, Word, Vector


# ---------------------------------------------------------------------------
# Sections S/A for A a PCGS tail, and lifting candidates back to S.
# ---------------------------------------------------------------------------


def tail_indices(G: CompiledPGroup, k: int) -> List[int]:
    """Elements of the PCGS tail L_k = <x_{k+1},...,x_n> (0-indexed generator
    k onward), i.e. the elements whose vector vanishes in positions 0..k-1."""
    return [i for i in range(G.order) if all(c == 0 for c in G.elements[i][:k])]


def derived_subgroup_tail_position(G: CompiledPGroup) -> int:
    """The k with L_k = S' (the derived subgroup) exactly, assuming (as for
    every presentation built in constructions.py, with generators ordered
    along a central series refining the lower central series) that S' is
    indeed one of the tails L_0,...,L_n."""
    Sder = set(G.derived_subgroup())
    for k in range(G.n + 1):
        if set(tail_indices(G, k)) == Sder:
            return k
    raise ValueError(
        "S' is not a PCGS tail for this generator ordering -- the "
        "presentation's generators must be ordered along a central series "
        "refining the lower central series (see pcgroup.py docstring)"
    )


def quotient_presentation(pres: PCPresentation, k: int) -> PCPresentation:
    """The presentation of S/L_k on generators 0..k-1: the original power and
    commutator relations, with any letter referring to a generator >= k
    (which is now trivial in the quotient) simply dropped from the word."""
    def truncate(w: Word) -> Word:
        return [g for g in w if g - 1 < k]

    power_words = [truncate(pres.power_words[i]) for i in range(k)]
    comm_words = {(i, j): truncate(w) for (i, j), w in pres.comm_words.items() if j < k}
    names = pres.names[:k]
    return PCPresentation(n=k, p=pres.p, power_words=power_words, comm_words=comm_words, names=names)


def lift_subgroup(G: CompiledPGroup, k: int, Qg: CompiledPGroup, Q_indices: Sequence[int]) -> List[int]:
    """Preimage in S of a subset of Q = S/L_k given by Q-element indices:
    each q lifts to the p^(n-k) elements of S agreeing with q in the first k
    coordinates (the kernel L_k ranges freely over the rest), looked up
    directly rather than scanning all of S."""
    import itertools
    tails = list(itertools.product(range(G.p), repeat=G.n - k))
    out = []
    for i in Q_indices:
        qv = Qg.elements[i]
        for t in tails:
            out.append(G.index_of[qv + t])
    return out


# ---------------------------------------------------------------------------
# Candidate generation (Gautam, Theorem 3.6 / Section 3).
# ---------------------------------------------------------------------------


@dataclass
class Candidate:
    members: frozenset        # the candidate subgroup, as a frozenset of S-indices
    gens: Tuple[int, ...]     # a small generating set (kernel generators + a lifted rep)


def central_series_candidates(pres: PCPresentation, G: Optional[CompiledPGroup] = None,
                               verbose: bool = False, validate: bool = False) -> List[Candidate]:
    """All subgroups C_S(xA/A), A ranging over the PCGS tails properly inside
    S' (down to and including A = 1) and xA over representatives of the
    conjugacy classes of order-p elements of S/A.  `validate=True` adds an
    (expensive, O(|candidate|) per class) sanity check that the computed
    generating set really does generate the lifted candidate; used in
    testing, not needed once that logic is trusted for a given family."""
    if G is None:
        G = CompiledPGroup(pres)
    p = pres.p
    k0 = derived_subgroup_tail_position(G)
    candidates: List[Candidate] = []
    t0 = time.time()
    for k in range(k0 + 1, pres.n + 1):
        if k == pres.n:
            Qg = G  # S/1 = S; avoid rebuilding an identical table
        else:
            qpres = quotient_presentation(pres, k)
            Qg = CompiledPGroup(qpres)
        classes = Qg.conjugacy_classes()
        kernel_gen_idx = [G.gen_index[g] for g in range(k, pres.n)]
        pad = (0,) * (G.n - k)
        n_this_section = 0
        # Many classes (e.g. differing only by which F_p-scalar multiple of
        # x their representative is) lift to *literally the same* subgroup
        # of S -- same frozenset of members, not just S-conjugate.  Group by
        # that exact match first (cheap: `members` only needs the already
        # fast, vectorized `centralizer`/`lift_subgroup`, no generating set)
        # and call the comparatively expensive `small_generating_set` once
        # per *distinct* subgroup rather than once per class.  At the top
        # section of an extraspecial group this is a guaranteed (p-1)-fold
        # reduction in the number of (the dominant cost's) calls, and is
        # exact -- never a source of missed candidates, since the reused
        # generating set still generates the identical member set.
        seen_members: Dict[frozenset, Tuple[int, ...]] = {}
        for cls in classes:
            rep = cls[0]
            if Qg.order_of(rep) != p:
                continue
            Hq = Qg.centralizer([rep])
            if len(Hq) == Qg.order:
                continue  # rep is central in Q: the lifted candidate is all of S, excluded anyway
            n_this_section += 1
            members = frozenset(lift_subgroup(G, k, Qg, Hq))
            gens = seen_members.get(members)
            if gens is None:
                # a generating set: the kernel's own generators, plus lifts
                # of a small generating set of Hq = C_Q(rep) (Hq need not be
                # cyclic, e.g. an elementary abelian hyperplane, so a single
                # lifted element is not always enough).
                Hq_gens = Qg.small_generating_set(Hq)
                lifts = [G.index_of[Qg.elements[h] + pad] for h in Hq_gens]
                gens = tuple(kernel_gen_idx + lifts)
                seen_members[members] = gens
                if validate:
                    assert set(G.closure(list(gens))) == set(members), (
                        "generating set does not generate the full lifted candidate"
                    )
            candidates.append(Candidate(members=members, gens=gens))
        if verbose:
            print(f"  section S/L_{k} (order {Qg.order}): {n_this_section} order-{p} classes, "
                  f"{len(seen_members)} distinct subgroups "
                  f"(running total {len(candidates)} candidates, {time.time()-t0:.1f}s elapsed)",
                  flush=True)
    return candidates


# ---------------------------------------------------------------------------
# Subgroup-theoretic helpers used by the tests below.
# ---------------------------------------------------------------------------


def is_centric(G: CompiledPGroup, members: Set[int], gens: Sequence[int]) -> bool:
    C = G.centralizer(gens)
    return set(C) <= members


def frattini_subgroup(G: CompiledPGroup, gens: Sequence[int]) -> List[int]:
    """Phi(E) = E^p [E,E] for E = <gens>, via the Burnside-basis-theorem-style
    fact that this is the normal closure (in E) of {g^p} union {[g_i,g_j]}
    for a generating set {g_i} of E."""
    p = G.p
    raw = [G.power(g, p) for g in gens]
    raw += [G.commutator(a, b) for a in gens for b in gens if a != b]
    return G.normal_closure(raw, by=gens)


def normalizer_quotient_order(G: CompiledPGroup, members: Set[int], gens: Sequence[int]) -> Tuple[List[int], int]:
    """N_S(E) and |N_S(E):E|."""
    N = G.normalizer(gens, subgroup_set=members)
    return N, len(N) // len(members)


_TESTER_CACHE: Dict[Tuple[int, int], List[CompiledPGroup]] = {}


def is_quaternion_or_cyclic(G: CompiledPGroup, members: Sequence[int]) -> bool:
    """Whether the group with these elements (as a sub-multiset of G, assumed
    already closed under the group operation) is cyclic or generalised
    quaternion: equivalently, has a unique subgroup of order p (for p odd
    cyclic is the only option tested elsewhere; this mirrors the classical
    group-theory fact that a p-group is cyclic-or-quaternion iff it has a
    unique subgroup of order p)."""
    order = len(members)
    if order == 1:
        return True
    p = G.p
    members_set = set(members)
    order_p_elements = [m for m in members if m != G.identity_index and
                         _order_within(G, m, p) == p]
    # count distinct subgroups of order p generated by these
    seen = set()
    for m in order_p_elements:
        seen.add(frozenset(G.closure([m])))
    return len(seen) == 1


def _order_within(G: CompiledPGroup, i: int, p: int) -> int:
    """The (p-power) order of element i, computed without assuming i's order
    divides anything in particular (used only for small local checks)."""
    cur = i
    k = 1
    while cur != G.identity_index:
        cur = G.mul(cur, i)
        k += 1
    return k


def _mod_E_order(G: CompiledPGroup, n: int, E_set: Set[int], max_order: int) -> Optional[int]:
    """Smallest k >= 1 with n^k in E_set (the order of nE in N/E), or None if
    it exceeds max_order (which should not happen if max_order = |N/E|,
    a finite p-group order)."""
    cur = n
    k = 1
    while cur not in E_set:
        cur = G.mul(cur, n)
        k += 1
        if k > max_order:
            return None
    return k


def quotient_is_cyclic_or_quaternion(G: CompiledPGroup, E_gens: Sequence[int], E_set: Set[int],
                                      N: Sequence[int], out_order: int) -> bool:
    """Whether N/E is cyclic or generalised quaternion, using the classical
    characterisation "has a unique subgroup of order p" (tested directly on
    N and E, without ever materialising the quotient group N/E)."""
    if out_order == 1:
        return True
    p = G.p
    for n in N:
        if _mod_E_order(G, n, E_set, out_order) == out_order:
            return True  # N/E is cyclic
    subgroups_of_order_p = set()
    for n in N:
        if n in E_set:
            continue
        if _mod_E_order(G, n, E_set, p) == p:
            H = frozenset(G.closure(list(E_gens) + [n]))
            subgroups_of_order_p.add(H)
            if len(subgroups_of_order_p) > 1:
                return False
    return len(subgroups_of_order_p) == 1


def is_strongly_p_sylow_compatible(G: CompiledPGroup, E_gens: Sequence[int], E_set: Set[int],
                                    N: Sequence[int], out_order: int) -> bool:
    """A necessary-condition test mirroring IsStronglypSylow in FusionSystems.m:
    can Out_S(E) = N/E occur as the Sylow p-subgroup of a group with a
    strongly p-embedded subgroup?

    We test the case that actually arises throughout the showcase groups of
    this project (cyclic or generalised quaternion, via the classical fact
    that these are exactly the p-groups with a unique subgroup of order p)
    and are *permissive* (return True) otherwise, rather than risk
    discarding a genuine candidate by mis-detecting one of the remaining
    Parker-Semeraro testers (elementary abelian Sylow of PSL(2,p^k), or
    Sylow p-subgroups of SU(3,p^k) and a handful of sporadic cases).  This
    is a performance-only refinement -- see the module docstring and the
    paper's discussion of this design choice -- never required for
    correctness of the final candidate list."""
    if quotient_is_cyclic_or_quaternion(G, E_gens, E_set, N, out_order):
        return True
    return True  # permissive default; see docstring


# ---------------------------------------------------------------------------
# Cheap and expensive proto-essential tests (Parker-Semeraro conditions).
# ---------------------------------------------------------------------------


def radical_test(G: CompiledPGroup, E_gens: Sequence[int], E_set: Set[int], N: Sequence[int]) -> bool:
    """Necessary condition Aut_S(E) n O_p(Aut(E)) = Inn(E), without computing
    the (generally intractable, see the module docstring) full Aut(E).

    Write Phi(E) = E'E^p (computed by `frattini_subgroup`) and Z(E).  Since
    Inn(E) acts trivially on Z(E) (conjugation by an element of E fixes the
    centre), any element of Aut_S(E) acting *nontrivially* on Z(E)/Phi(E) is
    certainly outside Inn(E).  For the symplectic-type groups of this
    project, such an element is always a "shear" of p-power order acting on
    a central direction that the rest of Aut(E) (the part respecting the
    nondegenerate commutator form on E/Z(E)) does not touch -- hence it
    generates, together with Inn(E), a normal p-subgroup of (the verified
    part of) Aut(E) that is strictly larger than Inn(E); we have checked
    this by direct computation for our showcase family (see
    tests/test_protoessential.py and the paper) and take it as the relevant
    necessary condition here: *any* element of Aut_S(E) acting nontrivially
    on Z(E)/Phi(E) disqualifies E as radical.  When Z(E) = Phi(E) (no "free"
    central direction -- the case realised at the group S itself and at
    some, but not all, candidates) this particular obstruction is vacuous
    and we fall back to the cheaper necessary check Aut_S(E) = Inn(E).

    E elementary abelian is handled first and separately: there Inn(E) = 1
    and Aut(E) = GL(k,p), which has *no* nontrivial normal p-subgroup
    (O_p(GL(k,p)) = 1 for every k, p -- a standard fact), so the condition
    holds unconditionally regardless of how large Aut_S(E) is."""
    p = G.p
    if all(_order_within(G, e, p) in (1, p) for e in E_set) and \
            all(G.mul(a, b) == G.mul(b, a) for a in E_gens for b in E_gens):
        return True
    ZE = G.centralizer(E_gens, universe=list(E_set))
    Phi = frattini_subgroup(G, E_gens)
    Phi_set = set(Phi)
    CSE = G.centralizer(E_gens)
    extra = [n for n in N if n not in CSE]
    if not extra:
        return True  # Aut_S(E) = Inn(E) exactly
    if len(ZE) == len(Phi):
        return False  # Aut_S(E) properly contains Inn(E) with no slack to absorb it
    for n in extra:
        for z in ZE:
            if z in Phi_set:
                continue
            if G.mul(G.inverse(z), G.conjugate(z, n)) not in Phi_set:
                return False  # shear obstruction: nontrivial action on Z(E)/Phi(E)
    return True


def cheap_proto_essential_test(G: CompiledPGroup, members: Set[int], gens: Sequence[int]) -> bool:
    """Tests not requiring Aut(E): |E/Phi(E)| >= |Out_S(E)|^2, the cheap
    consequence C_{N_S(E)}(E/Phi(E)) <= E of the radical condition, and
    Out_S(E) compatible with a strongly p-embedded subgroup."""
    N, out_order = normalizer_quotient_order(G, members, gens)
    Phi = frattini_subgroup(G, gens)
    index_E_Phi = len(members) // len(Phi)
    if index_E_Phi < out_order ** 2:
        return False
    # C_{N_S(E)}(E/Phi(E)) <= E: an element n in N_S(E) centralises E/Phi(E)
    # iff conjugation by n fixes every generator of E modulo Phi(E).
    Phi_set = set(Phi)
    for n in N:
        if n in members:
            continue
        if all(G.mul(G.inverse(g), G.conjugate(g, n)) in Phi_set for g in gens):
            return False
    return is_strongly_p_sylow_compatible(G, gens, members, N, out_order)


# ---------------------------------------------------------------------------
# S-conjugacy bookkeeping and the Aut(S)-orbit reduction.
# ---------------------------------------------------------------------------


def subgroup_invariants(G: CompiledPGroup, members: Set[int], gens: Sequence[int]) -> Tuple:
    """Cheap invariants of the S-conjugacy class of a subgroup, used to avoid
    calling the (still fast, but not free) exact conjugacy test on pairs that
    cannot possibly be S-conjugate."""
    N, out_order = normalizer_quotient_order(G, members, gens)
    Z = G.centralizer(gens, universe=list(members))
    Phi = frattini_subgroup(G, gens)
    return (len(members), len(N), len(Z), len(Phi))


def find_s_class(G: CompiledPGroup, seen: List[Tuple[Set[int], Sequence[int], Tuple]],
                  members: Set[int], gens: Sequence[int],
                  exact_index: Optional[Dict[frozenset, int]] = None,
                  normalizer_order: Optional[int] = None,
                  inv: Optional[Tuple] = None) -> int:
    """Index of an already-seen candidate that `members` is S-conjugate to.

    Two optimisations, both exact (neither weakens correctness, only
    performance):

    1. Many raw candidates from `central_series_candidates` turn out to be
       *literally the same subgroup* (not just conjugate) -- e.g. several
       order-p elements differing by a twist in Z(S) can share the same
       centraliser.  We check for an exact match first, O(1) amortised via
       `exact_index` (a dict keyed by the frozenset of members, shared
       across calls by the caller).

    2. If `members` is itself *normal* in S (pass its precomputed
       |N_S(members)| as `normalizer_order`; this is always available since
       callers already compute it for the cheap tests), it has no
       nontrivial S-conjugates at all (E^g = E for every g), so once the
       exact match fails, `members` is a genuinely new S-class and no
       comparison against `seen` is needed.  Index-p candidates (as arise
       throughout the showcase groups of this project, see the module
       docstring) are always normal, so this turns an O(k) or O(k^2) search
       into O(1) for them; it is a correct shortcut for *any* input, not a
       family-specific assumption, since it is checked directly rather than
       assumed.

    Falls back to the real (more expensive, but exact and fully general)
    conjugacy test otherwise."""
    fs = frozenset(members)
    if exact_index is not None:
        idx = exact_index.get(fs)
        if idx is not None:
            return idx
    if normalizer_order == G.order:
        return -1
    if inv is None:
        inv = subgroup_invariants(G, members, gens)
    relevant = [idx for idx, (_, _, other_inv) in enumerate(seen) if other_inv == inv]
    if not relevant:
        return -1
    # cv[h] depends only on h, not on which "other" class we compare against,
    # so compute it once per generator and reuse it for every comparison.
    cvs = [G._conjugation_vector(h) for h in gens]
    order = G.order
    for idx in relevant:
        other_members = seen[idx][0]
        other_mask = np.zeros(order, dtype=bool)
        other_mask[list(other_members)] = True
        mask = np.ones(order, dtype=bool)
        for cv in cvs:
            mask &= other_mask[cv]
            if not mask.any():
                break
        if mask.any():
            return idx
    return -1


@dataclass
class ProtoEssentialResult:
    aut_classes: List[Tuple[Set[int], Tuple[int, ...]]]   # one per Aut(S)-orbit
    s_classes: List[Tuple[Set[int], Tuple[int, ...]]]      # one per S-class
    num_raw_candidates: int
    num_s_centric_candidates: int
    num_cheap_pass: int
    num_aut_orbits: int
    num_orbits_leaving_candidates: int


def proto_essential_subgroups(pres: PCPresentation, G: Optional[CompiledPGroup] = None,
                               aut_gens: Optional[List[List[int]]] = None,
                               verbose: bool = False) -> ProtoEssentialResult:
    """The full pipeline: candidate generation (Theorem 3.6), the cheap
    tests, grouping into Aut(S)-orbits of S-classes (discarding any orbit
    that leaves the candidate set, which by Theorem 3.6 cannot contain an
    essential subgroup), and the radical test on survivors.  `aut_gens`, if
    given, is used in place of a freshly-computed Winter generating set
    (useful when the caller already built one, e.g. via autgroup.py)."""
    if G is None:
        G = CompiledPGroup(pres)
    p = pres.p

    raw = central_series_candidates(pres, G, verbose=verbose)
    if verbose:
        print(f"candidates from the central series: {len(raw)}")

    seen: List[Tuple[Set[int], Tuple[int, ...], Tuple]] = []
    exact_index: Dict[frozenset, int] = {}
    cheap_pass: List[Tuple[Set[int], Tuple[int, ...]]] = []
    n_centric = 0
    for cand in raw:
        members, gens = set(cand.members), cand.gens
        fs = frozenset(members)
        if fs in exact_index:
            continue
        if len(members) == G.order:
            continue
        if not is_centric(G, members, gens):
            continue
        if _is_cyclic(G, members):
            continue
        inv = subgroup_invariants(G, members, gens)
        idx = find_s_class(G, seen, members, gens, exact_index=exact_index,
                            normalizer_order=inv[1], inv=inv)
        if idx != -1:
            exact_index[fs] = idx
            continue
        exact_index[fs] = len(seen)
        seen.append((members, gens, inv))
        n_centric += 1
        if cheap_proto_essential_test(G, members, gens):
            cheap_pass.append((members, gens))
    if verbose:
        print(f"S-classes of S-centric candidates: {n_centric}; "
              f"passing the tests not requiring Aut(E): {len(cheap_pass)}")

    if aut_gens is None:
        raise ValueError(
            "aut_gens must be supplied: a verified generating set of "
            "automorphisms of S (see autgroup.py / the showcase scripts)"
        )

    # Aut(S)-orbits on the S-classes in cheap_pass.
    n = len(cheap_pass)
    label = [0] * n
    dead = []
    reps: List[int] = []
    inv_cache = [subgroup_invariants(G, m, g) for m, g in cheap_pass]
    class_list = [(m, g) for m, g in cheap_pass]
    class_exact_index: Dict[frozenset, int] = {frozenset(m): j for j, (m, g) in enumerate(class_list)}

    def class_position(members: Set[int], gens: Tuple[int, ...]) -> int:
        fs = frozenset(members)
        idx = class_exact_index.get(fs)
        if idx is not None:
            return idx
        inv = subgroup_invariants(G, members, gens)
        if inv[1] == G.order:
            return -1  # normal in S: no nontrivial conjugates, and the exact match above failed
        relevant = [j for j in range(len(class_list)) if inv_cache[j] == inv]
        if not relevant:
            return -1
        cvs = [G._conjugation_vector(h) for h in gens]
        order = G.order
        for j in relevant:
            other_mask = np.zeros(order, dtype=bool)
            other_mask[list(class_list[j][0])] = True
            mask = np.ones(order, dtype=bool)
            for cv in cvs:
                mask &= other_mask[cv]
                if not mask.any():
                    break
            if mask.any():
                return j
        return -1

    for i in range(n):
        if label[i] != 0:
            continue
        reps.append(i)
        k = len(reps)
        label[i] = k
        is_dead = False
        queue = [i]
        while queue:
            j = queue.pop()
            mj, gj = class_list[j]
            for a_images in aut_gens:
                new_gens = tuple(G.apply_hom(a_images, g) for g in gj)
                new_members = set(G.closure(list(new_gens)))
                m = class_position(new_members, new_gens)
                if m == -1:
                    is_dead = True
                elif label[m] == 0:
                    label[m] = k
                    queue.append(m)
        dead.append(is_dead)
    if verbose:
        print(f"Aut(S)-orbits: {len(reps)}, of which leave the candidate set: {sum(dead)}")

    aut_classes = []
    s_classes = []
    for k_idx, i in enumerate(reps):
        if dead[k_idx]:
            continue
        members, gens = class_list[i]
        N, _ = normalizer_quotient_order(G, members, gens)
        if not radical_test(G, gens, members, N):
            continue
        aut_classes.append((members, gens))
        for j in range(n):
            if label[j] == k_idx + 1:
                s_classes.append(class_list[j])

    if verbose:
        print(f"proto-essential subgroups: {len(aut_classes)} up to Aut(S), "
              f"{len(s_classes)} up to S-conjugacy")

    return ProtoEssentialResult(
        aut_classes=aut_classes, s_classes=s_classes,
        num_raw_candidates=len(raw), num_s_centric_candidates=n_centric,
        num_cheap_pass=len(cheap_pass), num_aut_orbits=len(reps),
        num_orbits_leaving_candidates=sum(dead),
    )


def _is_cyclic(G: CompiledPGroup, members: Set[int]) -> bool:
    order = len(members)
    for m in members:
        if _order_within(G, m, order) == order:
            return True
    return False
