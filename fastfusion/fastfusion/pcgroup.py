"""
A pure-Python, from-scratch engine for computing in finite p-groups given by a
power-commutator (PC) presentation in which *every* relative order equals the
same prime p.  This is the computational foundation for the fast fusion-system
search implemented elsewhere in this package.

Presentation conventions
-------------------------
A group S of order p^n is given by generators x_1, ..., x_n (1-indexed in the
exposition below; the code uses 0-indexed generators 0..n-1, with x_{i} in the
exposition corresponding to index i-1 in the code) and:

  * power relations   x_i^p = w_i                for i = 1..n,
  * commutator relations [x_i, x_j] = c_{ij}      for 1 <= i < j <= n,

where every word w_i and c_{ij} involves *only* generators of index strictly
greater than i (resp. j).  This is precisely the statement that

    S = L_1 > L_2 > ... > L_n > L_{n+1} = 1,     L_i = <x_i, x_{i+1}, ..., x_n>

is a central series of S with elementary abelian factors of order p refining
the lower central series (L_{i+1} is normal in S and L_i/L_{i+1} is central in
S/L_{i+1}).  Note that a generator x_i can still have *actual* order larger
than p as a group element -- the power relation only says what x_i^p equals
once collected, which may be a nontrivial element of L_{i+1} (e.g. a "C_{p^2}
represented by two PCGS layers" situation).  Such a presentation is always
consistent when it arises from an explicit group construction (as all of ours
do, see constructions.py); we cross-check consistency empirically -- by
verifying the group axioms and, in testing, by independent agreement with GAP
-- rather than running a general Knuth-Bendix-style completion algorithm.

Because every relative order is the same prime p, elements of S correspond
bijectively to *exponent vectors* (e_1,...,e_n) in (Z/p)^n via the normal form

    x_1^{e_1} x_2^{e_2} ... x_n^{e_n},      0 <= e_i < p.

Two layers of representation
-----------------------------
1. ``PCPresentation``: the raw relations, together with ``collect`` -- a
   general "collection from the left" algorithm (Sims, *Computation with
   Finitely Presented Groups*, Ch. 9) that reduces an arbitrary word in the
   generators to normal form.  This works for groups of *any* nilpotency
   class and is used only to *compile* the presentation (one BFS pass).

2. ``CompiledPGroup``: the presentation compiled, once, into its regular
   permutation representation on {0, ..., p^n - 1} (indices of exponent
   vectors).  After compilation, every group operation (multiplication,
   inversion, conjugation, applying an endomorphism, subgroup closures,
   normalizers and centralizers) is implemented purely in terms of table
   look-ups and short loops over the n generators -- collection is never
   performed again.  Inverses in particular are obtained for free from
   Lagrange's theorem (x^{-1} = x^{|S|-1}, via binary exponentiation on the
   already-compiled multiplication), which sidesteps any need to reason
   about the *actual* order of a generator.  This is what makes the engine
   fast: for our examples p^n <= 5^7 = 78125 or 2^10 = 1024, every table fits
   comfortably in memory and every query below costs at most
   O(n) to O(n * p^n) elementary array operations.
"""

from __future__ import annotations

import random
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Sequence, Tuple

import numpy as np

Vector = Tuple[int, ...]       # a normal-form exponent vector, length n, entries in [0,p)
Word = List[int]               # a "dirty" word: a list of 1-indexed generator letters


# ---------------------------------------------------------------------------
# Layer 1: the presentation and collection from the left.
# ---------------------------------------------------------------------------


@dataclass
class PCPresentation:
    """A power-commutator presentation of a finite p-group, all relative orders p.

    Attributes
    ----------
    n : number of generators.
    p : the prime.
    power_words : power_words[i] (0-indexed, i = 0..n-1) is the word for x_{i+1}^p,
        a list of 1-indexed letters drawn from {i+2, ..., n} (generators strictly
        after x_{i+1}).  An empty list means x_{i+1}^p = 1.
    comm_words : comm_words[(i,j)] for 0 <= i < j <= n-1 is the word for
        [x_{i+1}, x_{j+1}] = x_{i+1}^{-1} x_{j+1}^{-1} x_{i+1} x_{j+1}, a list of
        1-indexed letters drawn from {j+2, ..., n}.  A pair absent from the dict
        means the commutator is trivial.
    names : optional human-readable generator names, for printing.
    """

    n: int
    p: int
    power_words: List[Word] = field(default_factory=list)
    comm_words: Dict[Tuple[int, int], Word] = field(default_factory=dict)
    names: Optional[List[str]] = None

    def __post_init__(self):
        if not self.power_words:
            self.power_words = [[] for _ in range(self.n)]
        assert len(self.power_words) == self.n
        for i, w in enumerate(self.power_words):
            for g in w:
                assert g > i + 1, (
                    f"power word for generator {i+1} refers to generator {g}, "
                    f"which is not strictly later"
                )
        for (i, j), w in self.comm_words.items():
            assert 0 <= i < j <= self.n - 1
            for g in w:
                assert g > j + 1, (
                    f"commutator word for [{i+1},{j+1}] refers to generator {g}, "
                    f"which is not strictly later than {j+1}"
                )
        if self.names is None:
            self.names = [f"x{i+1}" for i in range(self.n)]
        self._inv_comm_cache: Dict[Tuple[int, int], Word] = {}

    # -- collection from the left -------------------------------------------------

    def identity(self) -> Vector:
        return tuple([0] * self.n)

    def vector_to_word(self, v: Vector) -> Word:
        w: Word = []
        for idx, e in enumerate(v):
            w.extend([idx + 1] * (e % self.p))
        return w

    def vector_power(self, v: Vector, k: int) -> Vector:
        """x^k for x given by normal-form vector v, k >= 0, via binary
        exponentiation using `collect`.  Self-contained (no compiled table
        needed), so this can be used while the presentation is still being
        compiled."""
        assert k >= 0
        result = self.identity()
        base = v
        while k > 0:
            if k & 1:
                result = self.collect(self.vector_to_word(result) + self.vector_to_word(base))
            k >>= 1
            if k:
                base = self.collect(self.vector_to_word(base) + self.vector_to_word(base))
        return result

    def vector_inverse(self, v: Vector) -> Vector:
        """x^{-1} via Lagrange: x^{-1} = x^{|S|-1} (|S| = p^n)."""
        return self.vector_power(v, self.p ** self.n - 1)

    def comm_word(self, i: int, j: int) -> Word:
        """Word for [x_{i+1}, x_{j+1}] with i < j (0-indexed generators).  For
        i > j this is [x_{j+1}, x_{i+1}]^{-1}, computed via vector_inverse
        (correct regardless of the actual order of the generators involved),
        and memoised since it is requested repeatedly during collection."""
        if i < j:
            return self.comm_words.get((i, j), [])
        elif i > j:
            cached = self._inv_comm_cache.get((j, i))
            if cached is None:
                w = self.comm_words.get((j, i), [])
                v = self.collect(w)
                vi = self.vector_inverse(v)
                cached = self.vector_to_word(vi)
                self._inv_comm_cache[(j, i)] = cached
            return cached
        else:
            return []

    def collect(self, word: Sequence[int]) -> Vector:
        """Collect an arbitrary word of 1-indexed letters (each of exponent 1,
        repeats allowed, any order) into normal form.

        General "collection from the left": bubble letters into increasing
        order using the commutator relations, splicing in correction words;
        then repeatedly collapse any run of >= p copies of the same generator
        using the power relation.  Both kinds of substitution only ever
        introduce letters strictly later than the generators involved, which
        guarantees termination.
        """
        w: Word = list(word)
        p = self.p
        progress = True
        while progress:
            progress = False
            i = 0
            while i < len(w) - 1:
                a, b = w[i], w[i + 1]
                if a <= b:
                    i += 1
                    continue
                # a > b: x_a x_b = x_b x_a [x_a, x_b]
                comm = self.comm_word(a - 1, b - 1)
                w[i : i + 2] = [b, a] + comm
                progress = True
                i = max(i - 1, 0)
            # collapse p-th powers (word is now sorted; find runs >= p)
            i = 0
            while i < len(w):
                j = i
                while j < len(w) and w[j] == w[i]:
                    j += 1
                run = j - i
                if run >= p:
                    g = w[i]
                    keep = run % p
                    repl = self.power_words[g - 1] * ((run - keep) // p)
                    w[i:j] = [g] * keep + repl
                    progress = True
                    break
                i = j
        v = [0] * self.n
        for g in w:
            v[g - 1] += 1
        for idx in range(self.n):
            v[idx] %= p
        return tuple(v)


# ---------------------------------------------------------------------------
# Layer 2: compiled regular representation.
# ---------------------------------------------------------------------------


class CompiledPGroup:
    """A PCPresentation compiled into tables indexed by 0..order-1.

    ``elements[idx]`` is the normal-form vector of the element with index idx
    (index 0 is always the identity); ``index_of`` is its inverse.
    ``right[g, idx]`` is the index of elements[idx] * x_{g+1}.  All other
    operations (mul, inverse, conjugation, ...) are derived from ``right``
    alone, using binary exponentiation and Lagrange's theorem -- no further
    calls to ``pres.collect`` occur after this table is built.
    """

    def __init__(self, pres: PCPresentation):
        self.pres = pres
        self.n = pres.n
        self.p = pres.p
        self.order = pres.p ** pres.n
        self._compile()

    # -- compilation ---------------------------------------------------------

    def _compile(self):
        n, order = self.n, self.order
        pres = self.pres
        elements: List[Vector] = [pres.identity()]
        index_of: Dict[Vector, int] = {elements[0]: 0}
        right = np.full((n, order), -1, dtype=np.int64)
        parent = np.full(order, -1, dtype=np.int64)
        parent_gen = np.full(order, -1, dtype=np.int64)

        # BFS over the Cayley graph of right-multiplication by each generator,
        # using `pres.collect` only to append a single letter at a time.
        queue = [0]
        qi = 0
        while qi < len(queue):
            idx = queue[qi]
            qi += 1
            v = elements[idx]
            base_word = pres.vector_to_word(v)
            for g in range(n):
                if right[g, idx] != -1:
                    continue
                nv = pres.collect(base_word + [g + 1])
                nidx = index_of.get(nv)
                if nidx is None:
                    nidx = len(elements)
                    elements.append(nv)
                    index_of[nv] = nidx
                    parent[nidx] = idx
                    parent_gen[nidx] = g
                    queue.append(nidx)
                right[g, idx] = nidx
        assert len(elements) == order, (
            f"expected {order} elements, only reached {len(elements)}; "
            f"presentation may be inconsistent"
        )

        self.elements: List[Vector] = elements
        self.index_of: Dict[Vector, int] = index_of
        self.right: np.ndarray = right            # shape (n, order)
        self.parent: np.ndarray = parent
        self.parent_gen: np.ndarray = parent_gen
        self.identity_index = 0
        self.gen_index: List[int] = [self._gen_index(g) for g in range(n)]

        # Everything below uses only `right`, via mul/power; no more collect().
        self.inv: np.ndarray = np.array([self.power(idx, order - 1) for idx in range(order)],
                                          dtype=np.int64)

        conj = np.empty((n, order), dtype=np.int64)
        for g in range(n):
            ginv = int(self.inv[self.gen_index[g]])
            gidx = self.gen_index[g]
            for idx in range(order):
                conj[g, idx] = self.mul(self.mul(ginv, idx), gidx)
        self.conj: np.ndarray = conj

    def _gen_index(self, g: int) -> int:
        """Index of the pure generator x_{g+1} (vector e_g = 1, else 0)."""
        v = [0] * self.n
        v[g] = 1
        return self.index_of[tuple(v)]

    # -- basic operations, derived purely from `right` ------------------------

    def mul(self, i: int, j: int) -> int:
        """Index of elements[i] * elements[j], by decomposing elements[j]
        into its generator letters (increasing index, as in its own normal
        form) and right-multiplying step by step starting from i."""
        v = self.elements[j]
        cur = i
        right = self.right
        for g in range(self.n):
            e = v[g]
            if e:
                col = right[g]
                for _ in range(e):
                    cur = int(col[cur])
        return cur

    def power(self, i: int, e: int) -> int:
        if e < 0:
            e += self.order  # relies on inv already available; not used before inv is built
        r = self.identity_index
        base = i
        while e > 0:
            if e & 1:
                r = self.mul(r, base)
            e >>= 1
            if e:
                base = self.mul(base, base)
        return r

    def inverse(self, i: int) -> int:
        return int(self.inv[i])

    def conjugate(self, i: int, g: int) -> int:
        """Index of elements[g]^{-1} * elements[i] * elements[g]."""
        return self.mul(self.mul(self.inverse(g), i), g)

    def commutator(self, i: int, j: int) -> int:
        """Index of [elements[i], elements[j]] = i^{-1} j^{-1} i j."""
        a = self.mul(self.inverse(i), self.inverse(j))
        a = self.mul(a, i)
        a = self.mul(a, j)
        return a

    def order_of(self, i: int) -> int:
        if i == self.identity_index:
            return 1
        cur = i
        k = 1
        while cur != self.identity_index:
            cur = self.mul(cur, i)
            k += 1
        return k

    def letters_of(self, i: int) -> Word:
        return self.pres.vector_to_word(self.elements[i])

    def apply_hom(self, images: Sequence[int], i: int) -> int:
        """Given images[g] = phi(x_{g+1}) for a homomorphism phi (assumed
        well-defined), compute phi(elements[i])."""
        v = self.elements[i]
        cur = self.identity_index
        for g in range(self.n):
            e = v[g]
            if e:
                cur = self.mul(cur, self.power(images[g], e))
        return cur

    def _apply_hom_to_word(self, images: Sequence[int], word: Word) -> int:
        cur = self.identity_index
        for letter in word:
            cur = self.mul(cur, images[letter - 1])
        return cur

    def verify_endomorphism(self, images: Sequence[int]) -> bool:
        """Check that the map x_{g+1} -> elements[images[g]] respects every
        defining relation, i.e. extends to a well-defined endomorphism of S.
        Respecting the defining relations of a presentation is necessary and
        sufficient for a map on generators to extend to a homomorphism from
        the group they present."""
        n, p = self.n, self.p
        for g in range(n):
            lhs = self.power(images[g], p)
            rhs = self._apply_hom_to_word(images, self.pres.power_words[g])
            if lhs != rhs:
                return False
        for (i, j), word in self.pres.comm_words.items():
            lhs = self.commutator(images[i], images[j])
            rhs = self._apply_hom_to_word(images, word)
            if lhs != rhs:
                return False
        return True

    def is_automorphism(self, images: Sequence[int]) -> bool:
        if not self.verify_endomorphism(images):
            return False
        # A homomorphism of a finite group to itself is bijective iff
        # surjective iff the images generate the whole group.
        return len(self.closure(list(images))) == self.order

    # -- subgroup machinery ------------------------------------------------

    def small_generating_set(self, elements: Sequence[int], already_closed: bool = True) -> List[int]:
        """A small generating set for the subgroup <elements>.  By default
        `elements` is assumed to *already be a closed subgroup* (true for
        every caller in this project, since it is always the output of
        `centralizer`/`normalizer`/`closure` itself) so the target is just
        set(elements) -- no closure() call needed to establish it, which
        matters because calling closure() with the *entire* (possibly
        large) `elements` list as the generating set would itself cost
        O(|elements|^2); pass already_closed=False to fall back to
        computing it the slow way for an arbitrary (not necessarily closed)
        input.  Tries random subsets of increasing size first (fast: for a
        rank-r subgroup, a handful of random elements generate it with high
        probability once the subset size reaches about r), falling back to
        a greedy walk only if that fails."""
        elements = list(elements)
        if not elements:
            return []
        target = set(elements) if already_closed else set(self.closure(elements))
        if len(target) == 1:
            return []
        rng = random.Random(0)
        for size in range(1, min(len(elements), 16) + 1):
            for _ in range(3):
                subset = rng.sample(elements, size)
                if set(self.closure(subset)) == target:
                    return subset
        chosen: List[int] = []
        have = {self.identity_index}
        for e in elements:
            if e in have:
                continue
            chosen.append(e)
            have = set(self.closure(chosen))
            if have == target:
                break
        return chosen

    def closure(self, gens: Sequence[int]) -> List[int]:
        """The subgroup generated by the given element indices, as a sorted
        list of indices.  Standard closure-by-flooding: repeatedly multiply
        every known element by every generator (left and right) until no new
        elements appear.  Correct for any finite group; fast here because
        `mul` is table-driven."""
        seen = {self.identity_index}
        queue = [self.identity_index]
        gens = list(gens)
        qi = 0
        while qi < len(queue):
            e = queue[qi]
            qi += 1
            for g in gens:
                for ee in (self.mul(e, g), self.mul(g, e)):
                    if ee not in seen:
                        seen.add(ee)
                        queue.append(ee)
        return sorted(seen)

    def normal_closure(self, gens: Sequence[int], by: Optional[Sequence[int]] = None) -> List[int]:
        """Normal closure of <gens> under conjugation by the generators `by`
        (default: all n PCGS generators of the whole group)."""
        by = list(self.gen_index) if by is None else list(by)
        seen = set(self.closure(gens))
        changed = True
        while changed:
            changed = False
            new_elems = set()
            for e in list(seen):
                for g in by:
                    c = self.conjugate(e, g)
                    if c not in seen and c not in new_elems:
                        new_elems.add(c)
            if new_elems:
                seen = set(self.closure(sorted(seen | new_elems)))
                changed = True
        return sorted(seen)

    # -- fast (table-driven) normalizer / centralizer ------------------------

    def _conjugation_vector(self, h: int) -> np.ndarray:
        """orbit[idx] = index of elements[h] conjugated by elements[idx], for
        every idx in 0..order-1, computed in O(order) via the BFS tree used to
        build `right` (parent/parent_gen): conjugation by a product y*x_g
        equals (conjugation by y) then (conjugation by x_g)."""
        order = self.order
        out = np.empty(order, dtype=np.int64)
        out[0] = h
        parent = self.parent
        parent_gen = self.parent_gen
        conj = self.conj
        for idx in range(1, order):
            out[idx] = conj[int(parent_gen[idx]), out[int(parent[idx])]]
        return out

    def centralizer(self, gens: Sequence[int], universe: Optional[Sequence[int]] = None) -> List[int]:
        """C_S(<gens>) if universe is None, else C_U(<gens>) for the given
        universe U (a list of indices) -- i.e. the elements of U commuting with
        every element of gens.  It suffices to centralize a generating set."""
        order = self.order
        mask = np.ones(order, dtype=bool)
        for h in gens:
            cv = self._conjugation_vector(h)
            mask &= (cv == h)
        if universe is None:
            return list(np.nonzero(mask)[0])
        uni = np.asarray(universe, dtype=np.int64)
        return list(uni[mask[uni]])

    def normalizer(self, subgroup_gens: Sequence[int], subgroup_set: Optional[set] = None,
                   universe: Optional[Sequence[int]] = None) -> List[int]:
        """N_S(H) where H = <subgroup_gens>, if universe is None, else N_U(H)
        for a given universe U.  `subgroup_set` may be supplied as a
        precomputed Python set of H's elements to avoid recomputing it."""
        if subgroup_set is None:
            subgroup_set = set(self.closure(subgroup_gens))
        order = self.order
        in_H_full = np.zeros(order, dtype=bool)
        in_H_full[list(subgroup_set)] = True
        mask = np.ones(order, dtype=bool)
        for h in subgroup_gens:
            cv = self._conjugation_vector(h)
            mask &= in_H_full[cv]
        if universe is None:
            return list(np.nonzero(mask)[0])
        uni = np.asarray(universe, dtype=np.int64)
        return list(uni[mask[uni]])

    def center(self) -> List[int]:
        return self.centralizer(self.gen_index)

    def derived_subgroup(self) -> List[int]:
        gens = [self.commutator(i, j) for i in self.gen_index for j in self.gen_index if i != j]
        return self.closure(gens)

    # -- conjugacy classes of elements (within a universe) -----------

    def conjugacy_classes(self, universe: Optional[Sequence[int]] = None,
                           by: Optional[Sequence[int]] = None) -> List[List[int]]:
        """Partition `universe` (default: the whole group) into conjugacy
        classes under conjugation by `by` (default: the n PCGS generators,
        giving ordinary S-conjugacy)."""
        universe = list(range(self.order)) if universe is None else list(universe)
        by = list(self.gen_index) if by is None else list(by)
        uni_set = set(universe)
        seen = set()
        classes: List[List[int]] = []
        for start in universe:
            if start in seen:
                continue
            comp = [start]
            seen.add(start)
            qi = 0
            while qi < len(comp):
                e = comp[qi]
                qi += 1
                for g in by:
                    c = self.conjugate(e, g)
                    if c in uni_set and c not in seen:
                        seen.add(c)
                        comp.append(c)
            classes.append(comp)
        return classes

    # -- pretty printing -------------------------------------------------------

    def format(self, i: int) -> str:
        v = self.elements[i]
        names = self.pres.names
        parts = [f"{names[k]}^{e}" for k, e in enumerate(v) if e]
        return "*".join(parts) if parts else "1"
