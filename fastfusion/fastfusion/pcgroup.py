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

    def __init__(self, pres: PCPresentation, _slow: bool = False):
        self.pres = pres
        self.n = pres.n
        self.p = pres.p
        self.order = pres.p ** pres.n
        if _slow:
            self._compile_slow()
        else:
            self._compile_fast()

    # -- compilation ---------------------------------------------------------

    def _compile_slow(self):
        """Reference implementation: BFS over the Cayley graph of
        right-multiplication by each generator, using `pres.collect` to
        append one letter at a time.  Correct for a presentation of any
        nilpotency class, but collect()'s per-call overhead makes this
        O(order * n) *Python-level* collection calls -- around 20s already
        at order 5^7 for a single group, i.e. days across the tens of
        thousands of groups of that order the showcase needs. Kept only
        as the cross-validation oracle for `_compile_fast` (see
        tests/test_pcgroup.py) and as a documented fallback."""
        n, order = self.n, self.order
        pres = self.pres
        elements: List[Vector] = [pres.identity()]
        index_of: Dict[Vector, int] = {elements[0]: 0}
        right = np.full((n, order), -1, dtype=np.int64)
        parent = np.full(order, -1, dtype=np.int64)
        parent_gen = np.full(order, -1, dtype=np.int64)

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
        self._finish_compile(parent, parent_gen)

    def _compile_fast(self):
        """Build the regular representation bottom-up, one generator at a
        time, instead of by Cayley-graph BFS with general word collection.

        L_n = <x_n> is trivial to compile directly (order p, no relations
        among its own generators).  Given T := L_{K+1} = <x_{K+2},...,x_n>
        already compiled, L_K = <x_{K+1},...,x_n> is its extension by one
        generator x_{K+1}, with x_{K+1}^p = w and conjugation
        alpha(t) := x_{K+1}^{-1} t x_{K+1} both landing inside T (by the
        presentation's "only strictly later generators" invariant) -- so
        both are already known *elements of the already-compiled T*,
        computed once via `power_words`/`comm_words` fed through a single
        base-case collection, not one per group element.

        Elements of L_K are written as pairs (a,t), a in [0,p), t in T,
        standing for x_{K+1}^a * t -- new generator's exponent *first*,
        matching `right`'s own row convention (row 0 = the newest
        generator at each step), so that a layer's own tuple position g
        always agrees with `right`'s row g, which is the invariant every
        other method (`mul`, `power`, `apply_hom`, ...) relies on:
            (a,t) * (s,0) = (a, t*s)                            [s in T]
            (a,t) * (1,1) = (a+1, alpha(t))           if a < p-1
            (a,t) * (1,1) = (0, w*alpha(t))           if a = p-1
        `alpha` is computed once per layer (a handful of `pres.collect`
        calls total across the whole compilation, not one per element) and
        applied to the whole layer at once via the vectorised
        `apply_hom_array`; the one per-layer "fixed left factor" product
        (w*alpha(t), needed only for the p-1 -> 0 carry) uses
        `mul_array_left`, which needs T's own inverse table -- computed
        here by the same `power(idx, |T|-1)` Lagrange trick `_finish_compile`
        already uses for the outermost group, just applied once per layer
        instead of once overall.  Every other step is either a single
        `pres.collect` call or a vectorised NumPy array operation -- no
        per-element Python-level group operation anywhere in the T-sized
        work -- which is what takes compiling a single group of order 5^7
        from ~20s (collection-based) to a small fraction of that, the
        difference between the order-5^7 showcase (34,297 groups)
        finishing in this session and not."""
        n, p, pres = self.n, self.p, self.pres

        elements: List[Vector] = [()]
        right_t = np.zeros((0, 1), dtype=np.int64)

        for K in range(n - 1, -1, -1):
            m = len(elements)                  # |T| = |L_{K+1}|
            t_gens = n - K - 1                  # generators of T
            T = self._make_layer(t_gens, elements, right_t)
            T.inv = T.power_array(np.arange(m, dtype=np.int64), m - 1) if m else np.array([], dtype=np.int64)

            # alpha(x_{K+2+j}) = x_{K+2+j} * c^{-1}, c = [x_{K+1},x_{K+2+j}]
            # -- a word already entirely within T (comm_words only ever
            # reference generators strictly later than both arguments), so
            # `pres.collect` is called a handful of times total (once per
            # later generator per layer), not once per group element.  It
            # returns a full length-n vector; positions 0..K are always
            # zero (checked by PCPresentation.__post_init__), so the tail
            # [K+1:] is exactly T's own length-t_gens local vector, in T's
            # own (a-first) convention: T's own position j (0-indexed, row
            # j of T.right) holds global generator x_{K+2+j}, in increasing
            # order, directly matching `comm_word`'s own later-generator
            # indexing -- no reversal needed with this convention.
            alpha_gen_images = []
            for j in range(t_gens):
                global_0idx = K + 1 + j
                c_vec = pres.collect(pres.comm_word(K, global_0idx))[K + 1:]
                c_idx = T.index_of[c_vec]
                c_inv_idx = T.power(c_idx, m - 1)       # Lagrange: c^{-1} = c^{|T|-1}
                alpha_gen_images.append(T.mul(T.gen_index[j], c_inv_idx))
            # w = x_{K+1}^p, as an element of T.
            w_idx = T.index_of[pres.collect(pres.power_words[K])[K + 1:]]

            # alpha applied to the whole layer at once (one vectorised call
            # instead of m Python-level apply_hom calls).
            all_t = np.arange(m, dtype=np.int64)
            alpha1 = T.apply_hom_array(alpha_gen_images, all_t)

            new_order = p * m
            new_right = np.zeros((n - K, new_order), dtype=np.int64)
            new_elements: List[Vector] = [None] * new_order  # type: ignore
            for a in range(p):
                base = a * m
                for t in range(m):
                    new_elements[base + t] = (a,) + elements[t]

            # right-multiplication by a generator of T (row 1+g_local, T's
            # own row g_local = global generator x_{K+2+g_local}):
            # (a,t)*(s,0) = (a, t*s), independent of a.
            for g_local in range(t_gens):
                col_t = right_t[g_local]
                for a in range(p):
                    base = a * m
                    new_right[1 + g_local, base:base + m] = base + col_t
            # right-multiplication by x_{K+1} itself (row 0):
            # (a,t)*(1,1) = (a+1,alpha(t)) for a<p-1; (0,w*alpha(t)) for a=p-1.
            for a in range(p - 1):
                new_right[0, a * m:a * m + m] = (a + 1) * m + alpha1
            new_right[0, (p - 1) * m:(p - 1) * m + m] = T.mul_array_left(w_idx, alpha1)

            elements = new_elements
            right_t = new_right

        self.elements = elements
        self.index_of = {v: i for i, v in enumerate(elements)}
        self.right = right_t
        parent, parent_gen = self._bfs_tree_from_right()
        self._finish_compile(parent, parent_gen)

    def _make_layer(self, t_gens: int, elements: List[Vector], right: np.ndarray) -> "CompiledPGroup":
        """A bare CompiledPGroup wrapping an already-built (elements,right)
        table, so `mul`/`power`/`apply_hom` can be called on it directly --
        those methods only ever touch `self.elements`, `self.right`,
        `self.n`, `self.order`, `self.identity_index`."""
        T = CompiledPGroup.__new__(CompiledPGroup)
        T.n = t_gens
        T.p = self.p
        T.order = len(elements)
        T.elements = elements
        T.index_of = {v: i for i, v in enumerate(elements)}
        T.right = right
        T.identity_index = 0
        T.gen_index = [T._gen_index(g) for g in range(t_gens)]
        return T

    def _bfs_tree_from_right(self):
        """A parent/parent_gen BFS tree over the already-built `right`
        table (used by `_conjugation_vector`) -- a plain graph BFS, no
        presentation collection involved."""
        order = self.order
        parent = np.full(order, -1, dtype=np.int64)
        parent_gen = np.full(order, -1, dtype=np.int64)
        seen = np.zeros(order, dtype=bool)
        seen[0] = True
        queue = [0]
        qi = 0
        right = self.right
        while qi < len(queue):
            idx = queue[qi]
            qi += 1
            for g in range(self.n):
                nxt = int(right[g, idx])
                if not seen[nxt]:
                    seen[nxt] = True
                    parent[nxt] = idx
                    parent_gen[nxt] = g
                    queue.append(nxt)
        return parent, parent_gen

    def _finish_compile(self, parent, parent_gen):
        n, order = self.n, self.order
        self.parent: np.ndarray = parent
        self.parent_gen: np.ndarray = parent_gen
        self.identity_index = 0
        self.gen_index: List[int] = [self._gen_index(g) for g in range(n)]

        # Everything below uses only `right`, via mul/power; no more collect().
        # Vectorised (power_array) rather than one `power` call per element
        # -- matters as much here, at the outermost order-p^n scale, as it
        # does per-layer inside `_compile_fast`.
        self.inv: np.ndarray = self.power_array(np.arange(order, dtype=np.int64), order - 1)

        conj = np.empty((n, order), dtype=np.int64)
        all_idx = np.arange(order, dtype=np.int64)
        for g in range(n):
            ginv = int(self.inv[self.gen_index[g]])
            gidx = self.gen_index[g]
            conj[g] = self.mul_array_right(self.mul_array_left(ginv, all_idx), gidx)
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

    def mul_array_right(self, arr: np.ndarray, j: int) -> np.ndarray:
        """elements[i] * elements[j] for an entire NumPy array of i's at
        once, batching the same letter-by-letter right-multiplication as
        `mul` into O(n) vectorised NumPy steps (fancy indexing into `right`)
        regardless of how large `arr` is, instead of O(|arr|) separate
        Python-level `mul` calls.  Used wherever a closure-style computation
        needs to multiply many elements by one fixed element -- which is
        exactly what dominates `closure`/`_closure_extend` once a candidate
        subgroup gets into the thousands of elements (see pcgroup.py's
        module-level discussion and the paper's bottleneck section)."""
        v = self.elements[j]
        cur = arr
        right = self.right
        for g in range(self.n):
            e = v[g]
            if e:
                col = right[g]
                for _ in range(e):
                    cur = col[cur]
        return cur

    def mul_array_left(self, i: int, arr: np.ndarray) -> np.ndarray:
        """elements[i] * elements[j] for a fixed i and an entire array of
        j's, via i*x = (x^{-1} i^{-1})^{-1}: x^{-1} is the elementwise
        `inv` lookup, (.)*i^{-1} is `mul_array_right` (a fixed right factor,
        batched left argument -- exactly the case that function handles),
        and the outer inverse is again an elementwise `inv` lookup.  No
        separate "left multiplication table" is needed."""
        xinv = self.inv[arr]
        prod = self.mul_array_right(xinv, self.inverse(i))
        return self.inv[prod]

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

    def apply_hom_array(self, images: Sequence[int], idx_array: np.ndarray) -> np.ndarray:
        """`apply_hom(images, i)` for an entire NumPy array of i's at once:
        group elements by each coordinate's exponent (the exponent only
        ever takes p values) and batch the corresponding power-image
        multiplication via `mul_array_right` -- O(n*p) vectorised steps
        regardless of |idx_array|, instead of one Python-level `apply_hom`
        call per element.  Used by `_compile_fast` to apply the
        conjugation-by-the-new-generator automorphism to an entire
        already-compiled layer at once."""
        if not hasattr(self, "_elements_mat"):
            self._elements_mat = np.array(self.elements, dtype=np.int64)
        mat = self._elements_mat
        cur = np.full(len(idx_array), self.identity_index, dtype=np.int64)
        for g in range(self.n):
            coords = mat[idx_array, g]
            for e in range(1, self.p):
                mask = coords == e
                if mask.any():
                    img_e = self.power(images[g], e)
                    cur[mask] = self.mul_array_right(cur[mask], img_e)
        return cur

    def mul_array_pairwise(self, arr1: np.ndarray, arr2: np.ndarray) -> np.ndarray:
        """mul(arr1[i], arr2[i]) for every i at once, with *both* arguments
        varying per index (unlike `mul_array_right`/`mul_array_left`, which
        need one side fixed): group by each coordinate's exponent in arr2,
        same trick as `apply_hom_array`, batching each generator's
        right-multiplication over the matching subset of positions via
        NumPy fancy indexing -- O(n*p) vectorised steps regardless of the
        arrays' length.  Used by `power_array` to vectorise computing
        every element's inverse via Lagrange's theorem (x^{-1}=x^{|G|-1})
        across a whole layer at once in `_compile_fast`, rather than one
        Python-level `power` call per element."""
        if not hasattr(self, "_elements_mat"):
            self._elements_mat = np.array(self.elements, dtype=np.int64)
        mat = self._elements_mat
        cur = arr1.copy()
        for g in range(self.n):
            coords = mat[arr2, g]
            col = self.right[g]
            for e in range(1, self.p):
                mask = coords == e
                if mask.any():
                    idxs = np.nonzero(mask)[0]
                    sub = cur[idxs]
                    for _ in range(e):
                        sub = col[sub]
                    cur[idxs] = sub
        return cur

    def power_array(self, arr: np.ndarray, e: int) -> np.ndarray:
        """elements[i]^e for every i in arr at once, via binary
        exponentiation using `mul_array_pairwise` -- O(log(e) * n * p)
        vectorised steps regardless of |arr|."""
        result = np.full(len(arr), self.identity_index, dtype=np.int64)
        base = arr.copy()
        while e > 0:
            if e & 1:
                result = self.mul_array_pairwise(result, base)
            e >>= 1
            if e:
                base = self.mul_array_pairwise(base, base)
        return result

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

    def _flood(self, mask: np.ndarray, frontier: np.ndarray, gens: List[int]) -> None:
        """Expand `mask` (a boolean membership array, with `frontier`'s
        indices already set True in it) to the full closure under `gens`,
        by vectorised wave BFS: each round batch-multiplies the *entire*
        current frontier by every generator, on both sides, via
        `mul_array_right`/`mul_array_left` -- O(n) NumPy steps per
        generator per round, regardless of how large the frontier is,
        rather than one Python-level `mul` call per (frontier element,
        generator) pair. Mutates `mask` in place; does not return the
        frontier (callers that need the final element list read it off
        `mask` themselves, e.g. via `np.nonzero`)."""
        while frontier.size:
            parts = []
            for g in gens:
                parts.append(self.mul_array_right(frontier, g))
                parts.append(self.mul_array_left(g, frontier))
            cand = np.unique(np.concatenate(parts))
            novel = cand[~mask[cand]]
            if novel.size == 0:
                return
            mask[novel] = True
            frontier = novel

    def _closure_extend(self, have: set, gens: List[int], new_gen: int) -> set:
        """Given `have`, already closed under `gens`, returns the closure of
        have union {new_gen} under gens + [new_gen].  Seeds the flood from
        `have` as-is (it is already closed under the old generators, so
        there is no need to re-expand it through them) and only propagates
        the genuinely new elements the latest generator contributes, via
        the vectorised `_flood` above.  This is what makes incrementally
        building up a generating set, one random element at a time, cheap
        even when the final subgroup is large: `small_generating_set` below
        never re-floods work it has already paid for, and the flood itself
        is a handful of NumPy array operations per round rather than one
        Python function call per element."""
        order = self.order
        mask = np.zeros(order, dtype=bool)
        have_arr = np.fromiter(have, dtype=np.int64, count=len(have))
        mask[have_arr] = True
        all_gens = gens + [new_gen]
        seed = np.unique(np.concatenate([
            self.mul_array_right(have_arr, new_gen),
            self.mul_array_left(new_gen, have_arr),
        ]))
        frontier = seed[~mask[seed]]
        if frontier.size:
            mask[frontier] = True
        self._flood(mask, frontier, all_gens)
        return set(np.nonzero(mask)[0].tolist())

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
        input.

        Walks the elements in a fixed random order, incrementally extending
        a running generating set with `_closure_extend` whenever the next
        element is not yet in the span.  For a rank-r subgroup this needs
        only about r steps (Burnside basis theorem: random elements span the
        Frattini quotient quickly), and -- unlike re-running `closure` from
        scratch at every candidate size, as an earlier version of this
        function did -- every step's cost is proportional only to the
        elements *newly* discovered at that step, not to the size of the
        subgroup built up so far.  This is what makes the candidate
        generation in protoessential.py scale to subgroups of order into the
        tens of thousands (needed for the order-5^7 showcase group), where
        the old quadratic-in-candidate-size approach did not."""
        elements = list(elements)
        if not elements:
            return []
        target = set(elements) if already_closed else set(self.closure(elements))
        if len(target) == 1:
            return []
        rng = random.Random(0)
        shuffled = list(elements)
        rng.shuffle(shuffled)
        chosen: List[int] = []
        have: set = {self.identity_index}
        for e in shuffled:
            if e in have:
                continue
            have = self._closure_extend(have, chosen, e)
            chosen.append(e)
            if len(have) == len(target):
                break
        return chosen

    def closure(self, gens: Sequence[int]) -> List[int]:
        """The subgroup generated by the given element indices, as a sorted
        list of indices.  Standard closure-by-flooding (repeatedly multiply
        every known element by every generator, left and right, until no
        new elements appear -- correct for any finite group), via the
        vectorised wave-BFS `_flood`: every round costs O(n) NumPy array
        operations per generator regardless of the current frontier size,
        rather than one Python-level `mul` call per (element, generator)
        pair, which is what lets this stay fast even when the subgroup
        generated runs into the thousands of elements."""
        order = self.order
        mask = np.zeros(order, dtype=bool)
        mask[self.identity_index] = True
        gens = list(gens)
        if gens:
            frontier = np.array([self.identity_index], dtype=np.int64)
            self._flood(mask, frontier, gens)
        return np.nonzero(mask)[0].tolist()

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
