"""Explicit automorphisms of extraspecial p-groups, via Winter's theorem.

For S extraspecial of order p^{1+2n} with Z(S) = <z> of order p and
V = S/Z(S) the associated 2n-dimensional F_p-space carrying the
nondegenerate alternating commutator form B, Winter (1972) showed:

    Aut(S) = Inn(S) . Out(S),   Inn(S) ~= V (translations),

    Out(S) ~= CSp(2n,p) = Sp(2n,p).(p-1)   (p odd: the symplectic
              similitude group -- linear maps preserving B up to a scalar,
              which also acts on Z(S) by that same scalar);

    Out(S) ~= O^eps(2n,2)   (p = 2: the full orthogonal group of the
              quadratic refinement q, Witt type eps = +/- matching S; there
              is no extra scalar factor since F_2^* is trivial).

Rather than hand-deriving a verified minimal generating set for Sp(2n,p) or
O^eps(2n,2) symbolically (easy to get a sign or isotropy condition subtly
wrong, especially for p=2), this module takes a *generate-and-verify*
approach: it writes down a generous list of structurally-motivated candidate
linear maps on the basis x_1,y_1,...,x_n,y_n (per-plane SL(2,p)/O(2,2)-type
maps, scalars, and cross-plane mixing maps), lifts each candidate to a map on
all PCGS generators (fixing z, or scaling it for the odd-p scalar maps), and
keeps only those that pass `CompiledPGroup.is_automorphism` -- which checks
the proposed map against *every* defining relation of the presentation, and
is independently validated in tests/test_pcgroup.py.  Every automorphism
used anywhere in this project is therefore verified computationally, not
merely "derived by hand and trusted".

This does not certify that the resulting generating set is the *entire*
Sp(2n,p)/O^eps(2n,2) -- only that it is a verified subgroup.  As explained in
protoessential.py, this is immaterial for *correctness* of the fast
proto-essential search (Section 3 of Gautam's paper): using a (possibly
proper) subgroup of Aut(S) for the orbit-pruning step only ever reduces how
much redundant work is pruned, never the correctness of the final answer.
tests/test_autgroup.py checks, computationally, that the generating set found
here is at least large enough to act transitively on the natural candidate
set (the 1-dimensional subspaces of V, equivalently the hyperplanes), which
is the property that actually matters for pruning effectiveness; and for the
smallest cases (n=1) it checks the generated group has the full, exactly
correct order of Aut(S).
"""
from __future__ import annotations

from typing import List, Optional, Sequence, Tuple

from .pcgroup import CompiledPGroup
from .constructions import extraspecial


def _basis_images_identity(two_n: int) -> List[List[Tuple[int, int]]]:
    """images[k] = list of (basis_index, coeff) pairs: the image of basis
    vector k under the identity map, i.e. just [(k,1)]."""
    return [[(k, 1)] for k in range(two_n)]


def _apply_linear_map(G: CompiledPGroup, n: int, basis_images: Sequence[Sequence[Tuple[int, int]]],
                       z_power: int) -> List[int]:
    """Given basis_images[k] = [(j, coeff), ...] describing phi(e_k) = sum
    coeff * e_j (as a group-element product, exponents mod p), and
    phi(z) = z^{z_power}, build the full images list (length n_gens) for
    `G.apply_hom`/`G.is_automorphism`: images[k] for k < 2n is the group
    element phi(e_k), images[2n] = phi(z)."""
    p = G.p
    gens = G.gen_index
    two_n = 2 * n
    images = []
    for k in range(two_n):
        cur = G.identity_index if hasattr(G, "identity_index") else 0
        cur = 0
        for j, coeff in basis_images[k]:
            cur = G.mul(cur, G.power(gens[j], coeff % p))
        images.append(cur)
    images.append(G.power(gens[two_n], z_power % p))
    return images


def _is_automorphism_fast(G: CompiledPGroup, n: int, images: List[int]) -> bool:
    """Equivalent to G.is_automorphism(images) for our extraspecial
    presentations, but much faster at the sizes used in the showcase (order
    up to 5^7): checking the defining relations is already cheap, but
    `is_automorphism`'s surjectivity test (closure of the images, i.e.
    O(|S|) group multiplications) is not.  By the Burnside basis theorem, a
    set of elements generates a p-group S iff their images generate the
    Frattini quotient S/Phi(S); for our extraspecial groups Phi(S) = Z(S) =
    <z> (the last generator), so S/Phi(S) is exactly V = F_p^{2n} and we only
    need the 2n x 2n matrix of V-components of images[0..2n-1] to be
    invertible mod p, plus z's image to be a nontrivial power of z (which
    holds by construction in `_apply_linear_map`)."""
    if not G.verify_endomorphism(images):
        return False
    p, two_n = G.p, 2 * n
    mat = [list(G.elements[images[k]][:two_n]) for k in range(two_n)]
    # Gaussian elimination mod p to test invertibility.
    for col in range(two_n):
        pivot = None
        for row in range(col, two_n):
            if mat[row][col] % p != 0:
                pivot = row
                break
        if pivot is None:
            return False
        mat[col], mat[pivot] = mat[pivot], mat[col]
        inv = pow(mat[col][col], -1, p)
        mat[col] = [(x * inv) % p for x in mat[col]]
        for row in range(two_n):
            if row != col and mat[row][col] % p != 0:
                factor = mat[row][col]
                mat[row] = [(a - factor * b) % p for a, b in zip(mat[row], mat[col])]
    return True


def _try(G: CompiledPGroup, n: int, basis_images, z_power: int) -> Optional[List[int]]:
    images = _apply_linear_map(G, n, basis_images, z_power)
    if _is_automorphism_fast(G, n, images):
        return images
    return None


def winter_generators_odd_p(G: CompiledPGroup, n: int, p: int) -> List[List[int]]:
    """A verified generating set of automorphisms of the exponent-p
    extraspecial group of order p^{1+2n} (odd p), containing a large,
    explicit chunk of Inn(S) . CSp(2n,p): per-plane SL(2,p) (swap-invert +
    shears + diagonal scalars), a global scalar achieving every lambda in
    F_p^*, adjacent-plane transpositions, and adjacent-plane mixing
    transvections."""
    found: List[List[int]] = []

    def X(k):
        return [(k, 1)]

    for i in range(n):
        xi, yi = 2 * i, 2 * i + 1
        base = _basis_images_identity(2 * n)
        # swap + invert: x_i -> y_i, y_i -> x_i^{-1}
        im = list(base)
        im[xi] = [(yi, 1)]
        im[yi] = [(xi, p - 1)]
        r = _try(G, n, im, 1)
        if r:
            found.append(r)
        # shears: y_i -> y_i * x_i^c  (and symmetric x_i -> x_i * y_i^{-c})
        for c in range(1, p):
            im = list(base)
            im[yi] = [(yi, 1), (xi, c)]
            r = _try(G, n, im, 1)
            if r:
                found.append(r)
        # diagonal scalar within the plane: x_i -> x_i^c, y_i -> y_i^{c^{-1}}
        for c in range(2, p):
            cinv = pow(c, -1, p)
            im = list(base)
            im[xi] = [(xi, c)]
            im[yi] = [(yi, cinv)]
            r = _try(G, n, im, 1)
            if r:
                found.append(r)

    # global scalar on z (and correspondingly on all x_i, fixing y_i):
    # x_i -> x_i^c for every i, y_i unchanged; gives lambda = c on the form.
    for c in range(2, p):
        base = _basis_images_identity(2 * n)
        im = list(base)
        for i in range(n):
            im[2 * i] = [(2 * i, c)]
        r = _try(G, n, im, c)
        if r:
            found.append(r)

    # adjacent plane swap and mixing
    for i in range(n - 1):
        xi, yi, xj, yj = 2 * i, 2 * i + 1, 2 * i + 2, 2 * i + 3
        base = _basis_images_identity(2 * n)
        im = list(base)
        im[xi], im[xj] = [(xj, 1)], [(xi, 1)]
        im[yi], im[yj] = [(yj, 1)], [(yi, 1)]
        r = _try(G, n, im, 1)
        if r:
            found.append(r)
        # mixing transvection along v = x_i + x_j (c=1): recompute via the
        # transvection formula T_v(w) = w + B(w,v) v for the standard form
        # B(x_i,y_i)=1 etc.  B(y_i,v)=-1, B(y_j,v)=-1 (mod p), others B(.,v)=0.
        base = _basis_images_identity(2 * n)
        im = list(base)
        im[yi] = [(yi, 1), (xi, p - 1), (xj, p - 1)]
        im[yj] = [(yj, 1), (xi, p - 1), (xj, p - 1)]
        r = _try(G, n, im, 1)
        if r:
            found.append(r)

    return found


def winter_generators_p2(G: CompiledPGroup, n: int, squares: Sequence[int],
                          max_combo: int = 3) -> List[List[int]]:
    """A verified generating set of automorphisms of the p=2 extraspecial
    group of order 2^{1+2n} with quadratic form given by `squares` (see
    constructions.extraspecial).

    For p = 2, orthogonal transvections along isotropic vectors do *not*
    simply generalise the odd-p symplectic formula -- characteristic 2
    orthogonal geometry has extra sign/isotropy subtleties that are easy to
    get wrong by hand (an earlier version of this function did).  Rather
    than re-derive that theory symbolically, this function instead searches
    systematically: for every pair of basis positions (i,j) it tries the
    transposition "swap coordinates i and j", and for every basis position k
    and every small subset of the *other* positions it tries "add that
    subset onto coordinate k" (i.e. a shear); every candidate is lifted to a
    map on all PCGS generators (fixing z, since p=2 has no nontrivial
    scalars) and kept only if `CompiledPGroup.is_automorphism` accepts it.
    This is slower than a closed-form generating set but unconditionally
    correct, and in practice (tests/test_autgroup.py) already finds enough
    automorphisms to act transitively on the natural candidate set for
    n up to at least 2 in both the "+" and "-" types."""
    import itertools

    two_n = 2 * n
    found: List[List[int]] = []

    def test_images(im):
        images = _apply_linear_map(G, n, im, 1)
        if _is_automorphism_fast(G, n, images):
            found.append(images)

    for i in range(two_n):
        for j in range(i + 1, two_n):
            base = _basis_images_identity(two_n)
            im = list(base)
            im[i], im[j] = [(j, 1)], [(i, 1)]
            test_images(im)

    for k in range(two_n):
        others = [j for j in range(two_n) if j != k]
        for r in range(1, max_combo + 1):
            for combo in itertools.combinations(others, r):
                base = _basis_images_identity(two_n)
                im = list(base)
                im[k] = [(k, 1)] + [(j, 1) for j in combo]
                test_images(im)

    return found


def automorphism_generators(pres_n: int, p: int, n: int,
                             squares: Optional[Sequence[int]] = None) -> Tuple[CompiledPGroup, List[List[int]]]:
    """Convenience: build the extraspecial group of order p^{1+2n} and its
    verified Winter-automorphism generating set in one call."""
    pres = extraspecial(p, n, squares=squares)
    G = CompiledPGroup(pres)
    if p == 2:
        sq = squares if squares is not None else [0] * (2 * n)
        gens = winter_generators_p2(G, n, sq)
    else:
        gens = winter_generators_odd_p(G, n, p)
    return G, gens
