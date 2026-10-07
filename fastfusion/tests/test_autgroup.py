"""Tests for fastfusion.autgroup: every found generator is, by construction,
a verified automorphism (CompiledPGroup.is_automorphism).  Here we check (a)
for n=1 (D8, Q8, and the smallest odd-p case) that Inn(S) together with our
generators produces a permutation group of *exactly* the correct order
|Aut(S)|, computed independently from the classical formulas
|Aut(D8)|=8, |Aut(Q8)|=24, |Aut(extraspecial p^3, exponent p)| = p^2 * (p-1) * |GL(2,p)|/(p-1)...
actually |Aut| = |Inn|*|Out| = p^2 * |GSp(2,p)| = p^2 * (p-1)*|SL(2,p)| = p^2*(p-1)*p*(p^2-1);
and (b) for n=2 that the generators act transitively on the (p^4-1)/(p-1)
one-dimensional subspaces of V (equivalently, on the natural candidate list
of hyperplanes used by the proto-essential search) -- the property that
actually matters for pruning effectiveness, independent of whether the
generating set is literally all of Out(S).
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from fastfusion.pcgroup import CompiledPGroup
from fastfusion.constructions import extraspecial, witt_minus_squares
from fastfusion.autgroup import winter_generators_odd_p, winter_generators_p2, automorphism_generators


def permutation_of(G: CompiledPGroup, images) -> tuple:
    return tuple(G.apply_hom(images, i) for i in range(G.order))


def inner_permutations(G: CompiledPGroup) -> list:
    perms = []
    for g in G.gen_index:
        perms.append(tuple(G.conjugate(i, g) for i in range(G.order)))
    return perms


def compose(p1, p2):
    # (p1 then p2): result[i] = p2[p1[i]]
    return tuple(p2[x] for x in p1)


def closure_of_permutations(gens, limit=200000):
    ident = tuple(range(len(gens[0])))
    seen = {ident}
    queue = [ident]
    qi = 0
    while qi < len(queue):
        cur = queue[qi]
        qi += 1
        for g in gens:
            for nxt in (compose(cur, g), compose(g, cur)):
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
                    if len(seen) > limit:
                        raise RuntimeError("closure too large, aborting")
    return seen


def full_aut_order_via_closure(G, hom_gens):
    perms = inner_permutations(G) + [permutation_of(G, im) for im in hom_gens]
    return len(closure_of_permutations(perms))


def test_d8_full_automorphism_group():
    pres_n = 1
    G, gens = automorphism_generators(None, 2, 1, squares=[0, 0])
    print(f"D8: found {len(gens)} candidate generators passing is_automorphism")
    order = full_aut_order_via_closure(G, gens)
    print(f"|<Inn(S), found generators>| = {order}  (expect |Aut(D8)|=8)")
    assert order == 8


def test_q8_full_automorphism_group():
    G, gens = automorphism_generators(None, 2, 1, squares=witt_minus_squares(1))
    print(f"Q8: found {len(gens)} candidate generators passing is_automorphism")
    order = full_aut_order_via_closure(G, gens)
    print(f"|<Inn(S), found generators>| = {order}  (expect |Aut(Q8)|=24)")
    assert order == 24


def test_heisenberg_3_full_automorphism_group():
    # |Aut(extraspecial 3^(1+2), exponent 3)| = |Inn|*|Out| = 9 * |GSp(2,3)|
    # = 9 * (3-1)*|SL(2,3)| = 9*2*24 = 432.
    G, gens = automorphism_generators(None, 3, 1)
    print(f"extraspecial(3,1): found {len(gens)} candidate generators")
    order = full_aut_order_via_closure(G, gens, ) if False else None
    order = len(closure_of_permutations(inner_permutations(G) +
                [permutation_of(G, im) for im in gens], limit=1000))
    print(f"|<Inn(S), found generators>| = {order}  (expect |Aut|=432)")
    assert order == 432


def one_dim_subspace_reps(p, two_n):
    """Representatives of the (p^{2n}-1)/(p-1) one-dimensional subspaces of
    F_p^{2n}: for each nonzero vector, normalise by dividing by its first
    nonzero coordinate."""
    import itertools
    reps = set()
    for v in itertools.product(range(p), repeat=two_n):
        if all(c == 0 for c in v):
            continue
        first = next(c for c in v if c != 0)
        inv = pow(first, -1, p)
        norm = tuple((c * inv) % p for c in v)
        reps.add(norm)
    return reps


def orbit_of_vectors_under_hom(G, n, p, gens, start_vec):
    """Orbit of the 1-dim-subspace-representative `start_vec` (a tuple of
    length 2n over F_p) under the linear maps induced by `gens` (each a
    homomorphism image-list), tracked via normalised representatives."""
    def normalize(v):
        first = next((c for c in v if c != 0), None)
        if first is None:
            return v
        inv = pow(first, -1, p)
        return tuple((c * inv) % p for c in v)

    def apply_lin(images, v):
        # images[k] is a group-element index for phi(e_k); we need the
        # *linear* action on V = S/Z(S), which is exactly: write v as
        # sum v_k e_k, apply phi, reduce mod Z(S) i.e. just track the
        # exponent vector on the first 2n generators of the product
        # phi(e_0)^{v_0} * ... (since V is abelian, this commutes mod Z).
        cur = 0
        for k, c in enumerate(v):
            if c:
                cur = G.mul(cur, G.power(images[k], c))
        full = G.elements[cur]
        return tuple(full[:2 * n])

    seen = {normalize(start_vec)}
    queue = [start_vec]
    qi = 0
    while qi < len(queue):
        cur = queue[qi]
        qi += 1
        for im in gens:
            nxt = normalize(apply_lin(im, cur))
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    return seen


def test_transitivity_on_points_n2_odd_p():
    for p in (3, 5):
        n = 2
        G, gens = automorphism_generators(None, p, n)
        all_points = one_dim_subspace_reps(p, 2 * n)
        start = tuple([1] + [0] * (2 * n - 1))
        orbit = orbit_of_vectors_under_hom(G, n, p, gens, start)
        print(f"p={p}, n={n}: {len(gens)} generators, orbit size {len(orbit)} "
              f"of {len(all_points)} total 1-dim subspaces")
        assert orbit == all_points, "generators are not transitive on the 1-dim subspaces"


def test_transitivity_on_points_n2_p2():
    for squares_fn, label in [(lambda n: [0] * (2 * n), "plus"),
                                (witt_minus_squares, "minus")]:
        n = 2
        squares = squares_fn(n)
        G, gens = automorphism_generators(None, 2, n, squares=squares)
        all_points = one_dim_subspace_reps(2, 2 * n)
        start = tuple([1] + [0] * (2 * n - 1))
        orbit = orbit_of_vectors_under_hom(G, n, 2, gens, start)
        print(f"p=2 ({label}), n={n}: {len(gens)} generators, orbit size {len(orbit)} "
              f"of {len(all_points)} total 1-dim subspaces")
        assert orbit == all_points, f"({label}) generators are not transitive on the 1-dim subspaces"


if __name__ == "__main__":
    test_d8_full_automorphism_group()
    test_q8_full_automorphism_group()
    test_heisenberg_3_full_automorphism_group()
    test_transitivity_on_points_n2_odd_p()
    test_transitivity_on_points_n2_p2()
    print("\nALL AUTGROUP TESTS PASSED")
