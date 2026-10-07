"""Correctness tests for fastfusion.pcgroup, cross-checked against GAP."""
import itertools
import random
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from fastfusion.pcgroup import PCPresentation, CompiledPGroup
from gap_oracle import gap_invariants


def heisenberg_p(p):
    """Extraspecial group p^(1+2), exponent p: x,y,z with [x,y]=z, x^p=y^p=z^p=1."""
    return PCPresentation(n=3, p=p, comm_words={(0, 1): [3]}, names=["x", "y", "z"])


def cyclic_p2(p):
    """C_{p^2} as two PCGS layers: z1^p = z2, z2^p = 1."""
    return PCPresentation(n=2, p=p, power_words=[[2], []], names=["z1", "z2"])


def extraspecial_2_pair(x_sq, y_sq):
    """A single extraspecial "hyperbolic pair" of order 8: generators x,y,z
    (z LAST, i.e. the center/derived subgroup, matching the convention used
    throughout for odd p) with [x,y]=z and x^2 = z^{x_sq}, y^2 = z^{y_sq}
    (x_sq,y_sq in {0,1}).  (x_sq,y_sq)=(0,0) gives D8; any choice with at
    least one of x_sq,y_sq equal to 1 gives Q8 (all three such choices are
    isomorphic, by replacing x or y with xz / xy)."""
    return PCPresentation(n=3, p=2, power_words=[[3] if x_sq else [], [3] if y_sq else [], []],
                           comm_words={(0, 1): [3]}, names=["x", "y", "z"])


def dihedral_8():
    return extraspecial_2_pair(0, 0)


def quaternion_8():
    # q(a,b) = a*x_sq + b*y_sq + a*b (mod 2) must be 1 on all three nonzero
    # (a,b) for every noncentral coset to square to z (Q8 has no noncentral
    # involutions): q(1,0)=x_sq, q(0,1)=y_sq, q(1,1)=x_sq+y_sq+1, so we need
    # x_sq=y_sq=1.
    return extraspecial_2_pair(1, 1)


def wreath_cp_cp(p):
    """C_p wr C_p = base (C_p)^p extended by a cyclic group of order p acting
    by cyclically permuting the p base coordinates.  PCGS: a1,...,a_{p-1}
    (p-1 of the base coordinates, in "difference" form) plus the product
    coordinate, plus the top generator t.  We use the standard presentation:
    generators b_0,...,b_{p-1} (base, b_i^p=1, central product among
    themselves... but b_i's don't commute with t!) -- base is abelian
    (b_i commute with each other) but t permutes them, [b_i,t] = b_{i+1} b_i^{-1}
    (not expressible purely in LATER generators unless we order generators by
    t first then b_0,...,b_{p-1} with a chosen order matching orbits).  We
    place t FIRST (heaviest), then b_0,...,b_{p-1} in order, so [t,b_i] must be
    a word in b_{i+1},...,b_{p-1} ONLY -- but t^{b_i} involves b_{i+1} which is
    fine (later), yet the permutation also wraps b_{p-1} -> b_0 (EARLIER) which
    breaks the "later generators only" rule for raw b_i.  We instead use the
    standard trick: replace the base generators by b_0 and the "differences"
    d_i = b_i - b_{i-1} (so permutation becomes expressible via later
    differences plus a correction on b_0 that lands in the *product* which
    is central) -- this is exactly the classical construction of the PCGS for
    C_p wr C_p and is intricate, so for this test we only use p=2 (giving D8,
    already covered) and instead validate higher nilpotency class via a
    different, simpler route in test_wreath.py using an explicit base-change.
    (placeholder, see test_wreath.py)"""
    raise NotImplementedError


def dihedral_16():
    """D16 = <r,s | r^8=1, s^2=1, srs=r^-1>, nilpotency class 3 (stress-tests
    collection through several commutator substitution levels, and a
    generator (x3=r^2) whose actual order (4) exceeds p).
    PCGS (heaviest first): x1=s, x2=r, x3=r^2, x4=r^4.
    x2^2 = r^2 = x3;  x3^2 = r^4 = x4;  x4^2 = 1;  x1^2=1.
    [x1,x2]=[s,r]=r^-2 = x3*x4 (= r^2*r^4 = r^6 = r^-2);  [x1,x3]=[s,r^2]=r^-4=x4.
    """
    return PCPresentation(n=4, p=2,
                           power_words=[[], [3], [4], []],
                           comm_words={(0, 1): [3, 4], (0, 2): [4]},
                           names=["s", "r", "r2", "r4"])


def random_word(n, p, length):
    return [random.randint(1, n) for _ in range(length)]


def check_presentation(pres: PCPresentation, label: str, n_random_checks=200):
    print(f"\n=== {label}: compiling ===")
    G = CompiledPGroup(pres)
    assert len(G.elements) == G.order == pres.p ** pres.n
    print(f"order = {G.order}")

    # group-axiom sanity checks by random sampling
    rnd = random.Random(12345 + G.order)
    idxs = list(range(G.order))
    for _ in range(n_random_checks):
        a, b, c = (rnd.choice(idxs) for _ in range(3))
        # associativity
        assert G.mul(G.mul(a, b), c) == G.mul(a, G.mul(b, c))
        # identity
        assert G.mul(a, 0) == a and G.mul(0, a) == a
        # inverse
        assert G.mul(a, G.inverse(a)) == 0 and G.mul(G.inverse(a), a) == 0
    print("associativity / identity / inverse: OK (random sample)")

    # defining relations hold exactly (every element, not just sampled)
    for g in range(pres.n):
        lhs = G.power(G.gen_index[g], pres.p)
        rhs = G._apply_hom_to_word(G.gen_index, pres.power_words[g])
        assert lhs == rhs, f"power relation failed for generator {g}"
    for (i, j), w in pres.comm_words.items():
        lhs = G.commutator(G.gen_index[i], G.gen_index[j])
        rhs = G._apply_hom_to_word(G.gen_index, w)
        assert lhs == rhs, f"commutator relation failed for ({i},{j})"
    print("defining relations: OK (exact)")

    # closure of all generators is the whole group
    assert G.closure(G.gen_index) == list(range(G.order))
    print("generators generate the whole compiled group: OK")

    # structural invariants, computed via our own engine
    center = G.center()
    derived = G.derived_subgroup()
    eop = sorted((G.order_of(i) for i in range(G.order)))
    from collections import Counter
    profile = sorted([list(t) for t in Counter(eop).items()])
    classes = G.conjugacy_classes()
    print(f"|Z(S)| = {len(center)}, |S'| = {len(derived)}, "
          f"#conj classes = {len(classes)}, element-order profile = {profile}")

    gi = gap_invariants(pres)
    print(f"GAP:    order={gi.order} center={gi.center_order} derived={gi.derived_order} "
          f"frattini={gi.frattini_order} class={gi.nilpotency_class} exp={gi.exponent} "
          f"#classes={gi.num_conj_classes} id={gi.id_group}")

    assert gi.order == G.order
    assert gi.center_order == len(center)
    assert gi.derived_order == len(derived)
    assert gi.num_conj_classes == len(classes)
    assert gi.element_order_profile == profile, (gi.element_order_profile, profile)
    print(f"=== {label}: MATCHES GAP ===")
    return G, gi


def test_heisenberg_3():
    check_presentation(heisenberg_p(3), "Heisenberg group 3^(1+2) (exponent 3)")


def test_heisenberg_5():
    check_presentation(heisenberg_p(5), "Heisenberg group 5^(1+2) (exponent 5)")


def test_cyclic_4():
    G, gi = check_presentation(cyclic_p2(2), "C4 via two PCGS layers")
    assert gi.id_group == [4, 1]  # C4


def test_cyclic_9():
    G, gi = check_presentation(cyclic_p2(3), "C9 via two PCGS layers")
    assert gi.id_group == [9, 1]  # C9


def test_dihedral_8():
    G, gi = check_presentation(dihedral_8(), "D8")
    assert gi.id_group == [8, 3]  # D8 is SmallGroup(8,3) in GAP's library


def test_quaternion_8():
    G, gi = check_presentation(quaternion_8(), "Q8")
    assert gi.id_group == [8, 4]  # Q8 is SmallGroup(8,4)


def test_dihedral_16():
    G, gi = check_presentation(dihedral_16(), "D16")
    assert gi.nilpotency_class == 3
    assert gi.exponent == 8


def test_subgroup_machinery():
    """Exercise closure / normalizer / centralizer / conjugacy classes on D16
    and cross-check sizes against GAP-computed invariants of specific
    subgroups (center, derived subgroup already checked above; here check a
    non-normal cyclic subgroup's normalizer/centralizer by brute force
    comparison with an independent enumeration)."""
    pres = dihedral_16()
    G = CompiledPGroup(pres)
    s_idx = G.gen_index[0]   # the reflection generator
    # <s> should have order 2, and in D16, N_S(<s>) should have order 4
    # (= C_S(s), since <s> has order 2 so N=C here) and there are 4
    # conjugates of <s> (index of normalizer = |S|/|N| = 16/4=4).
    Hs = set(G.closure([s_idx]))
    assert len(Hs) == 2
    N = set(G.normalizer([s_idx], subgroup_set=Hs))
    C = set(G.centralizer([s_idx]))
    assert N == C
    assert len(N) == 4, len(N)
    # brute-force cross check: recompute normalizer by literally checking,
    # for every element g, whether conjugating s by g stays in {1,s}.
    brute_N = {g for g in range(G.order) if G.conjugate(s_idx, g) in Hs}
    assert brute_N == N
    print(f"subgroup machinery: |<s>|=2, |N_S(<s>)|=|C_S(s)|={len(N)} -- matches brute force")


def test_automorphism_verification():
    """Build the automorphism r->r, s->s*r^2 of D16 explicitly and check our
    verifier accepts it; and a non-automorphism is correctly rejected."""
    pres = dihedral_16()
    G = CompiledPGroup(pres)
    s, r, r2, r4 = G.gen_index
    # phi: s -> s*r2, r -> r, r2 -> r2, r4 -> r4  (an inner automorphism: this
    # is conjugation by some power of r, since s^r = s*r^-2 = s*r2*r4 -- let's
    # just test both a genuine inner automorphism and a deliberately broken map)
    phi_images = [G.mul(s, r2), r, r2, r4]
    assert G.is_automorphism(phi_images)
    bad_images = [G.mul(s, r), r, r2, r4]   # s -> s*r has the wrong order (s*r has order 4, not 2)
    assert not G.is_automorphism(bad_images)
    print("automorphism verification: accepts a genuine map, rejects a broken one")


if __name__ == "__main__":
    test_heisenberg_3()
    test_heisenberg_5()
    test_cyclic_4()
    test_cyclic_9()
    test_dihedral_8()
    test_quaternion_8()
    test_dihedral_16()
    test_subgroup_machinery()
    test_automorphism_verification()
    print("\nALL TESTS PASSED")
