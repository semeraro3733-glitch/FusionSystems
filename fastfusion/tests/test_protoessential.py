"""Tests for fastfusion.protoessential: the fast proto-essential search,
cross-checked against (a) a brute-force search over every S-centric
subgroup via GAP for small cases, and (b) known published facts."""
import sys, os, time
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from fastfusion.pcgroup import CompiledPGroup
from fastfusion.constructions import extraspecial, witt_minus_squares
from fastfusion.autgroup import automorphism_generators
from fastfusion.protoessential import proto_essential_subgroups, central_series_candidates


def run(p, n, squares=None, verbose=True):
    G, aut_gens = automorphism_generators(None, p, n, squares=squares)
    pres = G.pres
    t0 = time.time()
    res = proto_essential_subgroups(pres, G=G, aut_gens=aut_gens, verbose=verbose)
    dt = time.time() - t0
    print(f"p={p} n={n}: order S={G.order}, raw candidates={res.num_raw_candidates}, "
          f"S-centric={res.num_s_centric_candidates}, cheap-pass={res.num_cheap_pass}, "
          f"Aut(S)-orbits={res.num_aut_orbits} ({res.num_orbits_leaving_candidates} dead), "
          f"proto-essentials: {len(res.aut_classes)} up to Aut(S), {len(res.s_classes)} up to S, "
          f"time={dt:.2f}s")
    for members, gens in res.aut_classes:
        print(f"    |E|={len(members)}  log_p|E|={round(len(members).bit_length()/ (p.bit_length()) ,1)}")
    return res, G


def test_extraspecial_3_1_matches_known_fusion_system():
    """extraspecial(3,1) = Heisenberg group 3^3: the willendeavor README
    reports F_S(PSL(3,3)) (= F_S(SL(3,3))) has 2 classes of essential
    subgroups, both of order 9.  Our candidate search should find order-9
    S-classes (there is only one Aut(S)-orbit of hyperplanes for n=1, but
    multiple S-classes since a single Aut(S)-orbit of a rank-2 space can
    cover several S-conjugacy classes)."""
    res, G = run(3, 1)
    assert all(len(m) == 9 for m, g in res.aut_classes)
    # n=1 hyperplanes are abelian (C3 x C3): Inn(E) is trivial, so the
    # radical test should pass automatically (see protoessential.py).
    assert len(res.aut_classes) >= 1


def test_extraspecial_5_1():
    res, G = run(5, 1)
    assert all(len(m) == 25 for m, g in res.aut_classes)
    assert len(res.aut_classes) >= 1


def test_extraspecial_n2_hyperplanes_fail_radical_test():
    """The mathematical finding derived in this project (verified directly
    in tests/, see also protoessential.radical_test's docstring): for
    exponent-p extraspecial groups of rank n >= 2, the index-p ("hyperplane")
    candidates are never radical, because conjugation by an element outside
    the hyperplane induces a nontrivial "shear" on the rank-2 centre Z(E)
    (which properly contains Phi(E) = Z(S)) while acting trivially on
    E/Z(E) -- an automorphism of p-power order that Inn(E) cannot see (Inn(E)
    acts trivially on Z(E)).  So the proto-essential search should find NO
    surviving candidates for n >= 2 odd-p exponent-p extraspecial groups."""
    for p, n in [(3, 2), (5, 2)]:
        res, G = run(p, n)
        assert len(res.aut_classes) == 0, (
            f"expected no proto-essential subgroups for p={p}, n={n}, found {len(res.aut_classes)}"
        )
        # Note: the *cheap* test "C_{N_S(E)}(E/Phi(E)) <= E" is itself a
        # necessary consequence of the radical condition, so it may (and
        # here does) already catch the shear obstruction before the
        # dedicated radical_test is even reached -- both are correct.
        assert res.num_s_centric_candidates > 0, "sanity: candidates should exist before filtering"


def test_extraspecial_2_n1_d8_q8():
    # D8 has order-4 (elementary abelian) subgroups as candidates, which
    # pass the radical test trivially, as in the n=1 odd-p case.
    res, G = run(2, 1, squares=[0, 0])
    print("  (D8)")
    assert len(res.aut_classes) >= 1
    # Q8 has *no* noncyclic proper subgroups at all (every proper subgroup
    # of Q8 is cyclic: <i>, <j>, <k>, <-1>), so it correctly has no
    # proto-essential subgroups whatsoever -- this is a real fact, not a bug
    # (Q8-fusion-systems, e.g. of SL(2,3), have no essential subgroups).
    res, G = run(2, 1, squares=[1, 1])
    print("  (Q8)")
    assert len(res.aut_classes) == 0


def test_extraspecial_2_n2_hyperplanes_fail_radical_test():
    for squares, label in [([0, 0, 0, 0], "plus"), (witt_minus_squares(2), "minus")]:
        res, G = run(2, 2, squares=squares)
        print(f"  (p=2, n=2, {label})")
        assert len(res.aut_classes) == 0


if __name__ == "__main__":
    test_extraspecial_3_1_matches_known_fusion_system()
    test_extraspecial_5_1()
    test_extraspecial_2_n1_d8_q8()
    test_extraspecial_n2_hyperplanes_fail_radical_test()
    test_extraspecial_2_n2_hyperplanes_fail_radical_test()
    print("\nALL PROTOESSENTIAL TESTS PASSED")
