"""Tests for fastfusion.constructions, cross-checked against GAP."""
import sys
import os

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from fastfusion.pcgroup import PCPresentation, CompiledPGroup
from fastfusion import constructions as C
from gap_oracle import gap_invariants


def check(pres, label, **expect):
    G = CompiledPGroup(pres)
    gi = gap_invariants(pres)
    print(f"{label}: order={gi.order} center={gi.center_order} derived={gi.derived_order} "
          f"class={gi.nilpotency_class} exp={gi.exponent} id={gi.id_group}")
    assert gi.order == G.order == pres.p ** pres.n
    for key, val in expect.items():
        got = getattr(gi, key)
        assert got == val, f"{label}: expected {key}={val}, got {got}"
    # engine-side cross-check of center/derived subgroup sizes
    assert len(G.center()) == gi.center_order
    assert len(G.derived_subgroup()) == gi.derived_order
    return G, gi


def test_extraspecial_odd_p():
    for p, n in [(3, 1), (3, 2), (5, 1), (5, 2), (7, 1)]:
        pres = C.extraspecial(p, n)
        check(pres, f"extraspecial({p},{n})", center_order=p, derived_order=p,
              nilpotency_class=2, exponent=p)


def test_extraspecial_2_plus_minus():
    # n=1: plus=D8 (id [8,3]), minus=Q8 (id [8,4])
    check(C.extraspecial_plus(2, 1), "extraspecial_plus(2,1)=D8", id_group=[8, 3])
    check(C.extraspecial_minus(1), "extraspecial_minus(1)=Q8", id_group=[8, 4])
    # n=2, order 32: plus and minus types should both have center order 2,
    # derived order 2, class 2, but DIFFERENT element-order profiles (the
    # Witt index controls how many noncentral involutions there are), hence
    # different IdGroup.
    Gp, gip = check(C.extraspecial_plus(2, 2), "extraspecial_plus(2,2)", center_order=2,
                     derived_order=2, nilpotency_class=2)
    Gm, gim = check(C.extraspecial_minus(2), "extraspecial_minus(2)", center_order=2,
                     derived_order=2, nilpotency_class=2)
    assert gip.id_group != gim.id_group
    assert gip.element_order_profile != gim.element_order_profile
    print(f"plus profile: {gip.element_order_profile}")
    print(f"minus profile: {gim.element_order_profile}")


def test_direct_product():
    c2 = PCPresentation(n=1, p=2, names=["t"])   # trivial power word -> order 2
    base = C.extraspecial(2, 2)   # order 32, center order 2
    prod = C.direct_product([base, c2])
    G, gi = check(prod, "extraspecial(2,2) x C2", nilpotency_class=2)
    assert gi.order == 64
    assert gi.center_order == 4   # Z(A x B) = Z(A) x Z(B) = 2*2
    assert gi.derived_order == 2  # (A x B)' = A' x B' = 2*1


def test_extraspecial_5_7_builds_and_matches_structure():
    """The actual showcase group: extraspecial 5^(1+6) = 5^7.  We only check
    structural invariants quickly here (not a full GAP cross-check, since
    order 5^7 is outside GAP's small-group library and a *literal*
    GAP-side FromTheLeftCollector build of a 13-generator presentation at
    this size would itself take real time) -- compiling it here exercises
    the exact code path used in the showcase script."""
    import time
    pres = C.extraspecial(5, 3)
    t0 = time.time()
    G = CompiledPGroup(pres)
    dt = time.time() - t0
    assert G.order == 5 ** 7
    Z = G.center()
    Sder = G.derived_subgroup()
    assert len(Z) == 5
    assert len(Sder) == 5
    print(f"extraspecial(5,3): order 5^7={G.order}, compiled in {dt:.1f}s, "
          f"|Z(S)|={len(Z)}, |S'|={len(Sder)}")


if __name__ == "__main__":
    test_extraspecial_odd_p()
    test_extraspecial_2_plus_minus()
    test_direct_product()
    test_extraspecial_5_7_builds_and_matches_structure()
    print("\nALL CONSTRUCTION TESTS PASSED")
