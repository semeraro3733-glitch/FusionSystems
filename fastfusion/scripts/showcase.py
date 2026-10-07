"""Showcase: run the fast proto-essential search (Gautam, Section 3) on the
groups discussed in the paper -- the extraspecial group of order 5^7 (not
considered by the original Parker-Semeraro small-group-library-based search,
which tops out at p^6 for p >= 5) and a family of 2-groups reaching order
2^10.

Usage:  python3 scripts/showcase.py <name>
  name in {5_7, 2_9_plus, 2_9_minus, 2_10}
"""
import json
import sys
import os
import time

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from fastfusion.pcgroup import CompiledPGroup, PCPresentation
from fastfusion import constructions as C
from fastfusion.autgroup import automorphism_generators
from fastfusion.protoessential import proto_essential_subgroups


def describe_classes(G, classes):
    out = []
    for members, gens in classes:
        N = G.normalizer(gens, subgroup_set=members)
        out.append({
            "order": len(members),
            "log_p_order": round(__import__("math").log(len(members), G.p), 3),
            "index_in_S": G.order // len(members),
            "out_S_order": len(N) // len(members),
            "normal_in_S": len(N) == G.order,
        })
    return out


def run(label, G, aut_gens):
    print(f"=== {label}: |S| = {G.order} = {G.p}^{G.n} ===", flush=True)
    t0 = time.time()
    res = proto_essential_subgroups(G.pres, G=G, aut_gens=aut_gens, verbose=True)
    dt = time.time() - t0
    print(f"--- {label}: TOTAL TIME {dt:.1f}s ---")
    print(f"    raw candidates (Theorem 3.6):        {res.num_raw_candidates}")
    print(f"    S-classes of S-centric candidates:   {res.num_s_centric_candidates}")
    print(f"    passing cheap (Aut(E)-free) tests:    {res.num_cheap_pass}")
    print(f"    Aut(S)-orbits on those:               {res.num_aut_orbits}")
    print(f"      (of which leave the candidate set): {res.num_orbits_leaving_candidates}")
    print(f"    PROTO-ESSENTIAL: {len(res.aut_classes)} up to Aut(S), "
          f"{len(res.s_classes)} up to S-conjugacy")
    details = describe_classes(G, res.aut_classes)
    for d in details:
        print(f"      class: |E|={d['order']} (p^{d['log_p_order']}), "
              f"|S:E|={d['index_in_S']}, |Out_S(E)|={d['out_S_order']}, "
              f"E normal in S: {d['normal_in_S']}")
    return {
        "label": label, "order": G.order, "p": G.p, "n": G.n,
        "time_seconds": dt,
        "num_raw_candidates": res.num_raw_candidates,
        "num_s_centric_candidates": res.num_s_centric_candidates,
        "num_cheap_pass": res.num_cheap_pass,
        "num_aut_orbits": res.num_aut_orbits,
        "num_orbits_leaving_candidates": res.num_orbits_leaving_candidates,
        "num_proto_essential_aut_classes": len(res.aut_classes),
        "num_proto_essential_s_classes": len(res.s_classes),
        "classes": details,
    }


def build_5_7():
    t0 = time.time()
    G, aut_gens = automorphism_generators(None, 5, 3)
    print(f"[build 5^7: compile {time.time()-t0:.1f}s, {len(aut_gens)} automorphism generators]")
    return G, aut_gens


def build_2_9(minus=False):
    squares = C.witt_minus_squares(4) if minus else None
    t0 = time.time()
    G, aut_gens = automorphism_generators(None, 2, 4, squares=squares)
    print(f"[build 2^9 ({'minus' if minus else 'plus'}): compile {time.time()-t0:.1f}s, "
          f"{len(aut_gens)} automorphism generators]")
    return G, aut_gens


def build_2_10():
    """C2 [order 2] x extraspecial(2,4) [order 2^9] = order 2^10.  The extra
    central involution is a genuine direct factor, not folded into the
    symplectic structure (see README for the two genuinely different
    order-2^{2n+2} families and why we use this one).  C2 is placed *first*
    in the product so that z (the extraspecial factor's derived subgroup)
    remains the last generator overall -- required so that S' = <z> is
    still an exact PCGS tail (see pcgroup.py / protoessential.py docstrings)
    after concatenation.  Automorphisms used for Aut(S)-orbit pruning: the
    Winter generators of the extraspecial factor (acting as the identity on
    the extra C2), plus the identity on C2 -- a verified but *not generally
    maximal* subgroup of Aut(S); see the module docstring of autgroup.py and
    the paper for why this does not affect correctness, only pruning
    strength."""
    base = C.extraspecial_plus(2, 4)
    c2 = PCPresentation(n=1, p=2, names=["t"])
    prod = C.direct_product([c2, base])
    t0 = time.time()
    G = CompiledPGroup(prod)
    print(f"[build 2^10: compile {time.time()-t0:.1f}s]")
    G_base, aut_gens_base = automorphism_generators(None, 2, 4)
    # lift: an automorphism image is a *group element*, identified by its
    # normal-form vector; embed the base factor's vectors into the product
    # by prepending the (fixed, zero) C2 coordinate, then look up the
    # resulting product-group index.  t itself maps to t.
    lifted = []
    for im in aut_gens_base:
        full = [G.gen_index[0]] + [
            G.index_of[(0,) + G_base.elements[idx]] for idx in im
        ]
        if G.is_automorphism(full):
            lifted.append(full)
    print(f"[build 2^10: lifted {len(lifted)}/{len(aut_gens_base)} automorphisms of the "
          f"extraspecial factor]")
    return G, lifted


def build_small(p, n, minus=False):
    squares = C.witt_minus_squares(n) if (p == 2 and minus) else None
    G, aut_gens = automorphism_generators(None, p, n, squares=squares)
    return G, aut_gens


BUILDERS = {
    "5_7": build_5_7,
    "2_9_plus": lambda: build_2_9(minus=False),
    "2_9_minus": lambda: build_2_9(minus=True),
    "2_10": build_2_10,
    "3_3": lambda: build_small(3, 1),
    "5_3": lambda: build_small(5, 1),
    "2_3_plus": lambda: build_small(2, 1, minus=False),
    "2_3_minus": lambda: build_small(2, 1, minus=True),
    "3_5": lambda: build_small(3, 2),
    "5_5": lambda: build_small(5, 2),
    "2_5_plus": lambda: build_small(2, 2, minus=False),
    "2_5_minus": lambda: build_small(2, 2, minus=True),
}


if __name__ == "__main__":
    names = sys.argv[1:] if len(sys.argv) > 1 else ["5_7"]
    outdir = os.path.join(os.path.dirname(__file__), "..", "results")
    os.makedirs(outdir, exist_ok=True)
    for name in names:
        G, aut_gens = BUILDERS[name]()
        result = run(name, G, aut_gens)
        with open(os.path.join(outdir, f"{name}.json"), "w") as f:
            json.dump(result, f, indent=2)
        print(f"\n[results written to results/{name}.json]")
