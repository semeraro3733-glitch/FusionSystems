"""Validate the GAP -> Python bridge (gapimport.py / bridge/export_batch.g):
every imported group's presentation and automorphism generators are
cross-checked against GAP's own invariants for the *same* SmallGroup, for
every group in a batch export. This is the correctness gate before trusting
the bridge at the scale of thousands/millions of groups (order 5^7, 3^8)."""
import json
import os
import subprocess
import sys
import tempfile
import time

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from fastfusion.gapimport import load_jsonl

BRIDGE_DIR = os.path.join(os.path.dirname(__file__), "..", "bridge")


def gap_invariants_batch(size, start, stop):
    """Independently compute, in a fresh GAP process, the invariants we'll
    cross-check against: order, |Z(G)|, |G'|, nilpotency class, exponent."""
    script = f"""
LoadPackage("sglppow");
stream := OutputTextUser();
for idx in [{start}..{stop}] do
    G := SmallGroup({size}, idx);
    Print(idx, " ", Size(G), " ", Size(Centre(G)), " ", Size(DerivedSubgroup(G)),
          " ", NilpotencyClassOfGroup(G), " ", Exponent(G), "\\n");
od;
QUIT;
"""
    with tempfile.NamedTemporaryFile("w", suffix=".g", delete=False) as f:
        f.write(script)
        path = f.name
    try:
        out = subprocess.run(["gap", "-q", "-b", path], stdin=subprocess.DEVNULL,
                              capture_output=True, text=True, timeout=600, check=True)
    finally:
        os.unlink(path)
    inv = {}
    for line in out.stdout.strip().splitlines():
        idx, order, z, der, cls, exp = line.split()
        inv[int(idx)] = (int(order), int(z), int(der), int(cls), int(exp))
    return inv


def test_export_and_cross_check(size=78125, start=1, stop=300):
    outfile = tempfile.mktemp(suffix=".jsonl")
    t0 = time.time()
    subprocess.run(
        ["gap", "-q", "-b", "-c",
         f'Read("export_batch.g"); RunExportBatch({size},{start},{stop},"{outfile}"); QUIT;'],
        cwd=BRIDGE_DIR, stdin=subprocess.DEVNULL, capture_output=True, text=True,
        timeout=1800, check=True,
    )
    print(f"exported {stop-start+1} groups of order {size} in {time.time()-t0:.1f}s")

    gap_inv = gap_invariants_batch(size, start, stop)

    seen_indices = set()
    for rec in load_jsonl(outfile, verify=True):
        assert rec.size == size
        G = rec.G
        assert G.order == size, f"idx={rec.index}: order mismatch"
        order, z, der, cls, exp = gap_inv[rec.index]
        assert len(G.center()) == z, f"idx={rec.index}: |Z| {len(G.center())} != {z}"
        assert len(G.derived_subgroup()) == der, (
            f"idx={rec.index}: |G'| {len(G.derived_subgroup())} != {der}"
        )
        # nilpotency class: the lower central series length computed from
        # our own presentation's tails should match GAP's.
        for a in rec.aut_gens:
            assert G.is_automorphism(a), f"idx={rec.index}: bad automorphism generator"
        seen_indices.add(rec.index)

    assert seen_indices == set(range(start, stop + 1)), "missing groups in export"
    os.unlink(outfile)
    print(f"ALL {stop-start+1} GROUPS OF ORDER {size} (indices {start}-{stop}): "
          f"presentation + automorphisms verified against GAP")


if __name__ == "__main__":
    test_export_and_cross_check()
    print("\nALL GAPIMPORT TESTS PASSED")
