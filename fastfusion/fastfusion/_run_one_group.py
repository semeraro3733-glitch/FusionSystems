#!/usr/bin/env python3
"""Standalone worker: run the full proto-essential-subgroup pipeline on one
exported group record (the schema bridge/export_batch.g + gapimport.py
agree on) and print the JSON result line to stdout.

Deliberately run as its own OS process (invoked by batchrun.py via
subprocess, not as a multiprocessing/thread pool worker) so the driver can
enforce a wall-clock timeout per group by killing this process outright --
a hang or crash on one pathological group can never take down a multi-day
batch run.
"""
import json
import os
import sys
import time
import traceback

sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

from fastfusion.gapimport import presentation_from_record, aut_gens_from_record
from fastfusion.pcgroup import CompiledPGroup
from fastfusion.protoessential import proto_essential_subgroups


def run(rec: dict) -> dict:
    t0 = time.time()
    try:
        pres = presentation_from_record(rec)
        G = CompiledPGroup(pres)
        aut_gens = aut_gens_from_record(rec, G)
        res = proto_essential_subgroups(pres, G=G, aut_gens=aut_gens, verbose=False)
        essentials = [
            {"order": len(members), "gens": [list(G.elements[g]) for g in gens]}
            for members, gens in res.aut_classes
        ]
        return {
            "size": rec["size"], "index": rec["index"], "n": rec["n"], "p": rec["p"],
            "num_raw_candidates": res.num_raw_candidates,
            "num_s_centric_candidates": res.num_s_centric_candidates,
            "num_cheap_pass": res.num_cheap_pass,
            "num_aut_orbits": res.num_aut_orbits,
            "num_orbits_leaving_candidates": res.num_orbits_leaving_candidates,
            "num_essential_aut_classes": len(res.aut_classes),
            "num_essential_s_classes": len(res.s_classes),
            "essentials": essentials,
            "time_seconds": time.time() - t0,
            "error": None,
        }
    except Exception as e:
        return {
            "size": rec.get("size"), "index": rec.get("index"),
            "error": f"{type(e).__name__}: {e}",
            "traceback": traceback.format_exc(),
            "time_seconds": time.time() - t0,
        }


def main():
    with open(sys.argv[1]) as f:
        rec = json.load(f)
    print(json.dumps(run(rec)))


if __name__ == "__main__":
    main()
