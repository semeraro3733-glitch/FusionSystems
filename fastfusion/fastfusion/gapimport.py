"""Load groups exported by bridge/export_batch.g (one JSON object per line:
a PC presentation on generators refining the lower central series, plus a
generating set of Aut(G)) into this package's own engine.

This is the counterpart, for *arbitrary* p-groups pulled from GAP's
SmallGroups library (or the SglPPow/LiePRing extension for p^7, p>11, and
3^8), to constructions.py + autgroup.py, which only build the specific
symplectic-type families used in the hand-picked showcase. Nothing here
re-derives group theory GAP already gets right (presentations, Aut(G)); it
only translates GAP's output into the data structures the fast search
(protoessential.py, fclass.py) actually runs on.
"""
from __future__ import annotations

import json
from typing import Dict, Iterator, List, Tuple

from .pcgroup import CompiledPGroup, PCPresentation, Vector


def _vector_to_word(v: List[int], p: int) -> List[int]:
    w: List[int] = []
    for idx, e in enumerate(v):
        w.extend([idx + 1] * (e % p))
    return w


def presentation_from_record(rec: dict) -> PCPresentation:
    """Build a PCPresentation from one decoded JSON record."""
    n = rec["n"]
    p = rec["p"]
    power_words = [_vector_to_word(v, p) for v in rec["power_words"]]
    comm_words: Dict[Tuple[int, int], List[int]] = {}
    for i, j, v in rec["comm_words"]:
        comm_words[(i - 1, j - 1)] = _vector_to_word(v, p)
    return PCPresentation(n=n, p=p, power_words=power_words, comm_words=comm_words)


def aut_gens_from_record(rec: dict, G: CompiledPGroup) -> List[List[int]]:
    """Convert the exported automorphism images (exponent vectors) into
    this package's convention: aut_gens[k] is a length-n list of element
    *indices*, images[g] = index of phi_k(x_{g+1})."""
    p = G.p
    out = []
    for phi in rec["aut_gens"]:
        images = [G.index_of[tuple(e % p for e in v)] for v in phi]
        out.append(images)
    return out


class GapGroupRecord:
    """A single imported group: its CompiledPGroup and verified automorphism
    generators, plus GAP's own size/index for identification."""

    __slots__ = ("size", "index", "G", "aut_gens")

    def __init__(self, size: int, index: int, G: CompiledPGroup, aut_gens: List[List[int]]):
        self.size = size
        self.index = index
        self.G = G
        self.aut_gens = aut_gens


def load_jsonl(path: str, verify: bool = False) -> Iterator[GapGroupRecord]:
    """Stream groups from an export_batch.g output file.  `verify=True`
    additionally checks (expensively -- O(|G|) per automorphism) that every
    exported automorphism really is one, via `CompiledPGroup.is_automorphism`
    -- useful when first trusting a new GAP/library version, not needed on
    every run once that has been established for a given data source."""
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            rec = json.loads(line)
            pres = presentation_from_record(rec)
            G = CompiledPGroup(pres)
            aut_gens = aut_gens_from_record(rec, G)
            if verify:
                bad = [k for k, im in enumerate(aut_gens) if not G.is_automorphism(im)]
                if bad:
                    raise ValueError(
                        f"group size={rec['size']} index={rec['index']}: "
                        f"exported automorphism(s) {bad} failed verification"
                    )
            yield GapGroupRecord(rec["size"], rec["index"], G, aut_gens)
