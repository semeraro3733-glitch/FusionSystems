"""Cross-validation against GAP: given a PCPresentation, build the *same*
group in GAP directly as a polycyclic-collector group (via the `polycyclic`
package's `FromTheLeftCollector`), matching our PCGS exactly, generator for
generator -- no coset enumeration, no risk of GAP failing to recognise the
group as finite/nilpotent.  Used only for testing; the production code never
calls GAP.

Sign conventions, pinned down empirically against GAP (see commit message /
paper for the derivation):
  * SetPower(coll, g, w) sets  x_g^p = w  directly (no inversion needed).
  * SetCommutator(coll, h, g, w) requires h > g and sets Comm(h,g) = w, where
    Comm(a,b) = a^-1 b^-1 a b (matching our own convention).  Since our
    relations are stored for the *smaller* index first ([x_i,x_j], i<j), we
    must instead supply GAP with Comm(j+1, i+1) = [x_i,x_j]^{-1}, computed by
    our own (GAP-independent) PCPresentation.collect/vector_inverse.
"""
from __future__ import annotations

import json
import os
import subprocess
import tempfile
from dataclasses import dataclass
from typing import List, Optional

from fastfusion.pcgroup import PCPresentation


def _flat_gap_word(letters: List[int]) -> str:
    """[g1,g2,g3] (each exponent 1) -> GAP flat word '[g1,1,g2,1,g3,1]'."""
    parts = []
    for g in letters:
        parts.append(str(g))
        parts.append("1")
    return "[" + ",".join(parts) + "]"


def presentation_to_collector_gap(pres: PCPresentation) -> str:
    n, p = pres.n, pres.p
    lines = [
        'LoadPackage("polycyclic");',
        f'coll := FromTheLeftCollector({n});',
    ]
    for i in range(n):
        lines.append(f'SetRelativeOrder(coll, {i+1}, {p});')
    for i in range(n):
        w = pres.power_words[i]
        lines.append(f'SetPower(coll, {i+1}, {_flat_gap_word(w)});')
    for (i, j), w in pres.comm_words.items():
        v = pres.collect(w)
        vi = pres.vector_inverse(v)
        inv_word = pres.vector_to_word(vi)
        # Comm(j+1, i+1) = inv_word   (j+1 > i+1, as SetCommutator requires)
        lines.append(f'SetCommutator(coll, {j+1}, {i+1}, {_flat_gap_word(inv_word)});')
    lines.append('UpdatePolycyclicCollector(coll);')
    lines.append('if not IsConfluent(coll) then Print("NOT CONFLUENT\\n"); fi;')
    lines.append('G := PcpGroupByCollectorNC(coll);')
    return "\n".join(lines)


@dataclass
class GapInvariants:
    order: int
    center_order: int
    derived_order: int
    frattini_order: int
    nilpotency_class: int
    exponent: int
    num_conj_classes: int
    element_order_profile: List[List[int]]
    id_group: Optional[List[int]]
    rank: int


_TEMPLATE = r"""
{defn}
S := Image(IsomorphismPcGroup(G));
idg_avail := IdGroupsAvailable(Size(S));
if idg_avail then idg := IdGroup(S); else idg := [0,0]; fi;
eop := Collected(List(AsList(S), Order));
outstream := OutputTextFile("{outpath}", false);
PrintTo(outstream, "{{");
PrintTo(outstream, "\"order\":", Size(S), ",");
PrintTo(outstream, "\"center_order\":", Size(Center(S)), ",");
PrintTo(outstream, "\"derived_order\":", Size(DerivedSubgroup(S)), ",");
PrintTo(outstream, "\"frattini_order\":", Size(FrattiniSubgroup(S)), ",");
PrintTo(outstream, "\"nilpotency_class\":", NilpotencyClassOfGroup(S), ",");
PrintTo(outstream, "\"exponent\":", Exponent(S), ",");
PrintTo(outstream, "\"num_conj_classes\":", Length(ConjugacyClasses(S)), ",");
PrintTo(outstream, "\"element_order_profile\":", eop, ",");
PrintTo(outstream, "\"id_group_available\":", idg_avail, ",");
PrintTo(outstream, "\"id_group\":", idg, ",");
PrintTo(outstream, "\"rank\":", Rank(S));
PrintTo(outstream, "}}");
CloseStream(outstream);
QUIT;
"""


def gap_invariants(pres: PCPresentation, timeout: int = 180) -> GapInvariants:
    defn = presentation_to_collector_gap(pres)
    with tempfile.TemporaryDirectory() as d:
        outpath = os.path.join(d, "out.json")
        script = _TEMPLATE.format(defn=defn, outpath=outpath)
        gpath = os.path.join(d, "script.g")
        with open(gpath, "w") as f:
            f.write(script)
        proc = subprocess.run(["gap", "-q", gpath], timeout=timeout,
                               capture_output=True, text=True)
        if not os.path.exists(outpath):
            raise RuntimeError(f"GAP failed: stdout={proc.stdout}\nstderr={proc.stderr}")
        with open(outpath) as f:
            raw = f.read()
    data = json.loads(raw)
    idg = data["id_group"] if data["id_group_available"] else None
    return GapInvariants(
        order=data["order"], center_order=data["center_order"],
        derived_order=data["derived_order"], frattini_order=data["frattini_order"],
        nilpotency_class=data["nilpotency_class"], exponent=data["exponent"],
        num_conj_classes=data["num_conj_classes"],
        element_order_profile=sorted(data["element_order_profile"]),
        id_group=idg, rank=data["rank"],
    )
