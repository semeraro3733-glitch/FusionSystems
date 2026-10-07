"""Validate bridge/fusionsystem.g's direct-from-definition saturation checker
(IsSaturatedDatum) against ground truth with NO dependency on MAGMA or the
literature's published tables: the p-local fusion system of any actual
finite group G at a Sylow p-subgroup S is saturated by a classical theorem
(Broto-Levi-Oliver), so extracting (S, Aut_G(S), Aut_G(E)) directly from G
in GAP gives free, independently-checkable positive test cases, and
deliberately-inconsistent variants give negative ones.

This is the correctness gate for fusionsystem.g before it is trusted on any
real 5^7-scale data -- it is a from-scratch implementation (not a port of
FusionSystems.m/MAGMA, which was unavailable to cross-check against), so
this is the only available way to catch bugs before they'd otherwise show
up only as silently wrong fusion-system counts.
"""
import os
import subprocess
import sys

BRIDGE_DIR = os.path.join(os.path.dirname(__file__), "..", "bridge")

GAP_SCRIPT = r"""
Read("fusionsystem.g");

TestPSL3 := function(p)
    local G, Sgrp, ZS, allsubs, maxsubs, Ess, NGS, AutFSgens, NGE,
          AutFEssgens, datum, result;
    G := PSL(3,p);;
    Sgrp := SylowSubgroup(G,p);;
    ZS := Centre(Sgrp);;
    allsubs := AllSubgroups(Sgrp);;
    maxsubs := Filtered(allsubs, M -> Size(M) = Size(Sgrp)/p and IsSubset(M,ZS));;
    Ess := maxsubs[1];;
    NGS := Normalizer(G, Sgrp);;
    AutFSgens := List(GeneratorsOfGroup(NGS), g -> ConjugatorAutomorphism(Sgrp, g));;
    NGE := Normalizer(G, Ess);;
    AutFEssgens := List(GeneratorsOfGroup(NGE), g -> ConjugatorAutomorphism(Ess, g));;
    datum := FusionDatum(Sgrp, AutFSgens, [rec(grp := Ess, autFgens := AutFEssgens)]);;
    result := IsSaturatedDatum(datum);;
    Print("PSL3_", p, " ", result, "\n");
end;;

for p in [3,5,7] do TestPSL3(p); od;

## Negative control: Aut_F(S) taken as a Sylow p-subgroup of Aut(S) itself
## (so Inn(S), index p in it, cannot be Sylow-p in Aut_F(S)) -- this must
## violate the Sylow axiom at S and so must NOT be accepted as saturated.
Sgrp := SmallGroup(343,3);;
ZS := Centre(Sgrp);;
allsubs := AllSubgroups(Sgrp);;
maxsubs := Filtered(allsubs, M -> Size(M) = Size(Sgrp)/7 and IsSubset(M,ZS));;
Ess := maxsubs[1];;
FullAutS := AutomorphismGroup(Sgrp);;
SylAutS := SylowSubgroup(FullAutS, 7);;
FullAutEss := AutomorphismGroup(Ess);;
datum := FusionDatum(Sgrp, GeneratorsOfGroup(SylAutS),
             [rec(grp := Ess, autFgens := GeneratorsOfGroup(FullAutEss))]);;
Print("NEGATIVE ", IsSaturatedDatum(datum), "\n");

QUIT;
"""


def run_gap_validation():
    out = subprocess.run(
        ["gap", "-q", "-b"], input=GAP_SCRIPT, cwd=BRIDGE_DIR,
        capture_output=True, text=True, timeout=180, check=True,
    )
    return out.stdout


def test_psl3_ground_truth_and_negative_control():
    stdout = run_gap_validation()
    results = {}
    for line in stdout.strip().splitlines():
        parts = line.split()
        if len(parts) == 2:
            results[parts[0]] = parts[1]

    for p in (3, 5, 7):
        key = f"PSL3_{p}"
        assert key in results, f"missing output for {key}: {stdout}"
        assert results[key] == "true", (
            f"p={p}: the genuine fusion system of PSL(3,{p}) at its Sylow "
            f"subgroup must be saturated (classical theorem), but "
            f"IsSaturatedDatum said {results[key]}"
        )

    assert "NEGATIVE" in results, f"missing NEGATIVE output: {stdout}"
    assert results["NEGATIVE"] == "false", (
        "an Aut_F(S) whose p-part properly contains Inn(S) violates the "
        "Sylow axiom at S and must be rejected, but IsSaturatedDatum said "
        f"{results['NEGATIVE']}"
    )
    print("ALL FUSIONSYSTEM.G VALIDATION TESTS PASSED "
          "(PSL(3,3), PSL(3,5), PSL(3,7) ground truth + negative control)")


if __name__ == "__main__":
    test_psl3_ground_truth_and_negative_control()
