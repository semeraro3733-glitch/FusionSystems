// Regression test: the fast proto-essential search agrees with the original
// Parker-Semeraro search (which runs through all S-centric subgroups).
//
// Run from the directory containing FusionSystems.m:
//     magma tests/TestFastVsOriginal.m
//
// For these orders the GAP validation (validation/README.md) shows that every
// subgroup passing the original tests is among the candidates of Section 3 of
// arXiv:2607.24674, so both searches must return the same S-classes.

Attach("FusionSystems.m");

procedure Compare(G, ~failures)
    S:= PCGroup(G);
    A1, S1:= ProtoEssentialSubgroups(S: Fast:=true);
    A2, S2:= ProtoEssentialSubgroups(S: Fast:=false);
    ok:= #A1 eq #A2 and #S1 eq #S2 and
         forall{x: x in S1| exists{y: y in S2| #x eq #y and IsConjugate(S,x,y)}};
    if not ok then
        Append(~failures, G);
        printf "MISMATCH for %o: fast %o/%o, original %o/%o (Aut(S)/S-classes)\n",
            GroupName(G), #A1, #S1, #A2, #S2;
    end if;
end procedure;

failures:= [];
C3:= CyclicGroup(3);
Compare(WreathProduct(C3,C3), ~failures);
for q in [3^4, 3^5, 5^4] do
    t:= Cputime();
    for i in [1..NumberOfSmallGroups(q)] do
        G:= SmallGroup(q,i);
        if IsAbelian(G) then continue; end if;
        Compare(G, ~failures);
    end for;
    printf "order %o done in %o seconds\n", q, Cputime(t);
end for;

if #failures eq 0 then
    print "TestFastVsOriginal: PASSED";
else
    printf "TestFastVsOriginal: FAILED for %o groups\n", #failures;
end if;
quit;
