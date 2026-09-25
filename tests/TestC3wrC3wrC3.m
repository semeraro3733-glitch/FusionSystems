// Test of the fast proto-essential search on S = C3 wr C3 wr C3, the Sylow
// 3-subgroup of Sym(27), of order 3^13.
//
// Run from the directory containing FusionSystems.m:
//     magma tests/TestC3wrC3wrC3.m
//
// The expected values below were produced by the GAP port of
// ProtoEssentialSubgroups in validation/fast_protoessentials.g
// (see validation/run_c3wrc3wrc3.g and validation/README.md).
//
// Set RunOriginal:= true to also run the original Parker-Semeraro search,
// which computes all subgroups of S/Z(S) (order 3^12) and the automorphism
// group of every S-centric subgroup. Expect it to take a very long time.

RunOriginal:= false;

Attach("FusionSystems.m");

C3:= CyclicGroup(3);
W:= WreathProduct(WreathProduct(C3,C3),C3);
assert Degree(W) eq 27 and #W eq 3^13;   // so W is a Sylow 3-subgroup of Sym(27)
S:= PCGroup(W);

//////////////////////////////////////////////////////////////////////
// The candidates of Section 3.
//////////////////////////////////////////////////////////////////////
t:= Cputime();
L:= RefinedLowerCentralSeries(S);
assert #L eq 14 and forall{i: i in [1..13]| Index(L[i],L[i+1]) eq 3 and IsNormal(S,L[i+1])};
assert forall{i: i in [1..13]| CommutatorSubgroup(S,L[i]) subset L[i+1]};
Cands:= CentralSeriesCentralizers(S);
// The number of candidates depends on the choice of the refinement of the lower 
// central series (GAP's CompositionSeriesThrough gives 2638), the final result does not.
printf "CentralSeriesCentralizers: %o candidates in %o seconds\n", #Cands, Cputime(t);

//////////////////////////////////////////////////////////////////////
// The proto-essential subgroups.
//////////////////////////////////////////////////////////////////////
t:= Cputime();
AutReps, SReps:= ProtoEssentialSubgroups(S: Printing:=true);
tfast:= Cputime(t);
printf "ProtoEssentialSubgroups (Fast): %o Aut(S)-classes and %o S-classes in %o seconds\n",
    #AutReps, #SReps, tfast;

// For each Aut(S)-class: <log_3|E|, log_3|N_S(E):E|, |Z(E)|, |E:Phi(E)|, E normal in S>
Data:= {* <Valuation(#E,3), Valuation(Index(Normalizer(S,E),E),3), #Centre(E),
          Index(E,FrattiniSubgroup(E)), IsNormal(S,E)> : E in AutReps *};
Data;
SOrders:= {* Valuation(#E,3) : E in SReps *};
SOrders;

// EXPECTED VALUES PENDING: the GAP reference run (validation/run_c3wrc3wrc3.g) is
// still in progress; the assertions against it will be added here.

// The S-classes are pairwise distinct and every returned subgroup passes the
// original Parker-Semeraro proto-essential tests (as in the loop in the
// original AllProtoEssentials).
for i in [1..#SReps] do
    for j in [i+1..#SReps] do
        assert not IsConjugate(S,SReps[i],SReps[j]);
    end for;
end for;
function OriginalProtoEssentialTest(S,x)
    p:= 3;
    if x eq S or IsCyclic(x) or not IsSCentric(S,x) then return false; end if;
    Nx:=Normalizer(S,x);
    A:=AutYX(Nx,x);
    Ap:= SubMap(x`autopermmap,x`autoperm ,A);
    Innerp:= SubMap(x`autopermmap,x`autoperm ,Inn(x));
    if #(Ap meet pCore(x`autoperm, p)) ne #Innerp then return false; end if;
    P:= Index(Ap,Innerp);
    if Index(x,FrattiniSubgroup(x)) lt P^2 then return false; end if;
    SylTest, QC:=IsStronglypSylow(Ap/Innerp);
    if SylTest eq false then return false; end if;
    if QC eq false and IsSoluble(x`autoperm) then return false; end if;
    return true;
end function;
assert forall{E: E in SReps| OriginalProtoEssentialTest(S,E)};

//////////////////////////////////////////////////////////////////////
// Optionally: the original search.
//////////////////////////////////////////////////////////////////////
if RunOriginal then
    t:= Cputime();
    AutReps2, SReps2:= ProtoEssentialSubgroups(S: Fast:=false);
    printf "ProtoEssentialSubgroups (original): %o Aut(S)-classes and %o S-classes in %o seconds\n",
        #AutReps2, #SReps2, Cputime(t);
    assert forall{x: x in SReps| exists{y: y in SReps2| #x eq #y and IsConjugate(S,x,y)}};
end if;

print "TestC3wrC3wrC3: PASSED";
quit;
