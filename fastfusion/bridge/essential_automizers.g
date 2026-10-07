## GAP-side helper for the second half of the pipeline (fclass.py): given a
## group SmallGroup(size,idx) and an explicit subgroup E of it (specified by
## generators, as exponent vectors w.r.t. the *same* refined PCGS that
## export_batch.g used -- so Python and GAP agree on what "generator i"
## means), compute:
##   (a) Aut(E) and Out(E) = Aut(E)/Inn(E),
##   (b) the image of Aut_S(E) in Out(E) (supplied by the caller, as
##       generators of Aut_S(E) acting on E, again as exponent vectors --
##       this is cheap for us to compute in Python already via the
##       conjugation machinery, so there is no need to recompute N_S(E) in
##       GAP),
##   (c) every subgroup T with (image of Aut_S(E)) <= T <= Out(E) such that
##       T has a *proper* strongly p-embedded subgroup (checked directly
##       from the definition: H < T, Sylow_p(T) <= H up to conjugacy, and
##       N_T(P) <= H for every nontrivial p-subgroup P <= H) -- these are
##       exactly the candidates for Out_F(E) that could make E essential.
##
## Usage: Read this file, then call
##   EssentialAutomizerCandidates(size, idx, Egens, AutSEgens, outfile)
## where Egens and AutSEgens are GAP lists of exponent vectors (lists of
## p-adic digits of the same length as the group's rank), AutSEgens meaning
## the images of Egens under each chosen generator of Aut_S(E) (one record
## per generator: a list of images, each an exponent vector of an element
## of E).

LoadPackage("sglppow");

BuildRefinedPcgs := function(G)
    local lcs, c, gens, i, Hi, Hi1, quo, Q, csQ, j, repQ, rep, m;
    lcs := LowerCentralSeriesOfGroup(G);
    c := Length(lcs) - 1;
    gens := [];
    for i in [1..c] do
        Hi := lcs[i]; Hi1 := lcs[i+1];
        quo := NaturalHomomorphismByNormalSubgroup(Hi, Hi1);
        Q := Image(quo, Hi);
        csQ := CompositionSeries(Q);
        m := Length(csQ) - 1;
        for j in [1..m] do
            repQ := First(AsList(csQ[j]), x -> not x in csQ[j+1]);
            rep := PreImagesRepresentative(quo, repQ);
            Add(gens, rep);
        od;
    od;
    return gens;
end;

## Is H (a proper subgroup of T) strongly p-embedded in T?
IsStronglyPEmbedded := function(T, H, p)
    local sylT, P, allP;
    if Size(H) = Size(T) then return false; fi;
    sylT := SylowSubgroup(T, p);
    # H must contain *some* Sylow p-subgroup of T, i.e. a T-conjugate of
    # sylT; iterating a conjugacy class of subgroups yields the actual
    # conjugate subgroups themselves (not further "classes" needing their
    # own Representative()).
    if not ForAny(ConjugacyClassSubgroups(T, sylT), c -> IsSubset(H, c)) then
        return false;
    fi;
    # every nontrivial p-subgroup of H has its T-normalizer inside H
    allP := Filtered(AllSubgroups(H), P -> Size(P) > 1 and Size(P) mod p = 0
                      and IsPGroup(P) and PrimePGroup(P) = p);
    for P in allP do
        if not IsSubset(H, Normalizer(T, P)) then return false; fi;
    od;
    return true;
end;

HasStronglyPEmbeddedSubgroup := function(T, p)
    local subs, H;
    if Size(T) mod p <> 0 then return false; fi;
    for H in AllSubgroups(T) do
        if Size(H) < Size(T) and IsStronglyPEmbedded(T, H, p) then
            return true;
        fi;
    od;
    return false;
end;

EssentialAutomizerCandidates := function(size, idx, Egens, AutSEimages, outfile)
    local G, p, gens, pcgs, EgenElts, E, AutE, InnE, OutE, hom, AutSEinOut,
          genE, autSgen, imgs, phi, k, candT, results, T, stream, i, j, img;

    G := SmallGroup(size, idx);
    p := Factors(size)[1];
    gens := BuildRefinedPcgs(G);
    pcgs := PcgsByPcSequence(FamilyObj(One(G)), gens);

    EgenElts := List(Egens, v -> PcElementByExponents(pcgs, v));
    E := Subgroup(G, EgenElts);

    AutE := AutomorphismGroup(E);
    InnE := InnerAutomorphismsAutomorphismGroup(AutE);
    hom := NaturalHomomorphismByNormalSubgroup(AutE, InnE);
    OutE := Image(hom);

    # the images of Aut_S(E)'s generators, as automorphisms of E, mapped
    # into Out(E).
    AutSEinOut := [];
    for autSgen in AutSEimages do
        imgs := List(autSgen, v -> PcElementByExponents(pcgs, v));
        phi := GroupHomomorphismByImages(E, E, EgenElts, imgs);
        Add(AutSEinOut, Image(hom, phi));
    od;
    k := SubgroupNC(OutE, AutSEinOut);

    results := [];
    for T in AllSubgroups(OutE) do
        if IsSubset(T, k) and HasStronglyPEmbeddedSubgroup(T, p) then
            Add(results, T);
        fi;
    od;

    stream := OutputTextFile(outfile, false);
    SetPrintFormattingStatus(stream, false);
    PrintTo(stream, "{\"size\":", size, ",\"idx\":", idx, ",\"candidates\":[");
    for i in [1..Length(results)] do
        if i > 1 then PrintTo(stream, ","); fi;
        T := results[i];
        PrintTo(stream, "[");
        for j in [1..Length(GeneratorsOfGroup(T))] do
            if j > 1 then PrintTo(stream, ","); fi;
            phi := PreImagesRepresentative(hom, GeneratorsOfGroup(T)[j]);
            PrintTo(stream, "[");
            for img in List(EgenElts, x -> ExponentsOfPcElement(pcgs, Image(phi, x))) do
                PrintTo(stream, "[", JoinStringsWithSeparator(List(img,String),","), "],");
            od;
            PrintTo(stream, "]");
        od;
        PrintTo(stream, "]");
    od;
    PrintTo(stream, "]}\n");
    CloseStream(stream);
end;
