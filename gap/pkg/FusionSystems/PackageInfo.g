#############################################################################
##
##  PackageInfo.g for the GAP 4 package FusionSystems
##
SetPackageInfo( rec(

PackageName := "FusionSystems",
Subtitle := "Saturated fusion systems on finite p-groups: construction, saturation tests and classification",
Version := "1.0.0",
Date := "16/10/2026",
License := "GPL-2.0-or-later",

Persons := [
  rec(
    LastName      := "Parker",
    FirstNames    := "Chris",
    IsAuthor      := true,
    IsMaintainer  := false,
    Institution   := "University of Birmingham",
  ),
  rec(
    LastName      := "Semeraro",
    FirstNames    := "Jason",
    IsAuthor      := true,
    IsMaintainer  := true,
    Email         := "semeraro3733@googlemail.com",
    Institution   := "University of Loughborough",
  ),
],

Status := "dev",

SourceRepository := rec(
    Type := "git",
    URL := "https://github.com/semeraro3733-glitch/FusionSystems"),
IssueTrackerURL := Concatenation( ~.SourceRepository.URL, "/issues" ),
PackageWWWHome  := ~.SourceRepository.URL,
README_URL      := Concatenation( ~.PackageWWWHome, "/blob/main/gap/pkg/FusionSystems/README.md" ),
PackageInfoURL  := Concatenation( ~.PackageWWWHome, "/blob/main/gap/pkg/FusionSystems/PackageInfo.g" ),
ArchiveURL      := Concatenation( ~.PackageWWWHome, "/releases/download/v", ~.Version, "/FusionSystems-", ~.Version ),
ArchiveFormats := ".tar.gz",

AbstractHTML := Concatenation(
  "The <span class=\"pkgname\">FusionSystems</span> package is a GAP 4 ",
  "implementation of the Parker-Semeraro algorithms for saturated fusion ",
  "systems on finite p-groups (arXiv:2003.01600), with the fast ",
  "proto-essential subgroup search of Gautam (arXiv:2607.24674) and a ",
  "saturation test that avoids constructing the fusion graph."),

PackageDoc := rec(
  BookName  := "FusionSystems",
  ArchiveURLSubset := ["doc"],
  HTMLStart := "doc/chap0.html",
  PDFFile   := "doc/manual.pdf",
  SixFile   := "doc/manual.six",
  LongTitle := "Saturated fusion systems on finite p-groups",
),

Dependencies := rec(
  GAP := ">= 4.11",
  NeededOtherPackages := [ [ "autpgrp", ">= 1.10" ] ],
  SuggestedOtherPackages := [ [ "smallgrp", ">= 1.4" ], [ "GAPDoc", ">= 1.6" ] ],
  ExternalConditions := [ ],
),

AvailabilityTest := ReturnTrue,

TestFile := "tst/testall.g",

Keywords := [ "fusion systems", "saturated fusion systems", "essential subgroups",
              "p-local finite groups", "Parker-Semeraro algorithm" ],

));
