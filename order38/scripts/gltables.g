#############################################################################
##
##  gltables.g    Look-up tables: the subgroups H of GL_n(3) with a strongly
##                3-embedded subgroup, organised by their Sylow 3-subgroup T.
##
##  For an elementary abelian essential subgroup E = 3^n of a saturated
##  fusion system on a group S of order 3^8, Out_F(E) = Aut_F(E) <= GL_n(3)
##  has T = Aut_S(E) as a Sylow 3-subgroup, |T| <= 3^(8-n), and has a
##  strongly 3-embedded subgroup.  For n <= 4 the tables are complete (the
##  subgroups of GL_n(3) with 3-part at most 3^(8-n) are enumerated by the
##  cyclic extension method); for larger n only the non-3-soluble subgroups
##  are listed (perfect subgroup method).
##
LoadPackage( "FusionSystems", false );

FS38_AllowedT := function( T )
    return Size( T ) > 1 and ( IsCyclic( T ) or IsElementaryAbelian( T ) or ( Size( T ) = 27 and Exponent( T ) = 3 ) );
end;

# the largest normal p'-subgroup (assuming every nonabelian simple section has order divisible by p)
FS38_OpPrime := function( H, p )
    local R, pr;
    R := RadicalGroup( H );
    pr := Difference( PrimeDivisors( Size( R ) ), [ p ] );
    if Length( pr ) = 0 then return 1; fi;
    return Size( Core( R, HallSubgroup( R, pr ) ) );
end;

FS38_TypeString := function( T )
    if IsCyclic( T ) then return Concatenation( "C", String( Size( T ) ) ); fi;
    if IsElementaryAbelian( T ) then return Concatenation( "3^", String( LogInt( Size( T ), 3 ) ) ); fi;
    return "3^{1+2}_+";
end;

FS38_Describe := function( H )
    local s;
    if Size( H ) <= 2000 and Size( H ) <> 1024 then
        s := StructureDescription( H );
    elif Size( H ) <= 10^7 then
        s := StructureDescription( H );
    else
        s := Concatenation( "group of order ", String( Size( H ) ) );
    fi;
    return s;
end;


FS38_GLTable := function( n, complete )
    local G, iso, Gp, P, Ts, T, reps, res, cands, H, r, M, module, opts, t, V, mats, NT, cls, Tsyl, g;
    G := GL( n, 3 );
    iso := IsomorphismPermGroup( G );
    Gp := Image( iso );
    P := SylowSubgroup( Gp, 3 );
    Ts := Filtered( List( ConjugacyClassesSubgroups( P ), Representative ), T -> Size( T ) <= 3^( 8 - n ) and FS38_AllowedT( T ) );
    reps := [];
    for T in Ts do
        if ForAll( reps, R -> Size( R ) <> Size( T ) or RepresentativeAction( Gp, R, T ) = fail ) then Add( reps, T ); fi;
    od;
    SortBy( reps, Size );
    Info( InfoFusionSystems, 1, "GL(", n, ",3): ", Length( reps ), " classes of admissible 3-subgroups T of orders ", List( reps, Size ) );
    cls := fail;
    if complete then
        # all subgroups with 3-part at most 3^(8-n), computed once
        t := Runtime();
        if Size( Gp ) <= 10^8 then
            cls := List( ConjugacyClassesSubgroups( Gp ), Representative );
        else
            cls := List( ConjugacyClassesSubgroups( LatticeByCyclicExtension( Gp, function( H ) return FS_PPart( Size( H ), 3 ) <= 3^( 8 - n ); end ) ), Representative );
        fi;
        cls := Filtered( cls, H -> Size( H ) mod 3 = 0 and FS_PPart( Size( H ), 3 ) <= 3^( 8 - n ) );
        Info( InfoFusionSystems, 1, "  ", Length( cls ), " classes of subgroups of order divisible by 3 with 3-part <= 3^", 8 - n, " (", Runtime() - t, " ms)" );
    fi;
    res := [];
    for T in reps do
        t := Runtime();
        if cls <> fail then
            cands := [];
            for H in Filtered( cls, H -> FS_PPart( Size( H ), 3 ) = Size( T ) ) do
                Tsyl := SylowSubgroup( H, 3 );
                if IsNormal( H, Tsyl ) then continue; fi;
                g := RepresentativeAction( Gp, Tsyl, T );
                if g = fail then continue; fi;
                H := ConjugateSubgroup( H, g );
                if HasStronglyPEmbeddedSubgroup( H, 3 ) then Add( cands, H ); fi;
            od;
        else
            cands := FS_CandidatesInGroup( Gp, 3, T, true, rec() );
        fi;
        NT := Normalizer( Gp, T );
        # fuse under N_G(T) (FS_CandidatesInGroup already does, but be safe)
        r := rec( n := n, T := T, Tmats := List( GeneratorsOfGroup( T ), x -> PreImagesRepresentative( iso, x ) ),
                  Ttype := FS38_TypeString( T ), NT := Size( NT ), cands := [] );
        for H in cands do
            mats := List( GeneratorsOfGroup( H ), x -> PreImagesRepresentative( iso, x ) );
            module := GModuleByMats( mats, GF( 3 ) );
            Add( r.cands, rec( size := Size( H ), gens := mats,
                 desc := FS38_Describe( H ), NHT := Size( Normalizer( H, T ) ),
                 soluble := IsSolvableGroup( H ), O3prime := FS38_OpPrime( H, 3 ),
                 irreducible := MTX.IsIrreducible( module ),
                 composition := List( MTX.CompositionFactors( module ), m -> m.dimension ) ) );
        od;
        Info( InfoFusionSystems, 1, "  T of order ", Size( T ), " (", r.Ttype, "): ", Length( cands ), " candidates (", Runtime() - t, " ms)" );
        Add( res, r );
    od;
    return res;
end;

# write a table as GAP code (matrices) and as a LaTeX table
FS38_SaveGLTable := function( tab, gfile, texfile )
    local r, c, out, n, ints;
    n := tab[1].n;
    ints := m -> List( m, v -> List( v, IntFFE ) );
    out := OutputTextFile( gfile, false ); SetPrintFormattingStatus( out, false );
    AppendTo( out, "# GL(", n, ",3) look-up table: for each admissible T, the candidates H (generators as matrices over GF(3))\n" );
    AppendTo( out, "GLTABLE_", n, " := [\n" );
    for r in tab do
        AppendTo( out, "rec( Ttype := \"", r.Ttype, "\", Tmats := ", List( r.Tmats, ints ), ", NT := ", r.NT, ",\n   cands := [\n" );
        for c in r.cands do
            AppendTo( out, "     rec( size := ", c.size, ", desc := \"", c.desc, "\", NHT := ", c.NHT, ", soluble := ", c.soluble,
                      ", O3prime := ", c.O3prime, ", irreducible := ", c.irreducible, ", composition := ", c.composition,
                      ", gens := ", List( c.gens, ints ), " ),\n" );
        od;
        AppendTo( out, "   ] ),\n" );
    od;
    AppendTo( out, "];\n" );
    CloseStream( out );
    out := OutputTextFile( texfile, false ); SetPrintFormattingStatus( out, false );
    AppendTo( out, "% automatically generated by gltables.g\n" );
    AppendTo( out, "\\begin{longtable}{llrlrrll}\n\\caption{Subgroups $H$ of $\\GL_", n, "(3)$ with a strongly $3$-embedded subgroup, by Sylow $3$-subgroup $T$ (one $H$ per $N_{\\GL_", n, "(3)}(T)$-class; $|N_H(T)|$, $|O_{3'}(H)|$, whether $H$ is soluble, the dimensions of the composition factors of the natural module).}\\label{tab:gl", n, "}\\\\\n" );
    AppendTo( out, "\\toprule\n$T$ & $|N(T)|$ & $|H|$ & $H$ & $|N_H(T)|$ & $|O_{3'}(H)|$ & sol. & factors\\\\\n\\midrule\n\\endfirsthead\n\\toprule\n$T$ & $|N(T)|$ & $|H|$ & $H$ & $|N_H(T)|$ & $|O_{3'}(H)|$ & sol. & factors\\\\\n\\midrule\n\\endhead\n\\bottomrule\n\\endfoot\n" );
    for r in tab do
        if Length( r.cands ) = 0 then
            AppendTo( out, "$", r.Ttype, "$ & ", r.NT, " & \\multicolumn{6}{l}{none}\\\\\n" );
        fi;
        for c in r.cands do
            AppendTo( out, "$", r.Ttype, "$ & ", r.NT, " & ", c.size, " & \\texttt{", c.desc, "} & ", c.NHT, " & ", c.O3prime, " & ",
                      c.soluble, " & ", JoinStringsWithSeparator( List( c.composition, String ), "+" ), "\\\\\n" );
        od;
    od;
    AppendTo( out, "\\end{longtable}\n" );
    CloseStream( out );
end;
