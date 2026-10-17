#############################################################################
##
##  stage2.g      Stage 2: the saturated fusion systems with O_3(F) = 1 and
##                O^3(F) = F on one group of order 3^8, with a description of
##                each system and a comparison with reference systems.
##
Read( "/home/user/FusionSystems/order38/scripts/reduce.g" );
Read( "/home/user/FusionSystems/order38/scripts/known_groups.g" );

# a readable description of a subgroup E and of a fusion system F
FS38_SubgroupDesc := function( E )
    local s;
    if IsElementaryAbelian( E ) then return Concatenation( "3^", String( LogInt( Size( E ), 3 ) ) ); fi;
    if IsAbelian( E ) then return JoinStringsWithSeparator( List( AbelianInvariants( E ), String ), "x" ); fi;
    if Size( E ) = 27 and Exponent( E ) = 3 then return "3^{1+2}_+"; fi;
    if Size( E ) = 27 then return "3^{1+2}_-"; fi;
    s := Concatenation( "3^", String( LogInt( Size( E ), 3 ) ), " (|Z|=", String( Size( Center( E ) ) ), ", cl ", String( NilpotencyClassOfGroup( E ) ), ", exp ", String( Exponent( E ) ), ")" );
    if Size( E ) <= 729 then s := Concatenation( s, " #", String( IdGroup( E )[2] ) ); fi;
    return s;
end;

FS38_OutDesc := function( A, E )
    # A: group of automorphisms of E (model subgroup via handle) -> Out_F(E) description
    local h, q, O;
    h := FS_AutHandle( E );
    q := FS_OutData( E ).q;
    O := Image( q, A );
    if Size( O ) <= 2000 and Size( O ) <> 1024 then return StructureDescription( O ); fi;
    return Concatenation( "order ", String( Size( O ) ) );
end;

FS38_Describe := function( F )
    local S, r, i, E, hE, A, cpl, comps, c;
    S := F!.S;
    r := rec( OutFS := OutFSOrder( F ), OutFSdesc := "", ess := [] );
    cpl := FS_ComplementData( F );
    if Size( cpl.model ) <= 2000 then r.OutFSdesc := StructureDescription( cpl.model ); else r.OutFSdesc := Concatenation( "order ", String( Size( cpl.model ) ) ); fi;
    # the essential subgroups up to F-conjugacy (the stored list may contain
    # several S-class representatives of one F-class); nS is the number of
    # S-classes in the F-class
    comps := [];
    for i in [ 1 .. Length( F!.ess ) ] do
        E := F!.ess[i];
        c := Set( FS_ComponentOf( F, FS_NodeOf( F, E )[1] ) );
        if c in comps then continue; fi;
        Add( comps, c );
        hE := FS_AutHandle( E );
        A := FS_AutSubgroup( hE, Concatenation( FS_AutSGenerators( F, E ), F!.essauts[i] ) );
        Add( r.ess, rec( order := Size( E ), desc := FS38_SubgroupDesc( E ), index := Index( Normalizer( S, E ), E ),
                         nS := Length( c ),
                         OutFE := Size( A ) / Index( E, Center( E ) ), OutFEdesc := FS38_OutDesc( A, E ) ) );
    od;
    return r;
end;

# run AllFusionSystems on SmallGroup( 6561, id ) (or a given group), log to file
FS38_DescLine := function( d )
    return Concatenation( "|Out_F(S)| = ", String( d.OutFS ), " (", d.OutFSdesc, "); essentials: ",
              JoinStringsWithSeparator( List( d.ess, e -> Concatenation( e.desc, " [", String( e.nS ), " S-class(es), N:E=", String( e.index ), ", Out_F(E) = ", e.OutFEdesc, " of order ", String( e.OutFE ), "]" ) ), "; " ) );
end;

FS38_Stage2 := function( S, name, logfile, opts )
    local t, L, F, d, res, out, cheap;
    out := OutputTextFile( logfile, false ); SetPrintFormattingStatus( out, false );
    AppendTo( out, "# Stage 2 for ", name, "\n" );
    t := Runtime();
    # the proto-essential candidates of Stage 1a (stronger tests than the
    # package's own), unless the caller supplies them
    if not IsBound( opts.protoCandidates ) then
        cheap := FS38_Cheap( S );
        if cheap.status <> "survive" then
            AppendTo( out, "# Stage 1a rejects the group: ", cheap.reason, "\n# 0 fusion systems\nDONE\n" );
            CloseStream( out );
            return rec( systems := [], descriptions := [], time := Runtime() - t );
        fi;
        opts := ShallowCopy( opts );
        opts.protoCandidates := List( cheap.cands, c -> c.E );
        # complete automizer candidates from the GL_n(3) tables where available
        if not IsBound( opts.candidates ) then opts.candidates := FS38_TableCandidates; fi;
        AppendTo( out, "# ", Length( cheap.cands ), " candidate essential subgroups from Stage 1a, orders ", List( cheap.cands, c -> c.order ), "\n" );
    fi;
    FS_Diagnostics.incomplete := false; FS_Diagnostics.messages := [];
    L := AllFusionSystems( S, opts );
    AppendTo( out, "# ", Length( L ), " fusion systems (", Runtime() - t, " ms)\n" );
    if FS_Diagnostics.incomplete then
        AppendTo( out, "# WARNING: the enumeration of automizer candidates was incomplete: ",
                  JoinStringsWithSeparator( FS_Diagnostics.messages, "; " ), "\n" );
    fi;
    res := [];
    for F in L do
        d := FS38_Describe( F );
        Add( res, d );
        AppendTo( out, "F: ", FS38_DescLine( d ), "\n" );
    od;
    AppendTo( out, "DONE\n" );
    CloseStream( out );
    return rec( incomplete := FS_Diagnostics.incomplete, systems := L, descriptions := res, time := Runtime() - t );
end;
