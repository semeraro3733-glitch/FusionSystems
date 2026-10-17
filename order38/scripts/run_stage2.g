# Stage 2 over the Stage 1b survivors in order of difficulty.
#   gap -c 'Read("run_stage2.g"); FS38_RunStage2All( maxElab );'
# Reads data/stage1b_survivors.txt (analyze1b.py), treats the groups whose
# largest elementary abelian proto-essential subgroup has order <= maxElab,
# skips the ids with an existing logs/stage2_<id>.log ending in DONE, and
# appends a summary line per group to data/stage2.txt.
Read( "/home/user/FusionSystems/order38/scripts/stage2.g" );
FS38_Stage2Done := function( id )
    local f, s;
    f := Concatenation( "/home/user/FusionSystems/order38/logs/stage2_", String( id ), ".log" );
    if not IsExistingFile( f ) then return false; fi;
    s := StringFile( f );
    return s <> fail and PositionSublist( s, "DONE" ) <> fail;
end;
FS38_RunStage2All := function( maxElab )
    local f, line, parts, id, S, r, out, elab, m, protos, t;
    f := InputTextFile( "/home/user/FusionSystems/order38/data/stage1b_survivors.txt" );
    line := ReadLine( f );
    while line <> fail do
        parts := SplitString( line, ";" );
        line := ReadLine( f );
        if Length( parts ) < 3 or Int( parts[1] ) = fail then continue; fi;
        id := Int( parts[1] );
        # largest elementary abelian proto-essential: entries [order,index,true,...]
        elab := 1;
        for m in SplitString( parts[3], " " ) do
            protos := SplitString( Filtered( m, c -> not c in "[]" ), "," );
            if Length( protos ) >= 3 and protos[3] = "true" and Int( protos[1] ) > elab then elab := Int( protos[1] ); fi;
        od;
        if elab > maxElab then continue; fi;
        if FS38_Stage2Done( id ) then continue; fi;
        S := SmallGroup( 6561, id );
        t := Runtime();
        r := CALL_WITH_CATCH( FS38_Stage2, [ S, Concatenation( "SmallGroup(6561,", String( id ), ")" ),
                  Concatenation( "/home/user/FusionSystems/order38/logs/stage2_", String( id ), ".log" ), rec() ] );
        out := OutputTextFile( "/home/user/FusionSystems/order38/data/stage2.txt", true ); SetPrintFormattingStatus( out, false );
        if r[1] then
            AppendTo( out, id, ";", Length( r[2].systems ), ";", Runtime() - t, ";",
                      JoinStringsWithSeparator( List( r[2].descriptions, FS38_DescLine ), " | " ), "\n" );
        else
            AppendTo( out, id, ";error;", String( r[2] ), "\n" );
            AppendTo( Concatenation( "/home/user/FusionSystems/order38/logs/stage2_", String( id ), ".log" ), "ERROR ", String( r[2] ), "\n" );
        fi;
        CloseStream( out );
    od;
    CloseStream( f );
end;
