# Stage 1b over the survivors of Stage 1a.
#   gap -c 'Read("run_stage1b.g"); FS38_RunStage1bAll();'
# Reads data/stage1a_survivors.txt (written by analyze.py), skips the ids
# already in data/stage1b.txt, appends one line per group to data/stage1b.txt.
Read( "/home/user/FusionSystems/order38/scripts/stage1b.g" );
FS38_RunStage1bAll := function()
    local base, done, f, line, ids, id, S, r, parts, out;
    base := "/home/user/FusionSystems/order38/data/";
    done := [];
    if IsExistingFile( Concatenation( base, "stage1b.txt" ) ) then
        f := InputTextFile( Concatenation( base, "stage1b.txt" ) );
        line := ReadLine( f );
        while line <> fail do
            parts := SplitString( line, ";" );
            if Length( parts ) > 0 and Int( parts[1] ) <> fail then AddSet( done, Int( parts[1] ) ); fi;
            line := ReadLine( f );
        od;
        CloseStream( f );
    fi;
    ids := [];
    f := InputTextFile( Concatenation( base, "stage1a_survivors.txt" ) );
    line := ReadLine( f );
    while line <> fail do
        parts := SplitString( line, ";" );
        if Length( parts ) > 0 and Int( parts[1] ) <> fail and not Int( parts[1] ) in done then Add( ids, Int( parts[1] ) ); fi;
        line := ReadLine( f );
    od;
    CloseStream( f );
    Print( Length( ids ), " survivors to process\n" );
    for id in ids do
        S := SmallGroup( 6561, id );
        r := CALL_WITH_CATCH( FS38_Stage1b, [ S ] );
        out := OutputTextFile( Concatenation( base, "stage1b.txt" ), true ); SetPrintFormattingStatus( out, false );
        if r[1] then
            AppendTo( out, FS38_Stage1bLine( id, r[2] ), "\n" );
        else
            AppendTo( out, id, ";error;", String( r[2] ), "\n" );
        fi;
        CloseStream( out );
    od;
end;
