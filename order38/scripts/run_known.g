# Stage 2 for the Sylow 3-subgroups of Alt(18) and PSp4(9) (not identified
# in the library), with the look-up tables (GL6(3), T = 3^2 included).
#   gap -c 'Read("run_known.g"); FS38_RunKnown();'
Read( "/home/user/FusionSystems/order38/scripts/stage2.g" );
FS38_RunKnown := function()
    local K, i, r, name, logf, out, t;
    K := FS_KnownGroups38();
    for i in [ 1, 2 ] do
        name := K[i].name;
        logf := Concatenation( "/home/user/FusionSystems/order38/logs/stage2_known_", String( i ), ".log" );
        t := Runtime();
        r := CALL_WITH_CATCH( FS38_Stage2, [ K[i].group, name, logf, rec() ] );
        out := OutputTextFile( "/home/user/FusionSystems/order38/data/stage2_known.txt", true ); SetPrintFormattingStatus( out, false );
        if r[1] then
            AppendTo( out, name, ";", Length( r[2].systems ), ";", Runtime() - t, ";",
                      JoinStringsWithSeparator( List( r[2].descriptions, FS38_DescLine ), " | " ) );
            if IsBound( r[2].incomplete ) and r[2].incomplete then AppendTo( out, ";INCOMPLETE" ); fi;
            AppendTo( out, "\n" );
        else
            AppendTo( out, name, ";error;", String( r[2] ), "\n" );
        fi;
        CloseStream( out );
    od;
end;
