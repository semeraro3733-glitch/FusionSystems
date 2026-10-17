Read( "/home/user/FusionSystems/order38/scripts/stage2.g" );
SetInfoLevel( InfoFusionSystems, 0 );
# log: logs/reference_a18_sp49.log
LOGF := "/home/user/FusionSystems/order38/logs/reference_a18_sp49.log";;
out := OutputTextFile( LOGF, false );; SetPrintFormattingStatus( out, false );;
Say := function( arg ) CallFuncList( AppendTo, Concatenation( [ out ], arg ) ); end;;
refs := [ [ "Alt(18)", AlternatingGroup( 18 ) ], [ "Sym(18)", SymmetricGroup( 18 ) ], [ "Alt(19)", AlternatingGroup( 19 ) ],
          [ "Sym(19)", SymmetricGroup( 19 ) ], [ "Alt(20)", AlternatingGroup( 20 ) ], [ "Sym(20)", SymmetricGroup( 20 ) ],
          [ "PSp4(9)", PSp( 4, 9 ) ], [ "PGSp4(9) = PSp4(9).2 (diagonal)", PGO( 5, 9 ) ] ];;
for G in refs do
    t := Runtime();
    r := CALL_WITH_CATCH( GroupFusionSystem, [ G[2], 3 ] );
    if not r[1] then Say( G[1], ": ERROR ", r[2], "\n" ); continue; fi;
    F := r[2];
    d := FS38_Describe( F );
    Say( G[1], " (order ", Size( G[2] ), "): ", FS38_DescLine( d ), " (", Runtime() - t, " ms)\n" );
    Say( "    O_3(F) = 1: ", IsOpFTrivial( F ), ", O^3(F) = F: ", IsPPerfectFusionSystem( F ), "\n" );
od;
Say( "DONE\n" );
CloseStream( out );
QUIT;
