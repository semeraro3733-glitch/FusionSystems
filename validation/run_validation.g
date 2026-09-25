# Validation of the candidate reduction of Section 3 of arXiv:2607.24674.
#   gap -q -o 6g validation/fast_protoessentials.g validation/run_validation.g
for pn in [[2,3],[2,4],[2,5],[2,6],[3,3],[3,4],[3,5],[3,6],[5,3],[5,4],[7,3]] do
  bad := ValidateSmallGroups(pn[1], pn[2], [1..NumberSmallGroups(pn[1]^pn[2])]);
  if Length(bad) > 0 then Print("   not among candidates: ", Collected(List(bad, b -> b{[2,3]})), "\n"); fi;
od;
# The essential subgroups of some group fusion systems are among the candidates.
for Gp in [["PSL(3,4)", PSL(3,4), 2], ["PSL(3,8)", PSL(3,8), 2], ["PSL(3,9)", PSL(3,9), 3],
           ["PSp(4,3)", PSp(4,3), 3], ["Alt(9)", AlternatingGroup(9), 3],
           ["2^4:A5 (PerfectGroup(960,1))", PerfectGroup(IsPermGroup,960,1), 2],
           ["2^4:A5 (PerfectGroup(960,2))", PerfectGroup(IsPermGroup,960,2), 2],
           ["3^4:PSL2(9) (PerfectGroup(29160,4))", PerfectGroup(IsPermGroup,29160,4), 3],
           ["3^4.SL2(9) (PerfectGroup(58320,1))", PerfectGroup(IsPermGroup,58320,1), 3],
           ["3^4.SL2(9) (PerfectGroup(58320,2))", PerfectGroup(IsPermGroup,58320,2), 3]] do
  Print(Gp[1], " at p = ", Gp[3], ": [IdGroup(E), |Out_S(E)|, among candidates] = ",
        EssentialsOfGroupFound(Gp[2], Gp[3]), "\n");
od;
QUIT;
