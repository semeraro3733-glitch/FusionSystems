# Reference results for tests/TestC3wrC3wrC3.m.
#   gap -q -o 6g validation/fast_protoessentials.g validation/run_c3wrc3wrc3.g
W := WreathProduct(WreathProduct(CyclicGroup(IsPermGroup,3), CyclicGroup(IsPermGroup,3)),
                   CyclicGroup(IsPermGroup,3));;
S := Image(IsomorphismPcGroup(W));;
R := FastProtoEssentials(S);;
Print("Aut(S)-classes: ", Length(R[1]), "\n");
Print("S-classes: ", Length(R[2]), "\n");
Print("[log_3|E|, log_3|N_S(E):E|, |Z(E)|, |E:Phi(E)|, E normal in S] for the Aut(S)-classes:\n",
      Collected(List(R[1], E -> ClassData(S, E))), "\n");
Print("log_3|E| for the S-classes: ", Collected(List(R[2], E -> Log(Size(E), 3))), "\n");
QUIT;
