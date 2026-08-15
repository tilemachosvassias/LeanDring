G := SymmetricGroup(4);
K := AlternatingGroup(4);
chi := Irr(K)[2];
g := (1,2);
Print(chi^g, "\n");
