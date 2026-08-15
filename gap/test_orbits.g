G := SymmetricGroup(4);
K := AlternatingGroup(4);
chars := Filtered(Irr(K), x -> x[1] = 1);
N := Normalizer(G, K);
Print(List(OrbitsDomain(N, chars), Length), "\n");
