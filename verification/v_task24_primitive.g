# For Lemma iota-A we need: every maximal M < A_n of index < C(n,3) is
# A_{n-1} or (S2 x S_{n-2}) cap A_n.  Intransitive/imprimitive are handled by
# hand; here we verify the PRIMITIVE case directly from the library.
for n in [9..30] do
  bad := [];
  for i in [1..NrPrimitiveGroups(n)] do
    P := PrimitiveGroup(n, i);
    if Size(P) < Factorial(n)/2 then          # excludes A_n and S_n
      idx := (Factorial(n)/2) / Gcd(Size(P), Factorial(n)/2);
      # index of P cap A_n inside A_n:
      Q := Size(P);
      if not IsSubset(AlternatingGroup(n), GeneratorsOfGroup(P)) then Q := Q/2; fi;
      idx := (Factorial(n)/2)/Q;
      if idx < Binomial(n,3) then Add(bad, [i, Q, idx, StructureDescription(P)]); fi;
    fi;
  od;
  Print("n=", n, "  C(n,3)=", Binomial(n,3), "  primitive subgroups of A_n with index < C(n,3): ",
        Length(bad), " ", bad, "\n");
od;
QUIT;
