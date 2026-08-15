LoadPackage("ctbllib");;
# Does the rational 7-dim orthogonal character stay irreducible mod p, for p | |H|?
chk := function(nm, deg)
  local t, irr, ind, cand, p, tp, i, r, dec, primes;
  t := CharacterTable(nm);
  if t = fail then Print(nm, ": no table\n"); return; fi;
  irr := Irr(t); ind := Indicator(t,2);
  cand := Filtered([1..Length(irr)], i -> irr[i][1] = deg
            and Length(ClassPositionsOfKernel(irr[i])) = 1 and ind[i] = 1);
  primes := PrimeDivisors(Size(t));
  for p in primes do
    if p = 2 then continue; fi;
    tp := t mod p;
    if tp = fail then
      Print(nm, " mod ", p, ": Brauer table not available\n"); continue;
    fi;
    for i in cand do
      r := RestrictedClassFunction(irr[i], tp);
      dec := Decomposition(Irr(tp), [r], "nonnegative")[1];
      Print(nm, "  chi_", i, " (deg ", deg, ") mod ", p, ": decomposition ", dec,
            "  irreducible=", Number(dec, x -> x <> 0) = 1 and Maximum(dec) = 1, "\n");
    od;
  od;
end;;
chk("S6(2)", 7);
chk("2^3:sl(3,2)", 7);
chk("2^3.L3(2)", 7);
chk("P11/G2/L1/V1/ext2", 7);
chk("2.A5", 2);
QUIT;
