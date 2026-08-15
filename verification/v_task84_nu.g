# v_task84 -- independent check of v_task43's nu(S) for the four R6 groups and
# of the R6-CERT arithmetic.  nu_out(S) = min class size of an outer element of
# prime order, read off the character table of S.2 (CTblLib).
LoadPackage("ctbllib");;
NuOut := function(nameup, namedown)
  local t, s, fus, orders, sizes, i, best, cls;
  t := CharacterTable(nameup);
  s := CharacterTable(namedown);
  fus := GetFusionMap(s, t);
  orders := OrdersClassRepresentatives(t);
  sizes := SizesConjugacyClasses(t);
  best := infinity;
  for i in [1..Length(orders)] do
    if not (i in fus) and IsPrimeInt(orders[i]) then
      # class of an outer element of prime order; |x^{S.2}| = [S:C_S(x)]
      if sizes[i] < best then best := sizes[i]; cls := [i, orders[i]]; fi;
    fi;
  od;
  return [best, cls];
end;;
for p in [["HS.2","HS"],["McL.2","McL"],["Fi24","F3+"]] do
  r := NuOut(p[1], p[2]);
  Print("nu_out(", p[2], ") = ", r[1], "   (class index ", r[2], ")\n");
od;
Print("Co3: |Out| = 1, so nu = iota.\n");

# R6-CERT arithmetic, with the write-up's iota and |S| data
Print("\nR6-CERT: n_max = 2 + Int(Sqrt(6*|Out|*iota/v2(|S|))), trigger n0 from PhiV<=C(n,3)\n");
data := [ ["HS", 1100, 3850, 2, CharacterTable("HS")],
          ["McL",15400,15400, 2, CharacterTable("McL")],
          ["Co3",128800,128800,1, CharacterTable("Co3")],
          ["Fi24'",306936,4860485028,2, CharacterTable("F3+")] ];;
for d in data do
  ord := Size(d[5]);
  v2 := 0; t := ord; while t mod 2 = 0 do t := t/2; v2 := v2+1; od;
  K := d[4]*d[3];
  nmax := 2 + RootInt(Int(6*K/v2), 2);
  PhiV := Minimum(d[2]^2, ord);
  n0 := 3;
  while Binomial(n0,3) < PhiV do n0 := n0+1; od;
  if nmax < n0 then verd := "EMPTY for all n"; else verd := "window survives"; fi;
  Print(d[1], ": |S| = ", ord, "  v2 = ", v2, "  PhiV = ", PhiV,
        "  n0 = ", n0, "  n_max = ", nmax, "  => ", verd, "\n");
od;
Print("Fi24' (K2) ratio nu^2/(4|Out|iota) = ",
      Float(306936^2/(4*2*4860485028)), "  (claim 2.4228)\n");
Print("nu^3 = ", 306936^3, " vs C(52703,3) = ", Binomial(52703,3), "\n");
Print("DONE\n");
QUIT;
