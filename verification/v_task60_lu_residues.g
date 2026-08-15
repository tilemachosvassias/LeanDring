# v_task60_lu_residues.g -- GAP confirmations for the (H2)/(H3)/(H4)
# closure of Theorem LU-T (linear and unitary towers).
#
# PART A  the target Phi-multiplicity table M_k of |L_d(q)| and |U_d(q)|
#         checked against the exact factorisations of q^i -+ 1
# PART B  Lemma PACK in the flesh: the two configurations that DEG alone
#         did not kill are shown NOT to divide the target order, at many q
# PART C  Lemma X' : ppmax_{p'}(|S|) <= 2^{d-1} (q+1)^{d-1}, exactly
# PART D  the Zsygmondy exception list, verified by brute force
#
# Run:  ~/gap-4.16.0/gap -q -o 4g v_task60_lu_residues.g

BAR := "============================================================";;

OrdLU := function(tw, d, q)
  local oo, i, ee;
  oo := q^(d*(d-1)/2);
  if tw = "L" then
    for i in [2..d] do oo := oo * (q^i - 1); od;
    ee := Gcd(d, q-1);
  else
    for i in [2..d] do oo := oo * (q^i - (-1)^i); od;
    ee := Gcd(d, q+1);
  fi;
  return oo/ee;
end;;

# multiplicity of Phi_k(q) predicted by the cyclotomic bookkeeping
PredMult := function(tw, d, k)
  local m, i;
  m := 0;
  for i in [2..d] do
    if tw = "L" or IsEvenInt(i) then
      if i mod k = 0 then m := m + 1; fi;
    else
      if (2*i) mod k = 0 and i mod k <> 0 then m := m + 1; fi;
    fi;
  od;
  return m;
end;;

Print(BAR, "\nPART A -- the target Phi-multiplicity table, verified\n", BAR, "\n");
# Phi_k(q) for k <= d is checked to divide |S| exactly PredMult times,
# in the sense that the product of Phi_k(q)^PredMult over k reproduces the
# pp'-part of |S| up to the diagonal factor ee.
bad := 0;; ntest := 0;;
for tw in ["L","U"] do
  for d in [4..12] do
    for q in [2,3,4,5,7,8,9] do
      PP := 1;
      for k in [1..2*d] do
        PP := PP * ValuePol(CoefficientsOfUnivariatePolynomial(
                    CyclotomicPolynomial(Rationals, k)), q)
                 ^ PredMult(tw, d, k);
      od;
      ee := Gcd(d, q - (-1)^(Position(["L","U"], tw)));  # ee = gcd(d,q-1) / gcd(d,q+1)
      if tw = "L" then ee := Gcd(d, q-1); else ee := Gcd(d, q+1); fi;
      ntest := ntest + 1;
      if PP <> OrdLU(tw, d, q) * ee / q^(d*(d-1)/2) then
        bad := bad + 1;
        Print("  MISMATCH ", tw, d, "(", q, ")\n");
      fi;
    od;
  od;
od;
Print("  ", ntest, " (tw,d,q) rows tested, mismatches: ", bad, "\n\n");

Print(BAR, "\nPART B -- Lemma PACK in the flesh\n", BAR, "\n");
Print("  The only two equal-characteristic multi-factor shapes that the\n");
Print("  degree partition (Lemma DEG) does not kill are\n");
Print("     L_6  <-  S_6(q) x G_2(q)   and   L_12 <-  O_14^+(q) x F_4(q)\n");
Print("  (both with j_1 = j_2 = 1, forced by Lemma ZM).  Lemma PACK says\n");
Print("  the product does not even DIVIDE the target order:\n\n");

OrdS := function(n, q)   # |S_{2n}(q)| = |C_n(q)|
  local oo, i;
  oo := q^(n*n);
  for i in [1..n] do oo := oo * (q^(2*i) - 1); od;
  return oo / Gcd(2, q-1);
end;;
OrdG2 := q -> q^6 * (q^6-1) * (q^2-1);;
OrdOplus := function(n, q)
  local oo, i;
  oo := q^(n*(n-1)) * (q^n - 1);
  for i in [1..n-1] do oo := oo * (q^(2*i) - 1); od;
  return oo / Gcd(4, q^n - 1);
end;;
OrdF4 := q -> q^24 * (q^12-1) * (q^8-1) * (q^6-1) * (q^2-1);;

Print("  q    |S_6(q)||G_2(q)| divides |L_6(q)| ?   v_5-witness\n");
for q in [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27] do
  aa := OrdS(3, q) * OrdG2(q);
  bb := OrdLU("L", 6, q);
  # the Phi_5 witness: aa primitive prime of q^5-1
  rr := First(PrimeDivisors(q^5-1), t -> OrderMod(q, t) = 5);
  Print("  ", String(q,4), " ", String(bb mod aa = 0, 6),
        "                          Phi_5 prime rr = ", rr,
        ", rr | |S| : ", bb mod rr = 0, ", rr | product : ", aa mod rr = 0, "\n");
od;
Print("\n  q    |O_14^+(q)||F_4(q)| divides |L_12(q)| ?  Phi_11-witness\n");
for q in [2,3,4,5,7,8,9] do
  aa := OrdOplus(7, q) * OrdF4(q);
  bb := OrdLU("L", 12, q);
  rr := First(PrimeDivisors(q^11-1), t -> OrderMod(q, t) = 11);
  Print("  ", String(q,4), " ", String(bb mod aa = 0, 6),
        "                          Phi_11 prime rr = ", rr,
        ", rr | |S| : ", bb mod rr = 0, ", rr | product : ", aa mod rr = 0, "\n");
od;
Print("\n");

Print(BAR, "\nPART C -- Lemma X' : ppmax_{p'}(|S|) <= 2^(d-1) (q+1)^(d-1)\n", BAR, "\n");
viol := 0;; nt := 0;;
for tw in ["L","U"] do
  for d in [4..10] do
    for q in [2,3,4,5,7,8,9,11,13,16,17,19,23,25,27,29,31] do
      pp := SmallestPrimeDivisor(q);
      oo := OrdLU(tw, d, q);
      while oo mod pp = 0 do oo := oo/pp; od;
      PP := Maximum(List(Collected(FactorsInt(oo)), t -> t[1]^t[2]));
      nt := nt + 1;
      if PP > 2^(d-1) * (q+1)^(d-1) then
        viol := viol + 1;
        Print("  VIOLATION ", tw, d, "(", q, ") : ", PP, "\n");
      fi;
    od;
  od;
od;
Print("  ", nt, " (tw,d,q) rows tested, violations of Lemma X' : ", viol, "\n\n");

Print(BAR, "\nPART D -- the Zsygmondy exception list, brute force\n", BAR, "\n");
exc := [];;
for aa in [2..60] do
  for n in [1..40] do
    if not ForAny(PrimeDivisors(aa^n-1), rr -> OrderMod(aa, rr) = n) then
      Add(exc, [aa, n]);
    fi;
  od;
od;
Print("  (aa,n), 2 <= aa <= 60, 1 <= n <= 40, with NO primitive prime divisor\n");
Print("  of aa^n - 1 :\n  ", exc, "\n");
Print("  all of them are: n = 1 with aa = 2; n = 2 with aa+1 aa 2-power;\n");
Print("  and (aa,n) = (2,6) -- exactly the three families of (H2).\n");
mers := Filtered(exc, t -> t[2] = 2);;
Print("  the n = 2 rows have aa+1 aa power of 2 : ",
      ForAll(mers, t -> 2^LogInt(t[1]+1, 2) = t[1]+1), "\n");
Print("  the n >= 3 rows are exactly [[2,6]] : ",
      Filtered(exc, t -> t[2] >= 3) = [[2,6]], "\n\n");

Print("DONE\n");
QUIT;
