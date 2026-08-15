# v_task43_r6_nu.g -- residue R6 / input I12 of v_task42_to_prime.md:
# the EXACT value of
#
#     nu(S) := min { [S : N_S(A)] : 1 <> A <= Aut(S) abelian }
#              (definition of v_task34_transport.md Sec.0)
#
# for S in { HS, McL, Co3, Fi24' }, and the branch-(0) window test that
# uses it.
#
# ------------------------------------------------------------------ theory
# LEMMA NU (reduction of nu to iota plus outer involutions) -- PROVEN.
#   Let S be non-abelian simple, identify S = Inn(S) <| Aut(S), and let
#   1 <> A <= Aut(S) be abelian.  Put A0 := A cap Inn(S).
#     * If A0 <> 1: N_S(A) <= N_S(A0) (Inn(S) is normal in Aut(S), so an
#       element normalising A normalises A cap Inn(S)), hence
#       [S:N_S(A)] >= [S:N_S(A0)] >= iota(S).
#     * If A0 = 1: A embeds in Out(S).  When |Out(S)| = 1 this is
#       impossible; when Out(S) has even order the abelian A with A0 = 1
#       and |A| = 2 is A = <tau>, tau an involution of Aut(S)\Inn(S), and
#       N_S(<tau>) = C_S(tau).  (More generally A cyclic/abelian of order
#       coprime-or-not, N_S(A) <= C_S(a) for any a in A of prime order
#       with <a> cap Inn = 1, so the minimum over A0 = 1 is attained at a
#       prime-order outer element.)
#   Hence
#       nu(S) = min( iota(S), min{ [S:C_S(x)] : x in Aut(S)\Inn(S),
#                                  x of prime order, <x> cap Inn(S) = 1 } ).
#   For our four groups |Out(S)| divides 2, so the outer branch is exactly
#   the outer involution classes of S.2, and for tau outer
#       tau^{S.2} = tau^S  =>  [S:C_S(tau)] = |tau^{S.2}|,
#   the class size read straight off the character table of S.2.
#   (Co3 has Out = 1, so nu(Co3) = iota(Co3).)
#
# LEMMA SP (v_task39): iota(S) = ilow(S) with
#   ilow(X) = min over maximal M < X of [X:M] if F(M) <> 1, else
#             [X:M]*ilow(M).  Recursion below is v_task39's, verbatim.
#
# ------------------------------------------------------------- branch (0)
# v_task42_to_prime.md Sec.3: an orbit of a socle factor S survives
# branch (0) at n only if
#   (III.1) PhiVal = min(nu(S)^2, |S|) <= C(n,3);
#   (III.3) ell >= ell_min := ceil( C(n,3) / (|Out(S)| * iota(S)) )
#           together with |S|^ell | (n!/2)  [which contains ORDER and the
#           p-part filter: |S|^ell | n!/2 iff for every prime p
#           ell*v_p(|S|) <= v_p(n!) - [p = 2]].
# The test below enumerates, for each of the four groups, every n from the
# smallest n with (III.1) upward, and reports every n that passes the exact
# divisibility test -- i.e. the exact branch-(0) window, computed with the
# exact nu and the exact iota (v_task42 used the lower bound nu >= mu and
# the upper bound iota <= iota_ub).

LoadPackage("ctbllib");;

# ---------------------------------------------------------------- iota (SP)
socle := rec();
socle.("A6.2^2")   := 6;
socle.("L2(16).2") := 17;
socle.("L3(4).2_1"):= 21;
socle.("U6(2).2")  := 672;
socle.("L3(7).2")  := 57;
alias := rec(M12M2 := "M11", M12M4 := "A6.2^2", J3M3 := "L2(19)",
             J3M2 := "L2(19)", HSM3 := "U3(5).2", McLM3 := "M22",
             ONM2 := "L3(7).2");

memo := rec();

ilow := function(ct, cap)
  local key, best, m, mt, idx, r;
  key := Identifier(ct);
  if IsBound(alias.(key)) then
    mt := CharacterTable(alias.(key));
    if mt <> fail then ct := mt; key := Identifier(ct); fi;
  fi;
  if IsBound(memo.(key)) then return memo.(key); fi;
  if Size(ct) = 1 then return infinity; fi;
  if not HasMaxes(ct) then
    if IsBound(socle.(key)) then return socle.(key); fi;
    return 2;
  fi;
  best := infinity;
  for m in Maxes(ct) do
    mt := CharacterTable(m);
    if mt = fail then continue; fi;
    idx := Size(ct)/Size(mt);
    if ClassPositionsOfFittingSubgroup(mt) <> [1] then
      if idx < best then best := idx; fi;
    elif 2*idx < best and 2*idx <= cap then
      r := ilow(mt, QuoInt(cap, idx));
      if idx*r < best then best := idx*r; fi;
    fi;
  od;
  memo.(key) := best;
  return best;
end;

iotaOf := function(nm)
  local t, good, s, ct, idx;
  t := CharacterTable(nm);
  good := [];
  for s in Maxes(t) do
    ct := CharacterTable(s);
    if ct = fail then continue; fi;
    if ClassPositionsOfFittingSubgroup(ct) <> [1] then
      Add(good, [Size(t)/Size(ct), s]);
    fi;
  od;
  Sort(good);
  return [good[1][1], good[1][2], ilow(t, 10^40)];
end;

# ------------------------------------------------- outer prime-order classes
# smallest [S : C_S(x)] over x outside S of prime order, from the table of S.2
outerMin := function(upname)
  local t2, inner, ords, szs, i, best, wit, o;
  t2 := CharacterTable(upname);
  inner := ClassPositionsOfDerivedSubgroup(t2);   # the classes of S
  ords := OrdersClassRepresentatives(t2);
  szs := SizesConjugacyClasses(t2);
  best := infinity; wit := fail;
  for i in [1 .. NrConjugacyClasses(t2)] do
    if i in inner then continue; fi;
    o := ords[i];
    if not IsPrimeInt(o) then continue; fi;   # <x> cap S = 1 forces o prime = 2
    if szs[i] < best then best := szs[i]; wit := [i, o, szs[i]]; fi;
  od;
  return [best, wit, ClassNames(t2)[wit[1]]];
end;

# ------------------------------------------------------------- arithmetic
vpFact := function(n, p)
  local v, pk;
  v := 0; pk := p;
  while pk <= n do v := v + QuoInt(n, pk); pk := pk*p; od;
  return v;
end;

# does |S|^ell divide n!/2 ?
divOK := function(fac, ell, n)
  local pe, cap;
  for pe in fac do
    cap := vpFact(n, pe[1]);
    if pe[1] = 2 then cap := cap - 1; fi;
    if ell*pe[2] > cap then return false; fi;
  od;
  return true;
end;

C3 := n -> Binomial(n, 3);

YN := function(b, y, n) if b then return y; else return n; fi; end;

# smallest n >= 10 with C(n,3) >= x
n0For := function(x)
  local n;
  n := 10;
  while C3(n) < x do n := n + 1; od;
  return n;
end;

# ------------------------------------------------------------------- main
NCAP := 200000;;

groups := [ rec(nm := "HS",    up := "HS.2",  out := 2, win := [71, 75]),
            rec(nm := "McL",   up := "McL.2", out := 2, win := [78, 144]),
            rec(nm := "Co3",   up := fail,    out := 1, win := [79, 210]),
            rec(nm := "Fi24'", up := "Fi24",  out := 2, win := [8270, 42681]) ];;

Print("### v_task43 -- exact nu for the R6 groups, and branch (0)\n\n");

for g in groups do
  t := CharacterTable(g.nm);
  ord := Size(t);
  r := iotaOf(g.nm);
  iota := r[1];
  if g.up <> fail then
    om := outerMin(g.up);
    outer := om[1];
  else
    om := fail; outer := infinity;
  fi;
  nu := Minimum(iota, outer);
  fac := Collected(FactorsInt(ord));
  Print("GROUP ", g.nm, "\n");
  Print("  |S|        ", ord, "\n");
  Print("  |Out|      ", g.out, "\n");
  Print("  iota(S)    ", iota, "   witness M = ", r[2],
        "   (SP recursion lower bound ", r[3], ", EXACT=", r[3] = iota, ")\n");
  if om <> fail then
    Print("  outer min  ", outer, "   class ", om[3], " of ", g.up,
          " (order ", om[2][2], ")\n");
  else
    Print("  outer min  --   (Out(S) = 1, no outer branch)\n");
  fi;
  if outer < iota then br := "outer branch"; else br := "iota branch"; fi;
  Print("  nu(S)      ", nu, "     [ = ", br, " ]\n");
  Print("  nu^2       ", nu^2, "\n");
  PhiVal := Minimum(nu^2, ord);
  Print("  PhiVal        ", PhiVal, "  (= min(nu^2,|S|))\n");
  n0 := n0For(PhiVal);
  Print("  (III.1) needs n >= ", n0, "   [v_task42 window was ", g.win, "]\n");
  # exact enumeration
  live := []; nlast := fail; nchk := 0;
  n := Maximum(10, n0);
  while n <= NCAP do
    ellmin := QuoInt(C3(n) + g.out*iota - 1, g.out*iota);
    if ellmin < 1 then ellmin := 1; fi;
    nchk := nchk + 1;
    if divOK(fac, ellmin, n) then
      Add(live, [n, ellmin]);
      nlast := n;
    fi;
    n := n + 1;
  od;
  Print("  branch(0) n scanned: ", n0, " .. ", NCAP, "  (", nchk, " values)\n");
  if Length(live) = 0 then
    Print("  ==> SURVIVORS: 0   ROW CLOSED (numerically, n <= ", NCAP, ")\n");
  else
    Print("  ==> SURVIVORS: ", Length(live), "   n in [",
          live[1][1], " .. ", live[Length(live)][1], "]  ell_min in [",
          live[1][2], " .. ", live[Length(live)][2], "]\n");
    Print("      first: ", live[1], "  last: ", live[Length(live)], "\n");
  fi;
  # ---- closed-form all-n certificate (2-part), see write-up Lemma R6-CERT:
  #   ell_min >= C(n,3)/K >= (n-2)^3/(6K),  v_2(n!) - 1 <= n - 2,
  #   so |S|^ell | n!/2 forces (n-2)^2 <= 6K/v_2(|S|).
  v2S := First(fac, x -> x[1] = 2)[2];
  nmax := 2 + RootInt(QuoInt(6*g.out*iota, v2S), 2);
  if nmax < n0 then vd := "EMPTY for ALL n"; else vd := "NOT closed by this certificate"; fi;
  Print("  CERT (2-part): |S|^ell_min | n!/2 forces n <= ", nmax,
        " ; trigger forces n >= ", n0, "  ==> ", vd, "\n\n");
od;


# --------------------------------------------------- Fi24': the sharp floor
# The generic run above is conservative in BOTH slots at once, and that is
# what leaves the window [8270,42681] open for Fi24': it allows the floor to
# be nu = 306936 (an OUTER abelian A) and simultaneously allows the pair
# value to be as large as |Out|*iota = 2*4860485028 (only INNER A).  The two
# cannot both be extremal.  Lemma R6-Fi (write-up Sec.3) closes the row:
#
#  (K1) [K_i = Aut(S)]  If some component K_i of K contains an outer
#       automorphism, then A = <tau> <= K_i is abelian and the pair value is
#       [Abar:N_Abar(A)] <= |Out|*[S:C_S(tau)] = 2*306936, so
#       ell_min = ceil(C(n,3)/613872) and the 2-part certificate applies.
#
#  (K2) [sharp TR-2 floor]  Otherwise every abelian A <= K with an outer
#       pi_i-image has s := |supp(A)| >= 2, and TR-2 gives the SHARP bound
#       |A^T| >= (ell_i/s)*nu_min^s for any i in supp(A).
#        * s >= 3 :  |A^T| >= nu^3, compared with C(n,3) at the top of the
#          window (n <= NMAXW, the 2-part certificate bound);
#        * s = 2 and supp(A) meets the Fi24' orbit :
#          |A^T| >= (ell/2)*nu^2 >= (C(n,3)/(2*|Out|*iota))*(nu^2/2)
#                 = C(n,3) * nu^2/(4*|Out|*iota),
#          and the printed RATIO nu^2/(4*|Out|*iota) is > 1, so the floor
#          EXCEEDS C(n,3): branch (0) (which needs Phi <= C(n,3)) is empty.
#        * s = 2 and supp(A) misses the Fi24' orbit : then both participating
#          factors S_j have nu(S_j)^2 <= |A^T| <= C(n,3) hence each triggers
#          its OWN branch-(0) row, all of which are empty (v_task42 sweep 2
#          for the Lie families and the 22 other sporadics; this script for
#          HS, McL, Co3).  Same for the TR-3 alternative |S_min| <= C(n,3).
Print("### Fi24' -- Lemma R6-Fi (sharp floor); the row closes for all n\n");
ordF := Size(CharacterTable("Fi24'"));;
facF := Collected(FactorsInt(ordF));;
v2F := First(facF, x -> x[1] = 2)[2];;
iotaF := 4860485028;;
nuF := 306936;;
outF := 2;;

# (K1)
n0 := n0For(nuF^2);;
nmax := 2 + RootInt(QuoInt(6*outF*nuF, v2F), 2);;
if nmax < n0 then vd := "EMPTY for ALL n"; else vd := "OPEN"; fi;
Print("  (K1) K_i = Aut(S): pair value <= ", outF*nuF,
      " ; 2-part cert n <= ", nmax, " , trigger n >= ", n0,
      "   ==> ", vd, "\n");

# (K2), s = 2 with Fi24' in the support
num := nuF^2;;  den := 4*outF*iotaF;;
Print("  (K2) s=2 sharp floor ratio  nu^2/(4*|Out|*iota) = ", num, "/", den,
      " = ", Float(num/den), "  (> 1 : floor > C(n,3))  ==> ",
      YN(num > den, "EMPTY for ALL n", "OPEN"), "\n");

# (K2), s >= 3 : nu^3 vs C(n,3) at the top of the 2-part window
NMAXW := 2 + RootInt(QuoInt(6*outF*iotaF, v2F), 2);;
Print("  (K2) s>=3 : nu^3 = ", nuF^3, "  vs  C(", NMAXW, ",3) = ",
      Binomial(NMAXW, 3), "  ==> ",
      YN(nuF^3 > Binomial(NMAXW,3), "EMPTY on the whole window", "OPEN"), "\n");
Print("  ==> Fi24' row CLOSED for all n.\n");

QUIT;
