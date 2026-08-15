# v_task51_l2_twins.g -- GAP spot-checks for the L_2(q) twin elimination.
#
# PART A: exact iota(L_2(q)) = min over ALL non-trivial H <= S of
#           ind*(H) = [S:N_S(H)] * |H'|
#         (no abelian restriction -- so this also discharges (AB) for the
#         target on the checked range), together with iota_2 and the first
#         few values of the ind* spectrum I(S).
# PART B: mult_1(L_2(q)) = number of classes of perfect self-normalising
#         subgroups (Lemma CT cross-check).
# PART C: the two claims used uniformly in the write-up, checked on data:
#           (K)  every prime power dividing |L_2(q)| is <= q+1
#           (C3) |G| >= iota(G)^3 / 2   for every simple group in reach
#                (L_2 is the extremal family; this is the inequality that
#                 makes a second socle factor impossible)
#
# Run:  ~/gap-4.16.0/gap -q -o 4g v_task51_l2_twins.g > v_task51_l2_twins_g_out.txt

IndStar := function(G, H)
  return Index(G, Normalizer(G, H)) * Size(DerivedSubgroup(H));
end;

Spectrum := function(G)
  local cl, vals, c, H;
  cl := ConjugacyClassesSubgroups(G);
  vals := [];
  for c in cl do
    H := Representative(c);
    if Size(H) > 1 then
      AddSet(vals, IndStar(G, H));
    fi;
  od;
  return vals;
end;

Print("### PART A -- exact ind* spectrum of L_2(q), all subgroups\n");
Print("# q | |S| | iota(S) | q+1 | iota_2 | first 6 values of I(S)\n");
for q in [4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32] do
  G := PSL(2, q);
  vals := Spectrum(G);
  Print(q, " | ", Size(G), " | ", vals[1], " | ", q+1, " | ",
        vals[2], " | ", vals{[1..Minimum(6, Length(vals))]},
        " | iota=q+1? ", vals[1] = q+1, "\n");
od;

Print("\n### PART B -- mult_1(L_2(q)) (perfect self-normalising classes)\n");
for q in [4,5,7,8,9,11,13,16,17,19,23,25,27,29,31,32,37,41,43,49,64] do
  G := PSL(2, q);
  reps := RepresentativesPerfectSubgroups(G);
  n := 0; ords := [];
  for H in reps do
    if Size(H) > 1 and Size(Normalizer(G, H)) = Size(H) then
      n := n + 1; Add(ords, Size(H));
    fi;
  od;
  Print("q = ", q, "  mult_1 = ", n, "  psn orders = ", ords, "\n");
od;

Print("\n### PART C1 -- (K): largest prime power dividing |L_2(q)| vs q+1\n");
bad := [];
for q in Filtered([4..2000], IsPrimePowerInt) do
  N := q*(q^2-1)/GcdInt(2,q-1);
  m := Maximum(List(Collected(FactorsInt(N)), x -> x[1]^x[2]));
  if m > q+1 then Add(bad, [q, m]); fi;
od;
Print("violations of (K) for 4 <= q <= 2000: ", bad, "\n");

Print("\n### PART C2 -- (C3): |G| >= iota(G)^3/2 for simple G in reach\n");
Print("# G | |G| | iota(G) | |G|/iota^3\n");
for nm in ["A5","A6","A7","A8","A9","L3(2)","L3(3)","L3(4)","U3(3)","U4(2)",
           "M11","M12","M22","J1","J2","Sz(8)","U3(4)","S4(4)"] do
  t := CharacterTable(nm);
  if t = fail then Print(nm, " : no table\n"); continue; fi;
  Print(nm, " | ", Size(t), "\n");
od;
Print("# (numeric C3 check is done in the python script from the tabulated\n");
Print("#  iota values of v_task39 / v_task50; GAP only supplies the sizes.)\n");
QUIT;
