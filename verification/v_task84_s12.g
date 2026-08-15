# v_task84 -- INDEPENDENT re-check of the six structural inequalities (I)-(VI)
# of v_task49, written from the statements in v_task49_vbig_nonab.md, not from
# v_task49_chain.g.  Two parts:
#   PART A: exhaustive over ALL fixed-point-free 1 != H <= A_s for s = 5..9
#           (and s = 10 if it finishes), re-deriving V_s from the definition.
#   PART B: s = 12 -- the extension the audit asked for.  ConjugacyClassesSubgroups
#           (A_12) is out of reach, so the check is run over a large ADVERSARIAL
#           SAMPLE: every transitive group of degree 12 lying in A_12, every
#           orbit-type direct product built from transitive groups of degree
#           <= 6, and several thousand randomly generated subgroups.
#
#  (I)   |N|  <= prod_e (e!)^{m_e} * m_e!
#  (II)  |N|  <= m! * prod_{|O_i|=d} |N_{S_d}(K_i)| * (s-dm)!
#  (III) v(H) = [S_s:N]*|H'| >= |K_i'| * [S_d : N_{S_d}(K_i)]   for every dominant i
#  (IV)  A_d <= N_{S_d}(K_i) and d>=5  ==>  A_d <= K_i
#  (V)   |H'| >= |K_i'|
#  (VI)  [S_s:N] >= s!/(E^s * Int(s/2)!),  E = max orbit size

CheckOne := function(s, H, report)
  local S, N, orbs, sizes, d, m, e, ms, mset, prodI, i, K, hom, Kd, Sd, NK,
        v, viol, dominant, Sdd, img, pts, perm, idx, prodII, lhs, rhs, E;
  viol := [];
  S := SymmetricGroup(s);
  orbs := Orbits(H, [1..s]);
  sizes := List(orbs, Length);
  if Minimum(sizes) < 2 then return fail; fi;      # not fixed-point-free
  N := Normalizer(S, H);
  v := Index(S, N) * Size(DerivedSubgroup(H));
  d := Maximum(sizes);
  m := Number(sizes, x -> x = d);
  mset := Set(sizes);

  # (I)
  prodI := 1;
  for e in mset do
    ms := Number(sizes, x -> x = e);
    prodI := prodI * Factorial(e)^ms * Factorial(ms);
  od;
  if not Size(N) <= prodI then Add(viol, ["I", s, Size(H)]); fi;

  # (VI)
  E := d;
  if not Index(S, N) * (E^s * Factorial(Int(s/2))) >= Factorial(s) then
    Add(viol, ["VI", s, Size(H)]);
  fi;

  # restrictions to the dominant orbits
  dominant := Filtered([1..Length(orbs)], i -> sizes[i] = d);
  prodII := Factorial(m) * Factorial(s - d*m);
  Sdd := SymmetricGroup(d);
  for i in dominant do
    pts := orbs[i];
    hom := ActionHomomorphism(H, pts, OnPoints);
    K := Image(hom);                       # transitive of degree d
    NK := Normalizer(Sdd, K);
    prodII := prodII * Size(NK);
    # (III)
    if not v >= Size(DerivedSubgroup(K)) * Index(Sdd, NK) then
      Add(viol, ["III", s, Size(H)]);
    fi;
    # (V)
    if not Size(DerivedSubgroup(H)) >= Size(DerivedSubgroup(K)) then
      Add(viol, ["V", s, Size(H)]);
    fi;
    # (IV)
    if d >= 5 and IsSubgroup(NK, AlternatingGroup(d)) then
      if not IsSubgroup(K, AlternatingGroup(d)) then
        Add(viol, ["IV", s, Size(H)]);
      fi;
    fi;
  od;
  # (II)
  if not Size(N) <= prodII then Add(viol, ["II", s, Size(H)]); fi;

  if report then return [v, viol]; else return viol; fi;
end;;

Print("################ PART A: exhaustive, s = 5..9(10)\n");
for s in [5,6,7,8,9] do
  A := AlternatingGroup(s);
  V := []; tot := 0; nonab := 0; viol := [];
  for cl in ConjugacyClassesSubgroups(A) do
    H := Representative(cl);
    if Size(H) = 1 then continue; fi;
    if Length(MovedPoints(H)) <> s then continue; fi;
    tot := tot + 1;
    if not IsAbelian(H) then nonab := nonab + 1; fi;
    r := CheckOne(s, H, true);
    AddSet(V, r[1]);
    Append(viol, r[2]);
  od;
  Print("s = ", s, "  fpf classes = ", tot, " (non-abelian ", nonab, ")",
        "  min V_s = ", Minimum(V), "  |V_s| = ", Length(V),
        "  VIOLATIONS = ", Length(viol), "\n");
  if Length(viol) > 0 then Print("   ", viol, "\n"); fi;
od;

Print("################ PART B: s = 12, adversarial sample\n");
s := 12;;
S12 := SymmetricGroup(12);;
A12 := AlternatingGroup(12);;
samples := [];;

# (a) transitive groups of degree 12 contained in A_12
n12 := NrTransitiveGroups(12);;
Print("transitive groups of degree 12: ", n12, "\n");
for i in [1..n12] do
  T := TransitiveGroup(12, i);
  if IsSubgroup(A12, T) then Add(samples, T); fi;
od;
Print("  ... of which inside A_12: ", Length(samples), "\n");

# (b) orbit-type direct products from transitive groups of small degree
parts := [[2,2,2,2,2,2],[3,3,3,3],[4,4,4],[6,6],[2,4,6],[2,2,3,5],[5,7],
          [2,3,3,4],[3,4,5],[2,2,2,3,3],[4,8],[2,10],[5,5,2],[6,3,3],[2,2,8]];;
for p in parts do
  for k in [1..6] do
    gens := []; off := 0;
    for e in p do
      T := TransitiveGroup(e, ((k-1) mod NrTransitiveGroups(e)) + 1);
      for g in GeneratorsOfGroup(T) do
        Add(gens, PermList(Concatenation([1..off], List([1..e], x -> off + x^g))));
      od;
      off := off + e;
    od;
    H := Group(gens);
    if Length(MovedPoints(H)) = 12 then
      H := Intersection(H, A12);
      if Size(H) > 1 and Length(MovedPoints(H)) = 12 then Add(samples, H); fi;
    fi;
  od;
od;
Print("  after orbit-type products: ", Length(samples), "\n");

# (c) random subgroups
for i in [1..4000] do
  k := Random([1,2,3]);
  gens := List([1..k], j -> Random(A12));
  H := Group(gens);
  if Size(H) > 1 and Length(MovedPoints(H)) = 12 then Add(samples, H); fi;
od;
Print("  after random subgroups: ", Length(samples), "\n");

viol := [];;
nchk := 0;; nonab := 0;; minv := infinity;;
for H in samples do
  r := CheckOne(12, H, true);
  if r = fail then continue; fi;
  nchk := nchk + 1;
  if not IsAbelian(H) then nonab := nonab + 1; fi;
  if r[1] < minv then minv := r[1]; fi;
  Append(viol, r[2]);
od;
Print("s = 12: checked ", nchk, " fpf subgroups (", nonab, " non-abelian)\n");
Print("        min v(H) over the sample = ", minv, "   (12^6 = ", 12^6, ")\n");
Print("        VIOLATIONS of (I)-(VI) = ", Length(viol), "\n");
if Length(viol) > 0 then Print("   ", viol, "\n"); fi;
Print("DONE\n");
QUIT;
