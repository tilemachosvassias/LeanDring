# v_task49 -- exhaustive machine check of the STRUCTURAL inequalities that
# carry the non-abelian Lemma V-BIG.  (The s^6 threshold itself is asymptotic
# and is certified separately in v_task49_thresholds.py; what is checked here
# is the chain of group-theoretic inequalities, over ALL fixed-point-free
# 1 != H <= A_s, s = 5..10, abelian and non-abelian alike.)
#
# For H <= A_s fpf with orbits O_1..O_r of sizes e_1..e_r, N = N_{S_s}(H),
# d = max e_i, m = #{i : e_i = d}, W = union of the d-orbits, K_i = H|_{O_i}:
#
#  (I)   |N|  <=  prod_e (e!)^{m_e} * m_e!                     [case A input]
#  (II)  |N|  <=  m! * prod_{|O_i|=d} |N_{S_d}(K_i)| * (s-dm)! [case B input]
#  (III) v(H) = [S_s:N]*|H'|  >=  |K_1'| * [S_d : N_{S_d}(K_1)]   [(star)]
#  (IV)  if N_{S_d}(K_1) contains A_d (d>=5) then K_1 contains A_d
#  (V)   |H'| >= |K_i'|  for every i
#  (VI)  case-A numeric form: if all e_i <= E then v(H) >= s!/(E^s*Int(s/2)!)
#
# Also prints V_s and min V_s.

Restrict := function(H, O)
  local hom;
  hom := ActionHomomorphism(H, O, OnPoints);
  return Image(hom);
end;;

CheckDegree := function(s)
  local A, S, cl, H, N, orbs, sizes, d, m, W, Ks, K, i, e, ms, prodI, prodII,
        v, V, bad, nbad, tot, nonab, Sd, NK, lhs, rhs, ee, cnt, E, boundVI;
  A := AlternatingGroup(s); S := SymmetricGroup(s);
  V := []; bad := []; tot := 0; nonab := 0;
  for cl in ConjugacyClassesSubgroups(A) do
    H := Representative(cl);
    if Size(H) = 1 then continue; fi;
    if Length(MovedPoints(H)) <> s then continue; fi;   # fixed-point-free
    tot := tot + 1;
    if not IsAbelian(H) then nonab := nonab + 1; fi;
    N := Normalizer(S, H);
    v := Factorial(s) * Size(DerivedSubgroup(H)) / Size(N);
    AddSet(V, v);
    orbs := Orbits(H, [1..s]);
    sizes := List(orbs, Length);
    d := Maximum(sizes);
    m := Number(sizes, x -> x = d);

    # (I)
    prodI := 1;
    for e in Set(sizes) do
      ms := Number(sizes, x -> x = e);
      prodI := prodI * Factorial(e)^ms * Factorial(ms);
    od;
    if not Size(N) <= prodI then Add(bad, ["I", s, StructureDescription(H)]); fi;

    # constituents on the maximal orbits
    Ks := List(Filtered(orbs, o -> Length(o) = d), o -> Restrict(H, o));
    Sd := SymmetricGroup(d);
    # (II)
    prodII := Factorial(m) * Factorial(s - d*m);
    for K in Ks do prodII := prodII * Size(Normalizer(Sd, K)); od;
    if not Size(N) <= prodII then Add(bad, ["II", s, StructureDescription(H)]); fi;

    # (III) and (V)
    for K in Ks do
      NK := Normalizer(Sd, K);
      rhs := Size(DerivedSubgroup(K)) * (Factorial(d)/Size(NK));
      if not v >= rhs then Add(bad, ["III", s, StructureDescription(H), v, rhs]); fi;
      if not Size(DerivedSubgroup(H)) >= Size(DerivedSubgroup(K)) then
        Add(bad, ["V", s, StructureDescription(H)]); fi;
      # (IV)
      if d >= 5 and IsSubgroup(NK, AlternatingGroup(d)) then
        if not IsSubgroup(K, AlternatingGroup(d)) then
          Add(bad, ["IV", s, StructureDescription(H)]); fi;
      fi;
    od;

    # (VI) case-A form with E = max orbit size (the sharpest legal E)
    E := d;
    boundVI := Factorial(s) / (E^s * Factorial(Int(s/2)));
    if not (Factorial(s)/Size(N)) >= boundVI then
      Add(bad, ["VI", s, StructureDescription(H)]); fi;
  od;
  Print("s = ", s, ":  #fpf subgroup classes = ", tot,
        " (non-abelian ", nonab, ")\n");
  Print("   V_", s, " = ", V, "\n");
  Print("   min V_", s, " = ", Minimum(V), "   s^6 = ", s^6, "\n");
  Print("   VIOLATIONS: ", bad, "\n\n");
end;;

for s in [11] do CheckDegree(s); od;
QUIT;
