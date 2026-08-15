# Block-partitioned D-iso hunt.  d(G) is a D-invariant (canonical top
# block of Z^F/D_F), so D-iso classes respect the d-partition: we hunt each
# d-block independently.  Theory-covered groups are pre-tagged so their (huge)
# subgroup lattices are never enumerated:
#   ABELIAN     -> D-rigid within abelian (closed-form D_F SNF on file)
#   EXTRASPECIAL-> closed-form D_F SNF (opus_mk_snf_proof)
# The remaining non-abelian groups run the cheap-first chain
#   DKey (rk D, Galois, odd-block, conductors)  -> collisions only:
#   Gram SNF + etale field bag + canonical D_F-linkage.
# Groups whose subgroup-class count exceeds the cap are reported explicitly
# (never silently skipped), tagged OTHER so the residual is auditable.
#
# Caveat this does NOT remove: "vs-all" rigidity (could an abelian/metacyclic
# group be D-iso to a non-abelian one of the same d) is the open (E)/Theorem-R
# question; tagged groups are cleared only *within their theory class*.

Read("gap/df_linkage.g");   # brings dring + DFLinkage

IsExtraspecialD := function(G)
  local Z;
  Z := Centre(G);
  return Size(Z) = 2 and DerivedSubgroup(G) = Z and FrattiniSubgroup(G) = Z;
end;;

# deep invariant from one species-table build: [GramSNF, fieldbag, linkage]
DeepKeyD := function(G)
  local cls, T, n, i, j, k, gram, gsnf, fb, F, rows, TR, m, p, q, lk;
  cls := SpeciesClassesD(G); T := SpeciesTableD(G, cls); n := Length(cls);
  gram := List([1..n], i -> List([1..n], j -> Sum([1..n], k -> T[k][i]*T[k][j])));
  gsnf := ElementaryDivisorsMat(gram);
  fb := [];
  for i in [1..n] do
    F := Field(Rationals, T[i]);
    Add(fb, [DegreeOverPrimeField(F), Conductor(F),
             ForAll(T[i], x -> GaloisCyc(x,-1) = x)]);
  od;
  rows := Filtered([1..n], i -> ForAll(T[i], IsInt));
  TR := T{rows}; m := Length(rows); lk := [];
  for p in [1..m] do for q in [p+1..m] do
    Add(lk, DFL_v2(Gcd(List([1..n], j -> TR[p][j] - TR[q][j])))); od; od;
  return [gsnf, Collected(fb), Collected(lk)];
end;;

HuntBlock := function(order, d, cap)
  local ids, i, G, nsc, ab, es, ge, capskip, keys, mem, k, p, j, b, dk, dm, q,
        survivors, pr, r;
  ids := Filtered([1..NrSmallGroups(order)], i -> RankPGroup(SmallGroup(order,i)) = d);
  Print("### order ", order, ", d=", d, ": ", Length(ids), " groups ###\n");
  ab := []; es := []; ge := []; capskip := [];
  keys := []; mem := [];
  for i in ids do
    G := SmallGroup(order, i);
    if IsAbelian(G) then Add(ab, i); continue; fi;
    if IsExtraspecialD(G) then Add(es, i); continue; fi;
    # |G'|=2 = "generalized extraspecial" (central product E*A): near-abelian,
    # huge lattice, natural closed-form extension of the M_k theory -> pre-tag
    # cheaply (avoids enumerating the lattice just to hit the cap).
    if Size(DerivedSubgroup(G)) = 2 then Add(ge, i); continue; fi;
    nsc := Length(ConjugacyClassesSubgroups(G));
    if nsc > cap then Add(capskip, [i, nsc]); continue; fi;
    k := DKey(G);
    p := Position(keys, k);
    if p = fail then Add(keys, k); Add(mem, [i]); else Add(mem[p], i); fi;
  od;
  Print("  tagged ABELIAN (theory-rigid): ", Length(ab), "  ", ab, "\n");
  Print("  tagged EXTRASPECIAL (closed form): ", Length(es), "  ", es, "\n");
  Print("  tagged GEN-EXTRASPECIAL |G'|=2 (near-abelian, closed-form pending): ",
        Length(ge), "  ", ge, "\n");
  Print("  CAP-SKIP (|G'|>=4, nsc>", cap, ", generic RESIDUAL): ", Length(capskip),
        "  ", capskip, "\n");
  survivors := [];
  for j in [1..Length(keys)] do
    b := mem[j];
    if Length(b) <= 1 then continue; fi;
    Print("  [DKey collision] ", b, "\n");
    dk := []; dm := [];
    for i in b do
      k := DeepKeyD(SmallGroup(order, i));
      p := Position(dk, k);
      if p = fail then Add(dk, k); Add(dm, [i]); else Add(dm[p], i); fi;
    od;
    for q in [1..Length(dk)] do
      if Length(dm[q]) > 1 then
        Print("    *** SURVIVES GramSNF+fields+LINKAGE: ", dm[q], " ***\n");
        Add(survivors, dm[q]);
      else
        Print("    separated (deep key) -> ", dm[q], "\n");
      fi;
    od;
  od;
  Print("  == d=", d, " survivors: ", survivors, " ==\n");
  for b in survivors do for pr in Combinations(b,2) do
    if TomRowInvariantD(SmallGroup(order,pr[1])) <> TomRowInvariantD(SmallGroup(order,pr[2]))
    then Print("    ", pr, ": ToM differ (B not iso)\n");
    else Print("    ", pr, ": ToM agree\n"); fi;
  od; od;
  return rec(d:=d, abelian:=ab, extraspecial:=es, genextra:=ge,
             capskip:=capskip, survivors:=survivors);
end;;
