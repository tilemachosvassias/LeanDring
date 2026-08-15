# v_task30_iota2_g2.g -- compute I(G2(q)) = { [S:N_S(A)] : 1 <> A abelian }
# for S = G2(3) and G2(4), by the exhaustive method of v_task29_iota2_lie.g:
# every N_S(A) of index <= bound lies in a maximal subgroup, so enumerating
# LowIndexSubgroups inside each small-index maximal covers all candidates.
#
# GAP has no native G2(q) constructor.  We pull standard generators from
# AtlasRep -- for G2(4) a permutation rep of degree 416 is stored directly;
# for G2(3) only matrix reps exist, so we take the 7-dim GF(3) module and
# act on its 1-spaces (smallest orbit has length 364).  Maximal subgroups
# come from the ATLAS "maxes" straight-line programs, which are complete.

LoadPackage("atlasrep");;
AtlasOfGroupRepresentationsInfo.remote := true;;

IsNormOfAb := function(G, N)
  local A;
  for A in Filtered(NormalSubgroupsAbove(N, TrivialSubgroup(N), []),
                    x -> Size(x) > 1 and IsAbelian(x)) do
    if Normalizer(G, A) = N then return true; fi;
  od;
  return false;
end;

GetMaxes := function(name, gens, nmax)
  local L, i, prg;
  L := [];
  for i in [1..nmax] do
    prg := AtlasProgram(name, "maxes", i);
    Add(L, rec(name := prg.subgroupname,
               grp  := Group(ResultOfStraightLineProgram(prg.program, gens))));
  od;
  return L;
end;

run := function(nm, G, gens, nmax, bound)
  local t, mx, res, M, i, N;
  t := Runtime();
  Print(nm, ": perm degree ", NrMovedPoints(G), ", |G| = ", Size(G), "\n");
  mx := GetMaxes(nm, gens, nmax);
  SortBy(mx, x -> Index(G, x.grp));
  Print("  maximal subgroups: ",
        List(mx, x -> [x.name, Index(G, x.grp)]), "\n");
  res := [];
  for M in mx do
    i := Index(G, M.grp);
    if i <= bound then
      if IsNormOfAb(G, M.grp) then
        Add(res, i); Print("    N_S(A) at index ", i, " : ", M.name, "\n");
      fi;
      if i * 2 <= bound then
        for N in LowIndexSubgroups(M.grp, QuoInt(bound, i)) do
          if Size(N) < Size(M.grp) and IsNormOfAb(G, N) then
            Add(res, Index(G, N));
            Print("    N_S(A) at index ", Index(G, N),
                  " (inside ", M.name, ")\n");
          fi;
        od;
      fi;
    fi;
  od;
  Print("  -> I(", nm, ") up to ", bound, ": ", Set(res),
        "   [", Int((Runtime() - t) / 1000), "s]\n\n");
end;

# ---- G2(3): 7-dim GF(3), act on 1-spaces (orbits 364/351/378) ----------
g3 := AtlasGroup("G2(3)", Ring, GF(3), Dimension, 7);;
orbs := OrbitsDomain(g3, NormedRowVectors(GF(3)^7), OnLines);;
Print("G2(3) orbit sizes on 1-spaces: ", List(orbs, Length), "\n");
o := orbs[PositionMinimum(List(orbs, Length))];;
hom := ActionHomomorphism(g3, o, OnLines, "surjective");;
P3 := Image(hom);;
run("G2(3)", P3, List(GeneratorsOfGroup(g3), x -> Image(hom, x)), 10, 4000);

# ---- G2(4): stored permutation rep of degree 416 -----------------------
P4 := AtlasGroup("G2(4)", NrMovedPoints, 416);;
run("G2(4)", P4, GeneratorsOfGroup(P4), 8, 8000);

# ---- G2(5): stored permutation rep of degree 3906 ----------------------
# bound 7800 < 2*iota_1 = 7812, so no proper subgroup of a parabolic can
# contribute; the scan is still exhaustive below the bound.
P5 := AtlasGroup("G2(5)", NrMovedPoints, 3906);;
run("G2(5)", P5, GeneratorsOfGroup(P5), 7, 7800);

# ---- the ratio trick for G2 (Sec.4ar/4at) ------------------------------
# iota_1 = (q^6-1)/(q-1); the Borel is always N_S(long root subgroup), so
# iota_2 <= (q+1)*iota_1 and hence n = 3 + 4*rho*iota_2/iota_1 <= 8q+11.
# m_1*iota_1 = C(n,3) then forces iota_1 | C(n,3) with C(n,3) >= iota_1.
Print("ratio trick for G2(q):\n");
for q in Filtered([3..400], IsPrimePowerInt) do
  i1 := (q^6-1)/(q-1);
  nmax := 8*q+11;
  hits := Filtered([4..nmax], n -> Binomial(n,3) >= i1
                                   and Binomial(n,3) mod i1 = 0);
  if hits <> [] or Binomial(nmax,3) >= i1 then
    Print("  q=", q, " iota1=", i1, " n<=", nmax,
          " C(nmax,3)=", Binomial(nmax,3), " n with iota1|C(n,3): ", hits, "\n");
  fi;
od;
Print("  (no line printed for a q means C(8q+11,3) < iota1: impossible)\n");
# only q = 3 leaves a candidate n; there iota_2/iota_1 = 1456/364 = 4 exactly,
# so n = 3 + 4*rho*4 with rho in {1/2,1,2}:
Print("  q=3: n = 3+16*rho = ", List([1/2,1,2], r -> 3+16*r),
      "  vs allowed n = [ 14, 28 ]  -> empty intersection\n");
# and at q = 4, iota_2/iota_1 = 2080/1365 = 32/21, so n = 3 + 128*rho/21
# is not even an integer:
Print("  q=4: n = 3+(128/21)*rho = ", List([1/2,1,2], r -> 3+128*r/21),
      "  -> not integral\n");

QUIT;
