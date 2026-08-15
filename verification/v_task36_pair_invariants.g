####################################################################
# v_task36_pair_invariants.g
#
# The PAIR invariant  I(K <= Abar) = { [Abar : N_Abar(A)] :
#   1 <> A <= K abelian },  S <= K <= Abar <= Aut(S)   (v_task34 / I3).
#
# Two exact tools.
#
# TOOL 1 (fusion of S-classes).  For S simple and A <= S abelian,
#   |A^Abar| = f * |A^S|,  f = [Abar : S . N_Abar(A)],
# because S is normal in Abar so the S-orbits inside an Abar-orbit are
# permuted transitively by Abar and hence all have equal size.  Thus
#   f = [ Out_Abar : Out_Abar cap D(A) ],
#   D(A) := { image in Out(S) of a in Aut(S) : A^a is S-conjugate to A }.
# D(A) is a subgroup of Out(S) and is computed EXACTLY by looping over
# the (few) elements of Out(S).  Consequence used everywhere:
#   *** two S-classes can fuse only if they have the SAME S-index. ***
#
# TOOL 2 (direct, for K > S).  I(K <= Abar) up to a bound b is obtained
# from LowIndexSubgroups(Abar,b): every value [Abar:N_Abar(A)] <= b is
# realised by N = N_Abar(A) of index <= b, and A is then a nontrivial
# abelian normal subgroup of N contained in K with N_Abar(A) = N.
# Exhaustive below b, no sampling.  (Same method as v_task34.)
####################################################################

LogTo();

######## Tool 2 ####################################################

PairIvals := function(K, Abar, bound)
  local res, N, A, i, wit, k;
  res := []; wit := rec();
  for N in LowIndexSubgroups(Abar, bound) do
    i := Index(Abar, N);
    for A in NormalSubgroups(N) do
      if Size(A) > 1 and IsAbelian(A) and IsSubset(K, A)
         and Normalizer(Abar, A) = N then
        Add(res, i);
        k := Concatenation("i", String(i));
        if not IsBound(wit.(k)) then wit.(k) := StructureDescription(A); fi;
        break;
      fi;
    od;
  od;
  return rec(vals := Set(res), wit := wit);
end;

reportPair := function(nm, K, Abar, bound)
  local r, v, s;
  r := PairIvals(K, Abar, bound);
  s := "";
  for v in r.vals do
    s := Concatenation(s, String(v), "(", r.wit.(Concatenation("i",String(v))), ") ");
  od;
  Print(nm, "   |K|=", Size(K), " |Abar|=", Size(Abar),
        "   I(K<=Abar) up to ", bound, " : ", r.vals, "\n");
  Print("      witnesses: ", s, "\n");
  return r.vals;
end;

######## Tool 1 ####################################################

# All S-classes of abelian 1 <> A <= S with [S:N_S(A)] <= bound.
AbelianClasses := function(S, bound)
  local reps, N, A, ind, new, r;
  reps := [];
  for N in LowIndexSubgroups(S, bound) do
    ind := Index(S, N);
    for A in NormalSubgroups(N) do
      if Size(A) > 1 and IsAbelian(A) and Normalizer(S, A) = N then
        new := true;
        for r in reps do
          if r.ind = ind and Size(r.sub) = Size(A)
             and RepresentativeAction(S, r.sub, A, OnPoints) <> fail then
            new := false; break;
          fi;
        od;
        if new then Add(reps, rec(ind := ind, sub := A,
                                  desc := StructureDescription(A))); fi;
      fi;
    od;
  od;
  Sort(reps, function(a,b) return a.ind < b.ind; end);
  return reps;
end;

# D(A) <= Out(S) : the outer classes stabilising the S-class of A.
# Returns rec(out, hom, aut) plus for each rep the list of Out-elements
# stabilising it, given as their position in Elements(Out).
FusionData := function(S, bound)
  local aut, inn, hom, out, els, pre, reps, r, i, stab, a, img, res;
  aut := AutomorphismGroup(S);
  inn := InnerAutomorphismsAutomorphismGroup(aut);
  hom := NaturalHomomorphismByNormalSubgroup(aut, inn);
  out := Image(hom);
  els := Elements(out);
  pre := List(els, o -> PreImagesRepresentative(hom, o));
  reps := AbelianClasses(S, bound);
  res := [];
  for r in reps do
    stab := [];
    for i in [1..Length(els)] do
      img := Image(pre[i], r.sub);
      if RepresentativeAction(S, r.sub, img, OnPoints) <> fail then
        Add(stab, i);
      fi;
    od;
    Add(res, rec(ind := r.ind, desc := r.desc, sub := r.sub,
                 stabpos := stab, D := Subgroup(out, els{stab})));
  od;
  return rec(out := out, els := els, hom := hom, aut := aut, cls := res);
end;

# For every subgroup U of Out(S) (i.e. every admissible Abar with K=S),
# print I(S <= Abar) = { [U : U cap D(A)] * ind(A) }.
reportFusion := function(nm, S, bound)
  local fd, U, subs, c, vals, f, line, i;
  Print("---- ", nm, "  |S|=", Size(S), "  bound=", bound, "\n");
  fd := FusionData(S, bound);
  Print("   Out(S) = ", StructureDescription(fd.out),
        " of order ", Size(fd.out), "\n");
  Print("   S-classes (index, structure, |D(A)|, [Out:D]):\n");
  for c in fd.cls do
    Print("      ", c.ind, "  ", c.desc, "   |D|=", Size(c.D),
          "   f_max=", Size(fd.out)/Size(c.D), "\n");
  od;
  subs := List(ConjugacyClassesSubgroups(fd.out), Representative);
  for U in subs do
    vals := [];
    for c in fd.cls do
      f := Size(U)/Size(Intersection(U, c.D));
      Add(vals, f * c.ind);
    od;
    Print("   Abar/S = ", StructureDescription(U), " (order ", Size(U),
          ") :  I(S<=Abar) = ", Set(vals), "\n");
  od;
  Print("\n");
  return fd;
end;


# ---- extra reporters -----------------------------------------------

# Just the S-class list with multiplicities (cheap: no AutomorphismGroup).
countCls := function(nm, S, bound)
  local reps, r;
  reps := AbelianClasses(S, bound);
  Print("---- classcount ", nm, " |S|=", Size(S), " bound=", bound, "\n");
  for r in reps do Print("      index ", r.ind, "   ", r.desc, "\n"); od;
  Print("      indices: ", List(reps, r->r.ind), "\n\n");
  return reps;
end;

permAut := function(S)
  return Image(IsomorphismPermGroup(AutomorphismGroup(S)));
end;

####################################################################
# The runs.  NOTE: these were executed as SEPARATE GAP processes
# (one per block) because the heavy rows need ~1h and 12g each;
# v_task36_pair_invariants_out.txt is their concatenation.
####################################################################

Print("################ PART 1: fusion tables I(S <= Abar), K = S ################\n\n");

reportFusion("L3(2) = L2(7) ", PSL(3,2), 30);
reportFusion("L4(2) = A8    ", PSL(4,2), 60);
reportFusion("A6            ", AlternatingGroup(6), 60);
reportFusion("A7            ", AlternatingGroup(7), 60);
reportFusion("A8            ", AlternatingGroup(8), 90);
reportFusion("A9            ", AlternatingGroup(9), 150);
reportFusion("L3(3)         ", PSL(3,3), 130);
reportFusion("S4(3) = U4(2) ", PSp(4,3), 60);
reportFusion("Sp6(2)        ", PSp(6,2), 140);
reportFusion("L3(4)         ", PSL(3,4), 110);
reportFusion("L4(3)         ", PSL(4,3), 135);
reportFusion("S4(4)         ", PSp(4,4), 260);
reportFusion("L5(2)         ", PSL(5,2), 160);

Print("\n######## PART 1b: class multiplicities only (AutomorphismGroup ########\n");
Print("######## infeasible / unnecessary: Out acts trivially or every ########\n");
Print("######## index value carries a UNIQUE class, so f = 1 by (C1)) ########\n\n");

countCls("U4(3)", PSU(4,3), 290);
countCls("U5(2)", PSU(5,2), 300);
countCls("S4(5)", PSp(4,5), 330);

Print("\n################ PART 2: K > S  (outer abelian subgroups) ################\n\n");

reportPair("A6 <= S6         ", AlternatingGroup(6), SymmetricGroup(6), 60);
reportPair("S6 <= S6         ", SymmetricGroup(6), SymmetricGroup(6), 60);
reportPair("A7 <= S7         ", AlternatingGroup(7), SymmetricGroup(7), 60);
reportPair("S7 <= S7         ", SymmetricGroup(7), SymmetricGroup(7), 60);
reportPair("A8 <= S8         ", AlternatingGroup(8), SymmetricGroup(8), 90);
reportPair("S8 <= S8         ", SymmetricGroup(8), SymmetricGroup(8), 90);
reportPair("A9 <= S9         ", AlternatingGroup(9), SymmetricGroup(9), 150);
reportPair("S9 <= S9         ", SymmetricGroup(9), SymmetricGroup(9), 150);
reportPair("L3(2) <= PGL(2,7)", PSL(2,7), PGL(2,7), 30);
reportPair("PGL(2,7) full    ", PGL(2,7), PGL(2,7), 30);

G := permAut(PSL(3,3));;
reportPair("L3(3).2  K = Abar", G, G, 130);
reportPair("L3(3).2  K = S   ", Socle(G), G, 130);

G := permAut(PSp(4,3));;
reportPair("U4(2).2  K = Abar", G, G, 60);
reportPair("U4(2).2  K = S   ", Socle(G), G, 60);

G := permAut(PSL(4,2));;
reportPair("S8 = A8.2 K=Abar ", G, G, 90);
reportPair("S8 = A8.2 K=socle", Socle(G), G, 90);

G := permAut(PSL(3,4));;
reportPair("L3(4).D12 K=Abar ", G, G, 110);

G := permAut(PSp(4,4));;
reportPair("S4(4).4   K=Abar ", G, G, 260);

Print("\n### done\n");
