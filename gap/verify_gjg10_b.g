# Identify (xiv)/(xv) ids and verify Lemma 4.2: (ca^d)^p = a^{dp}
CheckP := function(p)
  local F, a, b, c, d4, rels, G14, G15, d, F3, aa, bb, cc, G1, G2, hom, ai, bi, ci, lhs, rhs, res;
  Print("=== p = ", p, " ===\n");
  # (xiv): <a,b,c,d | all^p, dc = acd, others commute>  = ((CpxCp):Cp) x Cp
  F := FreeGroup("a","b","c","d");
  rels := [F.1^p, F.2^p, F.3^p, F.4^p,
           F.4*F.3*(F.1*F.3*F.4)^-1,           # dc = a c d
           Comm(F.2,F.4), Comm(F.1,F.4), Comm(F.2,F.3), Comm(F.1,F.3), Comm(F.1,F.2)];
  G14 := F / rels;
  Print("  (xiv) IdGroup = ", IdGroup(G14), "\n");
  # (xv): <a,b,c,d | all^p, ab=ba, ac=ca, ad=da, cb=bc, db = abd, dc = bcd>
  rels := [F.1^p, F.2^p, F.3^p, F.4^p,
           Comm(F.1,F.2), Comm(F.1,F.3), Comm(F.1,F.4), Comm(F.3,F.2),
           F.4*F.2*(F.1*F.2*F.4)^-1,           # db = a b d
           F.4*F.3*(F.2*F.3*F.4)^-1];          # dc = b c d
  G15 := F / rels;
  Print("  (xv) IdGroup = ", IdGroup(G15), "\n");
  # Lemma 4.2 in (xii)/(xiii): (c a^d)^p = a^{dp}
  d := 1;
  F3 := FreeGroup("a","b","c");
  aa := F3.1; bb := F3.2; cc := F3.3;
  for res in [[1, "(xii)"], [First([2..p-1], x -> Jacobi(x,p) = -1), "(xiii)"]] do
    d := res[1];
    if res[2] = "(xii)" then
      rels := [aa^(p^2), bb^p, cc^p,
               bb*aa*(aa^(1+p)*bb)^-1, cc*aa*(aa^(1+p)*bb*cc)^-1, cc*bb*(aa^p*bb*cc)^-1];
    else
      rels := [aa^(p^2), bb^p, cc^p,
               bb*aa*(aa^(1+p)*bb)^-1, cc*aa*(aa^(1+d*p)*bb*cc)^-1, cc*bb*(aa^(d*p)*bb*cc)^-1];
    fi;
    G1 := F3 / rels;
    hom := IsomorphismPermGroup(G1);
    ai := Image(hom, G1.1); bi := Image(hom, G1.2); ci := Image(hom, G1.3);
    lhs := (ci*ai^d)^p; rhs := ai^(d*p);
    Print("  ", res[2], " d=", d, ": (ca^d)^p = a^{dp} : ", lhs = rhs,
          " ; ord(ca^d) = ", Order(ci*ai^d), " [p^2 = ", p^2, "]\n");
  od;
end;
for p in [5, 7, 11] do CheckP(p); od;
QUIT;
