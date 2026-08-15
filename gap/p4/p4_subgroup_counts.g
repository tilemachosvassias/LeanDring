# p4_subgroup_counts.g — settle the disputed subgroup-count row of the
# order-p^4 table, WITHOUT relying on any Roman-numeral <-> SmallGroup
# dictionary.
#
# THE DISPUTE
#   paper, Remark 3.10:            (xii),(xiii) have N_{p^2} = p^2 + p + 1
#   results/gjg10_verification_p4_table.md (GAP 4.15.1, 2026-07-18):
#                                  (xii),(xiii) have N_{p^2} = 2p^2 + p + 1
# If the second is right, then (x), (xi), (xii), (xiii) all share the count
# triple and Step 2 of Proposition 3.11 collapses. The two disagree because
# they identify the Roman numerals with different SmallGroup IDs.
#
# THE FIX: build the groups (xii) and (xiii) from the paper's OWN
# presentations, equations (3) and (4) of Section 4:
#
#   (xii)  <a,b,c | a^{p^2} = b^p = c^p = 1, ba = a^{1+p} b,
#                   ca = a^{1+p} c,  cb = a^p b c >
#   (xiii) <a,b,c | a^{p^2} = b^p = c^p = 1, ba = a^{1+p} b,
#                   ca = a^{1+dp} c, cb = a^{dp} b c >,   d a non-residue
#
# and count subgroups directly. No dictionary is involved, so the answer
# settles the paper's table row on its own terms. We also report IdGroup,
# so the dictionary used by the 2026-07-18 audit can be checked afterwards.
#
# Usage:  gap -q < gap/p4/p4_subgroup_counts.g > results/p4_subgroup_counts.log

CountsOf := function(G, p)
  # returns [ N_p, N_{p^2}, N_{p^3} ] : number of subgroups of each order
  local cl, n1, n2, n3, c, H;
  n1 := 0; n2 := 0; n3 := 0;
  for c in ConjugacyClassesSubgroups(G) do
    H := Representative(c);
    if   Size(H) = p   then n1 := n1 + Size(c);
    elif Size(H) = p^2 then n2 := n2 + Size(c);
    elif Size(H) = p^3 then n3 := n3 + Size(c);
    fi;
  od;
  return [n1, n2, n3];
end;

# the two presentations, parameterized by d (d = 1 gives (xii))
TwinGroup := function(p, d)
  local F, a, b, c, rels;
  F := FreeGroup("a", "b", "c");
  a := F.1; b := F.2; c := F.3;
  rels := [ a^(p^2), b^p, c^p,
            b*a*(a^(1+p)*b)^-1,
            c*a*(a^(1+d*p)*c)^-1,
            c*b*(a^(d*p)*b*c)^-1 ];
  return F / rels;
end;

NonResidue := function(p)
  local d;
  for d in [2 .. p-1] do
    if not d in List([1..p-1], x -> (x^2) mod p) then return d; fi;
  od;
  return fail;
end;

for p in [5, 7, 11] do
  Print("\n======== p = ", p, " ========\n");
  d := NonResidue(p);
  Print("quadratic non-residue d = ", d, "\n");

  for pair in [ ["(xii)  d=1", 1], [Concatenation("(xiii) d=", String(d)), d] ] do
    G := TwinGroup(p, pair[2]);
    P := Image(IsomorphismPermGroup(G));
    Print("\n", pair[1], "\n");
    Print("  |G| = ", Size(P), "   (must be ", p^4, ")\n");
    if Size(P) <> p^4 then
      Print("  !! presentation does not have order p^4 -- relators wrong\n");
      continue;
    fi;
    Print("  IdGroup       = ", IdGroup(P), "\n");
    Print("  exponent      = ", Exponent(P), "\n");
    Print("  |G'|          = ", Size(DerivedSubgroup(P)), "\n");
    Print("  |G^ab|        = ", Size(P)/Size(DerivedSubgroup(P)), "\n");
    cnt := CountsOf(P, p);
    Print("  (N_p, N_p2, N_p3) = ", cnt, "\n");
    Print("  paper predicts      [ ", p^2+p+1, ", ", p^2+p+1, ", ", p+1, " ]\n");
    Print("  audit file predicts [ ", p^2+p+1, ", ", 2*p^2+p+1, ", ", p+1, " ]\n");
    if cnt = [p^2+p+1, p^2+p+1, p+1] then
      Print("  ==> PAPER IS RIGHT\n");
    elif cnt = [p^2+p+1, 2*p^2+p+1, p+1] then
      Print("  ==> AUDIT FILE IS RIGHT -- Remark 3.10 and Prop 3.11 Step 2 must change\n");
    else
      Print("  ==> NEITHER -- investigate\n");
    fi;
  od;

  # For completeness: the counts of every group of order p^4, so the
  # Roman-numeral dictionary can be rebuilt from scratch if needed.
  Print("\n  all groups of order ", p^4, " (id : counts : |G^ab| : exponent):\n");
  for i in [1 .. NrSmallGroups(p^4)] do
    H := SmallGroup(p^4, i);
    Print("    ", i, " : ", CountsOf(H, p),
          " : ", Size(H)/Size(DerivedSubgroup(H)),
          " : ", Exponent(H),
          Concatenation(" : ", String(IsAbelian(H))), "\n");
  od;
od;

Print("\n== done ==\n");
QUIT;
