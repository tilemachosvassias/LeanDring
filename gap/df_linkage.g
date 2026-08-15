# Canonical D_F linkage.
#
# D_F = ev_F(D(G)) at the Z-valued (rational, Galois-fixed) species = a
# ring-intrinsic quotient of D(G) (AL0).  For points p,q in F,
#     ell(p,q) = v2( gcd over D_F of (x_p - x_q) )
#              = v2( gcd_j (TR[p][j] - TR[q][j]) ),
# TR = the rational rows of the full species table (rational species x basis).
# The multiset { ell(p,q) : p<q } is a canonical D-isomorphism invariant
# (basis-permutation-invariant; gcd over a lattice = gcd over any generating
# set).  Two independent computations (direct gcd; gcd over an HNF basis of
# D_F) are provided and agree on every tested group.
#
# Validated: on (32,13/14) gives |F|=59 (matches the trace-corrected count) and
# SEPARATES them at depth 3 (confirming the predicted depth-3 sigma3/sigma7
# shadow); on (64,13/14) separates, rkD=170.

Read("gap/dring_sieve_standalone.g");

DFL_v2 := function(r) if r = 0 then return 999; fi; return PValuation(r, 2); end;;

# rational (Z-valued) species rows of the full species table
DFRationalRows := function(G)
  local cls, T, n, rows;
  cls := SpeciesClassesD(G);
  T := SpeciesTableD(G, cls);
  n := Length(cls);
  rows := Filtered([1..n], i -> ForAll(T[i], IsInt));
  return rec(TR := T{rows}, n := n, F := Length(rows));
end;;

# canonical D_F linkage multiset (direct gcd over basis columns)
DFLinkage := function(G)
  local d, TR, n, m, p, q, L, j;
  d := DFRationalRows(G);
  TR := d.TR; n := d.n; m := d.F; L := [];
  for p in [1..m] do for q in [p+1..m] do
    Add(L, DFL_v2(Gcd(List([1..n], j -> TR[p][j] - TR[q][j]))));
  od; od;
  return rec(F := m, rkD := n, bag := Collected(L));
end;;

# independent cross-check: gcd over an HNF Z-basis of the lattice D_F
DFLinkageHNF := function(G)
  local d, B, m, p, q, L, i;
  d := DFRationalRows(G);
  B := HermiteNormalFormIntegerMat(TransposedMat(d.TR));  # rows = basis of D_F
  m := d.F; L := [];
  for p in [1..m] do for q in [p+1..m] do
    Add(L, DFL_v2(Gcd(List([1..Length(B)], i -> B[i][p] - B[i][q]))));
  od; od;
  return rec(F := m, rkD := d.n, bag := Collected(L));
end;;
