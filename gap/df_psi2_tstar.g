# df_psi2_tstar.g -- the psi_2 Adams operation T:(K,[y]) |-> (K,[y^2]) as a
# canonical D-invariant.  T is a ring endomorphism of D(G); rk(T^k) over GF(2),
# the fixed-point count, and the in-degree multiset of the T-functional-graph are
# D-iso invariants that need NO species table (only the squaring map on decorations).
#
# Validated separator: on (64,13/14) [previous sieve frontier] the GF(2) rank
# profile differs -- [67,38,32,32] vs [66,38,32,32].  On (128,1597/1598) [order-128
# frontier] every T-invariant coincides (see results/opus_order128_hunt_final.md).
#
# Usage:  Read this after dring_sieve_standalone.g, then  Tfingerprint(order,id);
Tfingerprint := function(ord, id)
  local G,cls,n,i,j,qi2,hidx,N,tmap,indeg,F,M,Mk,prof,r;
  G := SmallGroup(ord, id); cls := SpeciesClassesD(G); n := Length(cls); tmap := [];
  for i in [1..n] do
    qi2 := cls[i].q^2; hidx := cls[i].Hidx; N := Normalizer(G, cls[i].H);
    for j in [1..n] do
      if cls[j].Hidx = hidx and
         ForAny(Elements(N), g -> Image(cls[j].nat, PreImagesRepresentative(cls[j].nat, qi2)^g) = cls[j].q)
      then tmap[i] := j; break; fi;
    od;
  od;
  indeg := List([1..n], x -> 0);
  for i in [1..n] do indeg[tmap[i]] := indeg[tmap[i]] + 1; od;
  F := GF(2); M := NullMat(n, n, F);
  for i in [1..n] do M[i][tmap[i]] := One(F); od;
  Mk := IdentityMat(n, F); prof := [];
  for r in [1..4] do Mk := Mk * M; Add(prof, RankMat(Mk)); od;
  return rec(rkD := n,
             rankprofile := prof,
             fixed := Number([1..n], i -> tmap[i] = i),
             indegree := Collected(indeg));
end;;
