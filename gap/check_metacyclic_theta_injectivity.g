# Exact small regression for the proposed top-conductor Theta injectivity.
# Enumerates valid presentations with m=4, n=1..3, retains groups of
# maximal element order 16, and compares the cyclic-spine Theta signature
# with IdGroup.  This is a falsification guard, not a proof.

ThetaSignature := function(G, M)
  local classes, answer, class, C, generator, normalizer, image, x, k;
  classes := Filtered(ConjugacyClassesSubgroups(G), class ->
    IsCyclic(Representative(class)) and Size(Representative(class)) = M);
  answer := [];
  for class in classes do
    C := Representative(class);
    generator := First(Elements(C), x -> Order(x) = M);
    normalizer := Normalizer(G, C);
    image := [];
    for x in Elements(normalizer) do
      k := First([0..M-1], k -> generator^x = generator^k);
      AddSet(image, k);
    od;
    Add(answer, image);
  od;
  Sort(answer);
  return answer;
end;

NormalSpineCount := function(G, M)
  return Number(ConjugacyClassesSubgroups(G), class ->
    IsCyclic(Representative(class)) and
    Size(Representative(class)) = M and
    Size(Normalizer(G, Representative(class))) = Size(G));
end;

PrincipalUnits := function(M, s)
  return Filtered([1,3..M-1], x -> (x-1) mod 2^s = 0);
end;

ExpectedNearTheta := function(M, n, d)
  local answer, s, i;
  answer := [];
  for i in [1..2^d] do Add(answer, PrincipalUnits(M, d)); od;
  for s in [d+1..n] do
    for i in [1..2^(d-1)] do Add(answer, PrincipalUnits(M, s)); od;
  od;
  Sort(answer);
  return answer;
end;

RankD := function(G)
  local total, class, K, derived, normalizer, cosets, action;
  total := 0;
  for class in ConjugacyClassesSubgroups(G) do
    K := Representative(class);
    derived := DerivedSubgroup(K);
    normalizer := Normalizer(G, K);
    cosets := RightCosets(K, derived);
    action := function(coset, g)
      return RightCoset(derived, Representative(coset)^g);
    end;
    total := total + Length(OrbitsDomain(normalizer, cosets, action));
  od;
  return total;
end;

PresentationGroup := function(m, n, u, t)
  local M, N, F, a, b, Q, iso;
  M := 2^m; N := 2^n;
  F := FreeGroup("a", "b"); a := F.1; b := F.2;
  Q := F / [a^M, b^N/a^t, a^b/a^u];
  iso := IsomorphismPcGroup(Q);
  return Image(iso);
end;

RunThetaCheck := function()
  local m, M, n, N, u, t, G, key, position, keys, ids, id,
        presentations, collisions, i, d, nearChecks, rankedKeys,
        rankedIds, rankedPosition, rankedCollisions, rank;
  m := 4; M := 2^m;
  nearChecks := 0;
  keys := []; ids := []; presentations := [];
  rankedKeys := []; rankedIds := [];
  for n in [1..3] do
    N := 2^n;
    for u in Filtered([1,3..M-1], u -> PowerModInt(u, N, M) = 1) do
      for t in Filtered([0..M-1], t -> (u-1)*t mod M = 0) do
        G := PresentationGroup(m, n, u, t);
        if Size(G) <> M*N then Error("presentation collapsed"); fi;
        if Maximum(List(Elements(G), Order)) <> M then
          continue;
        fi;
        key := ThetaSignature(G, M);
        rank := RankD(G);
        if u <> 1 then
          d := PValuation(u-1, 2);
          if 2 <= d and d <= n then
            if NormalSpineCount(G, M) <> 2^d then
              Error("near-identity normal-spine formula failed");
            fi;
            if key <> ExpectedNearTheta(M, n, d) then
              Error("near-identity Theta formula failed");
            fi;
            nearChecks := nearChecks + 1;
          fi;
        fi;
        id := IdGroup(G);
        position := Position(keys, key);
        if position = fail then
          Add(keys, key); Add(ids, [id]);
          Add(presentations, [[n,u,t,id]]);
        else
          AddSet(ids[position], id);
          Add(presentations[position], [n,u,t,id]);
        fi;
        rankedPosition := Position(rankedKeys, [key, rank]);
        if rankedPosition = fail then
          Add(rankedKeys, [key, rank]); Add(rankedIds, [id]);
        else
          AddSet(rankedIds[rankedPosition], id);
        fi;
      od;
    od;
  od;
  collisions := Filtered([1..Length(keys)], i -> Length(ids[i]) > 1);
  rankedCollisions := Filtered([1..Length(rankedKeys)],
    i -> Length(rankedIds[i]) > 1);
  Print("theta signatures: ", Length(keys), "\n");
  Print("near-identity formula checks: ", nearChecks, "\n");
  Print("nonisomorphic collision buckets: ", Length(collisions), "\n");
  for i in collisions do
    Print("COLLISION ids=", ids[i], " theta=", keys[i], "\n");
    Print(" presentations=", presentations[i], "\n");
  od;
  Print("Theta+rank nonisomorphic collision buckets: ",
        Length(rankedCollisions), "\n");
  for i in rankedCollisions do
    Print("RANKED COLLISION ids=", rankedIds[i],
          " key=", rankedKeys[i], "\n");
  od;
end;

RunThetaCheck();
QUIT;
