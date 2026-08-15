# Does the intrinsic CONDUCTOR (ring-iso invariant) separate trivial decorations
# (decor-order 1 = F1) from involutions (decor-order 2)?  Both are Galois-fixed,
# so this tests the finest Galois-invariant refinement.  Disjoint => F1
# conductor-recognizable => D=>B.  Overlap => wall is below the conductor.
Read("gap/dring_sieve_standalone.g");;
DSelfTest();;

Conductor := function(G, c)     # per-species conductor (c a species record)
  local N, cnt, n;
  N := Normalizer(G, c.H); cnt := 0;
  for n in Elements(N) do
    if Image(c.nat, c.h ^ n) = c.q then cnt := cnt + 1; fi;
  od;
  return cnt / Size(c.Hp);
end;

Analyse := function(G, label)
  local cls, gal, n, i, j, gfix, dord, cond, c1, c2, coll;
  cls := SpeciesClassesD(G);
  gal := GaloisDataD(G, cls);
  n := Length(cls);
  gfix := List([1..n], i -> gal.perspecies[i] = 1);   # Galois-fixed
  dord := List([1..n], i -> Order(cls[i].q));
  cond := List([1..n], i -> Conductor(G, cls[i]));
  c1 := Set(Filtered([1..n], i -> gfix[i] and dord[i]=1), i -> cond[i]);
  c2 := Set(Filtered([1..n], i -> gfix[i] and dord[i]=2), i -> cond[i]);
  coll := 0;
  for i in [1..n] do for j in [1..n] do
    if i<>j and cls[i].Hidx=cls[j].Hidx and cond[i]=cond[j]
       and dord[i]=1 and dord[j]=2 then coll := coll+1; fi;
  od; od;
  Print("[", label, "] species=", n, " Galois-fixed=", Number(gfix,x->x),
        "\n     conductor-set F1(decor1)=", c1,
        "\n     conductor-set involutions(decor2)=", c2,
        "\n     GLOBAL separates? ", Intersection(c1,c2)=[],
        "  (overlap=", Intersection(c1,c2), ")",
        "\n     PER-FIBRE decor1/decor2 conductor collisions=", coll,
        " => ", ["SEPARATES","does NOT separate"][1+SignInt(coll)], "\n\n");
end;

Analyse(SmallGroup(32,27), "(32,27) rankZ=2 special");
Analyse(SmallGroup(32,32), "(32,32) rankZ=2 special");
Analyse(SmallGroup(64,135), "(64,135) isocat");
QUIT;
