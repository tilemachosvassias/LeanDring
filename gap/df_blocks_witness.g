# df_blocks_witness.g -- extract an explicit counterexample to the former
# S-subset-R lemma for the nonabelian D_F block model.
#
# Checked against SmallGroup(32,7), where results/df_nonabelian_snf_blocks.md
# reports the first failures.  Exact GAP group arithmetic only.

IsFusedRationalImage := function(G, H, h)
  local Hp, hom, A, a, N, orb, j;
  Hp := DerivedSubgroup(H);
  hom := NaturalHomomorphismByNormalSubgroupNC(H, Hp);
  A := Image(hom);
  a := Image(hom, h);
  N := Normalizer(G, H);
  orb := Set(Elements(N), n -> Image(hom, h^n));
  for j in Filtered([1..Order(a)], x -> IsOddInt(x)) do
    if not a^j in orb then
      return false;
    fi;
  od;
  return true;
end;

FusedRationalData := function(G, H, h)
  local Hp, hom, a, N, orb, powers;
  Hp := DerivedSubgroup(H);
  hom := NaturalHomomorphismByNormalSubgroupNC(H, Hp);
  a := Image(hom, h);
  N := Normalizer(G, H);
  orb := Set(Elements(N), n -> Image(hom, h^n));
  powers := List(Filtered([1..Order(a)], x -> IsOddInt(x)), j -> a^j);
  return rec(derived := Hp, quotient := Image(hom), image := a,
             normalizer := N, orbit := orb, oddPowers := powers);
end;

FindDFBlockWitness := function(ord, id)
  local G, subs, H, K, h, dH, dK, inverter;
  G := SmallGroup(ord, id);
  subs := AllSubgroups(G);
  for H in subs do
    if Size(H) > 1 then
      for h in Elements(H) do
        if IsFusedRationalImage(G, H, h) then
          for K in subs do
            if Size(H) < Size(K) and Size(K) < Size(G)
               and IsSubgroup(K, H)
               and not IsFusedRationalImage(G, K, h) then
              dH := FusedRationalData(G, H, h);
              dK := FusedRationalData(G, K, h);
              inverter := First(Elements(dH.normalizer),
                                n -> h^n * h in DerivedSubgroup(H));
              Print("GROUP: SmallGroup(", ord, ",", id, ") = ",
                    StructureDescription(G), "\n");
              Print("G generators: ", GeneratorsOfGroup(G), "\n");
              Print("H: size ", Size(H), ", structure ",
                    StructureDescription(H), ", generators ",
                    GeneratorsOfGroup(H), ", minimal generators ",
                    MinimalGeneratingSet(H), "\n");
              Print("K: size ", Size(K), ", structure ",
                    StructureDescription(K), ", generators ",
                    GeneratorsOfGroup(K), ", minimal generators ",
                    MinimalGeneratingSet(K), "\n");
              Print("h: ", h, ", order ", Order(h), "\n");
              Print("H': ", GeneratorsOfGroup(dH.derived),
                    "; A_H = ", StructureDescription(dH.quotient),
                    "; image order ", Order(dH.image), "\n");
              Print("N_G(H): size ", Size(dH.normalizer), ", generators ",
                    GeneratorsOfGroup(dH.normalizer), "\n");
              Print("H image orbit: ", dH.orbit,
                    "; odd powers: ", dH.oddPowers, "\n");
              Print("inverting element for H: ", inverter,
                    "; lies in N_G(K): ", inverter in dK.normalizer, "\n");
              Print("K': ", GeneratorsOfGroup(dK.derived),
                    "; A_K = ", StructureDescription(dK.quotient),
                    "; image order ", Order(dK.image), "\n");
              Print("N_G(K): size ", Size(dK.normalizer), ", generators ",
                    GeneratorsOfGroup(dK.normalizer), "\n");
              Print("K image orbit: ", dK.orbit,
                    "; odd powers: ", dK.oddPowers, "\n");
              return rec(G := G, H := H, K := K, h := h,
                         Hdata := dH, Kdata := dK);
            fi;
          od;
        fi;
      od;
    fi;
  od;
  return fail;
end;

witness := FindDFBlockWitness(32, 7);;
if witness = fail then
  Error("no witness found");
fi;
QUIT;
