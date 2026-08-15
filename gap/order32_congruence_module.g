# order32_congruence_module.g -- exact order-two congruence-module pilot for
# SmallGroup(32,49) and SmallGroup(32,50).
#
# Reads the committed integer species matrices, recomputes their Smith
# divisors, identifies C_2(D)[2] as the binary left orthogonal of D_F mod
# 2, and classifies its inclusion-minimal nonzero supports in the rank-one
# case. The subgroup labels are regenerated to locate the top G-fibre for
# the ground-truth FW2 comparison.

Read("gap/dring_sieve_standalone.g");

Brief9Pilot := function(id)
  local G, cls, mat, n, top, ed, mod2, base, check, minimalCount;

  Read(Concatenation("results/G32_", String(id), "_mat.g"));
  mat := ValueGlobal("DFMAT");
  n := Length(mat);
  ed := ElementaryDivisorsMat(mat);

  mod2 := List(mat, row -> List(row, x -> x mod 2));
  # mat has species as rows and basis generators as columns, so D_F is
  # the column lattice. Functionals a/2 satisfy TransposedMat(mat)*a=0.
  base := BaseIntMat(TransposedMat(mod2));
  if Length(base) <> 1 then
    Error("pilot expects rank one modulo 2");
  fi;
  check := Filtered([1..n], i -> base[1][i] <> 0);

  G := SmallGroup(32, id);
  cls := SpeciesClassesD(G);
  top := Filtered([1..Length(cls)], i -> Size(cls[i].H) = 32);
  if check <> [1..n] then
    Error("parity-check support is not the full coordinate set");
  fi;

  # For the even-weight code, the inclusion-minimal nonzero supports are
  # exactly all coordinate pairs.
  minimalCount := Binomial(Length(check), 2);

  Print("SmallGroup(32,", id, ")\n");
  Print("  Smith divisors: ", Collected(ed), "\n");
  Print("  rank over F_2: ", Length(base), "\n");
  Print("  parity-check support size: ", Length(check), " (all coordinates)\n");
  Print("  top-fibre coordinates: ", top, "\n");
  Print("  minimal supports: all ", minimalCount,
        " coordinate pairs\n");
  Print("  nontrivial order-two cyclic submodules: 2^", n - 1, " - 1\n");
  Print("  pair-support overlap graph: line graph L(K_", n,
        "), degree ", 2 * (Length(check) - 2), "\n");

  UnbindGlobal("DFMAT");
end;

Brief9Pilot(49);
Brief9Pilot(50);
QUIT;
