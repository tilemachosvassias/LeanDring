# v_task14_ineq.g
# PART B (v_task14, NOTES §4d/§4p): INEQ extension via the PROVEN radical
# census formulas.  Pure exact-rational formula evaluation, no groups.
#
# qBin(k,d) = Gaussian binomial [k,d]_2.
# I'_w(2m)  = # isotropic w-subspaces of nondegenerate symplectic 2m-space.
# S_w^eps(2m) = # totally singular w-subspaces of nondeg. quadratic space of
#   type eps (eps in {"plus","minus"}) on a 2m-dim space (w <= m for plus,
#   w <= m-1 for minus).
#
# Extraspecial: r_eps(n) = T3(2n) + T2nd(2n) + T1_eps(2n).
# Radical census (H = E_eps' x C2^rho, dim V = 2n, radical dim rho):
#   r(2n,rho,eps') = T3(2n) + T2(2n,rho) + T1(2n,rho,eps').

qBin := function(k, d)
  local i, num, den;
  if d < 0 or d > k then return 0; fi;
  if d = 0 or d = k then return 1; fi;
  num := 1; den := 1;
  for i in [0..d-1] do
    num := num * (2^(k-i) - 1);
    den := den * (2^(i+1) - 1);
  od;
  return num/den;
end;;

# I'_w(twom): isotropic w-subspaces of nondegenerate symplectic space dim twom
IwPrime := function(twom, w)
  local i, num, den;
  if w = 0 then return 1; fi;
  num := 1; den := 1;
  for i in [0..w-1] do
    num := num * (2^(twom - 2*i) - 1);
    den := den * (2^(i+1) - 1);
  od;
  return num/den;
end;;

# S_w^eps(twom): totally singular w-subspaces of nondeg. quadratic space,
# type eps in {"plus","minus"}, dim twom = 2m.
SwType := function(twom, w, eps)
  local m, i, num, den, a, b;
  m := twom / 2;
  if w = 0 then return 1; fi;
  num := 1; den := 1;
  for i in [0..w-1] do
    if eps = "plus" then
      a := 2^(m-i) - 1; b := 2^(m-i-1) + 1;
    else
      a := 2^(m-i) + 1; b := 2^(m-i-1) - 1;
    fi;
    num := num * a * b;
    den := den * (2^(i+1) - 1);
  od;
  return num/den;
end;;

T3 := twom -> Sum([0..twom], d -> qBin(twom, d) * 2^d);;

T2nd := twom -> Sum([0..twom/2], w -> IwPrime(twom, w));;

T1eps := function(twom, eps)
  local m;
  m := twom / 2;
  if eps = "plus" then
    return Sum([0..m], w -> SwType(twom, w, eps) * 2^w);
  else
    return Sum([0..m-1], w -> SwType(twom, w, eps) * 2^w);
  fi;
end;;

rExtraspecial := function(n, eps)
  return T3(2*n) + T2nd(2*n) + T1eps(2*n, eps);
end;;

# radical census helper sums
J := function(w, rho)
  return Sum([0..rho], r0 -> qBin(rho, r0) * 2^(w*(rho-r0) + r0));
end;;

K := function(w, rho)
  return Sum([0..rho], r0 -> qBin(rho, r0) * 2^(w*(rho-r0)) * 2^((w+r0)+r0));
end;;

T2census := function(twon, rho)
  local twomp;
  twomp := twon - rho;
  return Sum([0..twomp/2], w -> IwPrime(twomp, w) * J(w, rho));
end;;

T1census := function(twon, rho, eps)
  local twomp, mp;
  twomp := twon - rho;
  mp := twomp / 2;
  if eps = "plus" then
    return Sum([0..mp], w -> SwType(twomp, w, eps) * K(w, rho));
  else
    return Sum([0..mp-1], w -> SwType(twomp, w, eps) * K(w, rho));
  fi;
end;;

rRadical := function(twon, rho, eps)
  return T3(twon) + T2census(twon, rho) + T1census(twon, rho, eps);
end;;

# ---------------- anchor checks (MUST match) ----------------
Print("=== ANCHOR CHECKS: extraspecial r_eps(n) ===\n");
Print("r_+(1) = ", rExtraspecial(1,"plus"),  "  expected 20   match: ", rExtraspecial(1,"plus")  = 20,  "\n");
Print("r_-(1) = ", rExtraspecial(1,"minus"), "  expected 16   match: ", rExtraspecial(1,"minus") = 16,  "\n");
Print("r_+(2) = ", rExtraspecial(2,"plus"),  "  expected 381  match: ", rExtraspecial(2,"plus")  = 381, "\n");
Print("r_-(2) = ", rExtraspecial(2,"minus"), "  expected 349  match: ", rExtraspecial(2,"minus") = 349, "\n");
Print("r_+(3) = ", rExtraspecial(3,"plus"),  "  expected 27632  match: ", rExtraspecial(3,"plus")  = 27632, "\n");
Print("r_-(3) = ", rExtraspecial(3,"minus"), "  expected 27136  match: ", rExtraspecial(3,"minus") = 27136, "\n");

Print("\n=== ANCHOR CHECKS: radical census r(2n,rho,eps') ===\n");
Print("r(4,2,hyp) = ", rRadical(4,2,"plus"),  "  expected 583    match: ", rRadical(4,2,"plus")  = 583,   "\n");
Print("r(4,2,ell) = ", rRadical(4,2,"minus"), "  expected 407    match: ", rRadical(4,2,"minus") = 407,   "\n");
Print("r(6,2,hyp) = ", rRadical(6,2,"plus"),  "  expected 30099  match: ", rRadical(6,2,"plus")  = 30099, "\n");
Print("r(6,2,ell) = ", rRadical(6,2,"minus"), "  expected 27827  match: ", rRadical(6,2,"minus") = 27827, "\n");
Print("r(6,4,hyp) = ", rRadical(6,4,"plus"),  "  expected 51395  match: ", rRadical(6,4,"plus")  = 51395, "\n");
Print("r(6,4,ell) = ", rRadical(6,4,"minus"), "  expected 31747  match: ", rRadical(6,4,"minus") = 31747, "\n");

allAnchors := rExtraspecial(1,"plus") = 20 and rExtraspecial(1,"minus") = 16
  and rExtraspecial(2,"plus") = 381 and rExtraspecial(2,"minus") = 349
  and rExtraspecial(3,"plus") = 27632 and rExtraspecial(3,"minus") = 27136
  and rRadical(4,2,"plus") = 583 and rRadical(4,2,"minus") = 407
  and rRadical(6,2,"plus") = 30099 and rRadical(6,2,"minus") = 27827
  and rRadical(6,4,"plus") = 51395 and rRadical(6,4,"minus") = 31747;;
Print("\nALL ANCHORS MATCH: ", allAnchors, "\n");

# ---------------- main sweep: n = 4..8 ----------------
if allAnchors = false then
  Print("*** ANCHOR MISMATCH -- SKIPPING n=4..8 sweep ***\n");
else
Print("\n=== INEQ EXTENSION: n = 4..8 ===\n");
for n in [4..8] do
  rplus := rExtraspecial(n, "plus");
  rows := [];
  for rho in Filtered([2..2*n-2], x -> x mod 2 = 0) do
    for eps in ["plus", "minus"] do
      Add(rows, [rho, eps, rRadical(2*n, rho, eps)]);
    od;
  od;
  minval := Minimum(List(rows, x -> x[3]));
  argmin := [];
  for row in rows do
    if row[3] = minval then Add(argmin, [row[1], row[2]]); fi;
  od;
  Print("n=", n, "  2n=", 2*n, "  r_+(n)=", rplus, "\n");
  for row in rows do
    Print("    rho=", row[1], " eps=", row[2], "  r=", row[3],
          "  margin over r_+=", row[3] - rplus, "\n");
  od;
  Print("  MIN over (rho,eps'): ", minval, "  at ", argmin,
        "  margin=", minval - rplus,
        "  VERDICT: ", minval > rplus, "\n\n");
od;
fi;

Print("DONE\n");
QUIT;
