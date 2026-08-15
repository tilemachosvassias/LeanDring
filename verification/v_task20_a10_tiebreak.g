# v_task20_a10_tiebreak.g -- A10 vs twin#2 (S6 x A7, from v_task20_a10.g)
# TIE on mult1: both = 4 exactly. Need a secondary proven-cheap invariant
# (v_task16 method: nr conjugacy classes + involution count, exact from
# character tables / direct group construction) to separate this specific
# pair.

Print("=== A10 ===\n");
tA10 := CharacterTable("A10");;
ncA10 := NrConjugacyClasses(tA10);;
ordsA10 := OrdersClassRepresentatives(tA10);;
sizesA10 := SizesConjugacyClasses(tA10);;
invA10 := Sum(Filtered([1..Length(ordsA10)], i -> ordsA10[i]=2), i -> sizesA10[i]);;
Print("A10: |A10|=", Size(tA10), " nrClasses=", ncA10, " involutions=", invA10, "\n");

Print("\n=== twin#2 = S6 x A7 ===\n");
T2 := DirectProduct(SymmetricGroup(6), AlternatingGroup(7));;
Print("|T2|=", Size(T2), " (expect 1814400)\n");
t0 := Runtime();;
ccT2 := ConjugacyClasses(T2);;
Print("ConjugacyClasses computed, time(ms)=", Runtime()-t0, " nrClasses=", Length(ccT2), "\n");
invT2 := 0;;
for c in ccT2 do
  if Order(Representative(c)) = 2 then
    invT2 := invT2 + Size(c);
  fi;
od;
Print("twin#2 (S6 x A7): nrClasses=", Length(ccT2), " involutions=", invT2, "\n");

Print("\n=== VERDICT ===\n");
if ncA10 <> Length(ccT2) then
  Print("SEPARATED by nr classes: A10=", ncA10, " vs twin#2=", Length(ccT2), "\n");
elif invA10 <> invT2 then
  Print("SEPARATED by involution count: A10=", invA10, " vs twin#2=", invT2, "\n");
else
  Print("NOT SEPARATED by nrClasses or involutions either -- both TIE. Further invariant needed.\n");
fi;
Print("=== DONE a10_tiebreak ===\n");
