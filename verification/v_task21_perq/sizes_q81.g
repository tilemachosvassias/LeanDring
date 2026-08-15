Q := 81;;
#
# v_task21_sizes.g -- fast pass: just get counts and |M| for every maximal,
# for a given q. Sizes are precomputed/stored by the package so this is
# always fast regardless of q. Bound vars: Q (integer).
#
# ClassicalMaximals is not part of the standard GAP distribution.  Point
# CLASSICAL_MAXIMALS_PATH at a checkout of it before running this script;
# if it is installed as an ordinary GAP package, leave it unbound.
if IsBound(CLASSICAL_MAXIMALS_PATH) then
  SetPackagePath("ClassicalMaximals", CLASSICAL_MAXIMALS_PATH);
fi;
LoadPackage("ClassicalMaximals");
SetInfoLevel(InfoClassicalMaximals, 0);
BreakOnError := false;;

if not IsBound(Q) then Print("ERROR: Q not bound\n"); QUIT; fi;

q := Q;;
Print("=== SIZES q = ", q, " ===\n");
Print("q mod 4 = ", q mod 4, "  q mod 3 = ", q mod 3, "  IsPrimeInt(q) = ",
      IsPrimeInt(q), "  Factors(q) = ", Factors(q), "\n");

ms := ClassicalMaximalsGeneric("S", 6, q);;
Print("S,6,", q, ": count=", Length(ms), "\n");
for i in [1..Length(ms)] do
    Print("S_SIZE_", i, ": ", Size(ms[i]), "\n");
od;

mo := ClassicalMaximalsGeneric("O", 7, q);;
Print("O,7,", q, ": count=", Length(mo), "\n");
for i in [1..Length(mo)] do
    Print("O_SIZE_", i, ": ", Size(mo[i]), "\n");
od;

Print("=== END SIZES q = ", q, " ===\n");
QUIT;
