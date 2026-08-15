LoadPackage("ctbllib");;
# iota(S) <= smallest nontrivial conjugacy class size  (N(<x>) >= C(x)).
names := ["M11","M12","M22","M23","M24","J1","J2","J3","HS","McL","He","Ru","Suz",
          "Co1","Co2","Co3","Fi22","Fi23","Fi24'","HN","Th","ON","Ly","J4","B","M"];
for nm in names do
  t := CharacterTable(nm);
  if t = fail then continue; fi;
  szs := Filtered(SizesConjugacyClasses(t), s -> s > 1);
  Print(nm, " ", Size(t), " ", Minimum(szs), "\n");
od;
QUIT;
