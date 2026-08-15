# Independent audit of the class-count / det-ToM arithmetic underpinning
# sections 7l-7o (Lemmas 6CLS, FEWEST; cls(2^m) spectra; det ToM numerics).
# For every 2-group of order 4..64: #conjugacy classes of subgroups and
# det(TableOfMarks) = prod |N_G(H):H| = covol(B(G)).  Reports:
#  - all 2-groups with EXACTLY 6 subgroup classes (6CLS: must be Q8, C32);
#  - the class-count spectrum cls(2^m) per order;
#  - FEWEST: cyclic strictly fewest classes per order;
#  - det ToM for the groups cited in 7l-7o.

Print("=== class-count / det-ToM audit of RET-BR' sections 7l-7o ===\n");

six := [];
for m in [2,3,4,5,6] do
  ord := 2^m;
  ngr := NumberSmallGroups(ord);
  spectrum := [];
  cyc_classes := 0;
  min_classes := 10^9;
  for id in [1..ngr] do
    G := SmallGroup(ord, id);
    tom := TableOfMarks(G);
    ncls := Length(OrdersTom(tom));   # #conj classes of subgroups
    AddSet(spectrum, ncls);
    if ncls < min_classes then min_classes := ncls; fi;
    if IsCyclic(G) then cyc_classes := ncls; fi;
    if ncls = 6 then
      Add(six, [ord, id, StructureDescription(G)]);
    fi;
  od;
  Print("order ", ord, " (2^", m, "): ", ngr, " groups; cls-spectrum ",
        spectrum, "; cyclic has ", cyc_classes,
        "; min = ", min_classes,
        "; FEWEST(cyclic strict): ", cyc_classes = min_classes,
        " and unique-min: ",
        Number([1..ngr], id -> Length(OrdersTom(TableOfMarks(
          SmallGroup(ord,id)))) = min_classes) = 1, "\n");
od;

Print("\n2-groups with EXACTLY 6 subgroup classes (6CLS predicts Q8,C32):\n");
for x in six do Print("   ", x, "\n"); od;

Print("\n--- det ToM (= covol B(G)) for the cited groups ---\n");
cited := [ [8,4,"Q8"], [4,2,"V4"], [8,3,"D4"], [8,2,"C2xC4"],
           [16,14,"C2^3"], [8,5,"C2^3? check"], [32,1,"?"],
           [16,7,"?"], [16,9,"?"] ];
# resolve by structure instead of guessing ids:
targets := ["Q8","C4 x C2","D8","C2 x C2 x C2","C8","C32",
            "C2 x C2","Q16","D16","D8 : quotient"];
for spec in [ [4,"V4"], [8,"Q8"], [8,"D8"], [8,"C4xC2"], [8,"C2^3?"],
              [32,"C32"], [16,"Q16"], [16,"D16"], [16,"C2^3"] ] do
  ord := spec[1];
  for id in [1..NumberSmallGroups(ord)] do
    G := SmallGroup(ord,id);
    sd := StructureDescription(G);
    tom := TableOfMarks(G);
    det := DeterminantMat(MatTom(tom));
    ncls := Length(OrdersTom(tom));
    if sd = spec[2] or (spec[2]="V4" and sd="C2 x C2")
       or (spec[2]="Q8" and sd="Q8")
       or (spec[2]="D8" and sd="D8")
       or (spec[2]="C4xC2" and sd="C4 x C2")
       or (spec[2]="C32" and sd="C32")
       or (spec[2]="Q16" and sd="Q16")
       or (spec[2]="D16" and sd="D16")
       or (spec[2]="C2^3" and sd="C2 x C2 x C2")
       or (spec[2]="C2^3?" and sd="C2 x C2 x C2") then
      Print("   ", sd, " (ord ", ord, "): #classes=", ncls,
            ", det ToM=", det, " = 2^", LogInt(det,2), "\n");
    fi;
  od;
od;

# Q16/<z> = D8 (order 8 dihedral) class count check (7o oversized prediction)
Print("\n--- Q16 quotient by center: expect D8(order8) with... ---\n");
G := SmallGroup(16, 9);  # Q16
Print("   SmallGroup(16,9) = ", StructureDescription(G), "\n");
z := Centre(G);
Q := FactorGroup(G, z);
Print("   Q16/Z = ", StructureDescription(Q), ", #subgroup classes = ",
      Length(OrdersTom(TableOfMarks(Q))), "\n");

QUIT;
