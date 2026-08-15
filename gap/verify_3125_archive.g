# verify_3125_archive.g
#
# Exact, fast checks on the archived 2724 x 2724 species tables for
# SmallGroup(3125,68) and SmallGroup(3125,69).  This does NOT recompute either
# table.  It verifies the recovered permutation certificate entry by entry,
# checks the block-start ([H,1]) columns, and checks the full Galois row action.
#
# Run from the project root:
#   gap -q gap/verify_3125_archive.g
#
# Override the archive location before Read(), if necessary:
#   ArchiveRoot := "/path/to/gap/archive/";;
#   Read("gap/verify_3125_archive.g");

if not IsBound(ArchiveRoot) then
    ArchiveRoot := "gap/legacy/preprint_archive/";
fi;

Read(Concatenation(ArchiveRoot, "G3125_68"));
Read(Concatenation(ArchiveRoot, "G3125_69"));
Read("results/n_test_3125/perm3125.g");

BlockStarts3125 := function(T)
    local starts, n, j, size;
    starts := [];
    n := Length(T);
    j := 1;
    while j <= n do
        Add(starts, j);
        size := 1;
        while j + size <= n and T[j + size][j] <> 0 do
            size := size + 1;
        od;
        j := j + size;
    od;
    return starts;
end;

CheckCertificate3125 := function(A, B)
    local pR, ipC, n, i, j;
    pR := MappingPermListList(PRow[1], PRow[2]);
    ipC := Inverse(MappingPermListList(PCol[1], PCol[2]));
    n := Length(A);
    if Length(B) <> n then return false; fi;
    for i in [1..n] do
        if Length(A[i]) <> n or Length(B[i]) <> n then return false; fi;
        for j in [1..n] do
            if B[i ^ pR][j] <> A[i][j ^ ipC] then
                Print("certificate mismatch at [", i, ",", j, "]\n");
                return false;
            fi;
        od;
    od;
    return true;
end;

CheckGaloisRows3125 := function(T)
    local units, a, i, image;
    units := Filtered([1..24], a -> Gcd(a, 25) = 1);
    for a in units do
        for i in [1..Length(T)] do
            image := List(T[i], x -> GaloisCyc(x, a));
            if Position(T, image) = fail then
                Print("Galois row failure for a=", a, ", row=", i, "\n");
                return false;
            fi;
        od;
    od;
    return true;
end;

starts1 := BlockStarts3125(T1);;
starts2 := BlockStarts3125(T2);;
pC := MappingPermListList(PCol[1], PCol[2]);;

Print("archive_dimensions=", Length(T1), "x", Length(T1[1]), ",",
      Length(T2), "x", Length(T2[1]), "\n");
Print("certificate_all_entries=", CheckCertificate3125(T1, T2), "\n");
Print("subgroup_blocks=", Length(starts1), ",", Length(starts2),
      " same_starts=", starts1 = starts2, "\n");
Print("Pcol_aligns_H1_forward=",
      Set(List(starts1, x -> x ^ pC)) = Set(starts2),
      " inverse=",
      Set(List(starts2, x -> x ^ Inverse(pC))) = Set(starts1), "\n");
Print("G68_galois_all_units_mod25=", CheckGaloisRows3125(T1), "\n");
Print("G69_galois_all_units_mod25=", CheckGaloisRows3125(T2), "\n");
