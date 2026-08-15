LoadPackage("tomlib");

Print("Starting G5 Co-realizability filter...\n");
found_marks_identical := [];

for o in [1..32] do
    for i in [1..NrSmallGroups(o)] do
        G := SmallGroup(o, i);
        TM := TableOfMarks(G);
        M := MarksTom(TM);
        # M is a list of rows. We want columns.
        cols := [];
        n := Length(M);
        for c in [1..n] do
            col := [];
            for r in [1..n] do
                if c <= Length(M[r]) then
                    Add(col, M[r][c]);
                else
                    Add(col, 0); # lower triangular, so 0 if not present?
                    # Wait, MarksTom returns lower triangular lists.
                fi;
            od;
            Add(cols, col);
        od;
        
        # Check for identical columns
        for c1 in [1..n] do
            for c2 in [c1+1..n] do
                if cols[c1] = cols[c2] then
                    K1 := RepresentativeTom(TM, c1);
                    K2 := RepresentativeTom(TM, c2);
                    
                    A1 := AbelianInvariants(K1);
                    A2 := AbelianInvariants(K2);
                    
                    N1 := Normalizer(G, K1);
                    N2 := Normalizer(G, K2);
                    
                    W1_order := Size(N1) / Size(K1);
                    W2_order := Size(N2) / Size(K2);
                    
                    if A1 = A2 then
                        Add(found_marks_identical, rec(
                            G := [o, i],
                            A := A1,
                            W1_order := W1_order,
                            W2_order := W2_order
                        ));
                    fi;
                fi;
            od;
        od;
    od;
od;

Print("Found ", Length(found_marks_identical), " marks-identical pairs with same A in groups up to order 32.\n");
for pair in found_marks_identical do
    Print(pair, "\n");
od;

