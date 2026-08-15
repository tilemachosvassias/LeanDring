F := FreeGroup("a", "b");
a := F.1; b := F.2;

GetId := function(u, t)
    local rels, G;
    rels := [a^16, b^4 * a^-t, b^-1 * a * b * a^-u];
    G := F / rels;
    return IdGroup(G);
end;

Print(GetId(15, 0), "\n");
Print(GetId(7, 0), "\n");
Print(GetId(15, 8), "\n");
Print(GetId(9, 0), "\n");
Print(GetId(9, 2), "\n");
Print(GetId(5, 0), "\n");
Print(GetId(11, 0), "\n");
QUIT;
