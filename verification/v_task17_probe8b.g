g := PSU(3,8);;
Print("order=", Size(g), "\n");
gens := GeneratorsOfGroup(g);;
Print("num gens=", Length(gens), "\n");
Print("first gen: ", gens[1], "\n");
Print("dims: ", DimensionsMat(gens[1]), "\n");
Print("field of gen: ", DefaultFieldOfMatrix(gens[1]), "\n");
