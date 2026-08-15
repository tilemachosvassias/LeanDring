g := PSU(3,8);;
Print("order=", Size(g), " degree=", NrMovedPoints(g), "\n");
t0 := Runtime();
hom := SmallerDegreePermutationRepresentation(g);;
pg := Image(hom);;
Print("smaller degree=", NrMovedPoints(pg), " time=", Runtime()-t0, "\n");
