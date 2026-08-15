# Exact check for the smallest non-isomorphic isocategorical pair.
# Literature input: Meir--Szymik Example 3.1 identifies
# SmallGroup(64,135/136).  This script checks the B-rank, full-power-map table
# transform, and monomial-species rank.  The D semantics are regressed first.

Read("gap/dring_sieve_standalone.g");;
DSelfTest();;

G := SmallGroup(64,135);;
H := SmallGroup(64,136);;

Print("pair=[64,135/136]\n");
Print("exponents=", [Exponent(G),Exponent(H)], "\n");
Print("element-class-ranks=", [NrConjugacyClasses(G),NrConjugacyClasses(H)], "\n");
Print("B-ranks=", [Length(OrdersTom(TableOfMarks(G))),
                    Length(OrdersTom(TableOfMarks(H)))], "\n");
Print("D-ranks=", [Length(SpeciesClassesD(G)),
                    Length(SpeciesClassesD(H))], "\n");
Print("character-tables-with-power-maps-equivalent=",
      TransformingPermutationsCharacterTables(
        CharacterTable(G), CharacterTable(H)) <> fail, "\n");
QUIT;
