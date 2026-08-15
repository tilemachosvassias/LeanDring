Read("gap/dring_sieve_standalone.g");;
DSelfTest();;
SpCond := function(G, c)
  local N, cnt, n; N := Normalizer(G,c.H); cnt:=0;
  for n in Elements(N) do if Image(c.nat, c.h^n)=c.q then cnt:=cnt+1; fi; od;
  return cnt/Size(c.Hp); end;
Audit := function(G, lbl)
  local cls, gal, n, i, key, seen, coll, keys;
  cls := SpeciesClassesD(G); gal := GaloisDataD(G, cls); n := Length(cls);
  # D-iso invariants per species: (conductor, galois-orbit-size).  Does it fix |H|?
  seen := rec(); coll := 0; keys := [];
  for i in [1..n] do
    key := String([SpCond(G,cls[i]), gal.perspecies[i]]);
    if IsBound(seen.(key)) then
      if seen.(key) <> Size(cls[i].H) then coll := coll+1; fi;
    else seen.(key) := Size(cls[i].H); fi;
  od;
  Print("[",lbl,"] species=",n,
        "  species with SAME (conductor,orbit) but DIFFERENT |H|: ",coll,
        " => |H| ",["DETERMINED by (cond,orbit)","NOT determined"][1+SignInt(coll)],"\n");
end;
Audit(SmallGroup(32,27),"(32,27)");
Audit(SmallGroup(32,32),"(32,32)");
Audit(SmallGroup(64,5),"(64,5)");
QUIT;
