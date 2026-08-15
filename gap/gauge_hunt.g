Read("gap/dring_sieve_standalone.g");
v2r := function(r) if r = 0 then return 999; fi; return PValuation(r, 2); end;;

RatClassesD := function(G, cls)
  local ok, c, orb, a, keep;
  keep := [];
  for c in cls do
    ok := true;
    if Order(c.q) > 2 then
      orb := Orbit(Normalizer(G, c.H), c.q,
        function(q, n) return Image(c.nat, PreImagesRepresentative(c.nat, q)^n); end);
      for a in Filtered([2..Order(c.q)-1], x -> Gcd(x, Order(c.q)) = 1) do
        if not c.q^a in orb then ok := false; break; fi;
      od;
    fi;
    if ok then Add(keep, c); fi;
  od;
  return keep;
end;;

if not IsBound(ORDER) then ORDER := 8; fi;
if not IsBound(ID_START) then ID_START := 1; fi;
if not IsBound(ID_END) then ID_END := NrSmallGroups(ORDER); fi;

out_file := StringFormatted("results/gauge_hunt_{}_{}_{}.txt", ORDER, ID_START, ID_END);
out := OutputTextFile(out_file, false);
SetPrintFormattingStatus(out, false);

for id in [ID_START..ID_END] do
  G := SmallGroup(ORDER, id);
  name := StringFormatted("({},{})", ORDER, id);
  
  full := SpeciesClassesD(G);
  cls := RatClassesD(G, full);
  T := SpeciesTableD(G, full);
  
  ratRows := Filtered([1..Length(full)], r -> full[r] in cls);
  n := Length(ratRows);
  
  # Build rectangular V: columns are rational points, rows are all generators
  V := [];
  for c in [1..Length(T[1])] do
    Add(V, List(ratRows, r -> T[r][c]));
  od;
  
  # HNF to get square basis B
  B_full := HermiteNormalFormIntegerMat(V);
  # Filter to nonzero rows
  B := Filtered(B_full, r -> not ForAll(r, x -> x = 0));
  
  if Length(B) <> n then
     PrintTo(out, name, ": ERROR - B is not square (", Length(B), "x", n, ")\n");
     continue;
  fi;
  
  Tinv := Inverse(B);
  
  bad := []; cross := 0; minmargin := 999;
  for p in [1..n] do for q in [p+1..n] do
    if full[ratRows[p]].Hidx <> full[ratRows[q]].Hidx then
      l  := Minimum(List([1..n], i -> v2r(B[i][p]-B[i][q])));
      lv := -Minimum(List([1..n], i -> v2r(Tinv[p][i]-Tinv[q][i])));
      cross := cross + 1;
      if l >= lv then
        p_label := StringFormatted("(|K|={}, ord={}, idx={})", Size(full[ratRows[p]].H), Order(full[ratRows[p]].h), ratRows[p]);
        q_label := StringFormatted("(|K|={}, ord={}, idx={})", Size(full[ratRows[q]].H), Order(full[ratRows[q]].h), ratRows[q]);
        perm := (p, q);
        Vp := List(V, r -> Permuted(r, perm));
        
        # HNF-verify on the FULL rectangular matrix Vp
        Bp_full := HermiteNormalFormIntegerMat(Vp);
        Bp := Filtered(Bp_full, r -> not ForAll(r, x -> x = 0));
        ok := Bp = B;
        
        if not ok then
           PrintTo(out, "HNF FAILED FOR SURVIVOR IN ", name, "! p=", p, " q=", q, "\n");
        fi;
        Add(bad, [p, q, l, lv, p_label, q_label, ok]);
        Print("SURVIVOR: ", name, " ", p_label, " <-> ", q_label, "\n");
      fi;
      if lv - l < minmargin then minmargin := lv - l; fi;
    fi;
  od; od;
  
  line := StringFormatted("{} : {} rational pts, {} cross-fibre pairs; survivors: {}; min margin: {}", 
                          name, n, cross, Length(bad), minmargin);
  PrintTo(out, line, "\n");
  for b in bad do
    PrintTo(out, "  survivor: p=", b[1], " q=", b[2], " l=", b[3], " lv=", b[4], 
                 " labels: ", b[5], " <-> ", b[6], " HNF-preserves: ", b[7], "\n");
  od;
od;
CloseStream(out);
QUIT;
