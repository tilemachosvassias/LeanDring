Wr := function(s) local o; o:=OutputTextFile("/tmp/hunt128_run/cmp5.out",true);
  SetPrintFormattingStatus(o,false); WriteLine(o,s); CloseStream(o); end;;
# 5^5 counterexample pair vs the 2^7 frontier pair: are char tables Galois-conjugate
# (TransformingPermutations SUCCEEDS) or genuinely different (FAILS)?
tp := function(ord,i,j)
  local G,H,r;
  G:=SmallGroup(ord,i); H:=SmallGroup(ord,j);
  r:=TransformingPermutationsCharacterTables(CharacterTable(G),CharacterTable(H));
  Wr(Concatenation("(",String(ord),",",String(i),")/(",String(ord),",",String(j),
     "): char tables permutation-equal = ",String(r<>fail),
     "  [fail => genuinely different tables]"));
end;;
tp(3125,68,69);
tp(128,1597,1598);
Wr("DONE"); QUIT;
