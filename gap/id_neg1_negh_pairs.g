F := FreeGroup("a","b");
# m=5, n=2: u=-1=31, u=-h=15 mod 32
for u in [31,15] do
  G := F / [F.1^32, F.2^4, F.2^-1*F.1*F.2*F.1^-u];
  Print("128: n=2 u=", u, " t=0 -> ", IdGroup(G), "\n");
od;
# m=4, n=3: |G|=128, u^8=1 mod 16: u=-1=15, u=-h=7
for u in [15,7] do
  G := F / [F.1^16, F.2^8, F.2^-1*F.1*F.2*F.1^-u];
  Print("128: n=3 u=", u, " t=0 -> ", IdGroup(G), "\n");
od;
# 256: m=6,n=2: u=-1=63, -h=31; m=5,n=3: u=31,15; m=4,n=4: u=15,7
for u in [63,31] do
  G := F / [F.1^64, F.2^4, F.2^-1*F.1*F.2*F.1^-u];
  Print("256: n=2 u=", u, " -> ", IdGroup(G), "\n");
od;
for u in [31,15] do
  G := F / [F.1^32, F.2^8, F.2^-1*F.1*F.2*F.1^-u];
  Print("256: n=3 u=", u, " -> ", IdGroup(G), "\n");
od;
for u in [15,7] do
  G := F / [F.1^16, F.2^16, F.2^-1*F.1*F.2*F.1^-u];
  Print("256: n=4 u=", u, " -> ", IdGroup(G), "\n");
od;
QUIT;
