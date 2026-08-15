LoadPackage("TomLib");

G := SmallGroup(32, 49); # D4 o D4 (+)
# Let's find subgroups of order 8 that contain the center
z := Center(G);
K_list := Filtered(NormalSubgroups(G), K -> Size(K)=8 and IsSubset(K, z));
for K in K_list do
    Print("Type of K: ", IdGroup(K), "\n");
od;
QUIT;
