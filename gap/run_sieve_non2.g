Read("gap/dring_sieve_standalone.g");
for o in [1..32] do
    if o <> 1 and o <> 2 and o <> 4 and o <> 8 and o <> 16 and o <> 32 then
        Print("Sieving order ", o, "\n");
        DSieve(o);
    fi;
od;
QUIT;
