Read("gap/dring_sieve_standalone.g");
Read("gap/df_trace_corrected_snf.g");

G := SmallGroup(32, 48);
cls := SpeciesClassesD(G);
data := DFTraceLocalData(G, G); # Wait, DFTraceLocalData takes G and K.
# We need the full matrix over all K.
