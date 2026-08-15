# Trace-corrected, species-export-free D_F Smith profiles for the order-256
# T4 pair (1741,1742).  Run only after the order-32 regression passes.
Read("gap/dring_sieve_standalone.g");;
Read("gap/df_trace_corrected_snf.g");;

ed1 := DFTraceReport(256,1741);;
GASMAN("collect");
ed2 := DFTraceReport(256,1742);;

if ed1 = ed2 then
  Print("TRACE_DF_VERDICT 1741,1742 AGREE\n");
else
  Print("TRACE_DF_VERDICT 1741,1742 DIFFER\n");
fi;
QUIT;
