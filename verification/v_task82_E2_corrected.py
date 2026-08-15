import sys
sys.path.insert(0, __file__.rsplit("/", 1)[0])
import v_task60_lu_residues as V

# ---------------------------------------------------------------- the bug
# v_task60 PART E' uses  cap = 2^floor(3d/2)  as an upper bound for
# ppmax_{2'}(|S|) for BOTH towers.  That "q = 2 sharpening" of Lemma X'
# is FALSE for the unitary tower: at q = 2 the prime 3 divides EVERY
# factor 2^i-(-1)^i, so the 3-part of |U_d(2)| is about 3^{1.5d}, i.e.
# 2^{2.4d}.  (GAP: ppmax_{2'}(U_25(2)) = 3^34 = 1.67e16 against the
# claimed cap 2^37 = 1.37e11.)   The PROVEN Lemma X' bound
#        ppmax_{p'} <= 2^{d-1}(q+1)^{d-1} = 6^{d-1}  at q = 2
# is used here instead, for both towers.
src = open(V.__file__).read()
src = src.replace("            cap = 2 ** ((3 * d) // 2)",
                  "            cap = min(6 ** (d - 1), 2 ** ((3 * d) // 2)) "
                  "if X == 'L' else 6 ** (d - 1)")
ns = dict(V.__dict__)
exec(compile(src, "v_task60_patched", "exec"), ns)
dlo, dhi = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (21, 200)
print("### PART E' RE-RUN with the CORRECTED ppmax_{2'} cap")
ns["partE2_h3prime"](dlo, dhi)
