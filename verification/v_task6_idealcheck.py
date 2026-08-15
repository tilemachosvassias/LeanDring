# v_task6_idealcheck.py
# Task B-ideal: the Lean claim under audit concerns the IDEAL
#   brauerKernel := { x in D(G) : s(x) = 0 for ALL cyclic-faithful species s }
# (PRIMARY convention: the trivial pair counts as cyclic-faithful, per the
# auditee's own definition).  An automorphism may move the CF species SET yet
# still preserve this intersection-of-kernels ideal, so this is a separate,
# decisive test.
#
# Method: K = ker_Z of the CF-rows submatrix M of the species table
# (M has one row per CF species per Z[zeta_N]-coordinate; K = Z^n cap ker_Q M
# is automatically saturated).  Phi(b_c) = sum_r Ut[r][c] b_r (latauto.
# solve_matrix solves Bm*U = FB), so coordinates transform c -> Ut*c and
# Phi(K) = K  iff  M*(Ut*k) = 0 for a Q-basis k of ker M (Ut in GL_n(Z),
# saturated equal-rank sublattices with containment coincide; the enumerated
# automorphism list is closed under inversion).

import io
import sys
import contextlib
from fractions import Fraction

sys.path.insert(0, __file__.rsplit("/", 1)[0] + "/lib")
sys.path.insert(0, __file__.rsplit("/", 1)[0])

from fullaut3 import full_aut3
from dring2 import cyclic, dihedral, dicyclic
from swaprigid import FastDRing, direct_product
from v_task6_cfcheck import cf_species, Tee


def nullspace(M, n):
    """Q-basis of {v : M v = 0}, M a list of integer rows of length n."""
    A = [[Fraction(x) for x in row] for row in M]
    pivots = []
    r = 0
    for c in range(n):
        pr = next((i for i in range(r, len(A)) if A[i][c] != 0), None)
        if pr is None:
            continue
        A[r], A[pr] = A[pr], A[r]
        iv = 1 / A[r][c]
        A[r] = [v * iv for v in A[r]]
        for i in range(len(A)):
            if i != r and A[i][c] != 0:
                f = A[i][c]
                A[i] = [A[i][k] - f * A[r][k] for k in range(n)]
        pivots.append(c)
        r += 1
    free = [c for c in range(n) if c not in pivots]
    basis = []
    for fc in free:
        v = [Fraction(0)] * n
        v[fc] = Fraction(1)
        for i, pc in enumerate(pivots):
            v[pc] = -A[i][fc]
        basis.append(v)
    return basis


def ideal_check(name, ctor, node_cap):
    print(f"\n================ {name} ================", flush=True)
    buf = io.StringIO()
    with contextlib.redirect_stdout(Tee(sys.stdout, buf)):
        A = full_aut3(ctor, node_cap=node_cap)
    capped = "CAPPED" in buf.getvalue()
    D = FastDRing(ctor())
    n = len(D.species)
    out = {}
    for strict in (False, True):
        tag = "strict" if strict else "primary"
        CFs = sorted(i for i in range(n) if cf_species(D, i, strict))
        # M: one row per (CF species, coordinate of Z[zeta_N])
        M = [[D.table[s][b][r] for b in range(n)]
             for s in CFs for r in range(D.phiN)]
        K = nullspace(M, n)
        movers = []
        for Ut, (pi, twv) in A:
            ok = True
            for k in K:
                u = [sum(Ut[r][c] * k[c] for c in range(n)) for r in range(n)]
                if any(sum(row[c] * u[c] for c in range(n)) != 0 for row in M):
                    ok = False
                    break
            if not ok:
                movers.append((Ut, pi, twv))
        set_movers = [(Ut, pi, twv) for Ut, (pi, twv) in A
                      if any((i in CFs) != (pi[i] in CFs) for i in range(n))]
        print(f"[{tag}] CF species = {CFs}   dim ker = {len(K)} (of n={n})")
        print(f"[{tag}] ideal-level: {len(movers)} of {len(A)} automorphisms "
              f"move brauerKernel   (set-level movers: {len(set_movers)})")
        if movers:
            Ut, pi, twv = movers[0]
            print(f"[{tag}] IDEAL WITNESS: pi = {tuple(pi)}, twists = {twv}")
        out[tag] = (len(A), capped, len(movers), len(set_movers))
    # explicit call-out: the Q8-type witness pi = (1 0), identity twists
    swap01 = [(Ut, pi, twv) for Ut, (pi, twv) in A
              if pi[0] == 1 and pi[1] == 0
              and all(pi[i] == i for i in range(2, n))
              and all(a == 1 for a in twv.values())]
    for Ut, pi, twv in swap01:
        CFs = sorted(i for i in range(n) if cf_species(D, i, False))
        M = [[D.table[s][b][r] for b in range(n)]
             for s in CFs for r in range(D.phiN)]
        K = nullspace(M, n)
        bad = False
        for k in K:
            u = [sum(Ut[r][c] * k[c] for c in range(n)) for r in range(n)]
            if any(sum(row[c] * u[c] for c in range(n)) != 0 for row in M):
                bad = True
        print(f"  witness pi=(1 0)(rest fixed), no twist: "
              f"brauerKernel {'MOVED' if bad else 'PRESERVED'} "
              f"(primary convention)")
    return out


def main():
    groups = [
        ("C2", lambda: cyclic(2), 2 * 10**6),
        ("C4", lambda: cyclic(4), 2 * 10**6),
        ("V4", lambda: dihedral(2), 2 * 10**6),
        ("Q8", lambda: dicyclic(2), 2 * 10**6),
        ("D8", lambda: dihedral(4), 6 * 10**6),   # 4 940 462 nodes exhaust it
    ]
    table = {}
    for name, ctor, cap in groups:
        table[name] = ideal_check(name, ctor, cap)
    print("\n\n====== SUMMARY: brauerKernel ideal under Aut(D(G)) ======")
    print(f"{'G':>4} | {'|Aut|':>6} | {'exhaustive':>10} | "
          f"{'ideal (primary)':>16} | {'ideal (strict)':>15}")
    for name, v in table.items():
        na, capped, mi_p, _ = v["primary"]
        _, _, mi_s, _ = v["strict"]
        pv = "MOVED" if mi_p else ("PRESERVED" if not capped else "UNDECIDED")
        sv = "MOVED" if mi_s else ("PRESERVED" if not capped else "UNDECIDED")
        print(f"{name:>4} | {na:>6} | {str(not capped):>10} | "
              f"{pv:>16} | {sv:>15}")


if __name__ == "__main__":
    main()
