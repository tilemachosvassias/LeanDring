# cyclic_faithful_check.py
# Task B: falsification test of the claim
#   "the set of cyclic-faithful species {(L, mu): L cyclic, mu faithful linear
#    character} of D(G) is preserved by every ring automorphism of D(G)"
# using the exact Aut(D(G)) enumeration of python/fullaut3.py.
#
# Parametrizations (see dring2.DRing):
#   * species point i = (H, h*H') up to G-conjugacy; the claim's pair (L, mu
#     faithful) translates to: H cyclic AND h generates H (for cyclic H the
#     coset is a single element h, and under the duality of a cyclic group
#     "mu faithful" <-> "h a generator").  The label is Galois-invariant
#     (h generator => h^a generator, a coprime to N), so a twisted
#     automorphism s_i o Phi = gamma o s_{pi(i)} preserves the CF species set
#     iff the permutation pi does.
#   * basis element b = [K, lambda] (fused pair); CF iff K cyclic AND lambda
#     faithful on K (trivial kernel).  An automorphism preserves the standard
#     CF basis span iff the columns of its integral matrix Ut at CF indices
#     are supported on CF rows (same test full_aut3 uses for eta(B)).
#
# Convention (PRIMARY): the trivial pair (K=1, trivial char) counts as
# cyclic-faithful (kernel is trivial).  STRICT variant: K (resp. H)
# nontrivial.  Both are reported.

import io
import sys
import contextlib

sys.path.insert(0, __file__.rsplit("/", 1)[0] + "/../lib")

from fullaut3 import full_aut3
from dring2 import cyclic, dihedral, dicyclic
from swaprigid import FastDRing, direct_product


class Tee:
    def __init__(self, *streams): self.streams = streams
    def write(self, x):
        for s in self.streams: s.write(x)
    def flush(self):
        for s in self.streams: s.flush()


def is_cyclic(G, H):
    return max(G.ordv[x] for x in H) == len(H)


def cf_species(D, i, strict):
    H, cs, Hp, _ = D.species[i]
    if not is_cyclic(D.G, H):
        return False
    h = min(cs)          # for cyclic H, H' = 1 and the coset is {h}
    assert len(cs) == 1
    if D.G.ordv[h] != len(H):
        return False
    return len(H) > 1 if strict else True


def cf_basis(D, b, strict):
    K, lam = D.basis[b]
    if not is_cyclic(D.G, K):
        return False
    if sum(1 for x in K if lam[x] == 0) != 1:   # faithful <=> trivial kernel
        return False
    return len(K) > 1 if strict else True


def sdesc(D, i):
    H, cs, Hp, _ = D.species[i]
    h = min(cs)
    return (f"species#{i}(|H|={len(H)},cyclic={is_cyclic(D.G, H)},"
            f"ord(h)={D.G.ordv[h]})")


def bdesc(D, b):
    K, lam = D.basis[b]
    ker = sum(1 for x in K if lam[x] == 0)
    return (f"basis#{b}(|K|={len(K)},cyclic={is_cyclic(D.G, K)},"
            f"|ker(lam)|={ker})")


def check_group(name, ctor, node_cap=2 * 10**6):
    print(f"\n================ {name} ================", flush=True)
    buf = io.StringIO()
    with contextlib.redirect_stdout(Tee(sys.stdout, buf)):
        A = full_aut3(ctor, node_cap=node_cap)
    capped = "CAPPED" in buf.getvalue()
    D = FastDRing(ctor())          # same deterministic construction/indexing
    n = len(D.species)
    verdicts = {}
    for strict in (False, True):
        tag = "strict" if strict else "primary"
        CFs = {i for i in range(n) if cf_species(D, i, strict)}
        CFb = {b for b in range(n) if cf_basis(D, b, strict)}
        print(f"[{tag}] CF species = {sorted(CFs)}   CF basis = {sorted(CFb)}")
        movers_s, movers_b = [], []
        for Ut, (pi, twv) in A:
            # species-level: s_i o Phi = gamma o s_{pi[i]}
            bad = [i for i in range(n) if (i in CFs) != (pi[i] in CFs)]
            if bad:
                movers_s.append((pi, twv, bad))
            # basis-level: Phi(b_c) = sum_r Ut[r][c] b_r ; CF span preserved?
            badb = [(r, c) for c in CFb for r in range(n)
                    if r not in CFb and Ut[r][c] != 0]
            if badb:
                movers_b.append((Ut, pi, badb))
        print(f"[{tag}] species-level: {len(movers_s)} of {len(A)} "
              f"automorphisms move the CF species set")
        print(f"[{tag}] basis-level  : {len(movers_b)} of {len(A)} "
              f"automorphisms move the CF basis span")
        if movers_s:
            pi, twv, bad = movers_s[0]
            i = bad[0]
            print(f"[{tag}] SPECIES WITNESS: pi = {tuple(pi)}, twists = {twv}")
            print(f"[{tag}]   slot {i}: {sdesc(D, i)}  <-pulled back from->  "
                  f"{sdesc(D, pi[i])}   (CF status differs)")
        if movers_b:
            Ut, pi, badb = movers_b[0]
            r, c = badb[0]
            print(f"[{tag}] BASIS WITNESS: Phi({bdesc(D, c)}) has nonzero "
                  f"coefficient {Ut[r][c]} at {bdesc(D, r)}")
            print(f"[{tag}]   full matrix column {c}: "
                  f"{[Ut[rr][c] for rr in range(n)]}")
        verdicts[tag] = (len(A), capped, len(movers_s), len(movers_b))
    return verdicts


def main():
    groups = [
        ("C2", lambda: cyclic(2)),
        ("C4", lambda: cyclic(4)),
        ("V4", lambda: dihedral(2)),
        ("Q8", lambda: dicyclic(2)),
        ("C2xC4", lambda: direct_product(cyclic(2), cyclic(4), "C2xC4")),
        ("D8", lambda: dihedral(4)),
    ]
    table = {}
    for name, ctor in groups:
        table[name] = check_group(name, ctor)
    print("\n\n=========== SUMMARY (primary convention: K=1 counts as CF) "
          "===========")
    print(f"{'G':>6} | {'|Aut|':>6} | {'exhaustive':>10} | "
          f"{'species verdict':>16} | {'basis verdict':>14}")
    for name, v in table.items():
        na, capped, ms, mb = v["primary"]
        sv = "MOVED" if ms else ("PRESERVED" if not capped else "UNDECIDED")
        bv = "MOVED" if mb else ("PRESERVED" if not capped else "UNDECIDED")
        print(f"{name:>6} | {na:>6} | {str(not capped):>10} | "
              f"{sv:>16} | {bv:>14}")
    print("\n=========== SUMMARY (strict convention: K nontrivial) ===========")
    for name, v in table.items():
        na, capped, ms, mb = v["strict"]
        sv = "MOVED" if ms else ("PRESERVED" if not capped else "UNDECIDED")
        bv = "MOVED" if mb else ("PRESERVED" if not capped else "UNDECIDED")
        print(f"{name:>6} | {na:>6} | {str(not capped):>10} | "
              f"{sv:>16} | {bv:>14}")


if __name__ == "__main__":
    main()
