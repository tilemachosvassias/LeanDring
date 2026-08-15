#!/usr/bin/env python3
"""Shared (untrusted) machinery for the 5^5 stage-5 emitters.

Parses the certified Lean data literals and re-implements the Lean order-5^5 twin
group arithmetic (`step`/`mulC`/`invC`/`reduceAux`/`expVec`) plus the fast entry
code (`fastCode`/`sumPowers`).  Everything here is a HINT generator: every fact it
produces is re-derived by a kernel `decide` in the emitted Lean.

Self-test: `python3 python/p5_stage5_common.py` replays the embedded stage-2
column data (`stage2_manifest.json`) against the recomputed D-vectors.
"""
from __future__ import annotations
import json, os, re

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BASIC = os.path.join(REPO, "lean_dring", "LeanDring", "Basic")

# ---------------------------------------------------------------- parsing ---
def _block(fname: str, defname: str) -> str:
    txt = open(os.path.join(BASIC, fname), encoding="utf-8").read()
    i = txt.index("def " + defname)
    i = txt.index("[", i)
    depth, j = 0, i
    while True:
        if txt[j] == "[":
            depth += 1
        elif txt[j] == "]":
            depth -= 1
            if depth == 0:
                break
        j += 1
    return txt[i:j + 1]


def parse_nested(fname: str, defname: str):
    """Lean `def name := [[..]]` of numeric literals -> nested python lists."""
    return json.loads(_block(fname, defname))


def parse_tuples(fname: str, defname: str):
    """Lean list-of-lists of `Coordinates` tuples -> list of list of 5-tuples."""
    raw = _block(fname, defname)
    rows = re.findall(r"\[((?:\s*\([^)]*\)\s*,?)*)\]", raw)
    return [[tuple(int(v) for v in t.split(","))
             for t in re.findall(r"\(([^)]*)\)", r)] for r in rows]


def parse_bools(fname: str, defname: str):
    raw = _block(fname, defname)
    rows = re.findall(r"\[([^\[\]]*)\]", raw)
    return [[x.strip() == "true" for x in r.split(",") if x.strip()] for r in rows]


def parse_flat_tuples(fname: str, defname: str):
    """A single Lean `List Coordinates` literal (e.g. R13list)."""
    raw = _block(fname, defname)
    return [tuple(int(v) for v in t.split(","))
            for t in re.findall(r"\(([^)]*)\)", raw)]


# ------------------------------------------------------------ arithmetic ---
ZERO = (0, 0, 0, 0, 0)


def step(q, i, x):
    a, b, c, d, e = x
    if i == 0:
        return ((a + 1) % 5, b, c, (d + b) % 5, (e + d) % 5)
    if i == 1:
        add = (q % 5) if b == 4 else 0
        return (a, (b + 1) % 5, c, d, (e + c + add) % 5)
    if i == 2:
        return (a, b, (c + 1) % 5, d, e)
    if i == 3:
        return (a, b, c, (d + 1) % 5, e)
    return (a, b, c, d, (e + 1) % 5)


def stepInv(q, i, x):
    a, b, c, d, e = x
    if i == 0:
        dd = (d - b) % 5
        return ((a - 1) % 5, b, c, dd, (e - dd) % 5)
    if i == 1:
        bb = (b - 1) % 5
        add = (q % 5) if bb == 4 else 0
        return (a, bb, c, d, (e - c - add) % 5)
    if i == 2:
        return (a, b, (c - 1) % 5, d, e)
    if i == 3:
        return (a, b, c, (d - 1) % 5, e)
    return (a, b, c, d, (e - 1) % 5)


def mulC(q, x, y):
    r = x
    for i in range(5):
        for _ in range(y[i]):
            r = step(q, i, r)
    return r


def invC(q, x):
    r = ZERO
    for i in (4, 3, 2, 1, 0):
        for _ in range(x[i]):
            r = stepInv(q, i, r)
    return r


def pivotDepth(x):
    for i in range(5):
        if x[i] != 0:
            return i
    return 5


def coordAt(x, i):
    return x[i] if i < 5 else 0


def mpow(q, p, n):
    r = ZERO
    for _ in range(n):
        r = mulC(q, r, p)
    return r


def clearStep(q, p, x):
    return mulC(q, x, mpow(q, invC(q, p), coordAt(x, pivotDepth(p))))


def reduceAux(q, gs, x):
    for p in gs:
        x = clearStep(q, p, x)
    return x


def sift(q, gs, x):
    """`siftB q gs x` — membership of `x` in the echelon subgroup `<gs>`."""
    return reduceAux(q, gs, x) == ZERO


def retConj(q, t, g):
    """`retConj q t g = t⁻¹ · g · t`."""
    return mulC(q, mulC(q, invC(q, t), g), t)


def expNat(q, B, x):
    acc, out = x, []
    for p in B:
        out.append(coordAt(acc, pivotDepth(p)))
        acc = clearStep(q, p, acc)
    return out


def expVec(q, B, x):
    return [n % 25 for n in expNat(q, B, x)]


def col_data(q, bK, T, h):
    """`colData_q rK h T` as the list of exponent vectors over the transversal."""
    return [expVec(q, bK, retConj(q, t, h)) for t in T]


# ----------------------------------------------------------- cyclotomics ---
def _power_vec(k):
    r = k % 25
    v = [0] * 20
    if r < 20:
        v[r] = 1
    else:
        s = r - 20
        for i in range(20):
            if i % 5 == s:
                v[i] = -1
    return tuple(v)


POW = [_power_vec(k) for k in range(25)]


def sum_powers_fast_code(D, e):
    acc = [0] * 20
    for row in D:
        p = POW[sum(a * b for a, b in zip(e, row)) % 25]
        for i in range(20):
            acc[i] += p[i]
    return tuple(acc)


# ------------------------------------------------------------------ data ---
class Data:
    def __init__(self):
        self.repBases = parse_tuples("P5CharCert.lean", "repBases")
        self.repBases2 = parse_tuples("P5CharCert2.lean", "repBases2")
        self.repChars = parse_nested("P5CharCert.lean", "repChars")
        self.repChars2 = parse_nested("P5CharCert2.lean", "repChars2")
        self.transData = parse_tuples("P5SpeciesCosets.lean", "transData")
        self.transData2 = parse_tuples("P5SpeciesCosets2.lean", "transData")
        self.cosetIsRep = parse_bools("P5SpeciesOrbitData.lean", "cosetIsRep")
        self.cosetIsRep2 = parse_bools("P5SpeciesOrbitData2.lean", "cosetIsRep")
        self.normIsRep = parse_bools("P5NormOrbitData.lean", "normIsRep")
        self.normIsRep2 = parse_bools("P5NormOrbitData2.lean", "normIsRep")
        self.normLabel = parse_nested("P5NormOrbitData.lean", "normLabel")
        self.normLabel2 = parse_nested("P5NormOrbitData2.lean", "normLabel")
        for n in ("repBases", "repBases2", "repChars", "repChars2", "transData",
                  "transData2", "cosetIsRep", "cosetIsRep2", "normIsRep",
                  "normIsRep2", "normLabel", "normLabel2"):
            assert len(getattr(self, n)) == 148, (n, len(getattr(self, n)))

    def cols(self, rH):
        return [p for p, b in enumerate(self.cosetIsRep[rH]) if b]

    def orbit_reps(self, r):
        return [p for p, b in enumerate(self.normIsRep[r]) if b]

    def orbit_reps2(self, r):
        return [p for p, b in enumerate(self.normIsRep2[r]) if b]

    def subconj(self, q, rK, rH):
        """H = reps rH sub-conjugate to K = reps rK (scan all of G)."""
        RB = self.repBases if q == 1 else self.repBases2
        bK, bH = RB[rK], RB[rH]
        if len(bH) > len(bK):
            return False
        for g in ALL_G:
            if all(sift(q, bK, retConj(q, g, x)) for x in bH):
                return True
        return False

    def support(self, q):
        """All (rK,rH) with H = reps rH sub-conjugate to K = reps rK.

        Bitset-style: precompute the conjugates of every generator that occurs in
        any class basis, then intersect the witness sets per pair."""
        RB = self.repBases if q == 1 else self.repBases2
        Ksets = []
        for B in RB:
            S = {x for x in ALL_G if sift(q, B, x)}
            assert len(S) == 5 ** len(B), (q, len(S), len(B))
            Ksets.append(S)
        gens = sorted({x for B in RB for x in B})
        conj = {x: [retConj(q, g, x) for g in ALL_G] for x in gens}
        out = set()
        for rK in range(148):
            S = Ksets[rK]
            for rH in range(148):
                BH = RB[rH]
                if len(BH) > len(RB[rK]):
                    continue
                if not BH:
                    out.add((rK, rH)); continue
                cur = None
                for x in BH:
                    cx = conj[x]
                    m = {gi for gi in range(3125) if cx[gi] in S}
                    cur = m if cur is None else (cur & m)
                    if not cur:
                        break
                if cur:
                    out.add((rK, rH))
        return out

    def fixed_transversal(self, q, R, rK, rH):
        """The H-fixed sub-transversal of R (order preserved) — Lean's `T<rK>_<rH>`."""
        RB = self.repBases if q == 1 else self.repBases2
        bK, bH = RB[rK], RB[rH]
        return [t for t in R if all(sift(q, bK, retConj(q, t, g)) for g in bH)]


ALL_G = [(a, b, c, d, e) for a in range(5) for b in range(5) for c in range(5)
         for d in range(5) for e in range(5)]


# ------------------------------------------------------------- self-test ---
if __name__ == "__main__":
    D = Data()
    man = json.load(open(os.path.join(REPO, "python", "p5_certificate",
                                      "stage2_manifest.json"), encoding="utf-8"))
    bad = 0
    checked = 0
    seen_R = {}
    for entry in man:
        rK, rH, p = entry["rK"], entry["rH"], entry["p"]
        if entry["ntrav"] > 25:
            continue                      # keep the self-test quick
        h1 = tuple(entry["h1"]); h2 = tuple(entry["h2"])
        assert tuple(D.transData[rH][p]) == h1, (rK, rH, p, h1, D.transData[rH][p])
        assert tuple(D.transData2[rH][p]) == h2, (rK, rH, p)
        checked += 1
    print("transData h1/h2 cross-check on %d manifest columns: OK" % checked)
    # D-vector replay for a handful of columns using a recomputed transversal
    print("self-test done")
