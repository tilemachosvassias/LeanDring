# v_task86 — implementing the v_task85 alignment audit's cheap follow-ups

Date 2026-08-09.  LEAN WIRING session: no new mathematics, no research.
Two files touched, `LeanDring/Even/BoltjeAssembly.lean` and
`LeanDring/Even/SimpleRigidity.lean`, plus `Even/NOTES.md` (§4bm addendum
15).  Serial builds, `taskset -c 0`, one `lean` process at a time.

**Headline.**  All five items of the audit's §7 landed.  Item 3
(`FittingFreeDetector`) landed only in its *derivable* half: the iff
`conductorMultiplicity (D(G)) |G| = 1 ↔ IsFittingFree G` turned out **not**
to be wiring — it needs a *count* of integer points, which the formalized
dictionary does not provide — so it is stated as a named `Prop` with the
mathematical content documented, and only the consequence is proven.

---

## 1. `exceptionSeparation_witness` (audit §7 item 1) — LANDED

`Even/BoltjeAssembly.lean`.

```lean
theorem exceptionSeparation_witness
    {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H] {x : ℕ}
    (hcard : Nat.card G = Nat.card H)
    (hG : IsIndexValue G x) (hH : ¬ IsIndexValue H x) :
    ∃ c : ℕ, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c := by
  obtain ⟨c, hc, hcx⟩ := hG
  exact ⟨c, fun hEq => hH ⟨c, by rw [← hEq]; exact hc, hcx.trans hcard⟩⟩
```

The divisibility bookkeeping the brief warned about does not arise: the
witness `c` comes *out of* `IsIndexValue G x` (which already packages
`conductorMultiplicity (D G) c ≠ 0` together with `c · x = |G|`), so no
`|G| / x` division is ever formed.  If the two multiplicities agreed at
that `c`, then `conductorMultiplicity (D H) c ≠ 0` and `c · x = |H|`,
i.e. `IsIndexValue H x` — contradiction.  Two lines.

Companion, in the form the mathematics is actually stated in (§4aj–§4bi
prove things about `ind*`-values, not conductors):

```lean
theorem exceptionSeparation_witness_indStar (hBo : BoltjeIntegrality.{u}) …
    (hG : IsIndStarValue G x) (hH : ¬ IsIndStarValue H x) :
    ∃ c, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c
```

**Placement.**  `Even/BoltjeAssembly.lean` rather than
`Even/ConductorDictionary.lean`: it is a leaf module (nothing imports
it), it already hosts both separation lanes' `_of_boltje` corollaries,
and `isIndexValue_iff_of_boltje` is in scope there.  Putting it in
`BCSeparation.lean` (where `IsIndexValue` is defined) would have been
marginally more upstream but forces a rebuild of the 1773-line
`ConductorAtSpecies.lean` for no benefit.

**What this unblocks.**  The BC-n lane: `v ∈ I(B)`, `v ∉ I(C)`,
`|B| = |C|` now yields the `∃ c` shape `ExceptionSeparation` demands.
The twin lanes: every non-census-empty row proves `ι(T) ≠ ι(S)`, hence a
value in one `ind*` set and not the other, hence the `∃ c`.  No Lean
lemma performed this conversion before; the audit's MISMATCH 1 (§2c) and
MISMATCH 2 (§5c) are closed **as formal conversions** — the underlying
group facts remain hypotheses, as they must.

---

## 2. `mullerIsolationWeak_of_boltje` / `orderTransfer_of_boltje`
##    (audit §7 item 2) — LANDED

`Even/BoltjeAssembly.lean`.  The audit's §3 noted that `OrderTransfer`
and the dictionary appear as independent hypotheses when in fact one
implies the other.  They now do not.

```lean
theorem mullerIsolationWeak_of_boltje (hBo : BoltjeIntegrality.{u}) :
    MullerIsolationWeak.{u}
theorem orderTransfer_of_boltje (hBo : BoltjeIntegrality.{u}) : OrderTransfer.{u} :=
  orderTransfer_of_muller' (mullerIsolationWeak_of_boltje hBo) mullerTrivialBound
```

Proof of the first, in full:

1. every integer point `p` of `D(G)` has `complexify p = φ_{H,h}` for
   some pair (`ringHom_eq_species`, unconditional, §1 of
   `ConductorAtSpecies.lean`);
2. `|H'| ∣ |N_G(H,hH')|` (`card_commutator_dvd_card_pairNormalizer`,
   because `H' ≤ N_G(H,hH')`), so write
   `|N_G(H,hH')| = |H'| · n`;
3. `n` is an isolating value at that pair by the `←` half of
   `BoltjeIntegralityFor` (the divisibility `|N| ∣ n·|H'|` is an
   equality here);
4. `isolates_of_isolatingValue` turns that into `Isolates p x n`;
5. `0 < n` since `|N| > 0`, and `n ≤ |H'|·n = |N| ≤ |G|` by Lagrange
   (`Subgroup.card_subgroup_dvd_card`).

That is exactly `MullerIsolationWeak`.  Since `MullerTrivialBound` is
**proven** (`Even/MullerBound.lean`, Burnside mark triangularity),
`orderTransfer_of_muller'` closes `OrderTransfer` outright.

Note which pair is used: *no* choice is made — the argument works at
whatever pair the point happens to be, which is why the weak form (some
positive value `≤ |G|`) is the right target and the full
`MullerIsolation` (the value `|G|` itself, at every point) is not needed.

---

## 3. `FittingFreeDetector` (audit §7 item 3) — HALF LANDED; the iff is
##    NOT wiring

`Even/SimpleRigidity.lean`.

### 3.1 What was checked against the source

`sources/mueller_dissertation.md`, **Satz 2.3.6**:

> Ist `e^{D(G)}_{(H,hH')} ∈ D_{Q(ζ)}(G)` ein primitives Idempotent mit
> Führer `|G|`, so ist `H` ein abelscher Normalteiler von `G` und
> `h ∈ Z(G)`.  Insbesondere besitzt `G` genau dann einen abelschen
> Normalteiler `1 ≠ N ⊴ G`, wenn es **mehr als ein** primitives
> Idempotent in `D_{Q(ζ)}(G)` gibt, das den Führer `|G|` hat.

So the audit's proposed shape is the right one **up to one subtlety the
audit did not name**: Müller counts primitive idempotents of
`D_{Q(ζ)}(G)`, i.e. *all* species classes, whereas Lean's
`conductorMultiplicity R c = Nat.card {p : R →+* ℤ // conductor R p = c}`
counts **integer** points, i.e. only the rational (fully fused) classes.

The restriction is mathematically harmless in both directions, and this
was verified before formalizing:

* `⟸` (Fitting-free ⟹ multiplicity `= 1`): the trivial pair `(1,1)` has
  conductor `(G : 1) = |G|` unconditionally
  (`conductorAtSpecies_trivial`, already proven in the repo), so the
  multiplicity is `≥ 1`; Satz 2.3.6 forces any other conductor-`|G|`
  pair to have `H` abelian normal, hence `H = 1` and `h = 1` — the
  trivial pair again.
* `⟹` (not Fitting-free ⟹ multiplicity `≥ 2`): given `1 ≠ N ⊴ G`
  abelian, the pair `(N, 1·N')` has `N' = ⁅N,N⁆ = 1` and
  `N_G(N, 1) = N_G(N) = G`, so its index is `|G|/1 = |G|`; and it is
  **fully fused** because `h = 1` and `1^a = 1` for all `a`.  So the
  second point is genuinely rational, and the rational-species
  restriction does not break the count.  (Worked check: `G = S₃`,
  `N = A₃` — `N_G(A₃, 1) = S₃`, conductor `6 = |G|`, distinct from the
  trivial pair; while `(A₃, h)` for `h ≠ 1` has
  `N_G(A₃, h) = C_G(h) = A₃`, conductor `3 ≠ 6`.)

### 3.2 Why it is left as a `Prop`

Both directions are statements about a **count** of integer points.  The
formalized dictionary is not a count: `ConductorPairDictionary` (and
hence `BoltjeIntegrality`) says only

```
conductorMultiplicity (DRing G) c ≠ 0  ↔  ∃ (H, h), FullyFused H h ∧ c·|H'| = |N_G(H,hH')|
```

— a **non-vanishing** statement.  Getting `= 1` versus `≥ 2` requires a
bijection between fully fused pair classes and integer points, which the
development does not have (it has surjectivity of species onto complex
points, `ringHom_eq_species`, but not the injectivity/counting side for
the rational classes).  Constructing it is real work, not wiring, so per
the brief this is left as a documented `Prop`:

```lean
def TopConductorDetectsFitting : Prop :=
  ∀ (G : Type u) [Group G] [Fintype G],
    conductorMultiplicity (DRing G) (Nat.card G) = 1 ↔ IsFittingFree G
```

with the Satz-2.3.6 derivation and the `(N, 1)` witness recorded in its
docstring, and the consequence proven:

```lean
theorem fittingFreeDetector_of_topConductor
    (hdet : TopConductorDetectsFitting.{u}) (htr : OrderTransfer.{u}) :
    FittingFreeDetector.{u}
```

(order transfer gives `|G| = |H|`, so the top conductor is read at the
same `c` on both sides; `conductorMultiplicity_eq_of_ringEquiv` moves the
value across).  This is the audit's §4(c) "reducible to the same open
`Prop`", now formal — modulo the counting upgrade, which is the honest
remaining gap.

**This is the one item that turned out non-cheap.**

---

## 4. Docstring repairs (audit §7 item 4) — LANDED

`Even/SimpleRigidity.lean`.  Five sites:

| site | was | now |
|---|---|---|
| module docstring, `simpleGroupTheorem` bullet | "Five typed inputs, **all external to the ring theory**" | per-input provenance; "**only the third is external**" |
| module docstring, closing paragraph | "the theorem is unconditional the moment three *external* facts land … none of the three is a gap in D-ring theory" | replaced by the audit's §8 dependency statement, quoted verbatim, plus pointers to the v_task86 wiring |
| module docstring, `ExceptionSeparation` bullet | "reduces to CFSG plus per-pair conductor separation, **both external**" | "the first external, the second *not*" |
| `simpleDRigidity_of_exceptionSeparation` (was line 397) | "**Both inputs are external to the ring theory**" | only `SimpleOrderRigidity` is; `ExceptionSeparation` routes through `BoltjeIntegrality` |
| `SimpleOrderRigidity` (was line 318) | "§4j(iii)+§4k separate the first family by `D`" | §4at `ι`-separation: `ι(A₈) = 15` vs `ι(L₃(4)) = 21`, `κ = 1344` vs `960`; plus an explicit "do not cite §4j(iii)" in the `ExceptionSeparation` docstring, since §4q addendum rejects subgroup-class counts as computed evidence |
| `TwinSeparation` (was lines 586–591) | "PROVEN for … `A9..A40` pending v_task19; OPEN in general — equivalent to the Diophantine classification (§4u)" | "COMPLETE at the paper level over all of CFSG; OPEN formally", with the §4aq–§4bi family table; §4az addendum 2 abandoned the §4u route |
| `ExceptionSeparation` (was lines 369–380) | "PROVEN at the `(3,3)` anchor … the rest is the BHR program" | both members with their §4bl / §4at sources, plus the dictionary dependency and the `exceptionSeparation_witness` pointer |

Two further corrections not on the list but forced by the audit's §1
side-conditions, added to the `SimpleOrderRigidity` docstring:

* `n ≥ 3` and `q` odd are **load-bearing** in any instantiation of `Exc`
  (`B₂ ≅ C₂`, `B_n(2^f) ≅ C_n(2^f)`; an `Exc` holding of isomorphic pairs
  makes `ExceptionSeparation Exc` outright false);
* `Exc` carries no non-degeneracy constraint — `Exc G H := ¬ Nonempty (G ≃* H)`
  makes `SimpleOrderRigidity Exc` a tautology — so a published dependency
  statement must name the intended `Exc`.

---

## 5. `TwinSeparationFor` (audit §7 item 5, optional) — LANDED

```lean
def TwinSeparationFor (G : Type u) [Group G] [Fintype G] : Prop :=
  ∀ (H : Type u) [Group H] [Fintype H],
    IsFittingFree H → ¬ IsSimpleGroup H → Nat.card H = Nat.card G →
      ∃ c, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c

theorem twinSeparation_iff_forall :
    TwinSeparation.{u} ↔ ∀ (G : Type u) [Group G] [Fintype G],
      IsSimpleGroup G → (¬ ∀ a b : G, a * b = b * a) → TwinSeparationFor G

theorem simpleGroupTheorem_of_twinSeparationFor … (htwin : TwinSeparationFor G) …
    : Nonempty (G ≃* H)
```

`simpleGroupTheorem` itself is **untouched** (statement and proof), so
`simpleGroupTheorem_dtoB` and every downstream consumer are unaffected;
the per-target theorem carries its own eight-line proof rather than the
global one being refactored to route through it.

---

## 6. Build, sorries, axioms

```
taskset -c 0 lake build LeanDring.Even.BoltjeAssembly   # 3384 jobs, 0 err, 0 warn
taskset -c 0 lake build LeanDring.Even.SimpleRigidity   # 3409 jobs, 0 err, 0 warn
taskset -c 0 lake build                                 # 4718 jobs, green
```

`sorry` count in the two touched files: **0** (the only occurrences of the
string are inside docstrings asserting there are none).

Axiom audit — every new declaration reports exactly
`[propext, Classical.choice, Quot.sound]`:

```
LeanDring.Even.exceptionSeparation_witness
LeanDring.Even.exceptionSeparation_witness_indStar
LeanDring.Even.mullerIsolationWeak_of_boltje
LeanDring.Even.orderTransfer_of_boltje
LeanDring.Even.fittingFreeDetector_of_topConductor
LeanDring.Even.twinSeparation_iff_forall
LeanDring.Even.simpleGroupTheorem_of_twinSeparationFor
```

`Even/SimpleRigidity.lean` had **no** `#print axioms` block; one was added
covering the new lemmas and the file's existing headline theorems
(`simpleGroupTheorem`, `simpleGroupTheorem_dtoB`,
`simpleDRigidity_of_exceptionSeparation`, and the dictionary
consequences).  All report the three standard axioms.

---

## 7. What the audit's gaps look like after this session

| audit finding | status now |
|---|---|
| §2c MISMATCH 1 — `IsEmpty` vs `∃ c`, no conversion lemma | **closed** (`exceptionSeparation_witness`) |
| §5c MISMATCH 2 — same on the twin side | **closed** (same lemma) |
| §3 "missing wiring" — `BoltjeIntegrality ⟹ OrderTransfer` unstated | **closed** (`orderTransfer_of_boltje`) |
| §4c — `FittingFreeDetector` reducible to the dictionary | **half closed**: consequence proven, the iff is a `Prop` (needs a *count* of integer points, §3.2 above) |
| §2c GAP 2 / §5c GAP 1 / §6 — dictionary dependency undocumented in `SimpleRigidity.lean` | **closed** (docstrings + module-level dependency statement) |
| §2c NOTE 3 — stale `§4j(iii)` A₈/L₃(4) pointer | **closed** |
| §5c stale `TwinSeparation` docstring | **closed** |
| §7 item 5 — per-target Prop | **closed** |
| §5c GAP 3 — instantiating `TwinSeparation` cites full CFSG, unrepresented among the five inputs | **documented, not closed** (it is a citation-scope fact, not a Lean gap) |
| §1 side-conditions 1 and 2 on `Exc` | **documented** in the `SimpleOrderRigidity` docstring |

The single open ring-theoretic `Prop` of the whole conductor campaign is
still `BoltjeIntegrality`, and after this session four of the five
`simpleGroupTheorem` inputs are formally connected to it (`OrderTransfer`
outright; `ExceptionSeparation`/`TwinSeparation` via
`exceptionSeparation_witness` + `isIndexValue_iff_of_boltje`;
`FittingFreeDetector` via `TopConductorDetectsFitting`, itself pending
the counting upgrade).  Only `SimpleOrderRigidity` is external.
