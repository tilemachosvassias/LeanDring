# v_task85 — statement-alignment audit of `simpleGroupTheorem`'s five inputs
# (does the paper-level mathematics of §4aq–§4bl actually instantiate the
#  Lean Props of `Even/SimpleRigidity.lean`?)

Date 2026-08-08.  Read-only audit: no `.lean` file edited, no `lake` run,
`NOTES.md` untouched.  All line references are to the files as of this
session.

**Headline.**  Four of the five Props are aligned as stated.  The two
*separation* Props (`ExceptionSeparation`, `TwinSeparation`) are aligned
**in content** but carry a dependency that the file's own docstring
denies: instantiating them from the mathematics of §4aj–§4bl requires the
**conductor dictionary** (Müller Satz 2.3.3 + 2.3.6), i.e. exactly
`BoltjeIntegrality` — the one open Prop of the D-ring machinery itself.
`SimpleRigidity.lean` states that the five inputs are "all external to the
ring theory" (lines 108, 602, 118–124).  **That claim is false as written.**
Additionally there is a *shape* gap: the Lean Props demand an explicit
separating conductor multiplicity `c`, while the paper theorems (BC-n, SPT,
AT, the `-T` tower) conclude `IsEmpty (DRing G ≃+* DRing H)` / "no twin
exists".  The witness is recoverable in every case, but no Lean lemma
performs the conversion.

---

## 0. The theorem under audit

`LeanDring/Even/SimpleRigidity.lean:622`

```lean
theorem simpleGroupTheorem
    {Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop}
    (hord : SimpleOrderRigidity Exc) (hsep : ExceptionSeparation Exc)
    (htr : OrderTransfer.{u}) (hdet : FittingFreeDetector.{u})
    (htwin : TwinSeparation.{u})
    (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : IsSimpleGroup G) (hGa : ¬ ∀ a b : G, a * b = b * a)
    (hD : Nonempty (DRing G ≃+* DRing H)) :
    Nonempty (G ≃* H)
```

The proof body (lines 630–642) is five lines and is kernel-checked; the
audit is entirely about whether the five hypotheses are the statements the
program proved on paper.

---

## 1. `SimpleOrderRigidity Exc` — **VERDICT: ALIGNED** (with two mandatory
##    side-conditions on how `Exc` is instantiated)

### (a) Exact Lean statement (`SimpleRigidity.lean:320–325`)

```lean
def SimpleOrderRigidity
    (Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop) : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsSimpleGroup G → IsSimpleGroup H →
      (¬ ∀ a b : G, a * b = b * a) → (¬ ∀ a b : H, a * b = b * a) →
        Nat.card G = Nat.card H → Nonempty (G ≃* H) ∨ Exc G H
```

### (b) Instantiating mathematics

The CFSG order theorem (Artin–Tits): two nonabelian finite simple groups of
equal order are isomorphic, except `{A₈, L₃(4)}` (order 20160) and
`{B_n(q), C_n(q)}` for `n ≥ 3`, `q` odd.  Cited throughout (§4j(iii),
§4l, §4t, §4v); never proven here, and correctly typed as open.

### (c) Alignment analysis

* **Abelian edge case: clean.**  Mathlib's `IsSimpleGroup` includes `C_p`,
  but both `¬ ∀ a b, a*b = b*a` hypotheses exclude them, so the Prop never
  asks anything about cyclic simple groups.  ✓
* **Finiteness: clean.**  `[Fintype G]`, `[Fintype H]` are present, so
  `Nat.card` is the honest order.  ✓
* **Tits convention: harmless.**  Whether `²F₄(2)′` is counted as sporadic
  or Lie-type changes nothing: v_task50 §5 verified that the Tits group's
  order (like every sporadic order) is unique among all finite simple
  group orders, so it contributes no coincidence either way.  ✓
* **⚠ SIDE-CONDITION 1 (load-bearing).**  `Exc` must be **false on
  isomorphic pairs**.  `ExceptionSeparation Exc` (§2) demands a conductor
  multiplicity *difference* whenever `Exc G H` holds; a multiplicity
  difference is impossible when `G ≅ H`.  The naive instantiation

  > `Exc G H := (∃ n q, n ≥ 2 ∧ G ≅ B_n(q) ∧ H ≅ C_n(q)) ∨ …`

  is therefore **fatal**: `B_n(2^f) ≅ C_n(2^f)` (even characteristic) and
  `B₂ ≅ C₂`, so `Exc G G` would hold and `ExceptionSeparation Exc` would be
  outright FALSE.  The instantiation must carry the classical restrictions
  `n ≥ 3` **and `q` odd** (exactly the scope of Theorem BC-n, §4bl
  addendum: "*q even vacuous, n = 2 excluded as `B₂ ≅ C₂`*").
* **⚠ SIDE-CONDITION 2 (hygiene).**  `Exc` is a bare `Prop`-valued
  parameter with no non-degeneracy constraint.  Taking
  `Exc G H := ¬ Nonempty (G ≃* H)` makes `SimpleOrderRigidity Exc` a
  tautology (excluded middle) and dumps the entire content into
  `ExceptionSeparation Exc`.  This is not unsound — `simpleGroupTheorem`
  remains true — but it means the *division of labour* between the two
  Props is a modelling choice, not something the type system enforces.
  Any published dependency statement must therefore name the intended
  `Exc` explicitly rather than say "for some `Exc`".

---

## 2. `ExceptionSeparation Exc` — **VERDICT: MISMATCH (shape) + GAP
##    (hidden dictionary dependency)**

### (a) Exact Lean statement (`SimpleRigidity.lean:381–385`)

```lean
def ExceptionSeparation
    (Exc : ∀ (G : Type u) [Group G] (H : Type u) [Group H], Prop) : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsSimpleGroup G → IsSimpleGroup H → Nat.card G = Nat.card H → Exc G H →
      ∃ c : ℕ, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c
```

### (b) Instantiating mathematics

Two members, exactly matching the two CFSG order coincidences:

1. **`{B_n(q), C_n(q)}`, `n ≥ 3`, `q` odd — Theorem BC-n** (§4bl +
   addendum, v_task64/v_task65, audit PASSED):
   > `v_ε = qⁿ(qⁿ−ε)/2 ∈ I(B_n(q))` (anisotropic-point orbit) but
   > `v_ε ∉ I(C_n(q))` (every `ind*` value of `PSp_{2n}(q)` below `q^{2n}`
   > is `1` or divisible by `ι₁`, and `ι₁ ∤ v_ε`).  Hence
   > `I(B_n) ≠ I(C_n)` and `D(B_n(q)) ≇ D(C_n(q))`.
   Formalized in `Even/BCSeparation.lean` (`bcSeparation`) and, on purely
   group-theoretic hypotheses, in `Even/BoltjeAssembly.lean`
   (`bcSeparation_of_boltje`).
2. **`{A₈, L₃(4)}`**: the *valid* separation is by `ι`
   (= second-largest conductor): `ι(A₈) = ι(L₄(2)) = 15` (the `AGL(3,2)`
   exception, §4aj, §4as, §4at table line for `L₄(2)`: `I = {15, 35}`)
   against `ι(L₃(4)) = 21` (§4at table: `I(L₃(4)) = {21, 105, 210, 280}`).
   So `κ(A₈) = 20160/15 = 1344` vs `κ(L₃(4)) = 20160/21 = 960`.

### (c) Alignment analysis

* **⚠ MISMATCH 1 — shape.**  Every Lean deliverable in the BC lane
  concludes `IsEmpty (DRing B ≃+* DRing C)` (`BCSeparation.lean:260`,
  `BoltjeAssembly.lean:116`), never `∃ c, conductorMultiplicity … ≠ …`.
  `IsEmpty (DRing B ≃+* DRing C)` does **not** formally imply the `∃ c`
  form.  The witness *is* recoverable from the BC-n argument — from
  `IsIndexValue B v` we get `c` with `conductorMultiplicity (D B) c ≠ 0`
  and `c·v = |B| = |C|`; if `conductorMultiplicity (D C) c` were also `≠ 0`
  then `IsIndexValue C v` would hold, which `CIndexDichotomy` forbids —
  but **no Lean lemma does this**, so `ExceptionSeparation` is currently
  unreachable from `bcSeparation` inside the formal development.
  *Recommended fix:* one ~8-line lemma
  `exceptionSeparation_witness : IsIndexValue G x → ¬ IsIndexValue H x →
   Nat.card G = Nat.card H → ∃ c, conductorMultiplicity (DRing G) c ≠
   conductorMultiplicity (DRing H) c`.
* **⚠ GAP 2 — the dictionary is required, and only half-documented.**  The
  mathematics of BC-n lives in `ind*`-values (`I(G)`), i.e. in
  `IsIndStarValue` — pair normalizers and commutator subgroups.  The Lean
  Prop lives in `conductorMultiplicity`.  The bridge is
  `isIndexValue_iff_of_boltje` (`ConductorAtSpecies.lean` §12), which is
  **`BoltjeIntegrality`-conditional**.  This is correctly documented in
  `BoltjeAssembly.lean` and in v_task80 — but it is *not* documented in
  `SimpleRigidity.lean`, whose `ExceptionSeparation` docstring
  (lines 369–380) and `simpleGroupTheorem` docstring (line 611) present the
  Prop as "a per-pair census … external to the ring theory".  It is not
  external: without the dictionary the GAP-checked group facts do not touch
  `conductorMultiplicity` at all.
  The same holds for the `{A₈, L₃(4)}` member: `ι`/`κ` are conductor-multiset
  readings via Satz 2.3.3 + 2.3.6 (§4aj: "*By Satz 2.3.3 the pair `(H,hH')`
  has conductor `(N_G(H,hH'):H')` … so the conductor multiset contains
  `|N_G(H)|/|H'|` for every subgroup `H`*").
* **⚠ NOTE 3 — do not cite the §4j(iii) A₈/L₃(4) argument.**  §4j(iii)
  separates `A₈` from `L₃(4)` by "*subgroup class counts 137 vs 95 and
  distinct element-order sets*".  Those are Gap-1 wall-blocked invariants;
  §4q addendum explicitly rejects class/involution counts as
  "[COMPUTED evidence], NOT yet a proven D-ring separation".  The
  proven-tier separation is the `ι` one above.  `SimpleRigidity.lean`'s
  header (line 318) still points at "§4j(iii)+§4k" for this pair.
* **NOTE 4 — quantifier asymmetry (harmless).**  Unlike
  `SimpleOrderRigidity`, `ExceptionSeparation` does **not** carry the
  `¬ comm` hypotheses; it quantifies over abelian simple pairs too.  With
  any sane `Exc` this is vacuous, but formally it makes
  `ExceptionSeparation` slightly *stronger* than the theorem needs.  Also
  note it does not require `G ≇ H` — see Side-condition 1 in §1.
* **Coverage: complete.**  With `Exc` restricted as in §1, the two members
  above exhaust the CFSG order coincidences, and both are proven at the
  paper level (BC-n audit PASSED, v_task65).  ✓

---

## 3. `OrderTransfer` — **VERDICT: ALIGNED**

### (a) Exact Lean statement (`Even/Separation.lean:63–65`)

```lean
def OrderTransfer : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    Nonempty (DRing G ≃+* DRing H) → Nat.card G = Nat.card H
```

### (b) Instantiating mathematics

Müller, Diss. Jena 2008, **Satz 2.3.4** (`|G| = ` the maximal conductor,
attained at the trivial pair).  §4e, §4n.

### (c) Alignment analysis — is it *proven* in Lean?

**Not proven; it is a hypothesis, but a well-reduced one.**  The chain in
the repo:

| link | file | status |
|---|---|---|
| `mullerOrder_eq_of_ringEquiv` | `OrderTransfer.lean:127` | **PROVEN**, no hypotheses |
| `conductorMultiplicity_eq_of_ringEquiv` | `OrderTransfer.lean:150` | **PROVEN**, no hypotheses |
| `MullerTrivialBound` | `MullerBound.lean:459` | **PROVEN** (Burnside triangularity) |
| `MullerIsolationWeak` (⊃ needed half) | `ConductorDictionaryProofs.lean:202` | **OPEN** |
| `orderTransfer_of_muller'` | `ConductorDictionaryProofs.lean:247` | **PROVEN** from the two above |

So `OrderTransfer` rests on exactly one open statement,
`MullerIsolationWeak` ("at every integer point *some* positive value
`≤ |G|` is isolated"), which `SpeciesIsolation` (Müller's formula (2.8))
implies.  The Lean statement is a faithful rendering of Satz 2.3.4 — no
strengthening, no hidden quantifier.  ✓

**Missing wiring (cheap).**  `BoltjeIntegrality` implies
`MullerIsolationWeak`: `conductorAtSpecies_of_boltje` gives
`conductor · |H'| = |N_G(H,hH')|`, and `(N_G(H,hH') : H') ∣ |G|`, so every
conductor is `≤ |G|` and isolation at that value is exactly the witness
half.  **No Lean lemma states this**, so `OrderTransfer` and the dictionary
appear in the development as independent hypotheses when in fact one
implies the other.  Recommended: `mullerIsolationWeak_of_boltje` and
`orderTransfer_of_boltje`.

---

## 4. `FittingFreeDetector` — **VERDICT: ALIGNED** (assumed, never proven,
##    also reducible to the dictionary)

### (a) Exact Lean statement (`SimpleRigidity.lean:433–434, 457–459`)

```lean
def IsFittingFree (G : Type u) [Group G] : Prop :=
  ∀ N : Subgroup G, N.Normal → (∀ a b : N, a * b = b * a) → N = ⊥

def FittingFreeDetector : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    Nonempty (DRing G ≃+* DRing H) → IsFittingFree G → IsFittingFree H
```

### (b) Instantiating mathematics

Müller **Satz 2.3.6**: `D(G)` has more than one conductor-`|G|` idempotent
⟺ `G` has a nontrivial abelian normal subgroup.  §4j(ii), §4l, §4v input
table.  There is **no proof of `FittingFreeDetector` anywhere in the repo**
(grep: the identifier occurs only in `SimpleRigidity.lean`); it is a pure
cited-literature hypothesis.  This answers the audit brief's question (3)
for this Prop: *assumed, not proven*.

### (c) Alignment analysis

* **Definition match: ✓.**  For finite groups, "no nontrivial abelian
  normal subgroup" ⟺ "trivial Fitting subgroup" (if `F(G) ≠ 1` then
  `Z(F(G))` is a nontrivial abelian normal subgroup of `G`).  This is the
  paper's notion (socle a product of nonabelian simples).
* **Direction: ✓.**  Only `G` Fitting-free ⟹ `H` Fitting-free is asked;
  the symmetric version follows by applying it to `Φ.symm`.  The proof via
  Satz 2.3.6 needs *both* directions of Satz 2.3.6 (uniqueness for `G`,
  non-uniqueness for a non-Fitting-free `H`) plus order transfer (to know
  the two multiplicities are read at the *same* `c = |G| = |H|`).  No
  hidden strengthening: `D(G) ≅ D(H)` already forces `|G| = |H|` by Satz
  2.3.4, so the Prop is not stronger than the literature statement.
* **Trivial-group edge case: ✓** (`G = 1` is Fitting-free vacuously and
  `D(1) ≅ D(H)` forces `H = 1`).
* **Reducible to the same open Prop.**  Under the dictionary,
  "`conductorMultiplicity (D(G)) |G| = 1` ⟺ Fitting-free" is a
  pair-counting statement about `(H, hH')` with `N_G(H,hH') = G`, `H' = 1`
  — i.e. `FittingFreeDetector` is also a `BoltjeIntegrality` consequence,
  not an independent external input.

---

## 5. `TwinSeparation` — **VERDICT: content ALIGNED, but GAP (dictionary) +
##    MISMATCH (shape) + scope caveats**

### (a) Exact Lean statement (`SimpleRigidity.lean:592–596`)

```lean
def TwinSeparation : Prop :=
  ∀ (G H : Type u) [Group G] [Group H] [Fintype G] [Fintype H],
    IsSimpleGroup G → (¬ ∀ a b : G, a * b = b * a) →
      IsFittingFree H → ¬ IsSimpleGroup H → Nat.card H = Nat.card G →
        ∃ c : ℕ, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c
```

### (b) Instantiating mathematics

The whole twin-elimination campaign, family by family:

| row | source | mechanism |
|---|---|---|
| `A_n`, all `n ≥ 9` | Theorem AT (§4aj, §4ba + addenda 1–2, v_task47/48/49) | `ind*` value set / `κ`; (H2′) discharged |
| 26 sporadics + Tits | Theorem SPT (§4bb, v_task50) | 14 rows census-empty; 10 by orbit floor; 3 by floor + `c ∣ ∏|Out|` |
| `L₂` | Theorem L2-T (§4bc + addendum) | `ι(L₂(q)) = q+1`, orbit floor, Lemma C |
| `U₃`, `Sz`, `R` | U3-T/Sz-T/Ree-T (§4bd + addendum) | `ι` lemmas, `3 ∤ |Sz(q)|` |
| `L₃`, `S₄`, `G₂`, `³D₄`, `²F₄` | §4be, §4bf | Lemma B/EQ-EX |
| `F₄, E₆, ²E₆, E₇, E₈` | §4bg | Lemma MO-EX |
| `L_d`, `U_d`, `d ≥ 4` | LU-T (§4bh + addendum) | Lemma Z/X′/DEG/PACK-TOP |
| `Sp_{2n}, Ω_{2n+1}, PΩ^±_{2n}` | §4bi | Lemma MO-SPO |

§4bh addendum records the programme state: "**twin elimination is COMPLETE
for all of CFSG**".  So the *global* `∀ G` quantifier of the Lean Prop is,
at the paper level, covered — this is the one place where a global Prop
could easily have outrun the mathematics, and it does not.

### (c) Alignment analysis

* **⚠ GAP 1 — the dictionary dependency (the brief's central question,
  answered explicitly in §6 below).**  Every non-vacuous row is separated
  by an `ind*`/`ι`/`κ` fact, not by a `conductorMultiplicity` fact.  The
  conversion is Satz 2.3.3 + 2.3.6, i.e. `BoltjeIntegrality`.
* **⚠ MISMATCH 2 — shape (`¬ D-iso` vs `∃ c`).**  The paper theorems are
  stated as *non-existence*: v_task50 Theorem SPT — "*There is no
  Fitting-free non-simple finite group `T` with `|T| = |S|` **and
  `D(T) ≅ D(S)`***"; §4ba Theorem AT — "*no finite group `T ≇ A_n` with
  `D(T) ≅ D(A_n)` exists in the Fitting-free class*".  `TwinSeparation`
  quantifies over **all** equal-order Fitting-free non-simple `H` with **no
  D-isomorphism hypothesis** and demands a witness `c`.  Formally that is
  stronger.  It is nevertheless recoverable, because the arguments split
  cleanly:
  - *census-empty rows* (e.g. 14 sporadics, most Lie rows): no such `H`
    exists as a group at all ⟹ `TwinSeparation`'s hypotheses are
    unsatisfiable at that `G` ⟹ the `∃ c` is **vacuous**, and **no
    dictionary is needed for these rows**;
  - *orbit-floor rows*: the floor is derived from `P ⊆ I(T)` (Lemma TR-1,
    an unconditional identity, v_task50 §1.2) plus arithmetic, giving
    `ι(T) ≠ ι(S)` **without** assuming a D-isomorphism.  Then
    `κ(T) ≠ κ(S)`, and taking `c = max(κ(S), κ(T))` gives multiplicity
    `≥ 1` on one side and `0` on the other (nothing lies strictly between
    `κ` and the top conductor `|G|` — that is what `κ` means).  So the
    `∃ c` witness exists — *given the dictionary*.
  Again: **no Lean lemma performs any of this**; `ATSeparation.lean` /
  `BoltjeAssembly.lean` produce `IsEmpty (DRing A ≃+* DRing T)`, not
  `TwinSeparation`.
* **⚠ GAP 3 — full CFSG, not just the order theorem.**  Instantiating
  `TwinSeparation` needs the **classification itself** (to enumerate the
  candidate socle factors `S_i` of `H`), which is a strictly larger
  citation than `SimpleOrderRigidity`'s CFSG *order* theorem.  Nothing in
  the five-input list represents it.
* **Quantifier/edge-case hygiene: clean.**
  - `H` infinite? excluded by `[Fintype H]`.  ✓
  - `H` with trivial centre but nontrivial solvable radical? excluded by
    `IsFittingFree H` (the last nontrivial derived term of a nontrivial
    solvable normal subgroup is abelian and normal in `H`).  ✓
  - `H` trivial? impossible: `Nat.card H = Nat.card G > 1`.  ✓
  - `H` abelian? excluded by `IsFittingFree` + `Nontrivial`
    (`not_comm_of_fittingFree`).  ✓
  - `H` almost simple (socle a single nonabelian simple, `H ≠ Soc H`)?
    **included** in the Lean Prop and **covered** by the paper (`ℓ = 1`
    rows are exactly this case, §4bd/§4be).  ✓
  - universe: `G H : Type u`, both in the same universe; the paper
    argument is isomorphism-invariant, so no obstruction.  ✓
* **Scope caveats inherited from the paper** (must survive into the public
  statement): the standing literature package **H1** (KL/BHR/Vasilyev
  maximal-subgroup tables, ATLAS Maxes completeness, Zsygmondy, Bochert,
  Dickson, Ward, two David-type effective constants); (H3)/(H4)-style
  residues in the LU tower are recorded closed in §4bh addendum but rest
  on exact sweeps at named bounds; `Lemma C` is [PROVEN] (v_task52) and no
  longer a debt; `(AB)`/`(AB-S)` are discharged for `A_n` (v_task49) but
  §4bb still carries `(AB-S)` for the 13 non-census sporadic rows.
* **Stale docstring.**  `SimpleRigidity.lean:586–591` still records
  `TwinSeparation` as "*PROVEN for … `A9..A40` pending v_task19; OPEN in
  general — equivalent to the Diophantine classification…*".  That is the
  2026-08-06 state; §4az addendum 2 declared the uniform-Diophantine route
  permanently abandoned and §4ba–§4bi closed the families by the `ind*`
  route instead.  The docstring understates the current mathematics by a
  wide margin while overstating its independence from the dictionary.

---

## 6. The TwinSeparation-dictionary question, answered explicitly

> *Does instantiating `TwinSeparation` formally require `BoltjeIntegrality`,
> and is that dependency documented anywhere?*

**YES, for every non-vacuous row — and NO, it is not documented where it
matters.**

*Why yes.*  `TwinSeparation`'s conclusion is about
`conductorMultiplicity (DRing G) c`, a purely ring-theoretic quantity
(`OrderTransfer.lean:144`: `Nat.card {p : R →+* ℤ // conductor R p = c}`).
Every twin-elimination theorem in §4aj–§4bi concludes something about
`ι`, `κ`, or the `ind*` value set `I(G)` — purely group-theoretic
quantities (`IsIndStarValue`, `ConductorDictionary.lean:199`:
`∃ (H, h), FullyFused H h ∧ x·|N_G(H,hH')| = |G|·|H'|`).  The *only*
bridge between the two is Müller Satz 2.3.3 (+ Satz 2.3.6 to know the top
conductor is simple, so that `κ` is the second-largest conductor), and in
this development that bridge is exactly

```
BoltjeIntegrality  ⟹ ConductorPairDictionary  ⟹  IsIndexValue G x ↔ IsIndStarValue G x
                                                  (isIndexValue_iff_of_boltje)
```

with `BoltjeIntegrality` the single remaining open Prop of the whole
conductor campaign (v_task80 §6).  §4aj states the dependency in the
mathematics ("*By Satz 2.3.3 the pair `(H, hH')` has conductor
`(N_G(H,hH') : H')` … For `G` Fitting-free the conductor `|G|` occurs
exactly once (Satz 2.3.6) so `κ(G)` is precisely the second-largest
conductor*"), and v_task50 §1.1 repeats it as `(†)`.

*The one exception.*  Rows eliminated by the **order census alone** (no
admissible socle product exists: 14 of the 27 sporadic targets, and most of
the Lie rows after the floor prefilter) make `TwinSeparation`'s hypotheses
unsatisfiable at that `G`.  Those rows instantiate the Prop **vacuously and
dictionary-free**.  They are, however, a minority of the campaign and do
not cover `A_n` or the floor-killed rows.

*Where it is documented.*  `Even/BoltjeAssembly.lean` and
`verify/v_task80_lean_assembly.md` document it **for the BC-n and
Theorem-AT-endgame consumers** — that is the whole point of the
`_of_boltje` corollaries.  It is **not** documented in
`Even/SimpleRigidity.lean`, which is where `TwinSeparation` and
`ExceptionSeparation` are consumed, and whose docstrings assert the
opposite ("*Five typed inputs, all external to the ring theory*", line 108;
"*Both inputs are external to the ring theory*", line 397; "*None of the
three is a gap in D-ring theory*", line 124).  **This is the single most
important correction the audit produces.**

*Consequence for the epistemic ledger.*  Four of the five Props
(`OrderTransfer`, `FittingFreeDetector`, `ExceptionSeparation`,
`TwinSeparation`) are, once one asks *how they are to be discharged*,
consequences of **one** ring-theoretic Prop — `BoltjeIntegrality` — plus
group theory / CFSG.  Only `SimpleOrderRigidity` is genuinely and purely
external.  The programme is therefore *more* unified than the five-input
presentation suggests, and *less* independent of the D-ring machinery.

---

## 7. Concrete, cheap Lean work that would close the formal gaps

None of these is research; all are wiring lemmas of the kind already in the
repo.

1. `exceptionSeparation_witness` / `twinSeparation_witness`: from
   `IsIndexValue G x` + `¬ IsIndexValue H x` + `|G| = |H|`, produce
   `∃ c, conductorMultiplicity (DRing G) c ≠ conductorMultiplicity (DRing H) c`.
   (~10 lines; unblocks both separation Props from the BC/AT lanes.)
2. `mullerIsolationWeak_of_boltje` and `orderTransfer_of_boltje`
   (`ConductorAtSpecies` §12 + `conductor_le_card`).
3. `fittingFreeDetector_of_…`: state
   `conductorMultiplicity (DRing G) (Nat.card G) = 1 ↔ IsFittingFree G`
   as a Prop and derive `FittingFreeDetector` from it + `OrderTransfer`;
   then note it too follows from `BoltjeIntegrality`.
4. Docstring repairs in `SimpleRigidity.lean`: lines 108–124, 369–380,
   397, 586–591, 602–614 — replace "external to the ring theory" by the
   honest split (external: CFSG + CFSG order theorem + the group-theoretic
   censuses; internal-and-open: `BoltjeIntegrality`).
5. Optional: a `TwinSeparationFor G` (per-target) Prop, so that a single
   family's result can be recorded without the global `∀ G`.

---

## 8. The honest final dependency statement (for README / paper)

> **Dependency statement.**  The theorem "*every finite nonabelian simple
> group `G` is `D`-rigid among all finite groups: `D(H) ≅ D(G)` implies
> `H ≅ G` for arbitrary finite `H`, hence `B(H) ≅ B(G)`*" is established in
> two layers.  The **assembly** is kernel-checked in Lean 4 / Mathlib
> (`LeanDring/Even/SimpleRigidity.lean`, `simpleGroupTheorem` and
> `simpleGroupTheorem_dtoB`, `sorry`-free, axioms exactly
> `[propext, Classical.choice, Quot.sound]`), together with the
> ring-theoretic invariance results it runs on — `mullerOrder` and every
> conductor multiplicity are ring-isomorphism invariants
> (`mullerOrder_eq_of_ringEquiv`, `conductorMultiplicity_eq_of_ringEquiv`),
> Müller's trivial-pair bound (`mullerTrivialBound`, proven from Burnside
> mark triangularity), the arithmetic core of Theorem BC-n, and the
> Theorem-AT squeeze.  The assembly consumes five hypotheses, stated as
> typed `Prop`s: `OrderTransfer`, `FittingFreeDetector`,
> `SimpleOrderRigidity Exc`, `ExceptionSeparation Exc`, and
> `TwinSeparation`.  **Of these, only `SimpleOrderRigidity Exc` — the
> Artin–Tits order theorem, carried with its exception family as an opaque
> parameter because Mathlib has no groups of Lie type — is external to
> D-ring theory.**  The other four are discharged by the mathematics of
> this program (Theorem BC-n for the `B_n(q)/C_n(q)` family with `n ≥ 3`
> and `q` odd, the `ι`-separation of `A₈` from `L₃(4)`, and the complete
> twin elimination over CFSG: Theorem AT for `A_n`, Theorem SPT for the 26
> sporadics and the Tits group, and the `L₂/U₃/Sz/R/L₃/S₄/G₂/³D₄/²F₄/F₄/
> E₆/²E₆/E₇/E₈/L_d/U_d/Sp/Ω/PΩ^±` towers) **only through Müller's
> conductor dictionary (Satz 2.3.3 together with Satz 2.3.6)**, since those
> results are proven about `ind*`-values, `ι` and `κ` — group-theoretic
> quantities — whereas the Lean `Prop`s speak of conductor multiplicities.
> That dictionary is itself formalized here and reduced, kernel-checked, to
> **one** named open statement, `BoltjeIntegrality` (Boltje's integrality
> congruence together with Müller's idempotent-coefficient computation;
> `ConductorAtSpecies.lean` §12, consumed by `BoltjeAssembly.lean`).  The
> group-theoretic censuses themselves rest on the standing literature
> package: CFSG and its order theorem, the Kleidman–Liebeck / Bray–Holt–
> Roney-Dougal / Vasilyev maximal-subgroup and minimal-degree tables, ATLAS
> `Maxes` completeness, Zsygmondy, Bochert, Dickson, and two David-type
> effective constants.  **In short: kernel-checked assembly and invariance;
> conditional on one open ring-theoretic `Prop` (`BoltjeIntegrality`), the
> CFSG order theorem plus CFSG itself, and a named list of classical
> group-theoretic citations.  It is not, at present, a formal proof of the
> theorem, and the two separation `Prop`s are not independent of the D-ring
> machinery.**

---

## 9. Verdict table

| Prop | verdict | one-line reason |
|---|---|---|
| `SimpleOrderRigidity Exc` | **ALIGNED** | faithful CFSG order theorem; `Exc` must exclude `B_n(2^f) ≅ C_n(2^f)` and `n = 2`, else `ExceptionSeparation` is false |
| `ExceptionSeparation Exc` | **MISMATCH (shape) + GAP (dictionary)** | BC-n yields `IsEmpty (DRing B ≃+* DRing C)`, not `∃ c`; the `ind*` → `conductorMultiplicity` step is `BoltjeIntegrality`-conditional |
| `OrderTransfer` | **ALIGNED** | faithful Satz 2.3.4; reduced in Lean to `MullerIsolationWeak` (`MullerTrivialBound` proven); also a `BoltjeIntegrality` consequence, unwired |
| `FittingFreeDetector` | **ALIGNED** (assumed, never proven) | faithful Satz 2.3.6 consequence; `IsFittingFree` ≡ trivial Fitting subgroup for finite groups |
| `TwinSeparation` | **content ALIGNED; GAP (dictionary) + MISMATCH (shape) + full-CFSG citation** | census-empty rows are vacuous and dictionary-free; every other row needs Satz 2.3.3/2.3.6 and a witness-extraction lemma that does not exist |
