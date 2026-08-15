/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.SubgroupInventory.Twin1.AllSubgroupsProofs
import LeanDring.P5.Certificate.SubgroupInventory.Twin1.Complete
import LeanDring.P5.Certificate.Support.IndexCount
import Mathlib.Data.List.GetD

/-!
# Per-subgroup Frattini certificates for `NormalIndexFiveClosed`

`LeanDring.P5.Certificate.SubgroupInventory.Twin1.Complete` reduces completeness
of the 676-subgroup inventory to `NormalIndexFiveClosed`: closure of `allSubs`
under passage to *normal index-`5`* subgroups. This file builds the
**per-subgroup certification pipeline** that discharges that obligation, and runs
it on every one of the `676` inventory indices.

For each subgroup `H` (by its index `h` in `allBases`) a `FratCert` records:

* `phiIdx`  — the index of the Frattini subgroup `Φ(H)` in `allBases`;
* `wits`    — for each generator of the `Cgs` of `Φ(H)`, a **signed-atom witness
  word** expressing it as an explicit product of commutators `⁅a,b⁆^±1` and
  `5`th powers `(c^5)^±1` of elements of `H` (`a,b,c` given as coordinates,
  membership checked by the sift);
* `maxIdxs` — the indices in `allBases` of `H`'s maximal (= normal index-`5`)
  subgroups — the preimages of the hyperplanes of the Frattini quotient
  `H⧸Φ(H)`.

The Boolean **checker** `fratCertB` verifies, kernel-cheaply (sift + list
arithmetic only), four groups of conditions:

(i) **witnesses** — each witness word reproduces its `Φ`-generator, and every
    `a,b,c` sifts into `H`;
(ii) **maximals sit right** — every `maxIdxs` base has `Φ ⊆ allSubs[j] ⊆ H` and
    generator-length `= |H|`-length `- 1` (i.e. `card = card H / 5`);
(iii) **`Φ` is normal and contains the `5`-power/commutator generators** —
    pairwise commutators and `5`th powers of `H`'s generators sift into `Φ`, and
    `Φ` is normalized by `H`;
(iv) **exhaustive hyperplane count** — the `maxIdxs` are pairwise-distinct
    indices and number exactly `(card H / card Φ − 1)/4`.

Everything here is trusted only through the kernel `decide`s: the certificate
data itself is untrusted output of the generator
`LeanDring.P5.Certificate.Generators.Twin1.Gen` (`emitCert`/`renderCert`),
re-checked below. No `native_decide`, no new axioms.

The semantic step from `fratCertB h fc = true` to `InInv`-closure of
`allSubs[h]` under its normal index-`5` subgroups is isolated here as the named
hypothesis `FratDischarge` and proved in
`LeanDring.P5.Certificate.SubgroupInventory.Twin1.FratDischarge`. The
**aggregation glue** `normalIndexFiveClosed_of_all_certified`, deriving
`NormalIndexFiveClosed` from `FratDischarge` plus the coverage of all `676`
indices (`coverage_full`), is proved here.
-/

namespace LeanDring.P5Presentation

open Fin.NatCast

-- file-level maxHeartbeats: dozens of decide-heavy declarations below need it
set_option linter.style.setOption false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-! ## The certificate format -/

/-- A single signed-atom of a witness word: `(inv?, isPow5?, a, b)`, standing for
`(if isPow5 then a^5 else ⁅a,b⁆)` optionally inverted. -/
abbrev FratAtom := Bool × Bool × Coordinates × Coordinates

/-- A witness word: a list of signed atoms, read as a left-fold product. -/
abbrev FratWord := List FratAtom

/-- A per-subgroup Frattini certificate (untrusted data; verified by `fratCertB`). -/
structure FratCert where
  /-- Index in `allBases` of the Frattini subgroup `Φ(H)`. -/
  phiIdx : Nat
  /-- Indices in `allBases` of `H`'s maximal (normal index-`5`) subgroups. -/
  maxIdxs : List Nat
  /-- For each generator of the `Cgs` of `Φ(H)`, `(g, word)` with `word` a signed
  product of commutators / `5`th powers of `H`-elements evaluating to `g`. -/
  wits : List (Coordinates × FratWord)

/-! ## The kernel-cheap Boolean checker -/

/-- `allBases` retyped as raw coordinate lists (definitional). -/
def allBasesRaw : List (List Coordinates) := allBases

/-- The echelon base at index `i` in `allBases` (`[]` out of range). -/
def getB (i : Nat) : List Coordinates := allBasesRaw.getD i []

/-- Computable commutator `⁅a,b⁆ = a b a⁻¹ b⁻¹`. -/
def commutatorC (a b : Coordinates) : Coordinates :=
  mulC 1 (mulC 1 (mulC 1 a b) (invC 1 a)) (invC 1 b)

/-- The value of a signed atom. -/
def atomValC : FratAtom → Coordinates
  | (inv, isPow, a, b) =>
    let v := if isPow then mpow 1 a 5 else commutatorC a b
    if inv then invC 1 v else v

/-- The value of a witness word (left-fold product). -/
def wordValC (w : FratWord) : Coordinates :=
  w.foldl (fun acc a => mulC 1 acc (atomValC a)) (0, 0, 0, 0, 0)

/-- **The certificate checker.** Verifies (i)–(iv) using only sift and list
arithmetic — kernel-decidable, no `native_decide`. -/
def fratCertB (h : Nat) (fc : FratCert) : Bool :=
  let H := getB h
  let Phi := getB fc.phiIdx
  -- bounds
  Nat.blt h 676 && Nat.blt fc.phiIdx 676 && fc.maxIdxs.all (fun j => Nat.blt j 676) &&
  -- (i) witnesses reproduce the Φ generators, and every a,b,c sifts into H
  decide ((fc.wits.map Prod.fst) = Phi) &&
  fc.wits.all (fun gw =>
    decide (wordValC gw.2 = gw.1) &&
    gw.2.all (fun a => siftB 1 H a.2.2.1 && (a.2.1 || siftB 1 H a.2.2.2))) &&
  -- (iii) commutators & 5th powers of H's generators sift into Φ; Φ normal in H
  H.all (fun a => H.all (fun b => siftB 1 Phi (commutatorC a b))) &&
  H.all (fun a => siftB 1 Phi (mpow 1 a 5)) &&
  Phi.all (fun g => H.all (fun a =>
    siftB 1 Phi (conjC 1 a g) && siftB 1 Phi (conjC 1 (invC 1 a) g))) &&
  -- (ii) each maximal: Φ ⊆ K ⊆ H and |K| = |H|/5 (length differs by 1)
  fc.maxIdxs.all (fun j =>
    let K := getB j
    Phi.all (fun g => siftB 1 K g) && K.all (fun g => siftB 1 H g) &&
    Nat.beq (K.length + 1) H.length) &&
  -- (iv) maxIdxs pairwise distinct, and number (card H / card Φ − 1)/4 = (5^r−1)/4
  decide (fc.maxIdxs.Nodup) &&
  Nat.beq fc.maxIdxs.length ((5 ^ (H.length - Phi.length) - 1) / 4)

/-! ## Certificate data — all 676 subgroups (untrusted; from `Gen.renderCert`)

The certificates for every inventory index, split per order-stratum (matching the
`allBases = sub0 ++ sub1 ++ sub2 ++ sub3 ++ sub4 ++ sub5` layout) so each kernel
`decide` chunk stays small. Untrusted data; verified by `fratCertB` below. -/

set_option linter.style.longLine false in
/-- Stratum `sub0`: the trivial subgroup `⊥` (index `0`). -/
def certified0 : List (Nat × FratCert) :=
[
  (0, { phiIdx := 0, maxIdxs := [], wits := [] })
]

set_option linter.style.longLine false in
/-- Stratum `sub1`: the `156` order-`5` subgroups (indices `1 … 156`). -/
def certified1 : List (Nat × FratCert) :=
[
  (1, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (2, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (3, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (4, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (5, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (6, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (7, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (8, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (9, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (10, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (11, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (12, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (13, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (14, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (15, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (16, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (17, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (18, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (19, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (20, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (21, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (22, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (23, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (24, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (25, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (26, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (27, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (28, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (29, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (30, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (31, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (32, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (33, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (34, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (35, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (36, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (37, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (38, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (39, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (40, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (41, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (42, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (43, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (44, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (45, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (46, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (47, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (48, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (49, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (50, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (51, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (52, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (53, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (54, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (55, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (56, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (57, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (58, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (59, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (60, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (61, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (62, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (63, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (64, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (65, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (66, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (67, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (68, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (69, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (70, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (71, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (72, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (73, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (74, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (75, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (76, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (77, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (78, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (79, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (80, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (81, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (82, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (83, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (84, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (85, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (86, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (87, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (88, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (89, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (90, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (91, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (92, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (93, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (94, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (95, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (96, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (97, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (98, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (99, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (100, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (101, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (102, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (103, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (104, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (105, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (106, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (107, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (108, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (109, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (110, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (111, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (112, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (113, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (114, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (115, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (116, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (117, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (118, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (119, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (120, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (121, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (122, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (123, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (124, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (125, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (126, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (127, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (128, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (129, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (130, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (131, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (132, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (133, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (134, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (135, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (136, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (137, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (138, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (139, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (140, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (141, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (142, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (143, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (144, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (145, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (146, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (147, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (148, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (149, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (150, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (151, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (152, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (153, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (154, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (155, { phiIdx := 0, maxIdxs := [0], wits := [] }),
  (156, { phiIdx := 0, maxIdxs := [0], wits := [] })
]

set_option linter.style.longLine false in
/-- Stratum `sub2`: the `306` order-`5²` subgroups (indices `157 … 462`). -/
def certified2 : List (Nat × FratCert) :=
[
  (157, { phiIdx := 0, maxIdxs := [130,1,26,51,76,101], wits := [] }),
  (158, { phiIdx := 0, maxIdxs := [126,5,27,54,78,101], wits := [] }),
  (159, { phiIdx := 0, maxIdxs := [128,4,30,53,77,101], wits := [] }),
  (160, { phiIdx := 0, maxIdxs := [127,2,28,55,79,101], wits := [] }),
  (161, { phiIdx := 0, maxIdxs := [129,3,29,52,80,101], wits := [] }),
  (162, { phiIdx := 0, maxIdxs := [130,2,27,52,77,106], wits := [] }),
  (163, { phiIdx := 0, maxIdxs := [127,5,29,53,76,106], wits := [] }),
  (164, { phiIdx := 0, maxIdxs := [126,3,30,51,79,106], wits := [] }),
  (165, { phiIdx := 0, maxIdxs := [129,4,26,55,78,106], wits := [] }),
  (166, { phiIdx := 0, maxIdxs := [128,1,28,54,80,106], wits := [] }),
  (167, { phiIdx := 0, maxIdxs := [130,3,28,53,78,111], wits := [] }),
  (168, { phiIdx := 0, maxIdxs := [128,5,26,52,79,111], wits := [] }),
  (169, { phiIdx := 0, maxIdxs := [129,2,30,54,76,111], wits := [] }),
  (170, { phiIdx := 0, maxIdxs := [126,1,29,55,77,111], wits := [] }),
  (171, { phiIdx := 0, maxIdxs := [127,4,27,51,80,111], wits := [] }),
  (172, { phiIdx := 0, maxIdxs := [130,4,29,54,79,116], wits := [] }),
  (173, { phiIdx := 0, maxIdxs := [129,5,28,51,77,116], wits := [] }),
  (174, { phiIdx := 0, maxIdxs := [127,1,30,52,78,116], wits := [] }),
  (175, { phiIdx := 0, maxIdxs := [128,3,27,55,76,116], wits := [] }),
  (176, { phiIdx := 0, maxIdxs := [126,2,26,53,80,116], wits := [] }),
  (177, { phiIdx := 0, maxIdxs := [126,4,28,52,76,121], wits := [] }),
  (178, { phiIdx := 0, maxIdxs := [127,3,26,54,77,121], wits := [] }),
  (179, { phiIdx := 0, maxIdxs := [128,2,29,51,78,121], wits := [] }),
  (180, { phiIdx := 0, maxIdxs := [129,1,27,53,79,121], wits := [] }),
  (181, { phiIdx := 0, maxIdxs := [130,5,30,55,80,121], wits := [] }),
  (182, { phiIdx := 0, maxIdxs := [121,81,37,70,23,131], wits := [] }),
  (183, { phiIdx := 0, maxIdxs := [101,85,40,67,22,131], wits := [] }),
  (184, { phiIdx := 0, maxIdxs := [111,84,38,66,24,131], wits := [] }),
  (185, { phiIdx := 0, maxIdxs := [106,82,39,69,25,131], wits := [] }),
  (186, { phiIdx := 0, maxIdxs := [116,83,36,68,21,131], wits := [] }),
  (187, { phiIdx := 0, maxIdxs := [121,82,40,68,24,132], wits := [] }),
  (188, { phiIdx := 0, maxIdxs := [106,85,36,66,23,132], wits := [] }),
  (189, { phiIdx := 0, maxIdxs := [101,83,38,70,25,132], wits := [] }),
  (190, { phiIdx := 0, maxIdxs := [116,84,37,69,22,132], wits := [] }),
  (191, { phiIdx := 0, maxIdxs := [111,81,39,67,21,132], wits := [] }),
  (192, { phiIdx := 0, maxIdxs := [121,83,39,66,22,133], wits := [] }),
  (193, { phiIdx := 0, maxIdxs := [111,85,37,68,25,133], wits := [] }),
  (194, { phiIdx := 0, maxIdxs := [116,82,38,67,23,133], wits := [] }),
  (195, { phiIdx := 0, maxIdxs := [101,81,36,69,24,133], wits := [] }),
  (196, { phiIdx := 0, maxIdxs := [106,84,40,70,21,133], wits := [] }),
  (197, { phiIdx := 0, maxIdxs := [121,84,36,67,25,134], wits := [] }),
  (198, { phiIdx := 0, maxIdxs := [116,85,39,70,24,134], wits := [] }),
  (199, { phiIdx := 0, maxIdxs := [106,81,38,68,22,134], wits := [] }),
  (200, { phiIdx := 0, maxIdxs := [111,83,40,69,23,134], wits := [] }),
  (201, { phiIdx := 0, maxIdxs := [101,82,37,66,21,134], wits := [] }),
  (202, { phiIdx := 0, maxIdxs := [101,84,39,68,23,135], wits := [] }),
  (203, { phiIdx := 0, maxIdxs := [106,83,37,67,24,135], wits := [] }),
  (204, { phiIdx := 0, maxIdxs := [111,82,36,70,22,135], wits := [] }),
  (205, { phiIdx := 0, maxIdxs := [116,81,40,66,25,135], wits := [] }),
  (206, { phiIdx := 0, maxIdxs := [121,85,38,69,21,135], wits := [] }),
  (207, { phiIdx := 0, maxIdxs := [121,60,86,18,47,136], wits := [] }),
  (208, { phiIdx := 0, maxIdxs := [101,59,87,20,49,136], wits := [] }),
  (209, { phiIdx := 0, maxIdxs := [111,57,90,17,50,136], wits := [] }),
  (210, { phiIdx := 0, maxIdxs := [106,58,88,16,46,136], wits := [] }),
  (211, { phiIdx := 0, maxIdxs := [116,56,89,19,48,136], wits := [] }),
  (212, { phiIdx := 0, maxIdxs := [121,58,87,19,50,137], wits := [] }),
  (213, { phiIdx := 0, maxIdxs := [106,59,89,17,47,137], wits := [] }),
  (214, { phiIdx := 0, maxIdxs := [101,56,90,18,46,137], wits := [] }),
  (215, { phiIdx := 0, maxIdxs := [116,57,86,16,49,137], wits := [] }),
  (216, { phiIdx := 0, maxIdxs := [111,60,88,20,48,137], wits := [] }),
  (217, { phiIdx := 0, maxIdxs := [121,56,88,17,49,138], wits := [] }),
  (218, { phiIdx := 0, maxIdxs := [111,59,86,19,46,138], wits := [] }),
  (219, { phiIdx := 0, maxIdxs := [116,58,90,20,47,138], wits := [] }),
  (220, { phiIdx := 0, maxIdxs := [101,60,89,16,50,138], wits := [] }),
  (221, { phiIdx := 0, maxIdxs := [106,57,87,18,48,138], wits := [] }),
  (222, { phiIdx := 0, maxIdxs := [121,57,89,20,46,139], wits := [] }),
  (223, { phiIdx := 0, maxIdxs := [116,59,88,18,50,139], wits := [] }),
  (224, { phiIdx := 0, maxIdxs := [106,60,90,19,49,139], wits := [] }),
  (225, { phiIdx := 0, maxIdxs := [111,56,87,16,47,139], wits := [] }),
  (226, { phiIdx := 0, maxIdxs := [101,58,86,17,48,139], wits := [] }),
  (227, { phiIdx := 0, maxIdxs := [101,57,88,19,47,140], wits := [] }),
  (228, { phiIdx := 0, maxIdxs := [106,56,86,20,50,140], wits := [] }),
  (229, { phiIdx := 0, maxIdxs := [111,58,89,18,49,140], wits := [] }),
  (230, { phiIdx := 0, maxIdxs := [116,60,87,17,46,140], wits := [] }),
  (231, { phiIdx := 0, maxIdxs := [121,59,90,16,48,140], wits := [] }),
  (232, { phiIdx := 0, maxIdxs := [121,32,13,91,75,141], wits := [] }),
  (233, { phiIdx := 0, maxIdxs := [101,33,14,94,71,141], wits := [] }),
  (234, { phiIdx := 0, maxIdxs := [111,31,11,93,73,141], wits := [] }),
  (235, { phiIdx := 0, maxIdxs := [106,35,12,95,72,141], wits := [] }),
  (236, { phiIdx := 0, maxIdxs := [116,34,15,92,74,141], wits := [] }),
  (237, { phiIdx := 0, maxIdxs := [121,35,14,92,73,142], wits := [] }),
  (238, { phiIdx := 0, maxIdxs := [106,33,15,93,75,142], wits := [] }),
  (239, { phiIdx := 0, maxIdxs := [101,34,11,91,72,142], wits := [] }),
  (240, { phiIdx := 0, maxIdxs := [116,31,13,95,71,142], wits := [] }),
  (241, { phiIdx := 0, maxIdxs := [111,32,12,94,74,142], wits := [] }),
  (242, { phiIdx := 0, maxIdxs := [121,34,12,93,71,143], wits := [] }),
  (243, { phiIdx := 0, maxIdxs := [111,33,13,92,72,143], wits := [] }),
  (244, { phiIdx := 0, maxIdxs := [116,35,11,94,75,143], wits := [] }),
  (245, { phiIdx := 0, maxIdxs := [101,32,15,95,73,143], wits := [] }),
  (246, { phiIdx := 0, maxIdxs := [106,31,14,91,74,143], wits := [] }),
  (247, { phiIdx := 0, maxIdxs := [121,31,15,94,72,144], wits := [] }),
  (248, { phiIdx := 0, maxIdxs := [116,33,12,91,73,144], wits := [] }),
  (249, { phiIdx := 0, maxIdxs := [106,32,11,92,71,144], wits := [] }),
  (250, { phiIdx := 0, maxIdxs := [111,34,14,95,75,144], wits := [] }),
  (251, { phiIdx := 0, maxIdxs := [101,35,13,93,74,144], wits := [] }),
  (252, { phiIdx := 0, maxIdxs := [101,31,12,92,75,145], wits := [] }),
  (253, { phiIdx := 0, maxIdxs := [106,34,13,94,73,145], wits := [] }),
  (254, { phiIdx := 0, maxIdxs := [111,35,15,91,71,145], wits := [] }),
  (255, { phiIdx := 0, maxIdxs := [116,32,14,93,72,145], wits := [] }),
  (256, { phiIdx := 0, maxIdxs := [121,33,11,95,74,145], wits := [] }),
  (257, { phiIdx := 0, maxIdxs := [121,8,65,42,96,146], wits := [] }),
  (258, { phiIdx := 0, maxIdxs := [101,6,63,41,98,146], wits := [] }),
  (259, { phiIdx := 0, maxIdxs := [111,10,64,44,97,146], wits := [] }),
  (260, { phiIdx := 0, maxIdxs := [106,9,61,43,99,146], wits := [] }),
  (261, { phiIdx := 0, maxIdxs := [116,7,62,45,100,146], wits := [] }),
  (262, { phiIdx := 0, maxIdxs := [121,9,63,45,97,147], wits := [] }),
  (263, { phiIdx := 0, maxIdxs := [106,6,62,44,96,147], wits := [] }),
  (264, { phiIdx := 0, maxIdxs := [101,7,64,42,99,147], wits := [] }),
  (265, { phiIdx := 0, maxIdxs := [116,10,65,43,98,147], wits := [] }),
  (266, { phiIdx := 0, maxIdxs := [111,8,61,41,100,147], wits := [] }),
  (267, { phiIdx := 0, maxIdxs := [121,7,61,44,98,148], wits := [] }),
  (268, { phiIdx := 0, maxIdxs := [111,6,65,45,99,148], wits := [] }),
  (269, { phiIdx := 0, maxIdxs := [116,9,64,41,96,148], wits := [] }),
  (270, { phiIdx := 0, maxIdxs := [101,8,62,43,97,148], wits := [] }),
  (271, { phiIdx := 0, maxIdxs := [106,10,63,42,100,148], wits := [] }),
  (272, { phiIdx := 0, maxIdxs := [121,10,62,41,99,149], wits := [] }),
  (273, { phiIdx := 0, maxIdxs := [116,6,61,42,97,149], wits := [] }),
  (274, { phiIdx := 0, maxIdxs := [106,8,64,45,98,149], wits := [] }),
  (275, { phiIdx := 0, maxIdxs := [111,7,63,43,96,149], wits := [] }),
  (276, { phiIdx := 0, maxIdxs := [101,9,65,44,100,149], wits := [] }),
  (277, { phiIdx := 0, maxIdxs := [101,10,61,45,96,150], wits := [] }),
  (278, { phiIdx := 0, maxIdxs := [106,7,65,41,97,150], wits := [] }),
  (279, { phiIdx := 0, maxIdxs := [111,9,62,42,98,150], wits := [] }),
  (280, { phiIdx := 0, maxIdxs := [116,8,63,44,99,150], wits := [] }),
  (281, { phiIdx := 0, maxIdxs := [121,6,64,43,100,150], wits := [] }),
  (282, { phiIdx := 0, maxIdxs := [151,1,2,3,4,5], wits := [] }),
  (283, { phiIdx := 0, maxIdxs := [151,6,7,8,9,10], wits := [] }),
  (284, { phiIdx := 0, maxIdxs := [151,11,12,13,14,15], wits := [] }),
  (285, { phiIdx := 0, maxIdxs := [151,16,17,18,19,20], wits := [] }),
  (286, { phiIdx := 0, maxIdxs := [151,21,22,23,24,25], wits := [] }),
  (287, { phiIdx := 0, maxIdxs := [151,26,27,28,29,30], wits := [] }),
  (288, { phiIdx := 0, maxIdxs := [151,31,32,33,34,35], wits := [] }),
  (289, { phiIdx := 0, maxIdxs := [151,36,37,38,39,40], wits := [] }),
  (290, { phiIdx := 0, maxIdxs := [151,41,42,43,44,45], wits := [] }),
  (291, { phiIdx := 0, maxIdxs := [151,46,47,48,49,50], wits := [] }),
  (292, { phiIdx := 0, maxIdxs := [151,51,52,53,54,55], wits := [] }),
  (293, { phiIdx := 0, maxIdxs := [151,56,57,58,59,60], wits := [] }),
  (294, { phiIdx := 0, maxIdxs := [151,61,62,63,64,65], wits := [] }),
  (295, { phiIdx := 0, maxIdxs := [151,66,67,68,69,70], wits := [] }),
  (296, { phiIdx := 0, maxIdxs := [151,71,72,73,74,75], wits := [] }),
  (297, { phiIdx := 0, maxIdxs := [151,76,77,78,79,80], wits := [] }),
  (298, { phiIdx := 0, maxIdxs := [151,81,82,83,84,85], wits := [] }),
  (299, { phiIdx := 0, maxIdxs := [151,86,87,88,89,90], wits := [] }),
  (300, { phiIdx := 0, maxIdxs := [151,91,92,93,94,95], wits := [] }),
  (301, { phiIdx := 0, maxIdxs := [151,96,97,98,99,100], wits := [] }),
  (302, { phiIdx := 0, maxIdxs := [151,101,106,111,116,121], wits := [] }),
  (303, { phiIdx := 0, maxIdxs := [151,117,112,107,102,122], wits := [] }),
  (304, { phiIdx := 0, maxIdxs := [151,108,118,103,113,123], wits := [] }),
  (305, { phiIdx := 0, maxIdxs := [151,114,104,119,109,124], wits := [] }),
  (306, { phiIdx := 0, maxIdxs := [151,105,110,115,120,125], wits := [] }),
  (307, { phiIdx := 0, maxIdxs := [121,117,108,114,105,152], wits := [] }),
  (308, { phiIdx := 0, maxIdxs := [101,122,118,109,115,152], wits := [] }),
  (309, { phiIdx := 0, maxIdxs := [111,102,123,119,110,152], wits := [] }),
  (310, { phiIdx := 0, maxIdxs := [106,112,103,124,120,152], wits := [] }),
  (311, { phiIdx := 0, maxIdxs := [116,107,113,104,125,152], wits := [] }),
  (312, { phiIdx := 0, maxIdxs := [121,112,118,104,110,153], wits := [] }),
  (313, { phiIdx := 0, maxIdxs := [106,122,113,119,105,153], wits := [] }),
  (314, { phiIdx := 0, maxIdxs := [101,107,123,114,120,153], wits := [] }),
  (315, { phiIdx := 0, maxIdxs := [116,102,108,124,115,153], wits := [] }),
  (316, { phiIdx := 0, maxIdxs := [111,117,103,109,125,153], wits := [] }),
  (317, { phiIdx := 0, maxIdxs := [121,107,103,119,115,154], wits := [] }),
  (318, { phiIdx := 0, maxIdxs := [111,122,108,104,120,154], wits := [] }),
  (319, { phiIdx := 0, maxIdxs := [116,112,123,109,105,154], wits := [] }),
  (320, { phiIdx := 0, maxIdxs := [101,117,113,124,110,154], wits := [] }),
  (321, { phiIdx := 0, maxIdxs := [106,102,118,114,125,154], wits := [] }),
  (322, { phiIdx := 0, maxIdxs := [121,102,113,109,120,155], wits := [] }),
  (323, { phiIdx := 0, maxIdxs := [116,122,103,114,110,155], wits := [] }),
  (324, { phiIdx := 0, maxIdxs := [106,117,123,104,115,155], wits := [] }),
  (325, { phiIdx := 0, maxIdxs := [111,107,118,124,105,155], wits := [] }),
  (326, { phiIdx := 0, maxIdxs := [101,112,108,119,125,155], wits := [] }),
  (327, { phiIdx := 0, maxIdxs := [101,102,103,104,105,156], wits := [] }),
  (328, { phiIdx := 0, maxIdxs := [106,107,108,109,110,156], wits := [] }),
  (329, { phiIdx := 0, maxIdxs := [111,112,113,114,115,156], wits := [] }),
  (330, { phiIdx := 0, maxIdxs := [116,117,118,119,120,156], wits := [] }),
  (331, { phiIdx := 0, maxIdxs := [121,122,123,124,125,156], wits := [] }),
  (332, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,4,4,2),(0,0,0,0,0))])] }),
  (333, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,4,2,2),(0,0,0,0,0))])] }),
  (334, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,4,3,4),(0,0,0,0,0))])] }),
  (335, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,4,1,0),(0,0,0,0,0))])] }),
  (336, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,4,0,0),(0,0,0,0,0))])] }),
  (337, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,1,3,3),(0,0,0,0,0)),(false,true,(1,4,1,3,3),(0,0,0,0,0)),(false,true,(1,4,1,3,3),(0,0,0,0,0)),(false,true,(1,4,1,3,3),(0,0,0,0,0))])] }),
  (338, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,1,1,2),(0,0,0,0,0)),(false,true,(1,4,1,1,2),(0,0,0,0,0)),(false,true,(1,4,1,1,2),(0,0,0,0,0)),(false,true,(1,4,1,1,2),(0,0,0,0,0))])] }),
  (339, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,1,2,3),(0,0,0,0,0)),(false,true,(1,4,1,2,3),(0,0,0,0,0)),(false,true,(1,4,1,2,3),(0,0,0,0,0)),(false,true,(1,4,1,2,3),(0,0,0,0,0))])] }),
  (340, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,1,0,0),(0,0,0,0,0)),(false,true,(1,4,1,0,0),(0,0,0,0,0)),(false,true,(1,4,1,0,0),(0,0,0,0,0)),(false,true,(1,4,1,0,0),(0,0,0,0,0))])] }),
  (341, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,1,4,0),(0,0,0,0,0)),(false,true,(1,4,1,4,0),(0,0,0,0,0)),(false,true,(1,4,1,4,0),(0,0,0,0,0)),(false,true,(1,4,1,4,0),(0,0,0,0,0))])] }),
  (342, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,3,2,3),(0,0,0,0,0)),(false,true,(1,2,3,2,3),(0,0,0,0,0)),(false,true,(1,2,3,2,3),(0,0,0,0,0))])] }),
  (343, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,3,0,0),(0,0,0,0,0)),(false,true,(1,2,3,0,0),(0,0,0,0,0)),(false,true,(1,2,3,0,0),(0,0,0,0,0))])] }),
  (344, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,3,1,1),(0,0,0,0,0)),(false,true,(1,2,3,1,1),(0,0,0,0,0)),(false,true,(1,2,3,1,1),(0,0,0,0,0))])] }),
  (345, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,3,4,0),(0,0,0,0,0)),(false,true,(1,2,3,4,0),(0,0,0,0,0)),(false,true,(1,2,3,4,0),(0,0,0,0,0))])] }),
  (346, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,3,3,0),(0,0,0,0,0)),(false,true,(1,2,3,3,0),(0,0,0,0,0)),(false,true,(1,2,3,3,0),(0,0,0,0,0))])] }),
  (347, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,2,0,4),(0,0,0,0,0)),(false,true,(1,3,2,0,4),(0,0,0,0,0))])] }),
  (348, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,2,3,1),(0,0,0,0,0)),(false,true,(1,3,2,3,1),(0,0,0,0,0))])] }),
  (349, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,2,4,0),(0,0,0,0,0)),(false,true,(1,3,2,4,0),(0,0,0,0,0))])] }),
  (350, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,2,2,0),(0,0,0,0,0)),(false,true,(1,3,2,2,0),(0,0,0,0,0))])] }),
  (351, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,2,1,0),(0,0,0,0,0)),(false,true,(1,3,2,1,0),(0,0,0,0,0))])] }),
  (352, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,4,4,0),(0,0,0,0,0))])] }),
  (353, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,4,2,3),(0,0,0,0,0))])] }),
  (354, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,4,3,0),(0,0,0,0,0))])] }),
  (355, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,4,1,0),(0,0,0,0,0))])] }),
  (356, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,4,0,0),(0,0,0,0,0))])] }),
  (357, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,2,4,0),(0,0,0,0,0))])] }),
  (358, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,2,2,4),(0,0,0,0,0))])] }),
  (359, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,2,3,0),(0,0,0,0,0))])] }),
  (360, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,2,1,0),(0,0,0,0,0))])] }),
  (361, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,2,0,0),(0,0,0,0,0))])] }),
  (362, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,3,3,1),(0,0,0,0,0)),(false,true,(1,4,3,3,1),(0,0,0,0,0)),(false,true,(1,4,3,3,1),(0,0,0,0,0)),(false,true,(1,4,3,3,1),(0,0,0,0,0))])] }),
  (363, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,3,1,4),(0,0,0,0,0)),(false,true,(1,4,3,1,4),(0,0,0,0,0)),(false,true,(1,4,3,1,4),(0,0,0,0,0)),(false,true,(1,4,3,1,4),(0,0,0,0,0))])] }),
  (364, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,3,2,4),(0,0,0,0,0)),(false,true,(1,4,3,2,4),(0,0,0,0,0)),(false,true,(1,4,3,2,4),(0,0,0,0,0)),(false,true,(1,4,3,2,4),(0,0,0,0,0))])] }),
  (365, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,3,0,0),(0,0,0,0,0)),(false,true,(1,4,3,0,0),(0,0,0,0,0)),(false,true,(1,4,3,0,0),(0,0,0,0,0)),(false,true,(1,4,3,0,0),(0,0,0,0,0))])] }),
  (366, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,3,4,0),(0,0,0,0,0)),(false,true,(1,4,3,4,0),(0,0,0,0,0)),(false,true,(1,4,3,4,0),(0,0,0,0,0)),(false,true,(1,4,3,4,0),(0,0,0,0,0))])] }),
  (367, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,4,2,0),(0,0,0,0,0)),(false,true,(1,2,4,2,0),(0,0,0,0,0)),(false,true,(1,2,4,2,0),(0,0,0,0,0))])] }),
  (368, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,4,0,3),(0,0,0,0,0)),(false,true,(1,2,4,0,3),(0,0,0,0,0)),(false,true,(1,2,4,0,3),(0,0,0,0,0))])] }),
  (369, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,4,1,0),(0,0,0,0,0)),(false,true,(1,2,4,1,0),(0,0,0,0,0)),(false,true,(1,2,4,1,0),(0,0,0,0,0))])] }),
  (370, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,4,4,0),(0,0,0,0,0)),(false,true,(1,2,4,4,0),(0,0,0,0,0)),(false,true,(1,2,4,4,0),(0,0,0,0,0))])] }),
  (371, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,4,3,0),(0,0,0,0,0)),(false,true,(1,2,4,3,0),(0,0,0,0,0)),(false,true,(1,2,4,3,0),(0,0,0,0,0))])] }),
  (372, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,1,0,1),(0,0,0,0,0)),(false,true,(1,3,1,0,1),(0,0,0,0,0))])] }),
  (373, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,1,3,4),(0,0,0,0,0)),(false,true,(1,3,1,3,4),(0,0,0,0,0))])] }),
  (374, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,1,4,4),(0,0,0,0,0)),(false,true,(1,3,1,4,4),(0,0,0,0,0))])] }),
  (375, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,1,2,0),(0,0,0,0,0)),(false,true,(1,3,1,2,0),(0,0,0,0,0))])] }),
  (376, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,1,1,0),(0,0,0,0,0)),(false,true,(1,3,1,1,0),(0,0,0,0,0))])] }),
  (377, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,2,4,3),(0,0,0,0,0))])] }),
  (378, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,2,2,0),(0,0,0,0,0))])] }),
  (379, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,2,3,1),(0,0,0,0,0))])] }),
  (380, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,2,1,0),(0,0,0,0,0))])] }),
  (381, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,2,0,0),(0,0,0,0,0))])] }),
  (382, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,3,4,1),(0,0,0,0,0))])] }),
  (383, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,3,2,3),(0,0,0,0,0))])] }),
  (384, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,3,3,2),(0,0,0,0,0))])] }),
  (385, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,3,1,0),(0,0,0,0,0))])] }),
  (386, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,3,0,0),(0,0,0,0,0))])] }),
  (387, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,2,3,2),(0,0,0,0,0)),(false,true,(1,4,2,3,2),(0,0,0,0,0)),(false,true,(1,4,2,3,2),(0,0,0,0,0)),(false,true,(1,4,2,3,2),(0,0,0,0,0))])] }),
  (388, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,2,1,3),(0,0,0,0,0)),(false,true,(1,4,2,1,3),(0,0,0,0,0)),(false,true,(1,4,2,1,3),(0,0,0,0,0)),(false,true,(1,4,2,1,3),(0,0,0,0,0))])] }),
  (389, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,2,2,1),(0,0,0,0,0)),(false,true,(1,4,2,2,1),(0,0,0,0,0)),(false,true,(1,4,2,2,1),(0,0,0,0,0)),(false,true,(1,4,2,2,1),(0,0,0,0,0))])] }),
  (390, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,2,0,0),(0,0,0,0,0)),(false,true,(1,4,2,0,0),(0,0,0,0,0)),(false,true,(1,4,2,0,0),(0,0,0,0,0)),(false,true,(1,4,2,0,0),(0,0,0,0,0))])] }),
  (391, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,2,4,0),(0,0,0,0,0)),(false,true,(1,4,2,4,0),(0,0,0,0,0)),(false,true,(1,4,2,4,0),(0,0,0,0,0)),(false,true,(1,4,2,4,0),(0,0,0,0,0))])] }),
  (392, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,1,2,4),(0,0,0,0,0)),(false,true,(1,2,1,2,4),(0,0,0,0,0)),(false,true,(1,2,1,2,4),(0,0,0,0,0))])] }),
  (393, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,1,0,4),(0,0,0,0,0)),(false,true,(1,2,1,0,4),(0,0,0,0,0)),(false,true,(1,2,1,0,4),(0,0,0,0,0))])] }),
  (394, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,1,1,3),(0,0,0,0,0)),(false,true,(1,2,1,1,3),(0,0,0,0,0)),(false,true,(1,2,1,1,3),(0,0,0,0,0))])] }),
  (395, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,1,4,0),(0,0,0,0,0)),(false,true,(1,2,1,4,0),(0,0,0,0,0)),(false,true,(1,2,1,4,0),(0,0,0,0,0))])] }),
  (396, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,1,3,0),(0,0,0,0,0)),(false,true,(1,2,1,3,0),(0,0,0,0,0)),(false,true,(1,2,1,3,0),(0,0,0,0,0))])] }),
  (397, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,4,0,0),(0,0,0,0,0)),(false,true,(1,3,4,0,0),(0,0,0,0,0))])] }),
  (398, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,4,3,0),(0,0,0,0,0)),(false,true,(1,3,4,3,0),(0,0,0,0,0))])] }),
  (399, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,4,4,2),(0,0,0,0,0)),(false,true,(1,3,4,4,2),(0,0,0,0,0))])] }),
  (400, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,4,2,0),(0,0,0,0,0)),(false,true,(1,3,4,2,0),(0,0,0,0,0))])] }),
  (401, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,4,1,0),(0,0,0,0,0)),(false,true,(1,3,4,1,0),(0,0,0,0,0))])] }),
  (402, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,3,4,4),(0,0,0,0,0))])] }),
  (403, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,3,2,4),(0,0,0,0,0))])] }),
  (404, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,3,3,3),(0,0,0,0,0))])] }),
  (405, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,3,1,0),(0,0,0,0,0))])] }),
  (406, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,3,0,0),(0,0,0,0,0))])] }),
  (407, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,1,4,4),(0,0,0,0,0))])] }),
  (408, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,1,2,0),(0,0,0,0,0))])] }),
  (409, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,1,3,3),(0,0,0,0,0))])] }),
  (410, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,1,1,0),(0,0,0,0,0))])] }),
  (411, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,1,0,0),(0,0,0,0,0))])] }),
  (412, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,4,3,0),(0,0,0,0,0)),(false,true,(1,4,4,3,0),(0,0,0,0,0)),(false,true,(1,4,4,3,0),(0,0,0,0,0)),(false,true,(1,4,4,3,0),(0,0,0,0,0))])] }),
  (413, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,4,1,0),(0,0,0,0,0)),(false,true,(1,4,4,1,0),(0,0,0,0,0)),(false,true,(1,4,4,1,0),(0,0,0,0,0)),(false,true,(1,4,4,1,0),(0,0,0,0,0))])] }),
  (414, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,4,2,2),(0,0,0,0,0)),(false,true,(1,4,4,2,2),(0,0,0,0,0)),(false,true,(1,4,4,2,2),(0,0,0,0,0)),(false,true,(1,4,4,2,2),(0,0,0,0,0))])] }),
  (415, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,4,0,0),(0,0,0,0,0)),(false,true,(1,4,4,0,0),(0,0,0,0,0)),(false,true,(1,4,4,0,0),(0,0,0,0,0)),(false,true,(1,4,4,0,0),(0,0,0,0,0))])] }),
  (416, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,4,4,0),(0,0,0,0,0)),(false,true,(1,4,4,4,0),(0,0,0,0,0)),(false,true,(1,4,4,4,0),(0,0,0,0,0)),(false,true,(1,4,4,4,0),(0,0,0,0,0))])] }),
  (417, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,2,2,1),(0,0,0,0,0)),(false,true,(1,2,2,2,1),(0,0,0,0,0)),(false,true,(1,2,2,2,1),(0,0,0,0,0))])] }),
  (418, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,2,0,2),(0,0,0,0,0)),(false,true,(1,2,2,0,2),(0,0,0,0,0)),(false,true,(1,2,2,0,2),(0,0,0,0,0))])] }),
  (419, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,2,1,2),(0,0,0,0,0)),(false,true,(1,2,2,1,2),(0,0,0,0,0)),(false,true,(1,2,2,1,2),(0,0,0,0,0))])] }),
  (420, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,2,4,0),(0,0,0,0,0)),(false,true,(1,2,2,4,0),(0,0,0,0,0)),(false,true,(1,2,2,4,0),(0,0,0,0,0))])] }),
  (421, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,2,3,0),(0,0,0,0,0)),(false,true,(1,2,2,3,0),(0,0,0,0,0)),(false,true,(1,2,2,3,0),(0,0,0,0,0))])] }),
  (422, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,3,0,2),(0,0,0,0,0)),(false,true,(1,3,3,0,2),(0,0,0,0,0))])] }),
  (423, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,3,3,3),(0,0,0,0,0)),(false,true,(1,3,3,3,3),(0,0,0,0,0))])] }),
  (424, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,3,4,1),(0,0,0,0,0)),(false,true,(1,3,3,4,1),(0,0,0,0,0))])] }),
  (425, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,3,2,0),(0,0,0,0,0)),(false,true,(1,3,3,2,0),(0,0,0,0,0))])] }),
  (426, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,3,1,0),(0,0,0,0,0)),(false,true,(1,3,3,1,0),(0,0,0,0,0))])] }),
  (427, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,1,4,2),(0,0,0,0,0))])] }),
  (428, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,1,2,1),(0,0,0,0,0))])] }),
  (429, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,1,3,4),(0,0,0,0,0))])] }),
  (430, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,1,1,0),(0,0,0,0,0))])] }),
  (431, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,1,0,0),(0,0,0,0,0))])] }),
  (432, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,0,4,3),(0,0,0,0,0))])] }),
  (433, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,0,2,1),(0,0,0,0,0))])] }),
  (434, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,0,3,1),(0,0,0,0,0))])] }),
  (435, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,0,1,0),(0,0,0,0,0))])] }),
  (436, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (437, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,0,3,4),(0,0,0,0,0)),(false,true,(1,4,0,3,4),(0,0,0,0,0)),(false,true,(1,4,0,3,4),(0,0,0,0,0)),(false,true,(1,4,0,3,4),(0,0,0,0,0))])] }),
  (438, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,0,1,1),(0,0,0,0,0)),(false,true,(1,4,0,1,1),(0,0,0,0,0)),(false,true,(1,4,0,1,1),(0,0,0,0,0)),(false,true,(1,4,0,1,1),(0,0,0,0,0))])] }),
  (439, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0))])] }),
  (440, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0))])] }),
  (441, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0))])] }),
  (442, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,0,2,2),(0,0,0,0,0)),(false,true,(1,2,0,2,2),(0,0,0,0,0)),(false,true,(1,2,0,2,2),(0,0,0,0,0))])] }),
  (443, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,0,0,1),(0,0,0,0,0)),(false,true,(1,2,0,0,1),(0,0,0,0,0)),(false,true,(1,2,0,0,1),(0,0,0,0,0))])] }),
  (444, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,0,1,4),(0,0,0,0,0)),(false,true,(1,2,0,1,4),(0,0,0,0,0)),(false,true,(1,2,0,1,4),(0,0,0,0,0))])] }),
  (445, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,0,4,0),(0,0,0,0,0)),(false,true,(1,2,0,4,0),(0,0,0,0,0)),(false,true,(1,2,0,4,0),(0,0,0,0,0))])] }),
  (446, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0))])] }),
  (447, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,0,0,3),(0,0,0,0,0)),(false,true,(1,3,0,0,3),(0,0,0,0,0))])] }),
  (448, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,0,3,2),(0,0,0,0,0)),(false,true,(1,3,0,3,2),(0,0,0,0,0))])] }),
  (449, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,0,4,3),(0,0,0,0,0)),(false,true,(1,3,0,4,3),(0,0,0,0,0))])] }),
  (450, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,0,2,0),(0,0,0,0,0)),(false,true,(1,3,0,2,0),(0,0,0,0,0))])] }),
  (451, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,3,0,1,0),(0,0,0,0,0)),(false,true,(1,3,0,1,0),(0,0,0,0,0))])] }),
  (452, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,0,4,1),(0,0,0,0,0))])] }),
  (453, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,0,2,2),(0,0,0,0,0))])] }),
  (454, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,0,3,2),(0,0,0,0,0))])] }),
  (455, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,0,1,0),(0,0,0,0,0))])] }),
  (456, { phiIdx := 151, maxIdxs := [151], wits := [((0,0,0,0,1),[(false,true,(1,1,0,0,0),(0,0,0,0,0))])] }),
  (457, { phiIdx := 0, maxIdxs := [151,126,127,128,129,130], wits := [] }),
  (458, { phiIdx := 0, maxIdxs := [151,131,132,133,134,135], wits := [] }),
  (459, { phiIdx := 0, maxIdxs := [151,136,137,138,139,140], wits := [] }),
  (460, { phiIdx := 0, maxIdxs := [151,141,142,143,144,145], wits := [] }),
  (461, { phiIdx := 0, maxIdxs := [151,146,147,148,149,150], wits := [] }),
  (462, { phiIdx := 0, maxIdxs := [151,152,153,154,155,156], wits := [] })
]

set_option linter.style.longLine false in
/-- Stratum `sub3`: the `181` order-`5³` subgroups (indices `463 … 643`). -/
def certified3 : List (Nat × FratCert) :=
[
  (463, { phiIdx := 151, maxIdxs := [302,332,357,382,407,432], wits := [((0,0,0,0,1),[(false,true,(0,1,0,4,3),(0,0,0,0,0))])] }),
  (464, { phiIdx := 151, maxIdxs := [282,336,358,385,409,432], wits := [((0,0,0,0,1),[(false,true,(0,1,0,4,2),(0,0,0,0,0))])] }),
  (465, { phiIdx := 151, maxIdxs := [292,335,361,384,408,432], wits := [((0,0,0,0,1),[(false,true,(0,1,0,4,4),(0,0,0,0,0))])] }),
  (466, { phiIdx := 151, maxIdxs := [287,333,359,386,410,432], wits := [((0,0,0,0,1),[(false,true,(0,1,0,4,2),(0,0,0,0,0))])] }),
  (467, { phiIdx := 151, maxIdxs := [297,334,360,383,411,432], wits := [((0,0,0,0,1),[(false,true,(0,1,0,4,0),(0,0,0,0,0))])] }),
  (468, { phiIdx := 151, maxIdxs := [302,333,358,383,408,433], wits := [((0,0,0,0,1),[(false,true,(0,1,0,2,1),(0,0,0,0,0))])] }),
  (469, { phiIdx := 151, maxIdxs := [287,336,360,384,407,433], wits := [((0,0,0,0,1),[(false,true,(0,1,0,2,2),(0,0,0,0,0))])] }),
  (470, { phiIdx := 151, maxIdxs := [282,334,361,382,410,433], wits := [((0,0,0,0,1),[(false,true,(0,1,0,2,4),(0,0,0,0,0))])] }),
  (471, { phiIdx := 151, maxIdxs := [297,335,357,386,409,433], wits := [((0,0,0,0,1),[(false,true,(0,1,0,2,2),(0,0,0,0,0))])] }),
  (472, { phiIdx := 151, maxIdxs := [292,332,359,385,411,433], wits := [((0,0,0,0,1),[(false,true,(0,1,0,2,0),(0,0,0,0,0))])] }),
  (473, { phiIdx := 151, maxIdxs := [302,334,359,384,409,434], wits := [((0,0,0,0,1),[(false,true,(0,1,0,3,1),(0,0,0,0,0))])] }),
  (474, { phiIdx := 151, maxIdxs := [292,336,357,383,410,434], wits := [((0,0,0,0,1),[(false,true,(0,1,0,3,2),(0,0,0,0,0))])] }),
  (475, { phiIdx := 151, maxIdxs := [297,333,361,385,407,434], wits := [((0,0,0,0,1),[(false,true,(0,1,0,3,4),(0,0,0,0,0))])] }),
  (476, { phiIdx := 151, maxIdxs := [282,332,360,386,408,434], wits := [((0,0,0,0,1),[(false,true,(0,1,0,3,2),(0,0,0,0,0))])] }),
  (477, { phiIdx := 151, maxIdxs := [287,335,358,382,411,434], wits := [((0,0,0,0,1),[(false,true,(0,1,0,3,0),(0,0,0,0,0))])] }),
  (478, { phiIdx := 151, maxIdxs := [302,335,360,385,410,435], wits := [((0,0,0,0,1),[(false,true,(0,1,0,1,0),(0,0,0,0,0))])] }),
  (479, { phiIdx := 151, maxIdxs := [297,336,359,382,408,435], wits := [((0,0,0,0,1),[(false,true,(0,1,0,1,2),(0,0,0,0,0))])] }),
  (480, { phiIdx := 151, maxIdxs := [287,332,361,383,409,435], wits := [((0,0,0,0,1),[(false,true,(0,1,0,1,4),(0,0,0,0,0))])] }),
  (481, { phiIdx := 151, maxIdxs := [292,334,358,386,407,435], wits := [((0,0,0,0,1),[(false,true,(0,1,0,1,2),(0,0,0,0,0))])] }),
  (482, { phiIdx := 151, maxIdxs := [282,333,357,384,411,435], wits := [((0,0,0,0,1),[(false,true,(0,1,0,1,0),(0,0,0,0,0))])] }),
  (483, { phiIdx := 151, maxIdxs := [282,335,359,383,407,436], wits := [((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (484, { phiIdx := 151, maxIdxs := [287,334,357,385,408,436], wits := [((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (485, { phiIdx := 151, maxIdxs := [292,333,360,382,409,436], wits := [((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (486, { phiIdx := 151, maxIdxs := [297,332,358,384,410,436], wits := [((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (487, { phiIdx := 151, maxIdxs := [302,336,361,386,411,436], wits := [((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (488, { phiIdx := 151, maxIdxs := [302,412,387,362,337,437], wits := [((0,0,0,0,1),[(false,true,(1,4,0,3,4),(0,0,0,0,0)),(false,true,(1,4,0,3,4),(0,0,0,0,0)),(false,true,(1,4,0,3,4),(0,0,0,0,0)),(false,true,(1,4,0,3,4),(0,0,0,0,0))])] }),
  (489, { phiIdx := 151, maxIdxs := [282,416,388,365,339,437], wits := [((0,0,0,0,1),[(false,true,(1,4,0,3,1),(0,0,0,0,0)),(false,true,(1,4,0,3,1),(0,0,0,0,0)),(false,true,(1,4,0,3,1),(0,0,0,0,0)),(false,true,(1,4,0,3,1),(0,0,0,0,0))])] }),
  (490, { phiIdx := 151, maxIdxs := [292,415,391,364,338,437], wits := [((0,0,0,0,1),[(false,true,(1,4,0,3,0),(0,0,0,0,0)),(false,true,(1,4,0,3,0),(0,0,0,0,0)),(false,true,(1,4,0,3,0),(0,0,0,0,0)),(false,true,(1,4,0,3,0),(0,0,0,0,0))])] }),
  (491, { phiIdx := 151, maxIdxs := [287,413,389,366,340,437], wits := [((0,0,0,0,1),[(false,true,(1,4,0,3,3),(0,0,0,0,0)),(false,true,(1,4,0,3,3),(0,0,0,0,0)),(false,true,(1,4,0,3,3),(0,0,0,0,0)),(false,true,(1,4,0,3,3),(0,0,0,0,0))])] }),
  (492, { phiIdx := 151, maxIdxs := [297,414,390,363,341,437], wits := [((0,0,0,0,1),[(false,true,(1,4,0,3,0),(0,0,0,0,0)),(false,true,(1,4,0,3,0),(0,0,0,0,0)),(false,true,(1,4,0,3,0),(0,0,0,0,0)),(false,true,(1,4,0,3,0),(0,0,0,0,0))])] }),
  (493, { phiIdx := 151, maxIdxs := [302,413,388,363,338,438], wits := [((0,0,0,0,1),[(false,true,(1,4,0,1,1),(0,0,0,0,0)),(false,true,(1,4,0,1,1),(0,0,0,0,0)),(false,true,(1,4,0,1,1),(0,0,0,0,0)),(false,true,(1,4,0,1,1),(0,0,0,0,0))])] }),
  (494, { phiIdx := 151, maxIdxs := [287,416,390,364,337,438], wits := [((0,0,0,0,1),[(false,true,(1,4,0,1,1),(0,0,0,0,0)),(false,true,(1,4,0,1,1),(0,0,0,0,0)),(false,true,(1,4,0,1,1),(0,0,0,0,0)),(false,true,(1,4,0,1,1),(0,0,0,0,0))])] }),
  (495, { phiIdx := 151, maxIdxs := [282,414,391,362,340,438], wits := [((0,0,0,0,1),[(false,true,(1,4,0,1,0),(0,0,0,0,0)),(false,true,(1,4,0,1,0),(0,0,0,0,0)),(false,true,(1,4,0,1,0),(0,0,0,0,0)),(false,true,(1,4,0,1,0),(0,0,0,0,0))])] }),
  (496, { phiIdx := 151, maxIdxs := [297,415,387,366,339,438], wits := [((0,0,0,0,1),[(false,true,(1,4,0,1,3),(0,0,0,0,0)),(false,true,(1,4,0,1,3),(0,0,0,0,0)),(false,true,(1,4,0,1,3),(0,0,0,0,0)),(false,true,(1,4,0,1,3),(0,0,0,0,0))])] }),
  (497, { phiIdx := 151, maxIdxs := [292,412,389,365,341,438], wits := [((0,0,0,0,1),[(false,true,(1,4,0,1,0),(0,0,0,0,0)),(false,true,(1,4,0,1,0),(0,0,0,0,0)),(false,true,(1,4,0,1,0),(0,0,0,0,0)),(false,true,(1,4,0,1,0),(0,0,0,0,0))])] }),
  (498, { phiIdx := 151, maxIdxs := [302,414,389,364,339,439], wits := [((0,0,0,0,1),[(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0))])] }),
  (499, { phiIdx := 151, maxIdxs := [292,416,387,363,340,439], wits := [((0,0,0,0,1),[(false,true,(1,4,0,2,1),(0,0,0,0,0)),(false,true,(1,4,0,2,1),(0,0,0,0,0)),(false,true,(1,4,0,2,1),(0,0,0,0,0)),(false,true,(1,4,0,2,1),(0,0,0,0,0))])] }),
  (500, { phiIdx := 151, maxIdxs := [297,413,391,365,337,439], wits := [((0,0,0,0,1),[(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0))])] }),
  (501, { phiIdx := 151, maxIdxs := [282,412,390,366,338,439], wits := [((0,0,0,0,1),[(false,true,(1,4,0,2,3),(0,0,0,0,0)),(false,true,(1,4,0,2,3),(0,0,0,0,0)),(false,true,(1,4,0,2,3),(0,0,0,0,0)),(false,true,(1,4,0,2,3),(0,0,0,0,0))])] }),
  (502, { phiIdx := 151, maxIdxs := [287,415,388,362,341,439], wits := [((0,0,0,0,1),[(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0)),(false,true,(1,4,0,2,0),(0,0,0,0,0))])] }),
  (503, { phiIdx := 151, maxIdxs := [302,415,390,365,340,440], wits := [((0,0,0,0,1),[(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0))])] }),
  (504, { phiIdx := 151, maxIdxs := [297,416,389,362,338,440], wits := [((0,0,0,0,1),[(false,true,(1,4,0,0,1),(0,0,0,0,0)),(false,true,(1,4,0,0,1),(0,0,0,0,0)),(false,true,(1,4,0,0,1),(0,0,0,0,0)),(false,true,(1,4,0,0,1),(0,0,0,0,0))])] }),
  (505, { phiIdx := 151, maxIdxs := [287,412,391,363,339,440], wits := [((0,0,0,0,1),[(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0))])] }),
  (506, { phiIdx := 151, maxIdxs := [292,414,388,366,337,440], wits := [((0,0,0,0,1),[(false,true,(1,4,0,0,3),(0,0,0,0,0)),(false,true,(1,4,0,0,3),(0,0,0,0,0)),(false,true,(1,4,0,0,3),(0,0,0,0,0)),(false,true,(1,4,0,0,3),(0,0,0,0,0))])] }),
  (507, { phiIdx := 151, maxIdxs := [282,413,387,364,341,440], wits := [((0,0,0,0,1),[(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0)),(false,true,(1,4,0,0,0),(0,0,0,0,0))])] }),
  (508, { phiIdx := 151, maxIdxs := [282,415,389,363,337,441], wits := [((0,0,0,0,1),[(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0))])] }),
  (509, { phiIdx := 151, maxIdxs := [287,414,387,365,338,441], wits := [((0,0,0,0,1),[(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0))])] }),
  (510, { phiIdx := 151, maxIdxs := [292,413,390,362,339,441], wits := [((0,0,0,0,1),[(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0))])] }),
  (511, { phiIdx := 151, maxIdxs := [297,412,388,364,340,441], wits := [((0,0,0,0,1),[(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0))])] }),
  (512, { phiIdx := 151, maxIdxs := [302,416,391,366,341,441], wits := [((0,0,0,0,1),[(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0))])] }),
  (513, { phiIdx := 151, maxIdxs := [302,367,417,342,392,442], wits := [((0,0,0,0,1),[(false,true,(1,2,0,2,2),(0,0,0,0,0)),(false,true,(1,2,0,2,2),(0,0,0,0,0)),(false,true,(1,2,0,2,2),(0,0,0,0,0))])] }),
  (514, { phiIdx := 151, maxIdxs := [282,371,418,345,394,442], wits := [((0,0,0,0,1),[(false,true,(1,2,0,2,1),(0,0,0,0,0)),(false,true,(1,2,0,2,1),(0,0,0,0,0)),(false,true,(1,2,0,2,1),(0,0,0,0,0))])] }),
  (515, { phiIdx := 151, maxIdxs := [292,370,421,344,393,442], wits := [((0,0,0,0,1),[(false,true,(1,2,0,2,4),(0,0,0,0,0)),(false,true,(1,2,0,2,4),(0,0,0,0,0)),(false,true,(1,2,0,2,4),(0,0,0,0,0))])] }),
  (516, { phiIdx := 151, maxIdxs := [287,368,419,346,395,442], wits := [((0,0,0,0,1),[(false,true,(1,2,0,2,0),(0,0,0,0,0)),(false,true,(1,2,0,2,0),(0,0,0,0,0)),(false,true,(1,2,0,2,0),(0,0,0,0,0))])] }),
  (517, { phiIdx := 151, maxIdxs := [297,369,420,343,396,442], wits := [((0,0,0,0,1),[(false,true,(1,2,0,2,0),(0,0,0,0,0)),(false,true,(1,2,0,2,0),(0,0,0,0,0)),(false,true,(1,2,0,2,0),(0,0,0,0,0))])] }),
  (518, { phiIdx := 151, maxIdxs := [302,368,418,343,393,443], wits := [((0,0,0,0,1),[(false,true,(1,2,0,0,1),(0,0,0,0,0)),(false,true,(1,2,0,0,1),(0,0,0,0,0)),(false,true,(1,2,0,0,1),(0,0,0,0,0))])] }),
  (519, { phiIdx := 151, maxIdxs := [287,371,420,344,392,443], wits := [((0,0,0,0,1),[(false,true,(1,2,0,0,1),(0,0,0,0,0)),(false,true,(1,2,0,0,1),(0,0,0,0,0)),(false,true,(1,2,0,0,1),(0,0,0,0,0))])] }),
  (520, { phiIdx := 151, maxIdxs := [282,369,421,342,395,443], wits := [((0,0,0,0,1),[(false,true,(1,2,0,0,4),(0,0,0,0,0)),(false,true,(1,2,0,0,4),(0,0,0,0,0)),(false,true,(1,2,0,0,4),(0,0,0,0,0))])] }),
  (521, { phiIdx := 151, maxIdxs := [297,370,417,346,394,443], wits := [((0,0,0,0,1),[(false,true,(1,2,0,0,0),(0,0,0,0,0)),(false,true,(1,2,0,0,0),(0,0,0,0,0)),(false,true,(1,2,0,0,0),(0,0,0,0,0))])] }),
  (522, { phiIdx := 151, maxIdxs := [292,367,419,345,396,443], wits := [((0,0,0,0,1),[(false,true,(1,2,0,0,0),(0,0,0,0,0)),(false,true,(1,2,0,0,0),(0,0,0,0,0)),(false,true,(1,2,0,0,0),(0,0,0,0,0))])] }),
  (523, { phiIdx := 151, maxIdxs := [302,369,419,344,394,444], wits := [((0,0,0,0,1),[(false,true,(1,2,0,1,4),(0,0,0,0,0)),(false,true,(1,2,0,1,4),(0,0,0,0,0)),(false,true,(1,2,0,1,4),(0,0,0,0,0))])] }),
  (524, { phiIdx := 151, maxIdxs := [292,371,417,343,395,444], wits := [((0,0,0,0,1),[(false,true,(1,2,0,1,1),(0,0,0,0,0)),(false,true,(1,2,0,1,1),(0,0,0,0,0)),(false,true,(1,2,0,1,1),(0,0,0,0,0))])] }),
  (525, { phiIdx := 151, maxIdxs := [297,368,421,345,392,444], wits := [((0,0,0,0,1),[(false,true,(1,2,0,1,4),(0,0,0,0,0)),(false,true,(1,2,0,1,4),(0,0,0,0,0)),(false,true,(1,2,0,1,4),(0,0,0,0,0))])] }),
  (526, { phiIdx := 151, maxIdxs := [282,367,420,346,393,444], wits := [((0,0,0,0,1),[(false,true,(1,2,0,1,0),(0,0,0,0,0)),(false,true,(1,2,0,1,0),(0,0,0,0,0)),(false,true,(1,2,0,1,0),(0,0,0,0,0))])] }),
  (527, { phiIdx := 151, maxIdxs := [287,370,418,342,396,444], wits := [((0,0,0,0,1),[(false,true,(1,2,0,1,0),(0,0,0,0,0)),(false,true,(1,2,0,1,0),(0,0,0,0,0)),(false,true,(1,2,0,1,0),(0,0,0,0,0))])] }),
  (528, { phiIdx := 151, maxIdxs := [302,370,420,345,395,445], wits := [((0,0,0,0,1),[(false,true,(1,2,0,4,0),(0,0,0,0,0)),(false,true,(1,2,0,4,0),(0,0,0,0,0)),(false,true,(1,2,0,4,0),(0,0,0,0,0))])] }),
  (529, { phiIdx := 151, maxIdxs := [297,371,419,342,393,445], wits := [((0,0,0,0,1),[(false,true,(1,2,0,4,1),(0,0,0,0,0)),(false,true,(1,2,0,4,1),(0,0,0,0,0)),(false,true,(1,2,0,4,1),(0,0,0,0,0))])] }),
  (530, { phiIdx := 151, maxIdxs := [287,367,421,343,394,445], wits := [((0,0,0,0,1),[(false,true,(1,2,0,4,4),(0,0,0,0,0)),(false,true,(1,2,0,4,4),(0,0,0,0,0)),(false,true,(1,2,0,4,4),(0,0,0,0,0))])] }),
  (531, { phiIdx := 151, maxIdxs := [292,369,418,346,392,445], wits := [((0,0,0,0,1),[(false,true,(1,2,0,4,0),(0,0,0,0,0)),(false,true,(1,2,0,4,0),(0,0,0,0,0)),(false,true,(1,2,0,4,0),(0,0,0,0,0))])] }),
  (532, { phiIdx := 151, maxIdxs := [282,368,417,344,396,445], wits := [((0,0,0,0,1),[(false,true,(1,2,0,4,0),(0,0,0,0,0)),(false,true,(1,2,0,4,0),(0,0,0,0,0)),(false,true,(1,2,0,4,0),(0,0,0,0,0))])] }),
  (533, { phiIdx := 151, maxIdxs := [282,370,419,343,392,446], wits := [((0,0,0,0,1),[(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0))])] }),
  (534, { phiIdx := 151, maxIdxs := [287,369,417,345,393,446], wits := [((0,0,0,0,1),[(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0))])] }),
  (535, { phiIdx := 151, maxIdxs := [292,368,420,342,394,446], wits := [((0,0,0,0,1),[(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0))])] }),
  (536, { phiIdx := 151, maxIdxs := [297,367,418,344,395,446], wits := [((0,0,0,0,1),[(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0))])] }),
  (537, { phiIdx := 151, maxIdxs := [302,371,421,346,396,446], wits := [((0,0,0,0,1),[(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0)),(false,true,(1,2,0,3,0),(0,0,0,0,0))])] }),
  (538, { phiIdx := 151, maxIdxs := [302,397,347,422,372,447], wits := [((0,0,0,0,1),[(false,true,(1,3,0,0,3),(0,0,0,0,0)),(false,true,(1,3,0,0,3),(0,0,0,0,0))])] }),
  (539, { phiIdx := 151, maxIdxs := [282,401,348,425,374,447], wits := [((0,0,0,0,1),[(false,true,(1,3,0,0,1),(0,0,0,0,0)),(false,true,(1,3,0,0,1),(0,0,0,0,0))])] }),
  (540, { phiIdx := 151, maxIdxs := [292,400,351,424,373,447], wits := [((0,0,0,0,1),[(false,true,(1,3,0,0,3),(0,0,0,0,0)),(false,true,(1,3,0,0,3),(0,0,0,0,0))])] }),
  (541, { phiIdx := 151, maxIdxs := [287,398,349,426,375,447], wits := [((0,0,0,0,1),[(false,true,(1,3,0,0,0),(0,0,0,0,0)),(false,true,(1,3,0,0,0),(0,0,0,0,0))])] }),
  (542, { phiIdx := 151, maxIdxs := [297,399,350,423,376,447], wits := [((0,0,0,0,1),[(false,true,(1,3,0,0,0),(0,0,0,0,0)),(false,true,(1,3,0,0,0),(0,0,0,0,0))])] }),
  (543, { phiIdx := 151, maxIdxs := [302,398,348,423,373,448], wits := [((0,0,0,0,1),[(false,true,(1,3,0,3,2),(0,0,0,0,0)),(false,true,(1,3,0,3,2),(0,0,0,0,0))])] }),
  (544, { phiIdx := 151, maxIdxs := [287,401,350,424,372,448], wits := [((0,0,0,0,1),[(false,true,(1,3,0,3,1),(0,0,0,0,0)),(false,true,(1,3,0,3,1),(0,0,0,0,0))])] }),
  (545, { phiIdx := 151, maxIdxs := [282,399,351,422,375,448], wits := [((0,0,0,0,1),[(false,true,(1,3,0,3,3),(0,0,0,0,0)),(false,true,(1,3,0,3,3),(0,0,0,0,0))])] }),
  (546, { phiIdx := 151, maxIdxs := [297,400,347,426,374,448], wits := [((0,0,0,0,1),[(false,true,(1,3,0,3,0),(0,0,0,0,0)),(false,true,(1,3,0,3,0),(0,0,0,0,0))])] }),
  (547, { phiIdx := 151, maxIdxs := [292,397,349,425,376,448], wits := [((0,0,0,0,1),[(false,true,(1,3,0,3,0),(0,0,0,0,0)),(false,true,(1,3,0,3,0),(0,0,0,0,0))])] }),
  (548, { phiIdx := 151, maxIdxs := [302,399,349,424,374,449], wits := [((0,0,0,0,1),[(false,true,(1,3,0,4,3),(0,0,0,0,0)),(false,true,(1,3,0,4,3),(0,0,0,0,0))])] }),
  (549, { phiIdx := 151, maxIdxs := [292,401,347,423,375,449], wits := [((0,0,0,0,1),[(false,true,(1,3,0,4,1),(0,0,0,0,0)),(false,true,(1,3,0,4,1),(0,0,0,0,0))])] }),
  (550, { phiIdx := 151, maxIdxs := [297,398,351,425,372,449], wits := [((0,0,0,0,1),[(false,true,(1,3,0,4,3),(0,0,0,0,0)),(false,true,(1,3,0,4,3),(0,0,0,0,0))])] }),
  (551, { phiIdx := 151, maxIdxs := [282,397,350,426,373,449], wits := [((0,0,0,0,1),[(false,true,(1,3,0,4,0),(0,0,0,0,0)),(false,true,(1,3,0,4,0),(0,0,0,0,0))])] }),
  (552, { phiIdx := 151, maxIdxs := [287,400,348,422,376,449], wits := [((0,0,0,0,1),[(false,true,(1,3,0,4,0),(0,0,0,0,0)),(false,true,(1,3,0,4,0),(0,0,0,0,0))])] }),
  (553, { phiIdx := 151, maxIdxs := [302,400,350,425,375,450], wits := [((0,0,0,0,1),[(false,true,(1,3,0,2,0),(0,0,0,0,0)),(false,true,(1,3,0,2,0),(0,0,0,0,0))])] }),
  (554, { phiIdx := 151, maxIdxs := [297,401,349,422,373,450], wits := [((0,0,0,0,1),[(false,true,(1,3,0,2,1),(0,0,0,0,0)),(false,true,(1,3,0,2,1),(0,0,0,0,0))])] }),
  (555, { phiIdx := 151, maxIdxs := [287,397,351,423,374,450], wits := [((0,0,0,0,1),[(false,true,(1,3,0,2,3),(0,0,0,0,0)),(false,true,(1,3,0,2,3),(0,0,0,0,0))])] }),
  (556, { phiIdx := 151, maxIdxs := [292,399,348,426,372,450], wits := [((0,0,0,0,1),[(false,true,(1,3,0,2,0),(0,0,0,0,0)),(false,true,(1,3,0,2,0),(0,0,0,0,0))])] }),
  (557, { phiIdx := 151, maxIdxs := [282,398,347,424,376,450], wits := [((0,0,0,0,1),[(false,true,(1,3,0,2,0),(0,0,0,0,0)),(false,true,(1,3,0,2,0),(0,0,0,0,0))])] }),
  (558, { phiIdx := 151, maxIdxs := [282,400,349,423,372,451], wits := [((0,0,0,0,1),[(false,true,(1,3,0,1,0),(0,0,0,0,0)),(false,true,(1,3,0,1,0),(0,0,0,0,0))])] }),
  (559, { phiIdx := 151, maxIdxs := [287,399,347,425,373,451], wits := [((0,0,0,0,1),[(false,true,(1,3,0,1,0),(0,0,0,0,0)),(false,true,(1,3,0,1,0),(0,0,0,0,0))])] }),
  (560, { phiIdx := 151, maxIdxs := [292,398,350,422,374,451], wits := [((0,0,0,0,1),[(false,true,(1,3,0,1,0),(0,0,0,0,0)),(false,true,(1,3,0,1,0),(0,0,0,0,0))])] }),
  (561, { phiIdx := 151, maxIdxs := [297,397,348,424,375,451], wits := [((0,0,0,0,1),[(false,true,(1,3,0,1,0),(0,0,0,0,0)),(false,true,(1,3,0,1,0),(0,0,0,0,0))])] }),
  (562, { phiIdx := 151, maxIdxs := [302,401,351,426,376,451], wits := [((0,0,0,0,1),[(false,true,(1,3,0,1,0),(0,0,0,0,0)),(false,true,(1,3,0,1,0),(0,0,0,0,0))])] }),
  (563, { phiIdx := 151, maxIdxs := [302,352,377,402,427,452], wits := [((0,0,0,0,1),[(false,true,(1,1,0,4,1),(0,0,0,0,0))])] }),
  (564, { phiIdx := 151, maxIdxs := [282,356,378,405,429,452], wits := [((0,0,0,0,1),[(false,true,(1,1,0,4,1),(0,0,0,0,0))])] }),
  (565, { phiIdx := 151, maxIdxs := [292,355,381,404,428,452], wits := [((0,0,0,0,1),[(false,true,(1,1,0,4,2),(0,0,0,0,0))])] }),
  (566, { phiIdx := 151, maxIdxs := [287,353,379,406,430,452], wits := [((0,0,0,0,1),[(false,true,(1,1,0,4,2),(0,0,0,0,0))])] }),
  (567, { phiIdx := 151, maxIdxs := [297,354,380,403,431,452], wits := [((0,0,0,0,1),[(false,true,(1,1,0,4,0),(0,0,0,0,0))])] }),
  (568, { phiIdx := 151, maxIdxs := [302,353,378,403,428,453], wits := [((0,0,0,0,1),[(false,true,(1,1,0,2,2),(0,0,0,0,0))])] }),
  (569, { phiIdx := 151, maxIdxs := [287,356,380,404,427,453], wits := [((0,0,0,0,1),[(false,true,(1,1,0,2,1),(0,0,0,0,0))])] }),
  (570, { phiIdx := 151, maxIdxs := [282,354,381,402,430,453], wits := [((0,0,0,0,1),[(false,true,(1,1,0,2,2),(0,0,0,0,0))])] }),
  (571, { phiIdx := 151, maxIdxs := [297,355,377,406,429,453], wits := [((0,0,0,0,1),[(false,true,(1,1,0,2,2),(0,0,0,0,0))])] }),
  (572, { phiIdx := 151, maxIdxs := [292,352,379,405,431,453], wits := [((0,0,0,0,1),[(false,true,(1,1,0,2,0),(0,0,0,0,0))])] }),
  (573, { phiIdx := 151, maxIdxs := [302,354,379,404,429,454], wits := [((0,0,0,0,1),[(false,true,(1,1,0,3,2),(0,0,0,0,0))])] }),
  (574, { phiIdx := 151, maxIdxs := [292,356,377,403,430,454], wits := [((0,0,0,0,1),[(false,true,(1,1,0,3,1),(0,0,0,0,0))])] }),
  (575, { phiIdx := 151, maxIdxs := [297,353,381,405,427,454], wits := [((0,0,0,0,1),[(false,true,(1,1,0,3,2),(0,0,0,0,0))])] }),
  (576, { phiIdx := 151, maxIdxs := [282,352,380,406,428,454], wits := [((0,0,0,0,1),[(false,true,(1,1,0,3,2),(0,0,0,0,0))])] }),
  (577, { phiIdx := 151, maxIdxs := [287,355,378,402,431,454], wits := [((0,0,0,0,1),[(false,true,(1,1,0,3,0),(0,0,0,0,0))])] }),
  (578, { phiIdx := 151, maxIdxs := [302,355,380,405,430,455], wits := [((0,0,0,0,1),[(false,true,(1,1,0,1,0),(0,0,0,0,0))])] }),
  (579, { phiIdx := 151, maxIdxs := [297,356,379,402,428,455], wits := [((0,0,0,0,1),[(false,true,(1,1,0,1,1),(0,0,0,0,0))])] }),
  (580, { phiIdx := 151, maxIdxs := [287,352,381,403,429,455], wits := [((0,0,0,0,1),[(false,true,(1,1,0,1,2),(0,0,0,0,0))])] }),
  (581, { phiIdx := 151, maxIdxs := [292,354,378,406,427,455], wits := [((0,0,0,0,1),[(false,true,(1,1,0,1,2),(0,0,0,0,0))])] }),
  (582, { phiIdx := 151, maxIdxs := [282,353,377,404,431,455], wits := [((0,0,0,0,1),[(false,true,(1,1,0,1,0),(0,0,0,0,0))])] }),
  (583, { phiIdx := 151, maxIdxs := [282,355,379,403,427,456], wits := [((0,0,0,0,1),[(false,true,(1,1,0,0,0),(0,0,0,0,0))])] }),
  (584, { phiIdx := 151, maxIdxs := [287,354,377,405,428,456], wits := [((0,0,0,0,1),[(false,true,(1,1,0,0,0),(0,0,0,0,0))])] }),
  (585, { phiIdx := 151, maxIdxs := [292,353,380,402,429,456], wits := [((0,0,0,0,1),[(false,true,(1,1,0,0,0),(0,0,0,0,0))])] }),
  (586, { phiIdx := 151, maxIdxs := [297,352,378,404,430,456], wits := [((0,0,0,0,1),[(false,true,(1,1,0,0,0),(0,0,0,0,0))])] }),
  (587, { phiIdx := 151, maxIdxs := [302,356,381,406,431,456], wits := [((0,0,0,0,1),[(false,true,(1,1,0,0,0),(0,0,0,0,0))])] }),
  (588, { phiIdx := 0, maxIdxs := [457,282,287,292,297,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,302,177,178,179,180,181], wits := [] }),
  (589, { phiIdx := 151, maxIdxs := [457,298,293,288,283,303], wits := [((0,0,0,0,1),[(false,false,(1,0,4,0,0),(0,0,0,1,0)),(false,false,(1,0,4,0,0),(0,0,0,1,0)),(false,false,(1,0,4,0,0),(0,0,0,1,0)),(false,false,(1,0,4,0,0),(0,0,0,1,0))])] }),
  (590, { phiIdx := 151, maxIdxs := [457,289,299,284,294,304], wits := [((0,0,0,0,1),[(false,false,(1,0,2,0,0),(0,0,0,1,0)),(false,false,(1,0,2,0,0),(0,0,0,1,0)),(false,false,(1,0,2,0,0),(0,0,0,1,0)),(false,false,(1,0,2,0,0),(0,0,0,1,0))])] }),
  (591, { phiIdx := 151, maxIdxs := [457,295,285,300,290,305], wits := [((0,0,0,0,1),[(false,false,(1,0,3,0,0),(0,0,0,1,0)),(false,false,(1,0,3,0,0),(0,0,0,1,0)),(false,false,(1,0,3,0,0),(0,0,0,1,0)),(false,false,(1,0,3,0,0),(0,0,0,1,0))])] }),
  (592, { phiIdx := 151, maxIdxs := [457,286,291,296,301,306], wits := [((0,0,0,0,1),[(false,false,(1,0,1,0,0),(0,0,0,1,0)),(false,false,(1,0,1,0,0),(0,0,0,1,0)),(false,false,(1,0,1,0,0),(0,0,0,1,0)),(false,false,(1,0,1,0,0),(0,0,0,1,0))])] }),
  (593, { phiIdx := 0, maxIdxs := [302,298,289,295,286,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,458,202,203,204,205,206], wits := [] }),
  (594, { phiIdx := 151, maxIdxs := [282,303,299,290,296,458], wits := [((0,0,0,0,1),[(false,false,(1,0,0,4,0),(0,0,1,4,0))])] }),
  (595, { phiIdx := 151, maxIdxs := [292,283,304,300,291,458], wits := [((0,0,0,0,1),[(false,false,(1,0,0,4,0),(0,0,1,3,0)),(false,false,(1,0,0,4,0),(0,0,1,3,0)),(false,false,(1,0,0,4,0),(0,0,1,3,0))])] }),
  (596, { phiIdx := 151, maxIdxs := [287,293,284,305,301,458], wits := [((0,0,0,0,1),[(false,false,(1,0,0,4,0),(0,0,1,2,0)),(false,false,(1,0,0,4,0),(0,0,1,2,0))])] }),
  (597, { phiIdx := 151, maxIdxs := [297,288,294,285,306,458], wits := [((0,0,0,0,1),[(false,false,(1,0,0,4,0),(0,0,1,1,0)),(false,false,(1,0,0,4,0),(0,0,1,1,0)),(false,false,(1,0,0,4,0),(0,0,1,1,0)),(false,false,(1,0,0,4,0),(0,0,1,1,0))])] }),
  (598, { phiIdx := 0, maxIdxs := [302,293,299,285,291,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,459,227,228,229,230,231], wits := [] }),
  (599, { phiIdx := 151, maxIdxs := [287,303,294,300,286,459], wits := [((0,0,0,0,1),[(false,false,(1,0,0,2,0),(0,0,1,2,0)),(false,false,(1,0,0,2,0),(0,0,1,2,0))])] }),
  (600, { phiIdx := 151, maxIdxs := [282,288,304,295,301,459], wits := [((0,0,0,0,1),[(false,false,(1,0,0,2,0),(0,0,1,4,0))])] }),
  (601, { phiIdx := 151, maxIdxs := [297,283,289,305,296,459], wits := [((0,0,0,0,1),[(false,false,(1,0,0,2,0),(0,0,1,1,0)),(false,false,(1,0,0,2,0),(0,0,1,1,0)),(false,false,(1,0,0,2,0),(0,0,1,1,0)),(false,false,(1,0,0,2,0),(0,0,1,1,0))])] }),
  (602, { phiIdx := 151, maxIdxs := [292,298,284,290,306,459], wits := [((0,0,0,0,1),[(false,false,(1,0,0,2,0),(0,0,1,3,0)),(false,false,(1,0,0,2,0),(0,0,1,3,0)),(false,false,(1,0,0,2,0),(0,0,1,3,0))])] }),
  (603, { phiIdx := 0, maxIdxs := [302,288,284,300,296,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,460,252,253,254,255,256], wits := [] }),
  (604, { phiIdx := 151, maxIdxs := [292,303,289,285,301,460], wits := [((0,0,0,0,1),[(false,false,(1,0,0,3,0),(0,0,1,3,0)),(false,false,(1,0,0,3,0),(0,0,1,3,0)),(false,false,(1,0,0,3,0),(0,0,1,3,0))])] }),
  (605, { phiIdx := 151, maxIdxs := [297,293,304,290,286,460], wits := [((0,0,0,0,1),[(false,false,(1,0,0,3,0),(0,0,1,1,0)),(false,false,(1,0,0,3,0),(0,0,1,1,0)),(false,false,(1,0,0,3,0),(0,0,1,1,0)),(false,false,(1,0,0,3,0),(0,0,1,1,0))])] }),
  (606, { phiIdx := 151, maxIdxs := [282,298,294,305,291,460], wits := [((0,0,0,0,1),[(false,false,(1,0,0,3,0),(0,0,1,4,0))])] }),
  (607, { phiIdx := 151, maxIdxs := [287,283,299,295,306,460], wits := [((0,0,0,0,1),[(false,false,(1,0,0,3,0),(0,0,1,2,0)),(false,false,(1,0,0,3,0),(0,0,1,2,0))])] }),
  (608, { phiIdx := 0, maxIdxs := [302,283,294,290,301,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,461,277,278,279,280,281], wits := [] }),
  (609, { phiIdx := 151, maxIdxs := [297,303,284,295,291,461], wits := [((0,0,0,0,1),[(false,false,(1,0,0,1,0),(0,0,1,1,0)),(false,false,(1,0,0,1,0),(0,0,1,1,0)),(false,false,(1,0,0,1,0),(0,0,1,1,0)),(false,false,(1,0,0,1,0),(0,0,1,1,0))])] }),
  (610, { phiIdx := 151, maxIdxs := [287,298,304,285,296,461], wits := [((0,0,0,0,1),[(false,false,(1,0,0,1,0),(0,0,1,2,0)),(false,false,(1,0,0,1,0),(0,0,1,2,0))])] }),
  (611, { phiIdx := 151, maxIdxs := [292,288,299,305,286,461], wits := [((0,0,0,0,1),[(false,false,(1,0,0,1,0),(0,0,1,3,0)),(false,false,(1,0,0,1,0),(0,0,1,3,0)),(false,false,(1,0,0,1,0),(0,0,1,3,0))])] }),
  (612, { phiIdx := 151, maxIdxs := [282,293,289,300,306,461], wits := [((0,0,0,0,1),[(false,false,(1,0,0,1,0),(0,0,1,4,0))])] }),
  (613, { phiIdx := 151, maxIdxs := [282,283,284,285,286,462], wits := [((0,0,0,0,1),[(false,false,(1,0,0,0,0),(0,0,1,4,0))])] }),
  (614, { phiIdx := 151, maxIdxs := [287,288,289,290,291,462], wits := [((0,0,0,0,1),[(false,false,(1,0,0,0,0),(0,0,1,2,0)),(false,false,(1,0,0,0,0),(0,0,1,2,0))])] }),
  (615, { phiIdx := 151, maxIdxs := [292,293,294,295,296,462], wits := [((0,0,0,0,1),[(false,false,(1,0,0,0,0),(0,0,1,3,0)),(false,false,(1,0,0,0,0),(0,0,1,3,0)),(false,false,(1,0,0,0,0),(0,0,1,3,0))])] }),
  (616, { phiIdx := 151, maxIdxs := [297,298,299,300,301,462], wits := [((0,0,0,0,1),[(false,false,(1,0,0,0,0),(0,0,1,1,0)),(false,false,(1,0,0,0,0),(0,0,1,1,0)),(false,false,(1,0,0,0,0),(0,0,1,1,0)),(false,false,(1,0,0,0,0),(0,0,1,1,0))])] }),
  (617, { phiIdx := 0, maxIdxs := [302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319,320,321,322,323,324,325,326,462,327,328,329,330,331], wits := [] }),
  (618, { phiIdx := 151, maxIdxs := [457,332,333,334,335,336], wits := [((0,0,0,0,1),[(false,true,(0,1,4,0,0),(0,0,0,0,0))])] }),
  (619, { phiIdx := 151, maxIdxs := [457,337,338,339,340,341], wits := [((0,0,0,0,1),[(false,true,(1,4,1,4,4),(0,0,0,0,0)),(false,true,(1,4,1,4,4),(0,0,0,0,0)),(false,true,(1,4,1,4,4),(0,0,0,0,0)),(false,true,(1,4,1,4,4),(0,0,0,0,0))])] }),
  (620, { phiIdx := 151, maxIdxs := [457,342,343,344,345,346], wits := [((0,0,0,0,1),[(false,true,(1,2,3,3,2),(0,0,0,0,0)),(false,true,(1,2,3,3,2),(0,0,0,0,0)),(false,true,(1,2,3,3,2),(0,0,0,0,0))])] }),
  (621, { phiIdx := 151, maxIdxs := [457,347,348,349,350,351], wits := [((0,0,0,0,1),[(false,true,(1,3,2,1,4),(0,0,0,0,0)),(false,true,(1,3,2,1,4),(0,0,0,0,0))])] }),
  (622, { phiIdx := 151, maxIdxs := [457,352,353,354,355,356], wits := [((0,0,0,0,1),[(false,true,(1,1,4,0,0),(0,0,0,0,0))])] }),
  (623, { phiIdx := 151, maxIdxs := [457,357,358,359,360,361], wits := [((0,0,0,0,1),[(false,true,(0,1,2,0,0),(0,0,0,0,0))])] }),
  (624, { phiIdx := 151, maxIdxs := [457,362,363,364,365,366], wits := [((0,0,0,0,1),[(false,true,(1,4,3,4,2),(0,0,0,0,0)),(false,true,(1,4,3,4,2),(0,0,0,0,0)),(false,true,(1,4,3,4,2),(0,0,0,0,0)),(false,true,(1,4,3,4,2),(0,0,0,0,0))])] }),
  (625, { phiIdx := 151, maxIdxs := [457,367,368,369,370,371], wits := [((0,0,0,0,1),[(false,true,(1,2,4,3,0),(0,0,0,0,0)),(false,true,(1,2,4,3,0),(0,0,0,0,0)),(false,true,(1,2,4,3,0),(0,0,0,0,0))])] }),
  (626, { phiIdx := 151, maxIdxs := [457,372,373,374,375,376], wits := [((0,0,0,0,1),[(false,true,(1,3,1,1,3),(0,0,0,0,0)),(false,true,(1,3,1,1,3),(0,0,0,0,0))])] }),
  (627, { phiIdx := 151, maxIdxs := [457,377,378,379,380,381], wits := [((0,0,0,0,1),[(false,true,(1,1,2,0,0),(0,0,0,0,0))])] }),
  (628, { phiIdx := 151, maxIdxs := [457,382,383,384,385,386], wits := [((0,0,0,0,1),[(false,true,(0,1,3,0,0),(0,0,0,0,0))])] }),
  (629, { phiIdx := 151, maxIdxs := [457,387,388,389,390,391], wits := [((0,0,0,0,1),[(false,true,(1,4,2,4,3),(0,0,0,0,0)),(false,true,(1,4,2,4,3),(0,0,0,0,0)),(false,true,(1,4,2,4,3),(0,0,0,0,0)),(false,true,(1,4,2,4,3),(0,0,0,0,0))])] }),
  (630, { phiIdx := 151, maxIdxs := [457,392,393,394,395,396], wits := [((0,0,0,0,1),[(false,true,(1,2,1,3,1),(0,0,0,0,0)),(false,true,(1,2,1,3,1),(0,0,0,0,0)),(false,true,(1,2,1,3,1),(0,0,0,0,0))])] }),
  (631, { phiIdx := 151, maxIdxs := [457,397,398,399,400,401], wits := [((0,0,0,0,1),[(false,true,(1,3,4,1,1),(0,0,0,0,0)),(false,true,(1,3,4,1,1),(0,0,0,0,0))])] }),
  (632, { phiIdx := 151, maxIdxs := [457,402,403,404,405,406], wits := [((0,0,0,0,1),[(false,true,(1,1,3,0,0),(0,0,0,0,0))])] }),
  (633, { phiIdx := 151, maxIdxs := [457,407,408,409,410,411], wits := [((0,0,0,0,1),[(false,true,(0,1,1,0,0),(0,0,0,0,0))])] }),
  (634, { phiIdx := 151, maxIdxs := [457,412,413,414,415,416], wits := [((0,0,0,0,1),[(false,true,(1,4,4,4,1),(0,0,0,0,0)),(false,true,(1,4,4,4,1),(0,0,0,0,0)),(false,true,(1,4,4,4,1),(0,0,0,0,0)),(false,true,(1,4,4,4,1),(0,0,0,0,0))])] }),
  (635, { phiIdx := 151, maxIdxs := [457,417,418,419,420,421], wits := [((0,0,0,0,1),[(false,true,(1,2,2,3,4),(0,0,0,0,0)),(false,true,(1,2,2,3,4),(0,0,0,0,0)),(false,true,(1,2,2,3,4),(0,0,0,0,0))])] }),
  (636, { phiIdx := 151, maxIdxs := [457,422,423,424,425,426], wits := [((0,0,0,0,1),[(false,true,(1,3,3,1,0),(0,0,0,0,0)),(false,true,(1,3,3,1,0),(0,0,0,0,0))])] }),
  (637, { phiIdx := 151, maxIdxs := [457,427,428,429,430,431], wits := [((0,0,0,0,1),[(false,true,(1,1,1,0,0),(0,0,0,0,0))])] }),
  (638, { phiIdx := 151, maxIdxs := [457,432,433,434,435,436], wits := [((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (639, { phiIdx := 151, maxIdxs := [457,437,438,439,440,441], wits := [((0,0,0,0,1),[(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0))])] }),
  (640, { phiIdx := 151, maxIdxs := [457,442,443,444,445,446], wits := [((0,0,0,0,1),[(false,true,(1,2,0,3,3),(0,0,0,0,0)),(false,true,(1,2,0,3,3),(0,0,0,0,0)),(false,true,(1,2,0,3,3),(0,0,0,0,0))])] }),
  (641, { phiIdx := 151, maxIdxs := [457,447,448,449,450,451], wits := [((0,0,0,0,1),[(false,true,(1,3,0,1,2),(0,0,0,0,0)),(false,true,(1,3,0,1,2),(0,0,0,0,0))])] }),
  (642, { phiIdx := 151, maxIdxs := [457,452,453,454,455,456], wits := [((0,0,0,0,1),[(false,true,(1,1,0,0,0),(0,0,0,0,0))])] }),
  (643, { phiIdx := 151, maxIdxs := [457,458,459,460,461,462], wits := [((0,0,0,0,1),[(false,false,(1,0,0,0,0),(0,0,0,1,0)),(false,false,(1,0,0,0,0),(0,0,0,1,0)),(false,false,(1,0,0,0,0),(0,0,0,1,0)),(false,false,(1,0,0,0,0),(0,0,0,1,0))])] })
]

set_option linter.style.longLine false in
/-- Stratum `sub4`: the `31` order-`5⁴` subgroups (indices `644 … 674`). -/
def certified4 : List (Nat × FratCert) :=
[
  (644, { phiIdx := 151, maxIdxs := [588,618,623,628,633,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,638,483,484,485,486,487], wits := [((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (645, { phiIdx := 151, maxIdxs := [588,634,629,624,619,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,639,508,509,510,511,512], wits := [((0,0,0,0,1),[(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0)),(false,true,(1,4,0,4,0),(0,0,0,0,0))])] }),
  (646, { phiIdx := 151, maxIdxs := [588,625,635,620,630,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,640,533,534,535,536,537], wits := [((0,0,0,0,1),[(false,true,(1,2,0,3,3),(0,0,0,0,0)),(false,true,(1,2,0,3,3),(0,0,0,0,0)),(false,true,(1,2,0,3,3),(0,0,0,0,0))])] }),
  (647, { phiIdx := 151, maxIdxs := [588,631,621,636,626,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,641,558,559,560,561,562], wits := [((0,0,0,0,1),[(false,true,(1,3,0,1,2),(0,0,0,0,0)),(false,true,(1,3,0,1,2),(0,0,0,0,0))])] }),
  (648, { phiIdx := 151, maxIdxs := [588,622,627,632,637,563,564,565,566,567,568,569,570,571,572,573,574,575,576,577,578,579,580,581,582,642,583,584,585,586,587], wits := [((0,0,0,0,1),[(false,true,(1,1,0,0,0),(0,0,0,0,0))])] }),
  (649, { phiIdx := 457, maxIdxs := [638,634,625,631,622,589], wits := [((0,0,0,1,0),[(false,false,(1,0,4,0,0),(0,1,0,0,0)),(false,false,(1,0,4,0,0),(0,1,0,0,0)),(false,false,(1,0,4,0,0),(0,1,0,0,0)),(false,false,(1,0,4,0,0),(0,1,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (650, { phiIdx := 457, maxIdxs := [618,639,635,626,632,589], wits := [((0,0,0,1,0),[(false,false,(1,0,4,4,2),(0,1,4,0,2)),(false,false,(1,0,4,4,2),(0,1,4,0,2)),(false,false,(1,0,4,4,2),(0,1,4,0,2)),(false,false,(1,0,4,4,2),(0,1,4,0,2))]),((0,0,0,0,1),[(false,true,(0,1,4,0,2),(0,0,0,0,0))])] }),
  (651, { phiIdx := 457, maxIdxs := [628,619,640,636,627,589], wits := [((0,0,0,1,0),[(false,false,(1,0,4,3,3),(0,1,3,0,2)),(false,false,(1,0,4,3,3),(0,1,3,0,2)),(false,false,(1,0,4,3,3),(0,1,3,0,2)),(false,false,(1,0,4,3,3),(0,1,3,0,2))]),((0,0,0,0,1),[(false,true,(0,1,3,0,2),(0,0,0,0,0))])] }),
  (652, { phiIdx := 457, maxIdxs := [623,629,620,641,637,589], wits := [((0,0,0,1,0),[(false,false,(1,0,4,1,2),(0,1,2,0,4)),(false,false,(1,0,4,1,2),(0,1,2,0,4)),(false,false,(1,0,4,1,2),(0,1,2,0,4)),(false,false,(1,0,4,1,2),(0,1,2,0,4))]),((0,0,0,0,1),[(false,true,(0,1,2,0,4),(0,0,0,0,0))])] }),
  (653, { phiIdx := 457, maxIdxs := [633,624,630,621,642,589], wits := [((0,0,0,1,0),[(false,false,(1,0,4,0,1),(0,1,1,0,0)),(false,false,(1,0,4,0,1),(0,1,1,0,0)),(false,false,(1,0,4,0,1),(0,1,1,0,0)),(false,false,(1,0,4,0,1),(0,1,1,0,0))]),((0,0,0,0,1),[(false,true,(0,1,1,0,0),(0,0,0,0,0))])] }),
  (654, { phiIdx := 457, maxIdxs := [638,629,635,621,627,590], wits := [((0,0,0,1,0),[(false,false,(1,0,2,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,2,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,2,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,2,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (655, { phiIdx := 457, maxIdxs := [623,639,630,636,622,590], wits := [((0,0,0,1,0),[(false,false,(1,0,2,4,4),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,2,4,4),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,2,4,4),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,2,4,4),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,2,0,4),(0,0,0,0,0))])] }),
  (656, { phiIdx := 457, maxIdxs := [618,624,640,631,637,590], wits := [((0,0,0,1,0),[(false,false,(1,0,2,3,1),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,2,3,1),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,2,3,1),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,2,3,1),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,4,0,2),(0,0,0,0,0))])] }),
  (657, { phiIdx := 457, maxIdxs := [633,619,625,641,632,590], wits := [((0,0,0,1,0),[(false,false,(1,0,2,1,3),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,2,1,3),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,2,1,3),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,2,1,3),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,1,0,0),(0,0,0,0,0))])] }),
  (658, { phiIdx := 457, maxIdxs := [628,634,620,626,642,590], wits := [((0,0,0,1,0),[(false,false,(1,0,2,0,1),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,2,0,1),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,2,0,1),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,2,0,1),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,3,0,2),(0,0,0,0,0))])] }),
  (659, { phiIdx := 457, maxIdxs := [638,624,620,636,632,591], wits := [((0,0,0,1,0),[(false,false,(1,0,3,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,3,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,3,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,3,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (660, { phiIdx := 457, maxIdxs := [628,639,625,621,637,591], wits := [((0,0,0,1,0),[(false,false,(1,0,3,4,2),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,3,4,2),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,3,4,2),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,3,4,2),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,3,0,2),(0,0,0,0,0))])] }),
  (661, { phiIdx := 457, maxIdxs := [633,629,640,626,622,591], wits := [((0,0,0,1,0),[(false,false,(1,0,3,3,1),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,3,3,1),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,3,3,1),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,3,3,1),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,1,0,0),(0,0,0,0,0))])] }),
  (662, { phiIdx := 457, maxIdxs := [618,634,630,641,627,591], wits := [((0,0,0,1,0),[(false,false,(1,0,3,1,0),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,3,1,0),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,3,1,0),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,3,1,0),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,4,0,2),(0,0,0,0,0))])] }),
  (663, { phiIdx := 457, maxIdxs := [623,619,635,631,642,591], wits := [((0,0,0,1,0),[(false,false,(1,0,3,0,3),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,3,0,3),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,3,0,3),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,3,0,3),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,2,0,4),(0,0,0,0,0))])] }),
  (664, { phiIdx := 457, maxIdxs := [638,619,630,626,637,592], wits := [((0,0,0,1,0),[(false,false,(1,0,1,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,1,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,1,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,1,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] }),
  (665, { phiIdx := 457, maxIdxs := [633,639,620,631,627,592], wits := [((0,0,0,1,0),[(false,false,(1,0,1,4,0),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,1,4,0),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,1,4,0),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,1,4,0),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,1,0,0),(0,0,0,0,0))])] }),
  (666, { phiIdx := 457, maxIdxs := [623,634,640,621,632,592], wits := [((0,0,0,1,0),[(false,false,(1,0,1,3,1),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,1,3,1),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,1,3,1),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,1,3,1),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(true,true,(0,1,2,0,4),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,2,0,4),(0,0,0,0,0))])] }),
  (667, { phiIdx := 457, maxIdxs := [628,624,635,641,622,592], wits := [((0,0,0,1,0),[(false,false,(1,0,1,1,4),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,1,1,4),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,1,1,4),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,1,1,4),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(true,true,(0,1,3,0,2),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,3,0,2),(0,0,0,0,0))])] }),
  (668, { phiIdx := 457, maxIdxs := [618,629,625,636,642,592], wits := [((0,0,0,1,0),[(false,false,(1,0,1,0,2),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,1,0,2),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,1,0,2),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,1,0,2),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(true,true,(0,1,4,0,2),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,4,0,2),(0,0,0,0,0))])] }),
  (669, { phiIdx := 151, maxIdxs := [588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,643,613,614,615,616,617], wits := [((0,0,0,0,1),[(false,false,(1,0,0,0,0),(0,0,0,1,0)),(false,false,(1,0,0,0,0),(0,0,0,1,0)),(false,false,(1,0,0,0,0),(0,0,0,1,0)),(false,false,(1,0,0,0,0),(0,0,0,1,0))])] }),
  (670, { phiIdx := 457, maxIdxs := [618,619,620,621,622,643], wits := [((0,0,0,1,0),[(false,false,(1,0,0,0,0),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,4,0,2)),(true,true,(0,1,4,0,2),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,4,0,2),(0,0,0,0,0))])] }),
  (671, { phiIdx := 457, maxIdxs := [623,624,625,626,627,643], wits := [((0,0,0,1,0),[(false,false,(1,0,0,0,0),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,2,0,4)),(true,true,(0,1,2,0,4),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,2,0,4),(0,0,0,0,0))])] }),
  (672, { phiIdx := 457, maxIdxs := [628,629,630,631,632,643], wits := [((0,0,0,1,0),[(false,false,(1,0,0,0,0),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,3,0,2)),(true,true,(0,1,3,0,2),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,3,0,2),(0,0,0,0,0))])] }),
  (673, { phiIdx := 457, maxIdxs := [633,634,635,636,637,643], wits := [((0,0,0,1,0),[(false,false,(1,0,0,0,0),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,1,0,0)),(true,true,(0,1,1,0,0),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,1,0,0),(0,0,0,0,0))])] }),
  (674, { phiIdx := 457, maxIdxs := [638,639,640,641,642,643], wits := [((0,0,0,1,0),[(false,false,(1,0,0,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] })
]

set_option linter.style.longLine false in
/-- Stratum `sub5`: the top subgroup `⊤` (index `675`). -/
def certifiedTop : List (Nat × FratCert) :=
[
  (675, { phiIdx := 457, maxIdxs := [644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674], wits := [((0,0,0,1,0),[(false,false,(1,0,0,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0)),(false,false,(1,0,0,0,0),(0,1,0,0,0)),(true,true,(0,1,0,0,0),(0,0,0,0,0))]),((0,0,0,0,1),[(false,true,(0,1,0,0,0),(0,0,0,0,0))])] })
]

/-- **The full certificate list**: all `676` subgroups, keyed by inventory index
`0 … 675` in order. Untrusted data; verified by `certified_checks` below. -/
def certified : List (Nat × FratCert) :=
  certified0 ++ certified1 ++ certified2 ++ certified3 ++ certified4 ++ certifiedTop

/-! ## Verification (chunked kernel `decide`s) and coverage

Each stratum is verified by a single kernel `decide` (per-stratum, kept small).
The `certified_keys` decide checks only that the list is keyed by `0 … 675` in
order — it does **not** re-run `fratCertB` — and bridges to the `coverage`
hypothesis consumed by the aggregation layer. -/

open Cgs in
/-- Chunk `sub0` (`⊥`). -/
theorem certified_check0 : (certified0.all (fun c => fratCertB c.1 c.2)) = true := by decide

open Cgs in
/-- Chunk `sub1` (order `5`). -/
theorem certified_check1 : (certified1.all (fun c => fratCertB c.1 c.2)) = true := by decide

open Cgs in
/-- Chunk `sub2` (order `5²`). -/
theorem certified_check2 : (certified2.all (fun c => fratCertB c.1 c.2)) = true := by decide

open Cgs in
/-- Chunk `sub3` (order `5³`). -/
theorem certified_check3 : (certified3.all (fun c => fratCertB c.1 c.2)) = true := by decide

open Cgs in
/-- Chunk `sub4` (order `5⁴`, `31` subgroups). -/
theorem certified_check4 : (certified4.all (fun c => fratCertB c.1 c.2)) = true := by decide

open Cgs in
/-- Chunk `sub5` (the top subgroup `⊤`, `31` maximals — the worst case). -/
theorem certified_checkTop : (certifiedTop.all (fun c => fratCertB c.1 c.2)) = true := by decide

/-- **The whole `676`-record list is certificate-valid**, reassembled from the six
per-stratum chunks. -/
theorem certified_check_all : (certified.all (fun c => fratCertB c.1 c.2)) = true := by
  simp only [certified, List.all_append, certified_check0, certified_check1, certified_check2,
    certified_check3, certified_check4, certified_checkTop, Bool.and_true]

/-- **Every `(h, fc) ∈ certified` passes `fratCertB`.** -/
theorem certified_checks : ∀ p ∈ certified, fratCertB p.1 p.2 = true :=
  fun p hp => List.all_eq_true.mp certified_check_all p hp

/-- **The list is keyed by every index `0 … 675`, in order.** A single kernel
`decide` over the first components only (the `fratCertB` checks are done above). -/
theorem certified_keys : certified.map Prod.fst = List.range 676 := by decide

/-- **Full certificate coverage**: every index `h < 676` carries a valid
certificate in `certified`. Consumes `certified_keys` (index presence) and
`certified_checks` (validity) — no `fratCertB` is re-run here. -/
theorem coverage_full :
    ∀ h, h < 676 → ∃ fc, (h, fc) ∈ certified ∧ fratCertB h fc = true := by
  intro h hh
  have hmem : h ∈ certified.map Prod.fst := by
    rw [certified_keys]; exact List.mem_range.mpr hh
  rw [List.mem_map] at hmem
  obtain ⟨p, hp, hpe⟩ := hmem
  have hpp : (h, p.2) = p := by rw [← hpe]
  exact ⟨p.2, hpp ▸ hp, hpp ▸ certified_checks p hp⟩

/-! ## The subgroup at an inventory index, and the covering of `InInv` -/

/-- The subgroup presented by the echelon base at index `h` in `allBases`. -/
def subAt (h : Nat) : Subgroup (Coordinate 1) := ofList 1 hq1 (allBases.getD h [])

/-- For `h < 676`, the base at index `h` is a genuine inventory member. -/
theorem getD_mem_allBases (h : Nat) (hlt : h < 676) : allBases.getD h [] ∈ allBases := by
  have hl : h < allBases.length := by rw [allBases_card]; exact hlt
  rw [List.getD_eq_getElem allBases [] hl]
  exact List.getElem_mem hl

/-- For `h < 676`, `subAt h` is in the inventory. -/
theorem inInv_subAt (h : Nat) (hlt : h < 676) : InInv (subAt h) := by
  obtain ⟨c, hc, hg⟩ := mem_allSubs_of_mem_allBases _ (getD_mem_allBases h hlt)
  refine ⟨c, hc, ?_⟩
  unfold subAt
  rw [Cgs.toSubgroup, hg]

/-- **Every inventory subgroup is `subAt` of some index `< 676`.** The bridge from
the existential `InInv` to a concrete index the certificate data is keyed by. -/
theorem exists_index_of_inInv (H : Subgroup (Coordinate 1)) (hH : InInv H) :
    ∃ i, i < 676 ∧ subAt i = H := by
  obtain ⟨c, hc, rfl⟩ := hH
  have hg : c.gens ∈ allBases := by
    rw [← allSubs_gens]; exact List.mem_map_of_mem hc
  obtain ⟨i, hi, hgi⟩ := List.getElem_of_mem hg
  refine ⟨i, by rw [← allBases_card]; exact hi, ?_⟩
  unfold subAt
  rw [List.getD_eq_getElem allBases [] hi, hgi, Cgs.toSubgroup]

/-! ## The isolated per-subgroup discharge obligation and the aggregation glue

`FratDischarge` states the group-theoretic content of a certificate: a valid
certificate at index `h` closes `subAt h` under its normal index-`5` subgroups.
Its proof constructs the `CommGroup` structure on `↥(subAt h) ⧸ Φ` of exponent
`∣ 5` from certificate conditions (i)/(iii), transports the hyperplane count
`card_index_five_subgroups` (`= (5^r−1)/4`) across the quotient correspondence,
and exhausts it with the `card`-matched distinct `maxIdxs` (conditions (ii)/(iv)
plus `allSubs_pairwise_distinct`); see
`LeanDring.P5.Certificate.SubgroupInventory.Twin1.FratDischarge`. Isolating it as
a named hypothesis lets the aggregation glue below be proved independently of
it. -/

/-- The per-subgroup discharge obligation, proved as `fratDischarge` in
`LeanDring.P5.Certificate.SubgroupInventory.Twin1.FratDischarge`. -/
def FratDischarge : Prop :=
  ∀ (h : Nat) (fc : FratCert), fratCertB h fc = true →
    ∀ M : Subgroup (Coordinate 1), M < subAt h →
      (M.subgroupOf (subAt h)).Normal → M.relIndex (subAt h) = 5 → InInv M

/-- **Per-`H` closure on the certified list.** Under `FratDischarge`, every
subgroup in `certified` has its normal index-`5` subgroups back in the inventory. -/
theorem inv_closed_on_certified (hdis : FratDischarge) :
    ∀ p ∈ certified, ∀ M : Subgroup (Coordinate 1), M < subAt p.1 →
      (M.subgroupOf (subAt p.1)).Normal → M.relIndex (subAt p.1) = 5 → InInv M :=
  fun p hp => hdis p.1 p.2 (certified_checks p hp)

/-- **The aggregation glue.** If the certificate list covers *every* index
`0 … 675` with a valid certificate, then — under `FratDischarge` — the sharpened
Frattini-completeness obligation `NormalIndexFiveClosed` holds, and hence (via
`allSubs_complete_of_normalIndexFiveClosed`) the full inventory is complete. -/
theorem normalIndexFiveClosed_of_all_certified
    (hdis : FratDischarge)
    (coverage : ∀ h, h < 676 → ∃ fc, (h, fc) ∈ certified ∧ fratCertB h fc = true) :
    NormalIndexFiveClosed := by
  intro H hH M hM hnorm hidx
  obtain ⟨i, hi, rfl⟩ := exists_index_of_inInv H hH
  obtain ⟨fc, _hmem, hchk⟩ := coverage i hi
  exact hdis i fc hchk M hM hnorm hidx

/-- **Completeness, packaged.** Under `FratDischarge` and full coverage,
every subgroup of `Coordinate 1` is presented by a member of `allSubs`. -/
theorem allSubs_complete_of_all_certified
    (hdis : FratDischarge)
    (coverage : ∀ h, h < 676 → ∃ fc, (h, fc) ∈ certified ∧ fratCertB h fc = true) :
    ∀ K : Subgroup (Coordinate 1), ∃ c ∈ allSubs, c.toSubgroup = K :=
  allSubs_complete_of_normalIndexFiveClosed
    (normalIndexFiveClosed_of_all_certified hdis coverage)

/-!
## Module note — how `FratDischarge` is proved

Everything above is kernel-checked and independent of `FratDischarge` itself,
which is proved in
`LeanDring.P5.Certificate.SubgroupInventory.Twin1.FratDischarge`. For a fixed
valid certificate at index `h` (write `P := ↥(subAt h)`, a finite `5`-group, and
`Φ := frattini P`) the argument runs:

* `M ⊴ P` of relative index `5` ⟹ `M.subgroupOf` is a **coatom** ⟹ `Φ ≤ M`
  (`frattini_le_coatom`), and likewise each `maxIdxs` base `K_j` is a coatom with
  `Φ ≤ K_j` and `[P : K_j] = 5` (checker condition (ii): `card K_j = card P / 5`).
* **CommGroup on `Q := P ⧸ Φ`, exponent `∣ 5`.** Certificate (iii) certifies that
  every pairwise commutator and `5`th power of `P`'s generators sifts into `Φ`;
  closing under `Subgroup.closure_induction` gives `⁅P,P⁆ ≤ Φ` (abelian quotient)
  and `∀ x, x^5 ∈ Φ` (exponent `∣ 5`). Certificate (i)'s witness words pin the
  `Φ`-generators as products of those commutators/`5`th powers, forcing `Φ ≤ M`
  for *any* normal index-`5` `M` (`P/M` abelian of exponent `5`).
* **Count + exhaustion.** `card_index_five_subgroups Q` gives exactly
  `(card Q − 1)/4 = (5^r − 1)/4` index-`5` subgroups of `Q`; pushing forward
  along `QuotientGroup.mk' Φ` maps the index-`5` subgroups of `P` containing `Φ`
  injectively into them. Certificate (iv) makes `maxIdxs` realise exactly
  `(5^r − 1)/4` such subgroups, distinct by (ii)/(iv) + `allSubs_pairwise_distinct`
  ⟹ they exhaust the list ⟹ `M` is one of them ⟹ `InInv M`.
-/

end LeanDring.P5Presentation
