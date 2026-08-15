/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharCert
import LeanDring.P5.Certificate.Characters.Twin1.CharData

/-!
# `#eval` sizing report for the species-table support

**Outside the build closure.** Nothing imports this file; it contains no
theorems and carries no part of the trust base. It is kept as the provenance of
the sizing figures quoted for the certificate: how many of the `148² = 21904`
subgroup-class pairs `(K, H)` can carry a nonzero species entry, and how much
transversal data certifying them costs.

A species entry at `(K, H)` vanishes unless `H` is subconjugate to `K`, for
which `|H| ≤ |K|` is a necessary condition; `classSupport` counts the pairs that
survive that test, and `suppCostUnits` weights each surviving column by the size
`|G/K| = 5^(5 - ordExp K)` of the transversal its certificate needs. The order-25
stratum (`ordExp = 2`) is reported separately: it is where the two twins'
species entries actually differ.
-/

namespace LeanDring.P5Presentation

/-- order exponent (log_5 |K|) per class = echelon basis length. -/
def ordExp (r : Nat) : Nat := (repBases.getD r []).length
def ordHist : List (Nat × Nat) :=
  (List.range 6).map (fun k => (k, ((List.range 148).filter (fun r => ordExp r == k)).length))

/-- Number of ordered class pairs `(K, H)` with `ordExp H ≤ ordExp K` — the
    necessary condition for `H` to be subconjugate to `K`, and hence an upper
    bound on the support of the species table at subgroup-class level. -/
def classSupport : Nat :=
  ((List.range 148).map (fun rK =>
    ((List.range 148).filter (fun rH => ordExp rH ≤ ordExp rK)).length)).sum

/-- `Σ_K (#support columns of K) · |G/K|`, with `|G/K| = 5^(5 - ordExp K)` the
    size of the transversal each column's certificate carries. -/
def suppCostUnits : Nat :=
  ((List.range 148).map (fun rK =>
    (((List.range 148).filter (fun rH => ordExp rH ≤ ordExp rK)).length) *
      (5 ^ (5 - ordExp rK)))).sum

#eval ordHist              -- #classes per order exponent
#eval classSupport         -- support pairs at subgroup-class level, out of 148² = 21904
#eval (148*148 : Nat)
#eval suppCostUnits        -- Σ (support columns) · |G/K|
-- The order-25 stratum (ordExp = 2, |K| = 25, |G/K| = 125), where the twins'
-- entries differ: number of such classes, then columns surviving the order test.
#eval ((List.range 148).filter (fun r => ordExp r == 2)).length
#eval ((List.range 148).filter (fun rH => ordExp rH ≤ 2)).length

end LeanDring.P5Presentation
