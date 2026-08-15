/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P4.NpTwoCounts
import LeanDring.P4.NoTableIso

/-!
# Closing the order-`p⁴` species-table sweep: the residual pairs

A handful of order-`p⁴` pairs agree on the order-`p` subgroup count and on the
abelianization order, and so survive the earlier separations. Those recorded
here are separated by the **order-`p²` subgroup count** (`P4NpTwoCounts`), which
is `2p² + p + 1` for `G9`, `Gid3` and `Gid8` but `p² + p + 1` for `CH7` and
`Model p d`. The remaining pair `G9`/`Gid3`, tied on every count through `p²`,
is separated by the order-`p³` count in `P4OrderP3`
(`isEmpty_tableIso_g9_gid3`).

Together with the earlier `isEmpty_tableIso_*` theorems and the (xii)/(xiii)
twin separation, every non-isomorphic pair of order-`p⁴` groups (`p ≥ 5`) has a
machine-checked species-table separation.
-/

namespace LeanDring

namespace P4

open DRing

variable {p : ℕ} [Fact p.Prime] [Fact (Odd p)]

/-- **G9 vs CH7**: separated by the order-`p²` subgroup count
(`2p²+p+1` vs `p²+p+1`). -/
theorem isEmpty_tableIso_g9_ch7 :
    IsEmpty (SpeciesTableIso (G9 p) (CH7 p)) := by
  constructor
  intro T
  have h := T.card_subgroups_eq (p ^ 2)
  rw [card_order_p2_subgroups_g9, card_order_p2_subgroups_ch7] at h
  have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
  omega

/-- **CH7 vs Gid3**: separated by the order-`p²` subgroup count
(`p²+p+1` vs `2p²+p+1`). -/
theorem isEmpty_tableIso_ch7_gid3 :
    IsEmpty (SpeciesTableIso (CH7 p) (Gid3 p)) := by
  constructor
  intro T
  have h := T.card_subgroups_eq (p ^ 2)
  rw [card_order_p2_subgroups_ch7, card_order_p2_subgroups_gid3] at h
  have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
  omega

/-- **Gid8 vs Model** (`d ≠ 0`, covering both twins `d = 1` / `d = QNR`):
separated by the order-`p²` subgroup count (`2p²+p+1` vs `p²+p+1`). -/
theorem isEmpty_tableIso_gid8_model (hp5 : 5 ≤ p) {d : ZMod p} (hd : d ≠ 0) :
    IsEmpty (SpeciesTableIso (Gid8 p) (Model p d)) := by
  constructor
  intro T
  have h := T.card_subgroups_eq (p ^ 2)
  rw [card_order_p2_subgroups_gid8 p hp5, card_order_p2_subgroups_model p hp5 hd] at h
  have hpos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos 2
  omega

end P4

end LeanDring
