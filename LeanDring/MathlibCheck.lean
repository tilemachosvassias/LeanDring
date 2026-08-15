/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.RepresentationTheory.Character

/-!
# Mathlib availability check

Standalone sanity check that the pinned Mathlib dependency is available and
imports resolve. Not imported by the `LeanDring` root module; build explicitly
via `lake env lean LeanDring/MathlibCheck.lean`.
-/

#check @MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
