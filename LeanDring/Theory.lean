/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory.Cyclotomic.CyclotomicCode
import LeanDring.Theory.Cyclotomic.CyclotomicNonMem
import LeanDring.Theory.DRing.AbelianTwo
import LeanDring.Theory.DRing.Adams
import LeanDring.Theory.DRing.Bridge
import LeanDring.Theory.DRing.BridgeCounts
import LeanDring.Theory.DRing.BridgeEntries
import LeanDring.Theory.DRing.BridgeRecognition
import LeanDring.Theory.DRing.BridgeTransport
import LeanDring.Theory.DRing.Burnside
import LeanDring.Theory.DRing.Census
import LeanDring.Theory.DRing.CharTorsion
import LeanDring.Theory.DRing.Classification
import LeanDring.Theory.DRing.DecideIso
import LeanDring.Theory.DRing.Decomposition
import LeanDring.Theory.DRing.DtoB
import LeanDring.Theory.DRing.FreeBasis
import LeanDring.Theory.DRing.GabCount
import LeanDring.Theory.DRing.GrothendieckRing
import LeanDring.Theory.DRing.Induced
import LeanDring.Theory.DRing.MarkInjectivity
import LeanDring.Theory.DRing.Marks
import LeanDring.Theory.DRing.MarksAbelianization
import LeanDring.Theory.DRing.Monomial
import LeanDring.Theory.DRing.Species
import LeanDring.Theory.DRing.SpeciesConj
import LeanDring.Theory.DRing.SpeciesInjectivity
import LeanDring.Theory.DRing.SplitDG
import LeanDring.Theory.DRing.SplitTorsionUnits
import LeanDring.Theory.DRing.SubgroupCount
import LeanDring.Theory.DRing.Unipotent
import LeanDring.Theory.DRing.Units
import LeanDring.Theory.Gauss.GaussRootNumber
import LeanDring.Theory.Gauss.GaussSign
import LeanDring.Theory.Gauss.GaussSignTheorem
import LeanDring.Theory.OddOrder.OddOrder

/-!
# LeanDring.Theory

Aggregator for the hand-written group- and D-ring theory library:
subdirectories `DRing/`, `OddOrder/`, `Gauss/`, `Cyclotomic/`. These files
import only Mathlib and other `LeanDring.Theory` files.
-/
