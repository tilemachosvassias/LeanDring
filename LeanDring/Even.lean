/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Even.ATSeparation
import LeanDring.Even.Arity
import LeanDring.Even.Assembly
import LeanDring.Even.ZModUnitsPPow
import LeanDring.Even.BCSeparation
import LeanDring.Even.BoltjeAssembly
import LeanDring.Even.BoltjeCongruence
import LeanDring.Even.BurnsideGhost
import LeanDring.Even.BurnsideMarks
import LeanDring.Even.Cancellation
import LeanDring.Even.CentralSylowTwo
import LeanDring.Even.ConductorAtSpecies
import LeanDring.Even.ConductorDictionary
import LeanDring.Even.ConductorDictionaryGalois
import LeanDring.Even.ConductorDictionaryProofs
import LeanDring.Even.CriterionT
import LeanDring.Even.DedekindOdd
import LeanDring.Even.DedekindOrderP
import LeanDring.Even.Descent
import LeanDring.Even.Functorial
import LeanDring.Even.GaugeGroup
import LeanDring.Even.Intrinsic
import LeanDring.Even.Linkage
import LeanDring.Even.MarksSlice
import LeanDring.Even.MullerBound
import LeanDring.Even.MullerIsolation
import LeanDring.Even.OrderTransfer
import LeanDring.Even.Profiles
import LeanDring.Even.Separation
import LeanDring.Even.Shadow
import LeanDring.Even.SimpleRigidity
import LeanDring.Even.SpeciesRationality
import LeanDring.Even.SpeciesSeparation
import LeanDring.Even.SpeciesSurjectivity
import LeanDring.Even.SubgroupMoebius
import LeanDring.Even.TIR
import LeanDring.Even.Target
import LeanDring.Even.Transport
import LeanDring.Even.Triples

/-!
# The even-order layer, aggregated

Imports every module of `LeanDring/Even/`.

Importing this file from the root module puts the even-order work inside
the build closure, and `LeanDring/AxiomAudit.lean` imports it directly and
prints the axiom set of every module below, so that a `lake build` of the
root, and the axiom audit, cover Sections 6 and 7 of the paper as well as
Parts I--II.

What that shows is *not* that Theorems C and D are unconditionally
kernel-checked. They are formally verified **implications** whose
hypotheses are named `Prop`s — `BoltjeIntegrality`, `SimpleOrderRigidity`,
`TwinSeparation`, `CoprimeTensorFactorization`, and the rest. What the
audit does show is that those implications, and everything else in the
layer, are proved with no `sorry` and on the three standard axioms. The
accounting of which hypotheses are external, and why, is §7.6 of the
paper.
-/
