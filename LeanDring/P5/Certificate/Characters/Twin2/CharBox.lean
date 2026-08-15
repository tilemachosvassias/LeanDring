/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.P5.Certificate.Characters.Twin1.CharBox
import LeanDring.P5.Certificate.Characters.Twin2.CharExhaust

/-!
# q=2 completeness by a row-combination certificate (Step 3, `k ≥ 4`, twin q=2)

The q=2 twin of `LeanDring.P5.Certificate.Characters.Twin1.CharBox`. All of the
group-independent `ZMod 25` linear-algebra machinery (`constraintRows`, `boxVecs`,
`stdRow`, `linComb`, `dotZ_stdRow`, `dotZ_linComb_zero`, `constraints_zero`,
`mem_boxVecs`) is reused verbatim from that file; only the per-representative
discharge engine `charsAtComplete_of_cert2` is restated against the q=2 embedded
system (`repPR2`/`repCR2`, `basisAt2`, the q=2 bridge `charOKrows_iff2` and
reconstruction `charOK2_evalVec`).

Because the twin's fifth-power map differs, the q=2 power rows differ (in 106 of
the 148 reps); the box multipliers are the twin-invariant abelianization data but
the row-combination coefficients are regenerated for the q=2 constraint system.
-/

namespace LeanDring.P5Presentation

namespace Q2

open Fin.NatCast

set_option maxRecDepth 100000

/-- **Row-combination completeness engine (q=2).** Given per-coordinate annihilator
multipliers `mults` and integer row-combination coefficients `coeffs`, all
kernel-checked consistent with the embedded q=2 `charOKrows` system, the
completeness obligation `CharsAtComplete r` holds. Every hypothesis is a small
`decide` (no `25^k` enumeration). -/
theorem charsAtComplete_of_cert2 (r : Fin 148) (mults : List (ZMod 25))
    (coeffs : List (List (ZMod 25)))
    (hml : mults.length = (repPR2.getD r.val []).length)
    (hbl : (basisAt2 r).length = (repPR2.getD r.val []).length)
    (hcount : (boxVecs mults).length = charCounts.getD r.val 0)
    (hrowlen : (constraintRows (repPR2.getD r.val []) (repCR2.getD r.val []) mults.length).all
        (fun w => decide (w.length = mults.length)) = true)
    (hpr : (List.range (repPR2.getD r.val []).length).all
        (fun i => decide (((repPR2.getD r.val []).getD i []).length = mults.length)) = true)
    (hcert : (List.range mults.length).all (fun j =>
        decide (linComb mults.length (coeffs.getD j [])
          (constraintRows (repPR2.getD r.val []) (repCR2.getD r.val []) mults.length)
          = stdRow mults.length j (mults.getD j 0))) = true) :
    CharsAtComplete r := by
  change Nat.card (↥(reps r) →* ℂˣ) ≤ charCounts.getD r.val 0
  rw [← hcount,
    show Nat.card (↥(reps r) →* ℂˣ)
        = Nat.card (↥(ofList 2 hq2 (basisAt2 r)) →* ℂˣ) from by rw [reps_eq_ofList2 r]]
  apply card_hom_le_length (basisAt2 r) (wf_basisAt2 r) (boxVecs mults)
  intro χ
  set e := evalVec (basisAt2 r) χ with he
  have hrows := checker_at checkRows2_all r
  simp only [checkRows2, Bool.and_eq_true, decide_eq_true_eq] at hrows
  obtain ⟨hPR, hCR⟩ := hrows
  have hOKrows : charOKrows (repPR2.getD r.val []) (repCR2.getD r.val []) e = true := by
    rw [hPR, hCR]
    exact (charOKrows_iff2 (basisAt2 r) e).mpr (charOK2_evalVec (basisAt2 r) (wf_basisAt2 r) χ)
  have helen : e.length = mults.length := by
    rw [he, evalVec_length]; exact hbl.trans hml.symm
  have hpr' : ∀ i < (repPR2.getD r.val []).length,
      ((repPR2.getD r.val []).getD i []).length = mults.length := by
    intro i hi
    have := (List.all_eq_true.mp hpr) i (List.mem_range.mpr hi)
    rwa [decide_eq_true_eq] at this
  have hrowlen' : ∀ w ∈ constraintRows (repPR2.getD r.val []) (repCR2.getD r.val []) mults.length,
      w.length = mults.length := by
    intro w hw
    have := (List.all_eq_true.mp hrowlen) w hw
    rwa [decide_eq_true_eq] at this
  have hzero := constraints_zero (repPR2.getD r.val []) (repCR2.getD r.val []) e mults.length
    hml (helen) hpr' hOKrows
  apply mem_boxVecs mults e helen
  intro j hj
  have hcertj : linComb mults.length (coeffs.getD j [])
      (constraintRows (repPR2.getD r.val []) (repCR2.getD r.val []) mults.length)
      = stdRow mults.length j (mults.getD j 0) := by
    have := (List.all_eq_true.mp hcert) j (List.mem_range.mpr hj)
    rwa [decide_eq_true_eq] at this
  have hcomb := dotZ_linComb_zero e mults.length (coeffs.getD j [])
    (constraintRows (repPR2.getD r.val []) (repCR2.getD r.val []) mults.length) hrowlen' hzero
  rw [hcertj, dotZ_stdRow mults.length j e (mults.getD j 0) helen hj] at hcomb
  exact hcomb

end Q2

end LeanDring.P5Presentation
