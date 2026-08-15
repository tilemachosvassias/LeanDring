/-
Copyright (c) 2026 Tilemachos Vassias. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tilemachos Vassias (formalization assisted by Claude)
-/
import LeanDring.Theory
import LeanDring.P4
import LeanDring.P5
import LeanDring.Even

/-!
# Axiom audit

Reproducible certification that the headline theorems depend only on the
three standard axioms `[propext, Classical.choice, Quot.sound]` — no
`sorry`, no custom axioms. Building this file prints the axiom set of
each theorem below: 1300 `#print axioms` lines, of which the last 395
cover all 39 modules of the even-order layer (`LeanDring/Even/`).
-/

-- Stratum 1: foundations
#print axioms LeanDring.DRing.species_injective
#print axioms LeanDring.DRing.range_eta_eq_fix_psi_two

-- Stratum 2: basis and units
#print axioms LeanDring.DRing.basisOfCharPairClass
#print axioms LeanDring.DRing.torsion_unit_factorization
#print axioms LeanDring.DRing.torsion_unit_eq_charElt_mul
#print axioms LeanDring.DRing.eq_zero_of_one_add_pow_eq_one
#print axioms LeanDring.DRing.torsion_unit_eq_pm_charElt
#print axioms LeanDring.DRing.torsion_unit_eq_pm_charElt_of_pgroup
#print axioms LeanDring.DRing.card_charHom_eq_card_abelianization
#print axioms LeanDring.DRing.card_torsionUnits_eq
#print axioms LeanDring.DRing.card_abelianization_eq_of_speciesTableIso
#print axioms LeanDring.DRing.sharedSpeciesInvariants_of_pgroup
#print axioms LeanDring.DRing.SpeciesRigidityWitness.dringEquiv
#print axioms LeanDring.DRing.SpeciesRigidityWitness.sound_of_pgroup
#print axioms LeanDring.DRing.card_eq_and_subgroup_count_eq
#print axioms LeanDring.DRing.card_markClasses_eq
#print axioms LeanDring.DRing.SpeciesTableEncoding.decideSpeciesMatch_eq_true_iff
#print axioms LeanDring.DRing.SpeciesTableEncoding.nonempty_dringEquiv_of_decideSpeciesMatch
#print axioms LeanDring.DRing.SpeciesTableEncoding.checkCertificate_eq_true_iff
#print axioms LeanDring.DRing.SpeciesTableEncoding.hasSpeciesMatch_of_checkCertificate
#print axioms LeanDring.DRing.SpeciesTableEncoding.nonempty_dringEquiv_of_checkCertificate
#print axioms LeanDring.CyclotomicCode.reduce_eq_iff_eval_eq
#print axioms LeanDring.P5CyclotomicCode.eval_power
#print axioms LeanDring.P5CyclotomicCode.code_eq_iff_eval_eq
#print axioms LeanDring.P5CyclotomicCode.equalSums_eq_true_iff
#print axioms LeanDring.P5CyclotomicCode.sumPowers_eq_iff_value_eq
#print axioms LeanDring.P5CyclotomicCode.phi25_regression
#print axioms LeanDring.P5CyclotomicCode.one_ne_zeta_regression
#print axioms LeanDring.P5Presentation.relator_eq_one
#print axioms LeanDring.P5Presentation.card_coordinates
#print axioms LeanDring.P5Presentation.stepInv_step
#print axioms LeanDring.P5Presentation.step_stepInv
#print axioms LeanDring.P5Presentation.gen_pow_five
#print axioms LeanDring.P5Presentation.gen_conjugates
#print axioms LeanDring.P5Presentation.normalForm_step_four
#print axioms LeanDring.P5Presentation.normalForm_step_three
#print axioms LeanDring.P5Presentation.normalForm_step_two
#print axioms LeanDring.P5Presentation.normalForm_step_one
#print axioms LeanDring.P5Presentation.normalForm_step_zero
#print axioms LeanDring.P5Presentation.normalForm_step
#print axioms LeanDring.P5Presentation.normalForm_stepInv
#print axioms LeanDring.P5Presentation.normalForm_surjective
#print axioms LeanDring.P5Presentation.coordinateAction_gen
#print axioms LeanDring.P5Presentation.coordinateAction_normalForm
#print axioms LeanDring.P5Presentation.normalForm_injective
#print axioms LeanDring.P5Presentation.normalForm_bijective
#print axioms LeanDring.P5Presentation.normalFormEquiv68
#print axioms LeanDring.P5Presentation.normalFormEquiv69
#print axioms LeanDring.P5Presentation.normalForm_iterate_step
#print axioms LeanDring.P5Presentation.normalForm_iterate_stepInv
#print axioms LeanDring.P5Presentation.normalForm_mulC
#print axioms LeanDring.P5Presentation.normalForm_invC
#print axioms LeanDring.P5Presentation.mulC_assoc
#print axioms LeanDring.P5Presentation.normalFormMulEquiv

-- Canonical generating sequence: the induced-pcgs layer
#print axioms LeanDring.P5Presentation.coordAt_mulC_right
#print axioms LeanDring.P5Presentation.coordAt_zpow
#print axioms LeanDring.P5Presentation.mem_head_iff
#print axioms LeanDring.P5Presentation.sift_mem_iff
#print axioms LeanDring.P5Presentation.card_ofList
#print axioms LeanDring.P5Presentation.Cgs.sift_mem_iff
#print axioms LeanDring.P5Presentation.Cgs.card_toSubgroup
#print axioms LeanDring.P5Presentation.Cgs.cgsEquiv_iff

-- Subgroup inventory: 676 subgroups, per-order strata,
-- low-stratum well-formedness certified end-to-end
#print axioms LeanDring.P5Presentation.allBases_card
#print axioms LeanDring.P5Presentation.allBases_strata
#print axioms LeanDring.P5Presentation.allSubs_length
#print axioms LeanDring.P5Presentation.allSubs_orders
#print axioms LeanDring.P5Presentation.allSubs_strata
#print axioms LeanDring.P5Presentation.allSubs_pairwise_distinct
#print axioms LeanDring.P5Presentation.bot_mem_allSubs
#print axioms LeanDring.P5Presentation.top_mem_allSubs

-- Completeness of the 676-subgroup inventory. The downward
-- covering induction is unconditional; full completeness is conditional on the
-- single Frattini-completeness fact `MaximalsClosed` (see the module note in
-- P5/Certificate/SubgroupInventory/Twin1/Complete.lean).
#print axioms LeanDring.P5Presentation.card_lt
#print axioms LeanDring.P5Presentation.exists_maxProper
#print axioms LeanDring.P5Presentation.key
#print axioms LeanDring.P5Presentation.allSubs_complete_of_covering
#print axioms LeanDring.P5Presentation.covering_of_maximalsClosed
#print axioms LeanDring.P5Presentation.allSubs_complete_of_maximalsClosed

-- Step A of the `NormalIndexFiveClosed` discharge: the hyperplane count. A finite
-- abelian group of exponent dividing 5 has exactly (|Q|-1)/4 index-5 subgroups
-- (the Frattini-quotient count the Frattini step consumes). Fully unconditional.
#print axioms LeanDring.P5Presentation.card_prime_order_subgroups
#print axioms LeanDring.P5Presentation.card_index_five_subgroups

-- Stratum 3: the species-table transport
#print axioms LeanDring.DRing.SpeciesTableIso.card_subgroups_eq
#print axioms LeanDring.DRing.SpeciesTableIso.markBelow_rows
#print axioms LeanDring.DRing.SpeciesTableIso.card_fiber_eq

-- Müller's odd-order D ⇒ B theorem
#print axioms LeanDring.OddOrder.complexSpeciesColumn_linearIndependent
#print axioms LeanDring.OddOrder.everyComplexPointIsSpecies
#print axioms LeanDring.OddOrder.nontrivialSpeciesNotIntegerValued_of_odd
#print axioms LeanDring.OddOrder.allIntegerPointsAreMarks_of_odd
#print axioms LeanDring.OddOrder.burnsideEquivOfOddOrder

-- Quadratic Gauss sum, including the canonical positive-sign theorem
#print axioms LeanDring.GaussSign.gaussSum_quadratic_sq
#print axioms LeanDring.GaussSign.norm_gaussSum_quadratic
#print axioms LeanDring.GaussSign.gauss_eq
#print axioms LeanDring.GaussSign.rootNumber_χℂ_eq_one

-- Stratum 4: order p⁴
#print axioms LeanDring.P4.value_equation_impossible
#print axioms LeanDring.P4.Model.card_order_p_subgroups
#print axioms LeanDring.P4.Model.species_A_block_gauss
#print axioms LeanDring.P4.Model.species_sElt_gauss
#print axioms LeanDring.P4.Model.g1_entry_gauss_form
#print axioms LeanDring.P4.Model.g2_entry_gauss_form
#print axioms LeanDring.P4.isEmpty_tableIso_m6_m8
#print axioms LeanDring.P4.isEmpty_tableIso_g14_maxClass
#print axioms LeanDring.P4.isEmpty_tableIso_a31_a22
#print axioms LeanDring.P4.isEmpty_tableIso_model_model_of_entry_reduction
#print axioms LeanDring.P4.twin_entry_equality_impossible
#print axioms LeanDring.P4.zetaP2_pow_eq
#print axioms LeanDring.P4.exists_eq_zetaP2_pow_of_pow_eq
#print axioms LeanDring.P4.zeta8_pow_eight
#print axioms LeanDring.P4.zeta8_pow_four_p
#print axioms LeanDring.P4.zeta8_pow_two_p
#print axioms LeanDring.P4.stdAddChar_eq_zeta_pow
#print axioms LeanDring.P4.gauss_eq_sqrt_mul
#print axioms LeanDring.P4.Model.g1_entry_zeta_form
#print axioms LeanDring.P4.Model.A_block_gauss_zeta
#print axioms LeanDring.P4.Model.g2_entry_zeta_form
#print axioms LeanDring.P4.Model.g1_phase_simp
#print axioms LeanDring.P4.Model.g2_phase_simp
#print axioms LeanDring.P4.Model.phase_gen_simp
#print axioms LeanDring.P4.Model.exp_phase_qr
#print axioms LeanDring.P4.Model.sign_qr
#print axioms LeanDring.P4.Model.A_block_qr_closed_form
#print axioms LeanDring.P4.Model.g1_exponent_identity
#print axioms LeanDring.P4.Model.g1_entry_form
#print axioms LeanDring.P4.Model.g2_exponent_identity
#print axioms LeanDring.P4.Model.g2_sign_identity
#print axioms LeanDring.P4.Model.g2_entry_form

#print axioms LeanDring.P4.Model.char_sElt_extraction
#print axioms LeanDring.P4.Model.u_eq_one_of_char_pow
#print axioms LeanDring.P4.Model.u_eq_kinv_of_char_pow
#print axioms LeanDring.P4.Model.kphase_simp
#print axioms LeanDring.P4.Model.A_block_kgen_closed_form
#print axioms LeanDring.P4.zetaP2_not_mem_adjoin_zetaP
#print axioms LeanDring.P4.mem_adjoin_of_pow_eq_one
#print axioms LeanDring.P4.eq_zero_of_mul_zetaP2_mem
#print axioms LeanDring.P4.pow_p2_root_mem_adjoin_iff
#print axioms LeanDring.P4.eq_pow_of_mul_eq_zetaP2_mul
#print axioms LeanDring.P4.exists_G1_entry_eq
#print axioms LeanDring.P4.entry_factor
#print axioms LeanDring.P4.disp_pow_p
#print axioms LeanDring.P4.entry_not_mem_adjoin
#print axioms LeanDring.P4.sElt_pow_psq
#print axioms LeanDring.P4.subA_pow_psq
#print axioms LeanDring.P4.eq_subA_of_charHom_card
#print axioms LeanDring.P4.A_block_mem_adjoin_iff
#print axioms LeanDring.P4.disp_pow_p_gen
#print axioms LeanDring.P4.entry_factor_gen
#print axioms LeanDring.P4.A_block_mem_adjoin_iff_gen
#print axioms LeanDring.P4.species_A_row_eq_zero_of_not_le
#print axioms LeanDring.P4.species_le_normal_eq
#print axioms LeanDring.P4.A_block_entry_eq_z_impossible
#print axioms LeanDring.P4.model_pow_psq
#print axioms LeanDring.P4.prime_normal_le_center
#print axioms LeanDring.P4.eq_subA_of_char_primitive
#print axioms LeanDring.P4.exists_char_values
#print axioms LeanDring.P4.zElt_eq_sElt_pow
#print axioms LeanDring.P4.exists_charDist
#print axioms LeanDring.P4.isEmpty_tableIso_model_model
#print axioms LeanDring.P5Presentation.p5_dring_iso_of_speciesMatch
#print axioms LeanDring.P4.card_omega2_model
#print axioms LeanDring.P4.a211_pow_psq
#print axioms LeanDring.P4.card_omega2_a211
#print axioms LeanDring.P4.mod3_pow_psq
#print axioms LeanDring.P4.g9_pow_psq
#print axioms LeanDring.P4.card_omega2_g9
#print axioms LeanDring.P4.ch7_pow_psq
#print axioms LeanDring.P4.card_omega2_ch7
#print axioms LeanDring.P4.card_omega2_a1111
#print axioms LeanDring.P4.lift24
#print axioms LeanDring.P4.card_p2_smul_torsion_zmod4
#print axioms LeanDring.P4.card_omega2_a4
#print axioms LeanDring.P4.m8_pow_psq
#print axioms LeanDring.P4.card_omega2_m8
#print axioms LeanDring.P4.gid3_pow_psq
#print axioms LeanDring.P4.card_omega2_gid3
#print axioms LeanDring.P4.gid8_pow_psq
#print axioms LeanDring.P4.card_omega2_gid8
#print axioms LeanDring.P4.card_p2_subgroups_socle
#print axioms LeanDring.P4.card_p2_le_socle_eq
#print axioms LeanDring.P4.not_isCyclic_iff_le_socle
#print axioms LeanDring.P4.card_p2_subgroups_abelian_exp_p
#print axioms LeanDring.P4.card_p2_subgroups_nonabelian_exp_p
#print axioms LeanDring.P4.card_order_p2_subgroups_gid3
#print axioms LeanDring.P4.card_order_p2_subgroups_gid8
#print axioms LeanDring.P4.card_order_p2_subgroups_g9
#print axioms LeanDring.P4.card_order_p2_subgroups_ch7
#print axioms LeanDring.P4.card_order_p2_subgroups_model
#print axioms LeanDring.P4.isEmpty_tableIso_g9_ch7
#print axioms LeanDring.P4.isEmpty_tableIso_ch7_gid3
#print axioms LeanDring.P4.isEmpty_tableIso_gid8_model
#print axioms LeanDring.P4.card_order_p3_subgroups_g9
#print axioms LeanDring.P4.card_order_p3_subgroups_gid3
#print axioms LeanDring.P4.isEmpty_tableIso_g9_gid3

-- The abelian 2-group target, cyclic slice (rank/SNF-coarsest invariant)
#print axioms LeanDring.burnsideRingCongr
#print axioms LeanDring.DRing.card_charPairClass_of_comm
#print axioms LeanDring.DRing.sum_card_subgroups_eq_of_dringEquiv
#print axioms LeanDring.AbelianTwo.sum_card_subgroups_cyclic_two
#print axioms LeanDring.AbelianTwo.mulEquivOfCyclicTwoGroup
#print axioms LeanDring.AbelianTwo.burnsideEquivOfCyclicTwoGroup
#print axioms LeanDring.P4.card_abelianization_of_comm
#print axioms LeanDring.P4.card_abelianization_lt_of_not_comm
#print axioms LeanDring.P4.isEmpty_tableIso_a31_m6
#print axioms LeanDring.P4.isEmpty_tableIso_a22_m8
#print axioms LeanDring.P4.isEmpty_tableIso_a211_g9
#print axioms LeanDring.P4.isEmpty_tableIso_a1111_g14
#print axioms LeanDring.P4.isEmpty_tableIso_a1111_maxClass
#print axioms LeanDring.P4.card_order_p3_subgroups_gid8
#print axioms LeanDring.P4.card_order_p3_subgroups_ch7
#print axioms LeanDring.P4.card_order_p3_subgroups_model
#print axioms LeanDring.P4.isEmpty_tableIso_g9_gid8
#print axioms LeanDring.P4.isEmpty_tableIso_ch7_model
#print axioms LeanDring.P4.isEmpty_tableIso_gid3_gid8

-- The complete 105/105 order-p⁴ pairwise separation
#print axioms LeanDring.P4.p4_pairwise_species_distinct

-- Naturality of species + transport of a species-table isomorphism along group isos
#print axioms LeanDring.DRing.species_natural
#print axioms LeanDring.DRing.SpeciesTableIso.ofMulEquiv
#print axioms LeanDring.DRing.SpeciesTableIso.trans
#print axioms LeanDring.DRing.SpeciesTableIso.congr

-- The conditional order-p⁴ capstone (species tables separate ALL groups of order p⁴)
#print axioms LeanDring.P4.p4_species_classifies

-- Subgroup inventory, step 1: p-group structure of a maximal subgroup of the order-5⁵ group,
-- proved unconditionally (normal, index 5, contains the Frattini subgroup), and the
-- reduction of `MaximalsClosed` to the sharper `NormalIndexFiveClosed`.
#print axioms LeanDring.P5Presentation.normal_of_maximal
#print axioms LeanDring.P5Presentation.relIndex_eq_five_of_maximal
#print axioms LeanDring.P5Presentation.frattini_le_of_maximal
#print axioms LeanDring.P5Presentation.maximalsClosed_of_normalIndexFiveClosed
#print axioms LeanDring.P5Presentation.allSubs_complete_of_normalIndexFiveClosed

-- Subgroup inventory, Frattini step (part 4): the per-subgroup Frattini-certification pipeline.
-- The kernel
-- checker `fratCertB` verified on the pilot slice (⊤ + the 31 order-5⁴ subgroups),
-- and the aggregation glue deriving `NormalIndexFiveClosed` from full certificate
-- coverage relative to the single isolated discharge obligation `FratDischarge`.
#print axioms LeanDring.P5Presentation.certified_checks
#print axioms LeanDring.P5Presentation.inInv_subAt
#print axioms LeanDring.P5Presentation.exists_index_of_inInv
#print axioms LeanDring.P5Presentation.inv_closed_on_certified
#print axioms LeanDring.P5Presentation.normalIndexFiveClosed_of_all_certified
#print axioms LeanDring.P5Presentation.allSubs_complete_of_all_certified

-- Subgroup inventory, Frattini step discharged: the isolated per-subgroup obligation
-- `FratDischarge` is now
-- proved unconditionally (abelian Frattini quotient of exponent 5 + hyperplane
-- exhaustion), and its now-unconditional (modulo certificate coverage) consequences.
#print axioms LeanDring.P5Presentation.fratDischarge
#print axioms LeanDring.P5Presentation.inv_closed_on_certified_uncond
#print axioms LeanDring.P5Presentation.normalIndexFiveClosed_of_coverage
#print axioms LeanDring.P5Presentation.allSubs_complete_of_coverage

-- Subgroup inventory, complete: full certificate coverage for all 676 subgroups
-- is discharged by the kernel `decide` `coverage_full`, making the completeness of the 676-subgroup
-- inventory UNCONDITIONAL. These are the headline inventory theorems.
#print axioms LeanDring.P5Presentation.certified_keys
#print axioms LeanDring.P5Presentation.coverage_full
#print axioms LeanDring.P5Presentation.normalIndexFiveClosed
#print axioms LeanDring.P5Presentation.maximalsClosed
#print axioms LeanDring.P5Presentation.allSubs_complete

-- Subgroup inventory, twin q=2 (SmallGroup(3125,69)): the full subgroup-inventory layer for
-- `Coordinate 2`, twin of the q=1 inventory stack. Inventory (676, strata [1,156,306,181,31,1]),
-- well-formedness, pairwise distinctness, per-subgroup Frattini certificates
-- (`fratCertB` at q=2 + full 676-record coverage), the discharged Frattini-step obligation
-- `fratDischarge`, and the UNCONDITIONAL headline completeness `allSubs2_complete`.
-- Twin-statistics note: raw echelon-base count is 826 (q=2) vs 830 (q=1); the
-- semantic subgroup count (676) and strata are identical between the twins.
#print axioms LeanDring.P5Presentation.Q2.allBases_card
#print axioms LeanDring.P5Presentation.Q2.allBases_strata
#print axioms LeanDring.P5Presentation.Q2.allSubs_length
#print axioms LeanDring.P5Presentation.Q2.allSubs_strata
#print axioms LeanDring.P5Presentation.Q2.allSubs_pairwise_distinct
#print axioms LeanDring.P5Presentation.Q2.bot_mem_allSubs
#print axioms LeanDring.P5Presentation.Q2.top_mem_allSubs
#print axioms LeanDring.P5Presentation.Q2.certified_checks
#print axioms LeanDring.P5Presentation.Q2.coverage_full
#print axioms LeanDring.P5Presentation.Q2.fratDischarge
#print axioms LeanDring.P5Presentation.Q2.normalIndexFiveClosed
#print axioms LeanDring.P5Presentation.Q2.maximalsClosed
#print axioms LeanDring.P5Presentation.allSubs2_complete

-- Subgroup conjugacy classes: the 148 subgroup conjugacy classes of `Coordinate 1`
-- (order 3125), certified as a kernel-checked conjugation index action.
-- 148 classes, 71 normal (GAP-matched).
#print axioms LeanDring.P5Presentation.reps_complete
#print axioms LeanDring.P5Presentation.reps_pairwise_nonconj
#print axioms LeanDring.P5Presentation.orbit_inv
#print axioms LeanDring.P5Presentation.classSize_sum
#print axioms LeanDring.P5Presentation.reps_normal_iff
#print axioms LeanDring.P5Presentation.normal_count

-- Subgroup conjugacy classes, twin q=2: the 148 subgroup conjugacy classes of `Coordinate 2`
-- (SmallGroup(3125,69)), certified as a kernel-checked conjugation index action.
-- 148 classes, 71 normal — identical twin statistics to q=1 (SmallGroup(3125,68)).
#print axioms LeanDring.P5Presentation.Q2.reps_complete
#print axioms LeanDring.P5Presentation.Q2.reps_pairwise_nonconj
#print axioms LeanDring.P5Presentation.Q2.orbit_inv
#print axioms LeanDring.P5Presentation.Q2.classSize_sum
#print axioms LeanDring.P5Presentation.Q2.reps_normal_iff
#print axioms LeanDring.P5Presentation.Q2.normal_count

-- Linear-character data: linear-character data for the 148 subgroup-class representatives. The
-- ZMod-25 exponent-vector model + collection-relation checker `charOK`; the
-- kernel-checked pilot (reps 0/1/28: valid + distinct + count |H^ab|); and the
-- certified aggregate counts (Σ_r |H^ab| = 5236, fibre {1:148, 5:3688, 25:1400}).
-- The extension obligation `CharExtendsAt` (valid vector ⇒ homomorphism) is the
-- single isolated hypothesis; not invoked by the certified facts below.
#print axioms LeanDring.P5Presentation.B28_eq_getB
#print axioms LeanDring.P5Presentation.chars1_valid
#print axioms LeanDring.P5Presentation.chars28_valid
#print axioms LeanDring.P5Presentation.chars28_nodup
#print axioms LeanDring.P5Presentation.chars28_count
#print axioms LeanDring.P5Presentation.charCount_total
#print axioms LeanDring.P5Presentation.charFibre_consistent
#print axioms LeanDring.P5Presentation.charFibre_totals

-- Linear-character data, twin q=2 (SmallGroup(3125,69)): linear-character data for the 148 reps
-- under the q=2 collection relations (`f₂⁵ = f₅²`, vs the twin's `f₅`), via the
-- q=2 checker `charOK2` (`mpow 2`/`clearStep 2`/q=2 `commutatorC`). Kernel-checked
-- pilot (reps 0/1/28: valid + distinct + count |H^ab|) and reused aggregate counts.
-- Twin divergence (generator-measured over all 148 reps): echelon bases differ in
-- 50 reps, power rows in 106, commutator rows in 0, character-vector sets in 34
-- (`{28…52}∪{64,67,73,76,90,95,100,105,110}`); counts invariant (Σ = 5236). The
-- pilot certifies this concretely: `B28_ne_q1` (rep-28 basis differs) and
-- `chars28_ne_q1` (rep-28 q=2 character list differs from q=1). `CharExtendsAt2`
-- is the isolated hypothesis, not invoked below.
#print axioms LeanDring.P5Presentation.Q2.B28_eq_getB
#print axioms LeanDring.P5Presentation.Q2.B28_ne_q1
#print axioms LeanDring.P5Presentation.Q2.chars1_valid
#print axioms LeanDring.P5Presentation.Q2.chars28_valid
#print axioms LeanDring.P5Presentation.Q2.chars28_nodup
#print axioms LeanDring.P5Presentation.Q2.chars28_count
#print axioms LeanDring.P5Presentation.Q2.chars28_ne_q1
#print axioms LeanDring.P5Presentation.Q2.charCount_total
#print axioms LeanDring.P5Presentation.Q2.charFibre_totals
-- `Coordinate 2` has exponent dividing 25 (every character value is a 25th root
-- of unity) — the q=2 twin of `mpow25_all`, holding despite the `f₂⁵ = f₅²` change.
#print axioms LeanDring.P5Presentation.Q2.mpow25_all

-- Character certification, twin q=2: the full per-representative character
-- certification for ALL 148 reps under the q=2 collection relations, twin of the
-- q=1 character-data part B plus the step-1/2/3 stack. `charsAt2 r` is kernel-certified `charOK2`-
-- valid, duplicate-free, of the aggregate length, over the genuine echelon basis of
-- `reps r` (via the q=2 row bridge `charOKrows_iff2`); `charsTotal2_certified`
-- rederives the headline total 5236 from the certified per-rep counts. Twin note:
-- counts are invariant (Σ = 5236, identical to q=1) though 34 character-vector sets
-- are reshaped (5ᵗʰ-power map `f₂⁵ = f₅²`).
#print axioms LeanDring.P5Presentation.Q2.charOKrows_iff2
#print axioms LeanDring.P5Presentation.Q2.charsAt2_valid
#print axioms LeanDring.P5Presentation.Q2.charsAt2_nodup
#print axioms LeanDring.P5Presentation.Q2.charsAt2_count
#print axioms LeanDring.P5Presentation.Q2.basisAt2_eq
#print axioms LeanDring.P5Presentation.Q2.reps_eq_ofList2
#print axioms LeanDring.P5Presentation.Q2.charsTotal2_certified

-- Character data, step 1, twin q=2: the extension obligation `CharExtendsAt` discharged for
-- `Coordinate 2` — a `charOK2`-valid vector yields an additive character functional
-- on `⟨B⟩` for every well-formed echelon basis, hence for each of the 148 reps.
#print axioms LeanDring.P5Presentation.Q2.charExtendsAt2_of_wf
#print axioms LeanDring.P5Presentation.Q2.charExtendsAt2_basisAt

-- Character data, step 2, twin q=2: the character-realization layer. Every certified
-- `charOK2`-valid vector of `reps r` becomes a genuine hom into ℂˣ; the map is
-- injective on the certified list (`charOfVec2_inj`), giving the semantic lower
-- bound `charCounts r ≤ |Hom(reps r, ℂˣ)|` (`charCounts2_le_card_hom`).
#print axioms LeanDring.P5Presentation.Q2.charOfVec2_gen
#print axioms LeanDring.P5Presentation.Q2.charOfVec2_inj
#print axioms LeanDring.P5Presentation.Q2.charCounts2_le_card_hom

-- Character data, step 3, twin q=2: character-count completeness. `pow25_eq_one` (ambient
-- exponent 25), `master_eval`, `charOK2_evalVec`, `evalVec_injective` and
-- `card_hom_le_length` yield `charsAtComplete_of_exhaustive`; `charsAtComplete_of_check2`
-- turns the decided `exhaustiveCheck2` into completeness. The eight k=3 chunk decides
-- (`exhaustiveCheck2_r55_62 … _r111_115`) assemble to `exhaustiveCheck2_le115`, and
-- the k≥4 classes use the row-combination box certificate (`charsAtComplete_of_cert2`,
-- `charsAtComplete2_116 … _147`). `charsAtComplete_all2` glues all 148, upgrading the
-- character count `charsAt_complete_all2` and abelianization order
-- `card_abelianization_reps_all2` to hypothesis-free equalities.
#print axioms LeanDring.P5Presentation.Q2.pow25_eq_one
#print axioms LeanDring.P5Presentation.Q2.master_eval
#print axioms LeanDring.P5Presentation.Q2.charOK2_evalVec
#print axioms LeanDring.P5Presentation.Q2.evalVec_injective
#print axioms LeanDring.P5Presentation.Q2.card_hom_le_length
#print axioms LeanDring.P5Presentation.Q2.charsAtComplete_of_exhaustive
#print axioms LeanDring.P5Presentation.Q2.charsAtComplete_of_check2
#print axioms LeanDring.P5Presentation.Q2.exhaustiveCheck2_r55_62
#print axioms LeanDring.P5Presentation.Q2.exhaustiveCheck2_r63_70
#print axioms LeanDring.P5Presentation.Q2.exhaustiveCheck2_r71_78
#print axioms LeanDring.P5Presentation.Q2.exhaustiveCheck2_r79_86
#print axioms LeanDring.P5Presentation.Q2.exhaustiveCheck2_r87_94
#print axioms LeanDring.P5Presentation.Q2.exhaustiveCheck2_r95_102
#print axioms LeanDring.P5Presentation.Q2.exhaustiveCheck2_r103_110
#print axioms LeanDring.P5Presentation.Q2.exhaustiveCheck2_r111_115
#print axioms LeanDring.P5Presentation.Q2.exhaustiveCheck2_le115
#print axioms LeanDring.P5Presentation.Q2.charsAtComplete2_le115
#print axioms LeanDring.P5Presentation.Q2.charsAt_complete2_le115
#print axioms LeanDring.P5Presentation.Q2.card_abelianization_reps2_le115
#print axioms LeanDring.P5Presentation.Q2.charsAtComplete_of_cert2
#print axioms LeanDring.P5Presentation.Q2.charsAtComplete2_116
#print axioms LeanDring.P5Presentation.Q2.charsAtComplete2_147
#print axioms LeanDring.P5Presentation.Q2.charsAtComplete_all2
#print axioms LeanDring.P5Presentation.Q2.charsAt_complete_all2
#print axioms LeanDring.P5Presentation.Q2.card_abelianization_reps_all2

-- Character certification, part B: the full per-representative character certification for ALL 148
-- class reps (not just the 0/1/28 pilot). For every `r : Fin 148` the embedded
-- vector list `charsAt r` is kernel-certified `charOK`-valid, duplicate-free,
-- of the aggregate `charCounts r` length, over the genuine echelon basis of
-- `reps r`. The per-vector check is reduced to pure `ZMod 25` linear algebra via
-- the bridge `charOKrows_iff`, the sift being run once per rep (`checkRows_all`).
-- `charsTotal_certified` rederives the headline total 5236 from these certified
-- per-rep counts. `CharExtendsAt` (valid vector ⇒ homomorphism) remains the sole
-- isolated obligation and is NOT invoked by any theorem below.
#print axioms LeanDring.P5Presentation.charOKrows_iff
#print axioms LeanDring.P5Presentation.charsAt_valid
#print axioms LeanDring.P5Presentation.charsAt_nodup
#print axioms LeanDring.P5Presentation.charsAt_count
#print axioms LeanDring.P5Presentation.basisAt_eq
#print axioms LeanDring.P5Presentation.reps_eq_ofList
#print axioms LeanDring.P5Presentation.charsTotal_certified

-- Character data, step 1: the isolated extension obligation `CharExtendsAt` discharged. A
-- `charOK`-valid exponent vector `e` yields an additive character functional
-- `charForm B e` on `⟨B⟩` for every well-formed echelon basis `B`
-- (`charExtendsAt_of_wf`), hence for each of the 148 class representatives
-- (`charExtendsAt_basisAt`). This is the "abelianized relators ⇒ well-defined
-- character" step of the pc collection presentation.
#print axioms LeanDring.P5Presentation.charExtendsAt_of_wf
#print axioms LeanDring.P5Presentation.charExtendsAt_basisAt

-- Character data, step 2: the character-realization layer. A fixed primitive 25th root of
-- unity `ζ₂₅` and its exponent map `zexp : ZMod 25 → ℂˣ` turn every certified
-- `charOK`-valid vector `e` of `reps r` into a genuine hom
-- `charOfVec r e : ↥(reps r) →* ℂˣ`. Evaluation at the echelon generators
-- (`charForm_getElem`, `charOfVec_gen`) makes `e ↦ charOfVec r e` injective on the
-- certified list (`charOfVec_inj`), whence the SEMANTIC lower bound
-- `charCounts r ≤ |Hom(reps r, ℂˣ)| = |(reps r)ᵃᵇ|` (`charCounts_le_card_hom`).
-- The converse (list exhaustiveness) is isolated as `CharsAtComplete`; from it
-- `charsAt_complete` and `card_abelianization_reps` upgrade the character-data aggregate.
#print axioms LeanDring.P5Presentation.zeta25_prim
#print axioms LeanDring.P5Presentation.zeta25_pow_card
#print axioms LeanDring.P5Presentation.zexp_add
#print axioms LeanDring.P5Presentation.zexp_inj
#print axioms LeanDring.P5Presentation.charsAt_vecLen
#print axioms LeanDring.P5Presentation.charOfVec_gen
#print axioms LeanDring.P5Presentation.charOfVec_inj
#print axioms LeanDring.P5Presentation.charCounts_le_card_hom
#print axioms LeanDring.P5Presentation.charsAt_complete
#print axioms LeanDring.P5Presentation.card_abelianization_reps

-- Normalizer-orbit partition of the certified character lists. For every
-- `r : Fin 148` the generator emits the `N_G(H)`-conjugation matrices, the
-- induced permutation of `charsAt r`, and a BFS orbit partition with spanning-tree
-- witnesses; the kernel certifies (sift-free) that the labels are action-invariant
-- (`checkAct_all`) and that every character reaches its orbit representative
-- (`checkTree_all`). Aggregates: the pair-class transversal `Σ orbits = 2724`
-- (= rank D(G) for q=1), the orbit-count distribution {1:1,5:12,9:61,13:5,25:56,
-- 29:1,45:11,125:1}, and the fibre split by character order {1:148, 5:2376,
-- 25:200}. Note it is the order-25 characters that fuse (1400→200), not
-- order-5; see the NormOrbits header
-- (P5/Certificate/ConjugacyClasses/Twin1/NormOrbits.lean).
-- `reach_from_rep`/`label_stable` are the combinatorial Prop-level API for the pair-class bridge.
#print axioms LeanDring.P5Presentation.checkAct_all
#print axioms LeanDring.P5Presentation.checkTree_all
#print axioms LeanDring.P5Presentation.checkLen_all
#print axioms LeanDring.P5Presentation.pairClassTotal
#print axioms LeanDring.P5Presentation.orbitCount_distribution
#print axioms LeanDring.P5Presentation.orbitFibre_by_order
#print axioms LeanDring.P5Presentation.orbitFibre_total
#print axioms LeanDring.P5Presentation.reach_from_rep
#print axioms LeanDring.P5Presentation.label_stable
#print axioms LeanDring.P5Presentation.reach_of_sameLabel

-- Normalizer-orbit partition, part 1 (the normalizer-orbit semantic grounding). The per-class
-- squeeze
-- `card_conjClass_reps` (the abstract G-conjugacy class of `reps r` has exactly
-- `classSizeNat r` members) yields the normalizer-card pin
-- `classSizeNat r · |N_G(reps r)| = 3125`; combined with the whole-range sift
-- certificate this closes `normAt_eq_final`: the emitted index `normIdxData r`
-- presents exactly `N_G(reps r)`, for all 148 representatives.
#print axioms LeanDring.P5Presentation.card_conjClass_reps
#print axioms LeanDring.P5Presentation.normalizer_card_pin
#print axioms LeanDring.P5Presentation.normAt_eq_final

-- Normalizer-orbit partition, part 2 (the emitted matrices realise genuine normalizer conjugation),
-- closing the data-provenance gap noted in the NormCard header
-- (P5/Certificate/ConjugacyClasses/Twin1/NormCard.lean). `normMats r` was
-- emitted from the coordinate generators `normGens r` of `normBasis B` (an
-- echelon base of `N_G(reps r)`), NOT the canonical inventory base
-- `getB (normIdxData r)`. Certifying the matrices against their own generators:
-- (a) each `n ∈ normGens r` lies in the link-1 normalizer, (b)+(c) `normGens r`
-- is a well-formed echelon base of the right order, so `normGens_generate`:
-- `⟨normGens r⟩ = N_G(reps r)`; (d) `normMats_realize`: the (j,i) matrix entry is
-- `expVec_B (nⱼ⁻¹ gᵢ nⱼ)` (orientation n⁻¹gn). `orbit_semantically_closed` then
-- grounds every `MatReach` orbit step in a genuine normalizer element (the
-- ordered `normGens r`-product), at the character-vector level.
#print axioms LeanDring.P5Presentation.normGens_generate
#print axioms LeanDring.P5Presentation.normMats_realize
#print axioms LeanDring.P5Presentation.orbit_semantically_closed

-- Normalizer-orbit partition, twin q=2 (SmallGroup(3125,69)): the normalizer-orbit partition of the
-- certified q=2 character lists `charsAt2 r`, twin of the q=1 partition stack. Data
-- regenerated from the q=2 group law by `LeanDring/P5/Certificate/Generators/Twin2/NormGen.lean`.
-- Kernel certifies (sift-free)
-- `checkAct_all` (matrices induce the emitted permutation, labels action-invariant)
-- and `checkTree_all` (every character reaches its orbit rep along the BFS tree).
-- Twin comparison: despite the q=2 5ᵗʰ-power map reshaping 34 of the k≤3 character
-- sets (so `normMats`/`normActPos`/`normLabel` diverge), the aggregate orbit
-- invariants are IDENTICAL to q=1: `pairClassTotal = 2724`, the orbit-count
-- distribution {1:1,5:12,9:61,13:5,25:56,29:1,45:11,125:1}, and the order-fibre
-- split `orbitFibre_by_order = {1:148, 5:2376, 25:200}`. `normIdxData` itself is
-- byte-identical to q=1 (normalizers are the same subgroup indices).
#print axioms LeanDring.P5Presentation.Q2.checkAct_all
#print axioms LeanDring.P5Presentation.Q2.checkTree_all
#print axioms LeanDring.P5Presentation.Q2.checkLen_all
#print axioms LeanDring.P5Presentation.Q2.pairClassTotal
#print axioms LeanDring.P5Presentation.Q2.orbitCount_distribution
#print axioms LeanDring.P5Presentation.Q2.orbitFibre_by_order
#print axioms LeanDring.P5Presentation.Q2.orbitFibre_total
#print axioms LeanDring.P5Presentation.Q2.reach_from_rep
#print axioms LeanDring.P5Presentation.Q2.label_stable
#print axioms LeanDring.P5Presentation.Q2.reach_of_sameLabel

-- Normalizer-orbit partition, part 1, twin q=2: the per-class squeeze
-- `card_conjClass_reps` yields the
-- normalizer-card pin `classSizeNat r · |N_G(reps r)| = 3125`; combined with the
-- whole-range sift certificate `normSiftCheck_all`, this closes `normAt_eq_final`:
-- the emitted (q=1-identical) `normIdxData r` presents exactly `N_G(reps r)` under
-- the q=2 group law, for all 148 representatives.
#print axioms LeanDring.P5Presentation.Q2.card_conjClass_reps
#print axioms LeanDring.P5Presentation.Q2.normalizer_card_pin
#print axioms LeanDring.P5Presentation.Q2.normAt_eq_final

-- Normalizer-orbit partition, part 2, twin q=2: the emitted matrices realise genuine normalizer
-- conjugation. `normGens_generate`: the regenerated `normGens r` generate
-- `N_G(reps r)`; `normMats_realize`: the (j,i) entry is `expVec2_B (nⱼ⁻¹ gᵢ nⱼ)`
-- (orientation n⁻¹gn, enforced by the whole-range `normRealizeCheck_all` decide);
-- `orbit_semantically_closed`: every `MatReach` orbit step is a genuine
-- `normGens r`-product element of `N_G(reps r)`, at the character-vector level.
#print axioms LeanDring.P5Presentation.Q2.normGens_generate
#print axioms LeanDring.P5Presentation.Q2.normMats_realize
#print axioms LeanDring.P5Presentation.Q2.orbit_semantically_closed

-- Step 3 (character-count completeness). The reconstruction of an arbitrary
-- character from its generator values: `pow25_eq_one` (the ambient exponent is
-- 25, so every character value is a 25th root of unity), `master_eval` (a
-- character is `zexp ∘ charForm` of its discrete-log vector on all of `⟨B⟩`),
-- `charOK_evalVec` (that vector is `charOK`-valid) and `evalVec_injective` yield
-- `charsAtComplete_of_exhaustive`: the completeness obligation reduces to the
-- certified list being exhaustive. `charsAtComplete_of_check` turns the decided
-- `exhaustiveCheck` into completeness; `charsAtComplete_le54` discharges it for
-- the `k ≤ 2` classes (representatives `0…54`) unconditionally, upgrading the
-- character count `charsAt_complete_le54` and abelianization order
-- `card_abelianization_reps_le54` to hypothesis-free equalities.
#print axioms LeanDring.P5Presentation.pow25_eq_one
#print axioms LeanDring.P5Presentation.master_eval
#print axioms LeanDring.P5Presentation.charOK_evalVec
#print axioms LeanDring.P5Presentation.charsAtComplete_of_exhaustive
#print axioms LeanDring.P5Presentation.charsAtComplete_of_check
#print axioms LeanDring.P5Presentation.charsAt_complete_le54
#print axioms LeanDring.P5Presentation.card_abelianization_reps_le54

-- Step 3, `k = 3` chunks (representatives `55…115`). Eight kernel `decide`s of
-- `exhaustiveCheck` (25³-bounded, chunked ~8 reps/file to stay under the elaborator
-- budget), assembled into a single range fact and upgraded to the same
-- unconditional character-count / abelianization-order statements as the `_le54`
-- family, now covering every `k ≤ 3` representative (`0…115`).
#print axioms LeanDring.P5Presentation.exhaustiveCheck_r55_62
#print axioms LeanDring.P5Presentation.exhaustiveCheck_r63_70
#print axioms LeanDring.P5Presentation.exhaustiveCheck_r71_78
#print axioms LeanDring.P5Presentation.exhaustiveCheck_r79_86
#print axioms LeanDring.P5Presentation.exhaustiveCheck_r87_94
#print axioms LeanDring.P5Presentation.exhaustiveCheck_r95_102
#print axioms LeanDring.P5Presentation.exhaustiveCheck_r103_110
#print axioms LeanDring.P5Presentation.exhaustiveCheck_r111_115
#print axioms LeanDring.P5Presentation.exhaustiveCheck_le115
#print axioms LeanDring.P5Presentation.charsAtComplete_le115
#print axioms LeanDring.P5Presentation.charsAt_complete_le115
#print axioms LeanDring.P5Presentation.card_abelianization_reps_le115

-- Step 3, `k ≥ 4` classes (representatives `116…147`, the last 32, including the
-- whole group `⊤` at `147`). The `25⁴`/`25⁵` brute enumeration is infeasible in
-- the kernel, so completeness is proved by a *row-combination certificate*: the
-- `charOK`-valid vectors are the solutions of a homogeneous `ZMod 25` linear
-- system, and per-coordinate integer coefficients (kernel-`decide`d via
-- `charsAtComplete_of_cert`) exhibit `m · eⱼ = 0`, confining every solution to a
-- product "box" of size `charCounts r`; `card_hom_le_length` then bounds the
-- character count. `charsAtComplete_all` glues these to the `k ≤ 3` certificates
-- for the full unconditional result over all 148 representatives, upgrading the
-- character count `charsAt_complete_all` and abelianization order
-- `card_abelianization_reps_all` to hypothesis-free equalities.
#print axioms LeanDring.P5Presentation.charsAtComplete_of_cert
#print axioms LeanDring.P5Presentation.charsAtComplete_116
#print axioms LeanDring.P5Presentation.charsAtComplete_147
#print axioms LeanDring.P5Presentation.charsAtComplete_all
#print axioms LeanDring.P5Presentation.charsAt_complete_all
#print axioms LeanDring.P5Presentation.card_abelianization_reps_all

-- The `CharPairClass` bridge for `Coordinate 1`. Surjectivity: Step-2
-- completeness recast as `exists_charOfVec_eq` (every character of `reps r` is a
-- listed one), subgroup-conjugation transport `isConjPair_reps_transport`, and
-- `pairClass_realized_by_listed` (every pair class is a listed character on some
-- representative). The character↔vector dictionary `charForm_genAct` (a
-- normalizer-generator matrix step = conjugation by that generator) fuses classes
-- one step at a time (`class_genAct_eq`); iterating along the certified BFS tree
-- (`class_reduces_to_rep`) yields `pairClass_realized_by_orbitRep`: every class is
-- the class at an orbit-representative position. `rank_dring_coordinate1_of_card`
-- is the conditional rank corollary.
#print axioms LeanDring.P5Presentation.exists_charOfVec_eq
#print axioms LeanDring.P5Presentation.isConjPair_reps_transport
#print axioms LeanDring.P5Presentation.pairClass_realized_by_listed
#print axioms LeanDring.P5Presentation.charForm_genAct
#print axioms LeanDring.P5Presentation.class_genAct_eq
#print axioms LeanDring.P5Presentation.class_reduces_to_rep
#print axioms LeanDring.P5Presentation.pairClass_realized_by_orbitRep
#print axioms LeanDring.P5Presentation.rank_dring_coordinate1_of_card

-- Pair-class census, final step (injectivity + count). `conjSub_of_isConjPair` turns a pair
-- conjugation into a subgroup conjugation, colliding with `reps_pairwise_nonconj`
-- across representatives. The dictionary-as-closure-induction
-- `conjLabelProp_of_mem_N` (generators via `charForm_genAct`, inverses via the
-- finite-order identity `a⁻¹ = a ^ (orderOf a - 1)`) drives the same-representative
-- case `orbitRep_class_inj_same`: two orbit reps in one class share a `normLabel`,
-- hence one position. `orbRepClass` is thus a bijection from the orbit-rep index
-- (`card_orbRepSigma = 2724`, from `pairClassTotal` + `card_fibre_eq`) onto the
-- pair classes, giving the unconditional `card_charPairClass_coordinate1 = 2724`
-- and `rank_dring_coordinate1 = 2724`.
#print axioms LeanDring.P5Presentation.conjSub_of_isConjPair
#print axioms LeanDring.P5Presentation.conjLabelProp_of_mem_N
#print axioms LeanDring.P5Presentation.orbitRep_class_inj_same
#print axioms LeanDring.P5Presentation.orbRepClass_bijective
#print axioms LeanDring.P5Presentation.card_fibre_eq
#print axioms LeanDring.P5Presentation.card_orbRepSigma
#print axioms LeanDring.P5Presentation.card_charPairClass_coordinate1
#print axioms LeanDring.P5Presentation.rank_dring_coordinate1

-- Pair-class bridge and census, q = 2 (row-side assembly for `Coordinate 2`). The exact
-- structural twin of the q = 1 stack above, run over the certified q = 2 stack
-- (`reps`/`reps_complete`/`reps_pairwise_nonconj`, `charOfVec2`/`charsAt_complete_all2`,
-- the q = 2 normalizer-orbit layer). Surjectivity `pairClass_realized_by_orbitRep`,
-- dictionary `charForm_genAct`/`class_genAct_eq`, injectivity `conjLabelProp_of_mem_N`/
-- `orbitRep_class_inj_same`, bijection `orbRepClass_bijective`, count
-- `card_orbRepSigma = 2724` (`pairClassTotal` q=2), giving the unconditional
-- `card_charPairClass_coordinate2 = 2724` and `rank_dring_coordinate2 = 2724`.
#print axioms LeanDring.P5Presentation.Q2.charForm2_genAct
#print axioms LeanDring.P5Presentation.Q2.class_genAct_eq
#print axioms LeanDring.P5Presentation.Q2.pairClass_realized_by_orbitRep
#print axioms LeanDring.P5Presentation.Q2.rank_dring_coordinate2_of_card
#print axioms LeanDring.P5Presentation.Q2.conjSub_of_isConjPair
#print axioms LeanDring.P5Presentation.Q2.conjLabelProp_of_mem_N
#print axioms LeanDring.P5Presentation.Q2.orbitRep_class_inj_same
#print axioms LeanDring.P5Presentation.Q2.orbRepClass_bijective
#print axioms LeanDring.P5Presentation.Q2.card_orbRepSigma
#print axioms LeanDring.P5Presentation.Q2.card_charPairClass_coordinate2
#print axioms LeanDring.P5Presentation.Q2.rank_dring_coordinate2

-- Species-side (column-side) coset enumeration, q = 1: the H'-coset layer, the
-- structural analogue of the character-data and orbit layers on cosets of `H' = [H,H]` instead of
-- characters.
-- `speciesCheck_all`: the eight per-rep boolean certificates (H' well-formed,
-- H' ≤ H, generator-commutators ∈ H', H' normal in H, |H^ab|·|H'| = |H|,
-- transversal ⊆ H, transversal distinct mod H', |transversal| = charCounts).
-- `hpSub_eq_derived`: the cardinality squeeze — the emitted H' equals the ambient
-- derived subgroup of `reps r` (uses `card_abelianization_reps_all`, no witnesses).
-- `transCard`: the certified transversal has |H/H'| = charCounts r elements.
-- Fibre split (computed on this certified data by the SpeciesEmit #evals,
-- P5/Certificate/SpeciesTable/Twin1/SpeciesEmit.lean):
-- species-side orbit fibre by order of hH' in H/H' = {148, 2376, 200}, raw =
-- {148, 3688, 1400} — both identical to the character side; the alternative
-- reading {148, 1176, 1400} (order-5 rather than order-25 fusion) is refuted
-- on the species side as well.
#print axioms LeanDring.P5Presentation.speciesCheck_all
#print axioms LeanDring.P5Presentation.hpSub_eq_derived
#print axioms LeanDring.P5Presentation.transCard

-- Species-side orbit layer: the N_G(H)-orbit partition of the certified
-- H'-coset transversals — the column analogue of the character-orbit layer.
-- `cosetOrbCheck_all`: per (r,k,p) the emitted index table is a genuine coset
-- action ((T[tab])⁻¹·nₖ⁻¹·T[p]·nₖ ∈ H', one siftB each), labels are
-- generator-invariant, and every coset reaches its orbit rep along a valid BFS
-- tree. `speciesOrbitTotal`: Σ orbits = 2724 (= rank D(G), q=1), matching the
-- character side `pairClassTotal`. `speciesOrbitFibre`: orbit fibre by order of
-- hH' in H/H' = {1:148, 5:2376, 25:200}, identical to `orbitFibre_by_order`.
-- `cosetReach_from_rep`/`cosetLabel_stable` are the combinatorial Prop API;
-- `speciesOrbit_semantically_closed` grounds it — orbit-connected cosets are
-- transported by a genuine element of N_G(reps r) (∏ normGens over the word;
-- `normGens_generate`), the exact analogue of `orbit_semantically_closed`.
#print axioms LeanDring.P5Presentation.cosetOrbCheck_all
#print axioms LeanDring.P5Presentation.speciesOrbitTotal
#print axioms LeanDring.P5Presentation.speciesOrbitCount_distribution
#print axioms LeanDring.P5Presentation.speciesOrbitFibre
#print axioms LeanDring.P5Presentation.speciesOrbitFibre_total
#print axioms LeanDring.P5Presentation.cosetReach_from_rep
#print axioms LeanDring.P5Presentation.cosetLabel_stable
#print axioms LeanDring.P5Presentation.speciesOrbit_semantically_closed

-- SpeciesColumn bridge (the column-side analogue of the pair-class bridge): reduce Müller's
-- species table to conjugacy classes of pairs (H, hH').
-- `species_eq_of_abelianization_eq`: THE hH'-invariance — φ_{H,h} = φ_{H,h'} whenever
-- Abelianization.of h = Abelianization.of h' (same coset hH'). Easy: the fixed-point
-- weight μ(·,x) : H →* ℂˣ is a hom into an abelian group, so kills [H,H]
-- (Abelianization.commutator_subset_ker). Two-sided generalisation of
-- OddOrder.species_eq_one_of_trivialFibre.
-- `species_of_conjSub`: the conjugation move φ_{H,h} = φ_{K,k} for K^g = H, h = gkg⁻¹.
-- `hasSpeciesMatch_of_reduced`: the abstract class-reduced bridge — a checked match
-- between two SpeciesColsComplete representative families upgrades to the full
-- DecideIso.HasSpeciesMatch (hence Nonempty (DRing ≃+* DRing)). Only the TARGET
-- family need be complete; NO column injectivity is used (the column side of
-- HasSpeciesMatch is purely existential).
-- `species_col_conj_to_reps`: concrete completeness step 1 for q=1 — every column conjugates
-- onto a column on one of the 148 reps r (reps_complete + species_of_conjSub).
#print axioms LeanDring.DRing.species_eq_of_abelianization_eq
#print axioms LeanDring.DRing.species_of_conjSub
#print axioms LeanDring.DRing.hasSpeciesMatch_of_reduced
#print axioms LeanDring.DRing.nonempty_dringEquiv_of_reduced
#print axioms LeanDring.DRing.species_col_conj_to_reps
-- Completeness capstone (q=1): the 2724 orbit-representative columns are a COMPLETE species
-- family for `Coordinate 1`. Step 2 (`exists_trans_pos`): reduce `h ∈ reps r` mod
-- `H'=[H,H]` to a certified transversal position — `reduceAux` is a canonical
-- left-coset transversal (`reduceAux_mul_mem`), so `p ↦ Abelianization.of ⟨T[p]⟩`
-- is an injection `Fin|T| ↪ H^ab` between sets of equal card `charCounts r`, hence
-- onto. Step 3 (`species_reduces_to_rep`): normalise a transversal position to its
-- N_G(reps r)-orbit rep along the certified BFS tree, each step a genuine
-- normalizer conjugation (`species_cosetStep` = `species_of_conjSub` + the residual
-- `H'`-shift `cosetActOK`). Capstone `speciesColsComplete_coordinate1`.
#print axioms LeanDring.DRing.species_eq_of_hpSub
#print axioms LeanDring.DRing.species_cosetStep
#print axioms LeanDring.DRing.exists_trans_pos
#print axioms LeanDring.DRing.species_reduces_to_rep
#print axioms LeanDring.DRing.speciesColsComplete_coordinate1
-- Completeness glue (column half): completeness composes into an abstract D-ring iso once the
-- still-open row-matching data (σ, hmatch) is supplied.
#print axioms LeanDring.DRing.dringEquiv_of_rowMatch_coordinate1

-- ============================================================================
-- Twin q=2 (SmallGroup(3125,69) = Coordinate 2): species-side (column-side) analogue
-- of the coset-orbit and completeness stack above. Same structural certificates over the q=2 group
-- law
-- (5th-power map differs from q=1; commutator rows are byte-identical, so the H'
-- derived subgroups `hpData` are byte-identical to q=1 while the coset
-- transversals `transData` are the law-dependent normal forms — same cardinalities,
-- 81/148 rows with different elements). Totals reproduce the q=1 twin exactly:
-- 2724 orbits, fibre {1:148, 5:2376, 25:200}, raw {148,3688,1400}, per-rep orbit
-- distribution {1:1, 5:12, 9:61, 13:5, 25:56, 29:1, 45:11, 125:1}.
-- Species-side q=2 cosets: eight per-rep certificates + the derived-subgroup cardinality
-- squeeze (uses `card_abelianization_reps_all2`).
#print axioms LeanDring.P5Presentation.Q2.speciesCheck_all
#print axioms LeanDring.P5Presentation.Q2.hpSub_eq_derived
#print axioms LeanDring.P5Presentation.Q2.transCard
-- Species-side q=2 orbit layer: N_G(H)-orbit partition of the H'-coset transversals.
#print axioms LeanDring.P5Presentation.Q2.cosetOrbCheck_all
#print axioms LeanDring.P5Presentation.Q2.speciesOrbitTotal
#print axioms LeanDring.P5Presentation.Q2.speciesOrbitCount_distribution
#print axioms LeanDring.P5Presentation.Q2.speciesOrbitFibre
#print axioms LeanDring.P5Presentation.Q2.speciesOrbitFibre_total
#print axioms LeanDring.P5Presentation.Q2.cosetReach_from_rep
#print axioms LeanDring.P5Presentation.Q2.cosetLabel_stable
#print axioms LeanDring.P5Presentation.Q2.speciesOrbit_semantically_closed
-- SpeciesColumn bridge, q=2: concrete step 1 for Coordinate 2 (the generic
-- reduction machinery `species_eq_of_abelianization_eq` / `species_of_conjSub` /
-- `hasSpeciesMatch_of_reduced` / `nonempty_dringEquiv_of_reduced` is REUSED from the
-- q=1 audit above — stated for arbitrary G, not duplicated).
#print axioms LeanDring.DRing.Q2.species_col_conj_to_reps
-- Completeness capstone, q=2: the 2724 orbit-representative columns are a COMPLETE species
-- family for Coordinate 2. Steps 2/3 follow the q=1 proofs over the q=2 group law.
#print axioms LeanDring.DRing.Q2.species_eq_of_hpSub
#print axioms LeanDring.DRing.Q2.species_cosetStep
#print axioms LeanDring.DRing.Q2.exists_trans_pos
#print axioms LeanDring.DRing.Q2.species_reduces_to_rep
#print axioms LeanDring.DRing.Q2.speciesColsComplete_coordinate2
-- Completeness glue (column half), q=2: completeness composes into an abstract D-ring iso
-- once the still-open row-matching data (σ, hmatch) is supplied.
#print axioms LeanDring.DRing.Q2.dringEquiv_of_rowMatch_coordinate2

-- Cell discharge, core: the species-entry-code machinery. `section_independence` (the crux)
-- makes Müller's summand independent of the coset section, so the abstract sum
-- over the noncomputable `fixedPoints H (G/K)` becomes a sum over a supplied
-- concrete transversal (`species_basisElt_transversal`), whose bijection is
-- built from `siftB`-decidable data plus one cardinality input
-- (`transversalEquiv`, `species_basisElt_of_transversal`). Concretely on
-- `Coordinate 1`: a certified character value is a literal `ζ₂₅`-power
-- (`charOfVec_val_summand`), the entry is the `ζ₂₅`-power sum with a
-- kernel-computable exponent list (`species_entry_eq_sum`), and equality of the
-- executable entry codes reflects equality of species values exactly
-- (`entryCode_eq_species`, via `sumPowers_eq_iff_value_eq`).
#print axioms LeanDring.section_independence
#print axioms LeanDring.DRing.species_basisElt_transversal
#print axioms LeanDring.DRing.species_basisElt_of_transversal
#print axioms LeanDring.P5Presentation.charOfVec_val_summand
#print axioms LeanDring.P5Presentation.species_entry_eq_sum
#print axioms LeanDring.P5Presentation.entryCode_eq_species

-- Cell discharge, core (`Coordinate 2` twin): the `q=2` twin of the concrete entry-code
-- layer (`LeanDring/P5/Certificate/SpeciesTable/Twin2/EntryCore.lean`), a token-transform of the
-- above sharing the generic
-- `section_independence` / `species_basisElt_of_transversal` bridges and the
-- `zeta25`/`sumPowers` cyclotomic-code machinery.
#print axioms LeanDring.P5Presentation.Q2.charOfVec2_val_summand
#print axioms LeanDring.P5Presentation.Q2.species_entry_eq_sum
#print axioms LeanDring.P5Presentation.Q2.entryCode_eq_species

-- Cell discharge, isolated inputs: the two non-`decide` hypotheses of the entry machinery,
-- proven generically. Piece 1 (`hfix`): per-generator conjugation-into-`K`
-- upgrades to `H`-fixedness of the coset (`mem_fixedPoints_of_gens`), with the
-- converse (`conj_mem_of_fixedPoints`) making fixedness an iff; concretely a
-- `siftB`-`Bool` (`coset_fixed_iff_siftB`). Piece 2 (`hcard`): a full coset
-- transversal (injective-mod-`K` + index count, `transversalMod_bijective`) reads
-- the fixed-point count as a filter (`card_fixedPoints_eq_filter`,
-- `card_fixedPoints_eq_of_filter_card`); coset equality is `decide`-able through
-- canonical `reduceAux` forms (`reduceAux_right_coset`, `coset_eq_iff_reduceAux`).
#print axioms LeanDring.conj_mem_of_closure
#print axioms LeanDring.mem_fixedPoints_of_gens
#print axioms LeanDring.conj_mem_of_fixedPoints
#print axioms LeanDring.card_fixedPoints_eq_filter
#print axioms LeanDring.card_fixedPoints_eq_of_filter_card
#print axioms LeanDring.transversalMod_bijective
#print axioms LeanDring.P5Presentation.coset_fixed_iff_siftB
#print axioms LeanDring.P5Presentation.reduceAux_right_coset
#print axioms LeanDring.P5Presentation.coset_eq_iff_reduceAux

-- Cell discharge, data layer (A-block priority slice): the reusable data-parameterized builders
-- that discharge, from emitted `siftB`-transversal data, the three non-`decide`
-- hypotheses (`hinj`/`hfix`/`hcard`) of `species_entry_eq_sum` per species cell —
-- one application each. `card_quotient_ofList` gives the quotient-card numeral
-- `|G/K| = 5^(5-|gK|)` (Lagrange, no carrier scan) for EVERY well-formed echelon
-- list, specialised to the class reps as `card_quotient_reps` (q=1) /
-- `Q2.card_quotient_reps2` (q=2 twin); for the order-25 A-block (42 length-2 classes)
-- this is `|G/K| = 125`. The generic builders `cosetFun_inj_of_reduceAux`,
-- `cosetFun_fix_of_siftB`, `fixedCard_eq_of_filter` are `q`-parameterized (serve BOTH
-- twins); `decMemOfList` is the `siftB`-decidable membership feeding `QuotientGroup.fintype`.
-- The class-rep adapters `repsFix_of_siftB` / `repsInj_of_reduceAux` / `repsFixedCard`
-- (q=1) and their `Q2.*2` twins reduce entryCode instantiation to one apply per cell.
#print axioms LeanDring.P5Presentation.card_quotient_ofList
#print axioms LeanDring.P5Presentation.card_quotient_reps
#print axioms LeanDring.P5Presentation.decMemOfList
#print axioms LeanDring.P5Presentation.cosetFun_inj_of_reduceAux
#print axioms LeanDring.P5Presentation.cosetFun_fix_of_siftB
#print axioms LeanDring.P5Presentation.fixedCard_eq_of_filter
#print axioms LeanDring.P5Presentation.repsFix_of_siftB
#print axioms LeanDring.P5Presentation.repsInj_of_reduceAux
#print axioms LeanDring.P5Presentation.repsFixedCard
#print axioms LeanDring.P5Presentation.Q2.card_quotient_reps2
#print axioms LeanDring.P5Presentation.Q2.repsFix_of_siftB2
#print axioms LeanDring.P5Presentation.Q2.repsInj_of_reduceAux2
#print axioms LeanDring.P5Presentation.Q2.repsFixedCard2

-- Cell discharge, A-block cells (emit-embed-decide loop, both twins): for the order-25
-- A-block classes rK ∈ {13,14,15} the 125-coset transversal `R` and the H-fixed
-- sub-transversals `T` are embedded as kernel data; `reduceAux`-injectivity, `siftB`
-- fixedness and the filter-count are discharged by `decide` and fed through the
-- adapters to give per-cell `species_entry_eq_sum` instantiations parametric in the
-- certified character `e` and column element `h`. `cell13_1` (order-5 column, |T|=25),
-- `cell13_13`/`cellNN_diag` (H=K diagonal, |T|=5), and their q=2 twins.
#print axioms LeanDring.P5Presentation.cell13_1
#print axioms LeanDring.P5Presentation.cell13_13
#print axioms LeanDring.P5Presentation.Q2.cell13_1_2
#print axioms LeanDring.P5Presentation.Q2.cell13_13_2
#print axioms LeanDring.P5Presentation.cell14_diag
#print axioms LeanDring.P5Presentation.Q2.cell14_diag_2
#print axioms LeanDring.P5Presentation.cell15_diag
#print axioms LeanDring.P5Presentation.Q2.cell15_diag_2

-- Cell discharge, A-block cells rK ∈ {16,…,54} (emit-embed-decide loop, both
-- twins): the full nonzero H-column set per order-25 A-block class. Transversal
-- data (`R`, `T`) is shared between twins (reduceAux normal forms coincide).
-- Each cell is a parametric `species_entry_eq_sum` instantiation.
#print axioms LeanDring.P5Presentation.cell16_0
#print axioms LeanDring.P5Presentation.Q2.cell16_0_2
#print axioms LeanDring.P5Presentation.cell16_2
#print axioms LeanDring.P5Presentation.Q2.cell16_2_2
#print axioms LeanDring.P5Presentation.cell16_3
#print axioms LeanDring.P5Presentation.Q2.cell16_3_2
#print axioms LeanDring.P5Presentation.cell16_4
#print axioms LeanDring.P5Presentation.Q2.cell16_4_2
#print axioms LeanDring.P5Presentation.cell16_5
#print axioms LeanDring.P5Presentation.Q2.cell16_5_2
#print axioms LeanDring.P5Presentation.cell16_9
#print axioms LeanDring.P5Presentation.Q2.cell16_9_2
#print axioms LeanDring.P5Presentation.cell16_11
#print axioms LeanDring.P5Presentation.Q2.cell16_11_2
#print axioms LeanDring.P5Presentation.cell16_16
#print axioms LeanDring.P5Presentation.Q2.cell16_16_2
#print axioms LeanDring.P5Presentation.cell17_0
#print axioms LeanDring.P5Presentation.Q2.cell17_0_2
#print axioms LeanDring.P5Presentation.cell17_2
#print axioms LeanDring.P5Presentation.Q2.cell17_2_2
#print axioms LeanDring.P5Presentation.cell17_3
#print axioms LeanDring.P5Presentation.Q2.cell17_3_2
#print axioms LeanDring.P5Presentation.cell17_4
#print axioms LeanDring.P5Presentation.Q2.cell17_4_2
#print axioms LeanDring.P5Presentation.cell17_5
#print axioms LeanDring.P5Presentation.Q2.cell17_5_2
#print axioms LeanDring.P5Presentation.cell17_9
#print axioms LeanDring.P5Presentation.Q2.cell17_9_2
#print axioms LeanDring.P5Presentation.cell17_11
#print axioms LeanDring.P5Presentation.Q2.cell17_11_2
#print axioms LeanDring.P5Presentation.cell17_17
#print axioms LeanDring.P5Presentation.Q2.cell17_17_2
#print axioms LeanDring.P5Presentation.cell18_0
#print axioms LeanDring.P5Presentation.Q2.cell18_0_2
#print axioms LeanDring.P5Presentation.cell18_2
#print axioms LeanDring.P5Presentation.Q2.cell18_2_2
#print axioms LeanDring.P5Presentation.cell18_3
#print axioms LeanDring.P5Presentation.Q2.cell18_3_2
#print axioms LeanDring.P5Presentation.cell18_4
#print axioms LeanDring.P5Presentation.Q2.cell18_4_2
#print axioms LeanDring.P5Presentation.cell18_5
#print axioms LeanDring.P5Presentation.Q2.cell18_5_2
#print axioms LeanDring.P5Presentation.cell18_9
#print axioms LeanDring.P5Presentation.Q2.cell18_9_2
#print axioms LeanDring.P5Presentation.cell18_11
#print axioms LeanDring.P5Presentation.Q2.cell18_11_2
#print axioms LeanDring.P5Presentation.cell18_18
#print axioms LeanDring.P5Presentation.Q2.cell18_18_2
#print axioms LeanDring.P5Presentation.cell19_0
#print axioms LeanDring.P5Presentation.Q2.cell19_0_2
#print axioms LeanDring.P5Presentation.cell19_1
#print axioms LeanDring.P5Presentation.Q2.cell19_1_2
#print axioms LeanDring.P5Presentation.cell19_12
#print axioms LeanDring.P5Presentation.Q2.cell19_12_2
#print axioms LeanDring.P5Presentation.cell19_19
#print axioms LeanDring.P5Presentation.Q2.cell19_19_2
#print axioms LeanDring.P5Presentation.cell20_0
#print axioms LeanDring.P5Presentation.Q2.cell20_0_2
#print axioms LeanDring.P5Presentation.cell20_2
#print axioms LeanDring.P5Presentation.Q2.cell20_2_2
#print axioms LeanDring.P5Presentation.cell20_12
#print axioms LeanDring.P5Presentation.Q2.cell20_12_2
#print axioms LeanDring.P5Presentation.cell20_20
#print axioms LeanDring.P5Presentation.Q2.cell20_20_2
#print axioms LeanDring.P5Presentation.cell21_0
#print axioms LeanDring.P5Presentation.Q2.cell21_0_2
#print axioms LeanDring.P5Presentation.cell21_3
#print axioms LeanDring.P5Presentation.Q2.cell21_3_2
#print axioms LeanDring.P5Presentation.cell21_12
#print axioms LeanDring.P5Presentation.Q2.cell21_12_2
#print axioms LeanDring.P5Presentation.cell21_21
#print axioms LeanDring.P5Presentation.Q2.cell21_21_2
#print axioms LeanDring.P5Presentation.cell22_0
#print axioms LeanDring.P5Presentation.Q2.cell22_0_2
#print axioms LeanDring.P5Presentation.cell22_4
#print axioms LeanDring.P5Presentation.Q2.cell22_4_2
#print axioms LeanDring.P5Presentation.cell22_12
#print axioms LeanDring.P5Presentation.Q2.cell22_12_2
#print axioms LeanDring.P5Presentation.cell22_22
#print axioms LeanDring.P5Presentation.Q2.cell22_22_2
#print axioms LeanDring.P5Presentation.cell23_0
#print axioms LeanDring.P5Presentation.Q2.cell23_0_2
#print axioms LeanDring.P5Presentation.cell23_5
#print axioms LeanDring.P5Presentation.Q2.cell23_5_2
#print axioms LeanDring.P5Presentation.cell23_12
#print axioms LeanDring.P5Presentation.Q2.cell23_12_2
#print axioms LeanDring.P5Presentation.cell23_23
#print axioms LeanDring.P5Presentation.Q2.cell23_23_2
#print axioms LeanDring.P5Presentation.cell24_0
#print axioms LeanDring.P5Presentation.Q2.cell24_0_2
#print axioms LeanDring.P5Presentation.cell24_6
#print axioms LeanDring.P5Presentation.Q2.cell24_6_2
#print axioms LeanDring.P5Presentation.cell24_12
#print axioms LeanDring.P5Presentation.Q2.cell24_12_2
#print axioms LeanDring.P5Presentation.cell24_24
#print axioms LeanDring.P5Presentation.Q2.cell24_24_2
#print axioms LeanDring.P5Presentation.cell25_0
#print axioms LeanDring.P5Presentation.Q2.cell25_0_2
#print axioms LeanDring.P5Presentation.cell25_7
#print axioms LeanDring.P5Presentation.Q2.cell25_7_2
#print axioms LeanDring.P5Presentation.cell25_12
#print axioms LeanDring.P5Presentation.Q2.cell25_12_2
#print axioms LeanDring.P5Presentation.cell25_25
#print axioms LeanDring.P5Presentation.Q2.cell25_25_2
#print axioms LeanDring.P5Presentation.cell26_0
#print axioms LeanDring.P5Presentation.Q2.cell26_0_2
#print axioms LeanDring.P5Presentation.cell26_8
#print axioms LeanDring.P5Presentation.Q2.cell26_8_2
#print axioms LeanDring.P5Presentation.cell26_12
#print axioms LeanDring.P5Presentation.Q2.cell26_12_2
#print axioms LeanDring.P5Presentation.cell26_26
#print axioms LeanDring.P5Presentation.Q2.cell26_26_2
#print axioms LeanDring.P5Presentation.cell27_0
#print axioms LeanDring.P5Presentation.Q2.cell27_0_2
#print axioms LeanDring.P5Presentation.cell27_9
#print axioms LeanDring.P5Presentation.Q2.cell27_9_2
#print axioms LeanDring.P5Presentation.cell27_12
#print axioms LeanDring.P5Presentation.Q2.cell27_12_2
#print axioms LeanDring.P5Presentation.cell27_27
#print axioms LeanDring.P5Presentation.Q2.cell27_27_2
#print axioms LeanDring.P5Presentation.cell28_0
#print axioms LeanDring.P5Presentation.Q2.cell28_0_2
#print axioms LeanDring.P5Presentation.cell28_12
#print axioms LeanDring.P5Presentation.Q2.cell28_12_2
#print axioms LeanDring.P5Presentation.cell28_28
#print axioms LeanDring.P5Presentation.Q2.cell28_28_2
#print axioms LeanDring.P5Presentation.cell29_0
#print axioms LeanDring.P5Presentation.Q2.cell29_0_2
#print axioms LeanDring.P5Presentation.cell29_12
#print axioms LeanDring.P5Presentation.Q2.cell29_12_2
#print axioms LeanDring.P5Presentation.cell29_29
#print axioms LeanDring.P5Presentation.Q2.cell29_29_2
#print axioms LeanDring.P5Presentation.cell30_0
#print axioms LeanDring.P5Presentation.Q2.cell30_0_2
#print axioms LeanDring.P5Presentation.cell30_12
#print axioms LeanDring.P5Presentation.Q2.cell30_12_2
#print axioms LeanDring.P5Presentation.cell30_30
#print axioms LeanDring.P5Presentation.Q2.cell30_30_2
#print axioms LeanDring.P5Presentation.cell31_0
#print axioms LeanDring.P5Presentation.Q2.cell31_0_2
#print axioms LeanDring.P5Presentation.cell31_12
#print axioms LeanDring.P5Presentation.Q2.cell31_12_2
#print axioms LeanDring.P5Presentation.cell31_31
#print axioms LeanDring.P5Presentation.Q2.cell31_31_2
#print axioms LeanDring.P5Presentation.cell32_0
#print axioms LeanDring.P5Presentation.Q2.cell32_0_2
#print axioms LeanDring.P5Presentation.cell32_12
#print axioms LeanDring.P5Presentation.Q2.cell32_12_2
#print axioms LeanDring.P5Presentation.cell32_32
#print axioms LeanDring.P5Presentation.Q2.cell32_32_2
#print axioms LeanDring.P5Presentation.cell33_0
#print axioms LeanDring.P5Presentation.Q2.cell33_0_2
#print axioms LeanDring.P5Presentation.cell33_12
#print axioms LeanDring.P5Presentation.Q2.cell33_12_2
#print axioms LeanDring.P5Presentation.cell33_33
#print axioms LeanDring.P5Presentation.Q2.cell33_33_2
#print axioms LeanDring.P5Presentation.cell34_0
#print axioms LeanDring.P5Presentation.Q2.cell34_0_2
#print axioms LeanDring.P5Presentation.cell34_12
#print axioms LeanDring.P5Presentation.Q2.cell34_12_2
#print axioms LeanDring.P5Presentation.cell34_34
#print axioms LeanDring.P5Presentation.Q2.cell34_34_2
#print axioms LeanDring.P5Presentation.cell35_0
#print axioms LeanDring.P5Presentation.Q2.cell35_0_2
#print axioms LeanDring.P5Presentation.cell35_12
#print axioms LeanDring.P5Presentation.Q2.cell35_12_2
#print axioms LeanDring.P5Presentation.cell35_35
#print axioms LeanDring.P5Presentation.Q2.cell35_35_2
#print axioms LeanDring.P5Presentation.cell36_0
#print axioms LeanDring.P5Presentation.Q2.cell36_0_2
#print axioms LeanDring.P5Presentation.cell36_12
#print axioms LeanDring.P5Presentation.Q2.cell36_12_2
#print axioms LeanDring.P5Presentation.cell36_36
#print axioms LeanDring.P5Presentation.Q2.cell36_36_2
#print axioms LeanDring.P5Presentation.cell37_0
#print axioms LeanDring.P5Presentation.Q2.cell37_0_2
#print axioms LeanDring.P5Presentation.cell37_12
#print axioms LeanDring.P5Presentation.Q2.cell37_12_2
#print axioms LeanDring.P5Presentation.cell37_37
#print axioms LeanDring.P5Presentation.Q2.cell37_37_2
#print axioms LeanDring.P5Presentation.cell38_0
#print axioms LeanDring.P5Presentation.Q2.cell38_0_2
#print axioms LeanDring.P5Presentation.cell38_12
#print axioms LeanDring.P5Presentation.Q2.cell38_12_2
#print axioms LeanDring.P5Presentation.cell38_38
#print axioms LeanDring.P5Presentation.Q2.cell38_38_2
#print axioms LeanDring.P5Presentation.cell39_0
#print axioms LeanDring.P5Presentation.Q2.cell39_0_2
#print axioms LeanDring.P5Presentation.cell39_12
#print axioms LeanDring.P5Presentation.Q2.cell39_12_2
#print axioms LeanDring.P5Presentation.cell39_39
#print axioms LeanDring.P5Presentation.Q2.cell39_39_2
#print axioms LeanDring.P5Presentation.cell40_0
#print axioms LeanDring.P5Presentation.Q2.cell40_0_2
#print axioms LeanDring.P5Presentation.cell40_12
#print axioms LeanDring.P5Presentation.Q2.cell40_12_2
#print axioms LeanDring.P5Presentation.cell40_40
#print axioms LeanDring.P5Presentation.Q2.cell40_40_2
#print axioms LeanDring.P5Presentation.cell41_0
#print axioms LeanDring.P5Presentation.Q2.cell41_0_2
#print axioms LeanDring.P5Presentation.cell41_12
#print axioms LeanDring.P5Presentation.Q2.cell41_12_2
#print axioms LeanDring.P5Presentation.cell41_41
#print axioms LeanDring.P5Presentation.Q2.cell41_41_2
#print axioms LeanDring.P5Presentation.cell42_0
#print axioms LeanDring.P5Presentation.Q2.cell42_0_2
#print axioms LeanDring.P5Presentation.cell42_12
#print axioms LeanDring.P5Presentation.Q2.cell42_12_2
#print axioms LeanDring.P5Presentation.cell42_42
#print axioms LeanDring.P5Presentation.Q2.cell42_42_2
#print axioms LeanDring.P5Presentation.cell43_0
#print axioms LeanDring.P5Presentation.Q2.cell43_0_2
#print axioms LeanDring.P5Presentation.cell43_12
#print axioms LeanDring.P5Presentation.Q2.cell43_12_2
#print axioms LeanDring.P5Presentation.cell43_43
#print axioms LeanDring.P5Presentation.Q2.cell43_43_2
#print axioms LeanDring.P5Presentation.cell44_0
#print axioms LeanDring.P5Presentation.Q2.cell44_0_2
#print axioms LeanDring.P5Presentation.cell44_12
#print axioms LeanDring.P5Presentation.Q2.cell44_12_2
#print axioms LeanDring.P5Presentation.cell44_44
#print axioms LeanDring.P5Presentation.Q2.cell44_44_2
#print axioms LeanDring.P5Presentation.cell45_0
#print axioms LeanDring.P5Presentation.Q2.cell45_0_2
#print axioms LeanDring.P5Presentation.cell45_12
#print axioms LeanDring.P5Presentation.Q2.cell45_12_2
#print axioms LeanDring.P5Presentation.cell45_45
#print axioms LeanDring.P5Presentation.Q2.cell45_45_2
#print axioms LeanDring.P5Presentation.cell46_0
#print axioms LeanDring.P5Presentation.Q2.cell46_0_2
#print axioms LeanDring.P5Presentation.cell46_12
#print axioms LeanDring.P5Presentation.Q2.cell46_12_2
#print axioms LeanDring.P5Presentation.cell46_46
#print axioms LeanDring.P5Presentation.Q2.cell46_46_2
#print axioms LeanDring.P5Presentation.cell47_0
#print axioms LeanDring.P5Presentation.Q2.cell47_0_2
#print axioms LeanDring.P5Presentation.cell47_12
#print axioms LeanDring.P5Presentation.Q2.cell47_12_2
#print axioms LeanDring.P5Presentation.cell47_47
#print axioms LeanDring.P5Presentation.Q2.cell47_47_2
#print axioms LeanDring.P5Presentation.cell48_0
#print axioms LeanDring.P5Presentation.Q2.cell48_0_2
#print axioms LeanDring.P5Presentation.cell48_12
#print axioms LeanDring.P5Presentation.Q2.cell48_12_2
#print axioms LeanDring.P5Presentation.cell48_48
#print axioms LeanDring.P5Presentation.Q2.cell48_48_2
#print axioms LeanDring.P5Presentation.cell49_0
#print axioms LeanDring.P5Presentation.Q2.cell49_0_2
#print axioms LeanDring.P5Presentation.cell49_12
#print axioms LeanDring.P5Presentation.Q2.cell49_12_2
#print axioms LeanDring.P5Presentation.cell49_49
#print axioms LeanDring.P5Presentation.Q2.cell49_49_2
#print axioms LeanDring.P5Presentation.cell50_0
#print axioms LeanDring.P5Presentation.Q2.cell50_0_2
#print axioms LeanDring.P5Presentation.cell50_12
#print axioms LeanDring.P5Presentation.Q2.cell50_12_2
#print axioms LeanDring.P5Presentation.cell50_50
#print axioms LeanDring.P5Presentation.Q2.cell50_50_2
#print axioms LeanDring.P5Presentation.cell51_0
#print axioms LeanDring.P5Presentation.Q2.cell51_0_2
#print axioms LeanDring.P5Presentation.cell51_12
#print axioms LeanDring.P5Presentation.Q2.cell51_12_2
#print axioms LeanDring.P5Presentation.cell51_51
#print axioms LeanDring.P5Presentation.Q2.cell51_51_2
#print axioms LeanDring.P5Presentation.cell52_0
#print axioms LeanDring.P5Presentation.Q2.cell52_0_2
#print axioms LeanDring.P5Presentation.cell52_12
#print axioms LeanDring.P5Presentation.Q2.cell52_12_2
#print axioms LeanDring.P5Presentation.cell52_52
#print axioms LeanDring.P5Presentation.Q2.cell52_52_2
#print axioms LeanDring.P5Presentation.cell53_0
#print axioms LeanDring.P5Presentation.Q2.cell53_0_2
#print axioms LeanDring.P5Presentation.cell53_10
#print axioms LeanDring.P5Presentation.Q2.cell53_10_2
#print axioms LeanDring.P5Presentation.cell53_12
#print axioms LeanDring.P5Presentation.Q2.cell53_12_2
#print axioms LeanDring.P5Presentation.cell53_53
#print axioms LeanDring.P5Presentation.Q2.cell53_53_2
#print axioms LeanDring.P5Presentation.cell54_0
#print axioms LeanDring.P5Presentation.Q2.cell54_0_2
#print axioms LeanDring.P5Presentation.cell54_11
#print axioms LeanDring.P5Presentation.Q2.cell54_11_2
#print axioms LeanDring.P5Presentation.cell54_12
#print axioms LeanDring.P5Presentation.Q2.cell54_12_2
#print axioms LeanDring.P5Presentation.cell54_54
#print axioms LeanDring.P5Presentation.Q2.cell54_54_2

-- Cell discharge, K-strata cells (emit-embed-decide loop, both twins): the cheap
-- strata beyond the A-block. 5^3 (rK 55-115, |R|=25), 5^4 (rK 116-146, |R|=5),
-- TOP (rK 147, |R|=1); transversal data shared between twins. Representative
-- audits per stratum (the full set is generated identically per the A-block
-- recipe via `species_entry_eq_sum`).
-- 5^3 stratum:
#print axioms LeanDring.P5Presentation.cell55_0
#print axioms LeanDring.P5Presentation.Q2.cell55_0_2
#print axioms LeanDring.P5Presentation.cell55_28
#print axioms LeanDring.P5Presentation.cell55_55
#print axioms LeanDring.P5Presentation.cell85_85
#print axioms LeanDring.P5Presentation.Q2.cell85_85_2
#print axioms LeanDring.P5Presentation.cell115_115
-- 5^4 stratum:
#print axioms LeanDring.P5Presentation.cell116_0
#print axioms LeanDring.P5Presentation.Q2.cell116_0_2
#print axioms LeanDring.P5Presentation.cell116_116
#print axioms LeanDring.P5Presentation.cell141_141
#print axioms LeanDring.P5Presentation.cell146_146
-- TOP stratum (rK 147, |R|=1):
#print axioms LeanDring.P5Presentation.cell147_0
#print axioms LeanDring.P5Presentation.Q2.cell147_0_2
#print axioms LeanDring.P5Presentation.cell147_147
#print axioms LeanDring.P5Presentation.Q2.cell147_147_2

-- Cell discharge, K=⊥ column (rK 0), proven ABSTRACTLY (no 3125-transversal), both twins:
-- the augmentation entry = |G| = 3125 (`species_bot_one_basisElt`) and the
-- off-augmentation zero pattern for H ≠ ⊥ (`species_basisElt_bot`), tied to the
-- presentation by `reps 0 = ⊥`.
#print axioms LeanDring.P5Presentation.reps_zero_eq_bot
#print axioms LeanDring.P5Presentation.reps_zero_eq_bot2
#print axioms LeanDring.P5Presentation.cell0_aug
#print axioms LeanDring.P5Presentation.cell0_aug2
#print axioms LeanDring.P5Presentation.cell0_zero
#print axioms LeanDring.P5Presentation.cell0_zero2

-- Cell discharge, order-5 stratum cells (rK 1-12, |K| = 5, |G/K| = 625), both twins:
-- the 12 order-5 K-classes
-- (`LeanDring/P5/Data/EntryK/C002.lean`…`LeanDring/P5/Data/EntryK/C013.lean`). Each has exactly two
-- nonzero H-columns: `H = ⊥` (`cellN_0`, abstract augmentation value `|G/K| = 625`,
-- no 625-coset transversal decide) and the `H = K` diagonal (`cellN_N`, |T| = 125,
-- via the emitted fixed sub-transversal and the
-- `LeanDring/P5/Certificate/SpeciesTable/EntryTransA.lean` adapters). The full
-- 625-coset transversal injectivity is the one heavy per-rK decide (O(n) IsChain
-- `cKey` route). Transversal data is shared byte-identically between the twins.
#print axioms LeanDring.P5Presentation.cell1_0
#print axioms LeanDring.P5Presentation.cell1_1
#print axioms LeanDring.P5Presentation.Q2.cell1_0_2
#print axioms LeanDring.P5Presentation.Q2.cell1_1_2
#print axioms LeanDring.P5Presentation.cell2_0
#print axioms LeanDring.P5Presentation.cell2_2
#print axioms LeanDring.P5Presentation.Q2.cell2_0_2
#print axioms LeanDring.P5Presentation.Q2.cell2_2_2
#print axioms LeanDring.P5Presentation.cell3_0
#print axioms LeanDring.P5Presentation.cell3_3
#print axioms LeanDring.P5Presentation.Q2.cell3_0_2
#print axioms LeanDring.P5Presentation.Q2.cell3_3_2
#print axioms LeanDring.P5Presentation.cell4_0
#print axioms LeanDring.P5Presentation.cell4_4
#print axioms LeanDring.P5Presentation.Q2.cell4_0_2
#print axioms LeanDring.P5Presentation.Q2.cell4_4_2
#print axioms LeanDring.P5Presentation.cell5_0
#print axioms LeanDring.P5Presentation.cell5_5
#print axioms LeanDring.P5Presentation.Q2.cell5_0_2
#print axioms LeanDring.P5Presentation.Q2.cell5_5_2
#print axioms LeanDring.P5Presentation.cell6_0
#print axioms LeanDring.P5Presentation.cell6_6
#print axioms LeanDring.P5Presentation.Q2.cell6_0_2
#print axioms LeanDring.P5Presentation.Q2.cell6_6_2
#print axioms LeanDring.P5Presentation.cell7_0
#print axioms LeanDring.P5Presentation.cell7_7
#print axioms LeanDring.P5Presentation.Q2.cell7_0_2
#print axioms LeanDring.P5Presentation.Q2.cell7_7_2
#print axioms LeanDring.P5Presentation.cell8_0
#print axioms LeanDring.P5Presentation.cell8_8
#print axioms LeanDring.P5Presentation.Q2.cell8_0_2
#print axioms LeanDring.P5Presentation.Q2.cell8_8_2
#print axioms LeanDring.P5Presentation.cell9_0
#print axioms LeanDring.P5Presentation.cell9_9
#print axioms LeanDring.P5Presentation.Q2.cell9_0_2
#print axioms LeanDring.P5Presentation.Q2.cell9_9_2
#print axioms LeanDring.P5Presentation.cell10_0
#print axioms LeanDring.P5Presentation.cell10_10
#print axioms LeanDring.P5Presentation.Q2.cell10_0_2
#print axioms LeanDring.P5Presentation.Q2.cell10_10_2
#print axioms LeanDring.P5Presentation.cell11_0
#print axioms LeanDring.P5Presentation.cell11_11
#print axioms LeanDring.P5Presentation.Q2.cell11_0_2
#print axioms LeanDring.P5Presentation.Q2.cell11_11_2
#print axioms LeanDring.P5Presentation.cell12_0
#print axioms LeanDring.P5Presentation.cell12_12
#print axioms LeanDring.P5Presentation.Q2.cell12_0_2
#print axioms LeanDring.P5Presentation.Q2.cell12_12_2

-- Cell discharge, fast-evaluator bridge + support layer
#print axioms LeanDring.P5Presentation.entryExpFast_eq
#print axioms LeanDring.P5Presentation.entryExpFast2_eq
#print axioms LeanDring.DRing.species_basisElt_eq_zero_of_not_subconj
#print axioms LeanDring.P5Presentation.entryCode_cross_eq_species

-- Cell discharge, stage-1 audited-real layer (twin-anatomy reduction): the `fastCode`
-- bridges (`entryCode`/`Q2.entryCode` = `sumPowers ∘ fastCode`), the generic
-- twin-equal congruence, and the packaged data-equality cell discharge.
#print axioms LeanDring.P5Presentation.entryCode_eq_fastCode
#print axioms LeanDring.P5Presentation.entryCode2_eq_fastCode
#print axioms LeanDring.P5Presentation.entry_eq_of_data_eq
#print axioms LeanDring.P5Presentation.species_eq_of_data_eq

-- Cell discharge, stage-3/4 residual-decide engine: the divergent-column
-- counterpart of `species_eq_of_data_eq`.  Every one of the 173,006 residual
-- real-decide cells (τ-moved, col-data-divergent, row-`e`-divergent) discharges
-- through this lemma: one kernel `decide` on the embedded fast codes, reflected
-- to the species equality via the proven cross-coordinate bridge.
#print axioms LeanDring.P5Presentation.species_eq_of_fastcode_eq

-- Cell discharge, stage-2 per-column certified data layer: the `colCert`
-- structures + the twin data-equality derivation `ColCert.hD` (stage-3 input),
-- with representative kernel-`decide`-bound instances (τ tier + col-data-divergent
-- tier). The `bind1`/`bind2` fields are the once-per-column expVec kernel decides;
-- `#print axioms` on an instance confirms they add no axiom beyond the standard three.
#print axioms LeanDring.P5Presentation.ColCert.hD
#print axioms LeanDring.P5Presentation.colCertDiv_13_13_5
#print axioms LeanDring.P5Presentation.colCertDiv_102_40_5
#print axioms LeanDring.P5Presentation.colCert_16_0_0

-- Cell discharge, stage-2 rest tier (twin-coincident columns, cheap |T| <= 25 stratum): 197
-- emitted modules / 11,804 columns, spot-checked via 3 representative instances
-- spanning the batch (chunk 0, chunk ~100, final chunk 196).
#print axioms LeanDring.P5Presentation.colCert_13_1_0
#print axioms LeanDring.P5Presentation.colCert_143_97_0
#print axioms LeanDring.P5Presentation.colCert_99_99_3

-- Cell discharge, stages 3-4 residual real-decide certificates: the
-- per-column `_match` all-rows decides for all 2,450 twin-divergent columns
-- (69 emitted modules, P5/Data/SpeciesDiv/C001..C069; same-`e`, sigma-robust
-- form). Spot-checked
-- via representatives spanning the batch and all |T| tiers (m = 25, 5, 1).
#print axioms LeanDring.P5Presentation.colCertDiv_102_40_5_match
#print axioms LeanDring.P5Presentation.colCertDiv_144_41_5_match
#print axioms LeanDring.P5Presentation.colCertDiv_147_44_10_match
#print axioms LeanDring.P5Presentation.colCertDiv_125_52_15_match

-- Cell discharge, tau-family cross-column certificates: the 108 tau-tier
-- `_tau_match` all-rows decides (3 emitted modules,
-- P5/Certificate/SpeciesTable/Twin2/SpeciesTau/Chunk01..03). Pairing
-- resolved from data: the IDENTITY column map validates all cells (GAP's gamma
-- was a row-convention artifact). Spot-checked
-- via representatives including a genuine-content pair (D1 != D2).
#print axioms LeanDring.P5Presentation.colCertDiv_13_13_5_tau_match
#print axioms LeanDring.P5Presentation.colCertDiv_118_68_19_tau_match
#print axioms LeanDring.P5Presentation.colCertDiv_85_85_110_tau_match
#print axioms LeanDring.P5Presentation.colCertDiv_147_86_4_tau_match

-- Cell discharge, stage-5 sigma layer: the per-class character alignment
-- tables + checks (Characters/Twin2/CharAlign.lean), the row equiv sigma itself
-- (RingIsomorphism/Twin2/Sigma.lean: sigmaEquiv = orbRepClass2 ∘ psi ∘
-- orbRepClass1⁻¹, bijective via the two proven 2724 counts), and the stage-5
-- support lemmas (Support/Stage5Core.lean).
-- classElt_sigmaEquiv_orbRepClass computes classElt (sigma c) into the exact
-- basisElt form the column certificates consume.
#print axioms LeanDring.P5Presentation.alnCheck_all
#print axioms LeanDring.P5Presentation.Q2.class_pos_eq_orbRepClass
#print axioms LeanDring.P5Presentation.psi_bijective
#print axioms LeanDring.P5Presentation.sigmaEquiv
#print axioms LeanDring.P5Presentation.classElt_sigmaEquiv_orbRepClass
#print axioms LeanDring.P5Presentation.species_zero_of_fixCard_zero
#print axioms LeanDring.P5Presentation.Q2.species_zero_of_fixCard_zero
#print axioms LeanDring.P5Presentation.species_zero_of_len_lt
#print axioms LeanDring.P5Presentation.Q2.species_zero_of_len_lt
#print axioms LeanDring.P5Presentation.species_bot_column
#print axioms LeanDring.P5Presentation.Q2.species_bot_column
#print axioms LeanDring.P5Presentation.basisAt_length_eq

-- Cell discharge, stage 5 complete — the theorem. The alignment-universal
-- per-column decides (P5/Data/SpeciesAlign/C001..C026), the off-support emptiness
-- certificates (P5/Data/FixZero/C001..C088, 296 batched decides), the stage-2 gap
-- fill (rK 13-15), the leaf/pair/master dispatch pyramid
-- (RingIsomorphism/Match*.lean), and the
-- capstone: hmatch + dring_equiv_coordinate12 = the formal main theorem,
--   Nonempty (DRing (Coordinate 1) ≃+* DRing (Coordinate 2)).
#print axioms LeanDring.P5Presentation.alnAll_28_0_0
#print axioms LeanDring.P5Presentation.fixz1_1
#print axioms LeanDring.P5Presentation.fz1_1_2
#print axioms LeanDring.P5Presentation.fz2_1_2
#print axioms LeanDring.P5Presentation.leaf_1_1_0
#print axioms LeanDring.P5Presentation.pair_1_1
#print axioms LeanDring.P5Presentation.master_0
#print axioms LeanDring.P5Presentation.master
#print axioms LeanDring.P5Presentation.hmatch
#print axioms LeanDring.P5Presentation.dring_equiv_coordinate12

-- Foundational landmarks.  All eight are
-- cited by the paper (and re-exported from `LeanDring/MainResults.lean`) but
-- were previously audited only transitively.
#print axioms LeanDring.DRing.rank_dring
#print axioms LeanDring.BurnsideRing.mark_injective
#print axioms LeanDring.FinGSet.isIso_of_fix_eq
#print axioms LeanDring.DRing.basisElt_eq_iff
#print axioms LeanDring.MonGSet.isIso_induced_iff_conjPair
#print axioms LeanDring.MonGSet.census_congr
#print axioms LeanDring.DRing.burnsideEquivOfPsiEquivariant
#print axioms LeanDring.DRing.burnsideEquivOfPsiTwoEquivariant

-- ============================================================================
-- The even-order layer (LeanDring/Even/*.lean): Sections 6 and 7 of the paper.
-- `import LeanDring.Even` above puts all 39 modules of the layer inside this audit.
--
-- Read the results below with §7.6 in hand. Most of this layer consists of verified
-- *implications* whose antecedents are named `Prop`s — `BoltjeIntegrality`,
-- `MullerIsolation`, `SimpleOrderRigidity`, `TwinSeparation`, `TwoGroupRigidity`,
-- `CoprimeTensorFactorization` and the rest. A hypothesis is a hypothesis, not an
-- axiom: the theorems below therefore report the same three standard axioms
-- [propext, Classical.choice, Quot.sound] that the rest of the corpus reports. What
-- the audit certifies is that the implications are `sorry`-free and kernel-checked,
-- not that their antecedents hold. Modules marked (unconditional) carry no such
-- hypothesis at all.
-- ============================================================================

-- Even/ATSeparation.lean: Theorem AT endgame — the binomial hole, the squeeze, and the
-- resulting A_n vs Fitting-free-twin separation (hypotheses: the ind* spectrum inclusion).
#print axioms LeanDring.Even.choose_three_mul_sub
#print axioms LeanDring.Even.choose_three_mul_sub_sub
#print axioms LeanDring.Even.choose_three_pos
#print axioms LeanDring.Even.holeLo_pos
#print axioms LeanDring.Even.holeLo_lt_holeHi
#print axioms LeanDring.Even.choose_three_lt_choose_four
#print axioms LeanDring.Even.choose_chain
#print axioms LeanDring.Even.squeeze
#print axioms LeanDring.Even.atSeparation
#print axioms LeanDring.Even.not_nonempty_dringEquiv_of_atSeparation

-- Even/Arity.lean: higher-arity linkage. Lattice identifications invert, transport the
-- arity-|S| linkage subgroups and the dual pairing, and respect the dual-difference subgroup.
#print axioms LeanDring.Even.IdentifiesLattices.symm
#print axioms LeanDring.Even.mem_sumLinkSubgroup_iff_lattice
#print axioms LeanDring.Even.sumLinkSubgroup_of_identifies
#print axioms LeanDring.Even.zpair_add_left
#print axioms LeanDring.Even.zpair_neg_left
#print axioms LeanDring.Even.comp_mem_dualLat_of_identifies
#print axioms LeanDring.Even.dualDiffSubgroup
#print axioms LeanDring.Even.dualDiffSubgroup_of_identifies
#print axioms LeanDring.Even.card_mem_sumLinkSubgroup

-- Even/Assembly.lean: the abstract assembly — the T-symmetric slice of the ghost lattice as a
-- subring, its transport along a lattice identification, and the MarksOntoSlice payoff for B(G).
#print axioms LeanDring.Even.ghost_comp_pointPush
#print axioms LeanDring.Even.precompHom
#print axioms LeanDring.Even.fixedSubring
#print axioms LeanDring.Even.mem_fixedSubring
#print axioms LeanDring.Even.ghost_mem_fixedSubring
#print axioms LeanDring.Even.mem_ghostLattice_iff_mem_range
#print axioms LeanDring.Even.identifiesLattices_trans
#print axioms LeanDring.Even.fixedSubringEquivOfIdentifies
#print axioms LeanDring.Even.MarksOntoSlice
#print axioms LeanDring.Even.burnsideNonempty_of_sliceRecognition

-- Even/BCSeparation.lean: Theorem BC-n — the anisotropic-point conductor separating B_n(q)
-- from C_n(q), plus the index-value transfer it runs on.
#print axioms LeanDring.Even.iota_coprime_base
#print axioms LeanDring.Even.add_one_lt_iota
#print axioms LeanDring.Even.lt_iota
#print axioms LeanDring.Even.not_dvd_of_two_mul_eq
#print axioms LeanDring.Even.lt_pow_two_mul
#print axioms LeanDring.Even.one_lt_of_two_mul_eq
#print axioms LeanDring.Even.pairNormalizer_le_normalizer
#print axioms LeanDring.Even.IsIndexValue.transfer
#print axioms LeanDring.Even.bcSeparation
#print axioms LeanDring.Even.not_nonempty_dringEquiv_of_bcSeparation

-- Even/BoltjeAssembly.lean: the conductor dictionary assembled — BoltjeIntegrality plus group
-- facts give the BC and AT separations, the exception witnesses, and order transfer.
#print axioms LeanDring.Even.bAnisotropicWitness_of_indStar
#print axioms LeanDring.Even.cIndexDichotomy_of_indStar
#print axioms LeanDring.Even.spectrumHole_of_indStar
#print axioms LeanDring.Even.twinWitness_of_indStar
#print axioms LeanDring.Even.bcSeparation_of_boltje
#print axioms LeanDring.Even.not_nonempty_dringEquiv_of_bcSeparation_of_boltje
#print axioms LeanDring.Even.atSeparation_of_boltje
#print axioms LeanDring.Even.not_nonempty_dringEquiv_of_atSeparation_of_boltje
#print axioms LeanDring.Even.exceptionSeparation_witness
#print axioms LeanDring.Even.exceptionSeparation_witness_indStar
#print axioms LeanDring.Even.mullerIsolationWeak_of_boltje
#print axioms LeanDring.Even.orderTransfer_of_boltje

-- Even/BoltjeCongruence.lean: Boltje's congruence, step four — the divisibility that feeds the
-- peel-off induction.
#print axioms LeanDring.Even.card_lt_card_of_lt
#print axioms LeanDring.Even.dvd_of_congruenceAt

-- Even/BurnsideGhost.lean: the assembled mark homomorphism ρ_G: B(G) → (Subgroup G → ℤ) and the
-- peel-off step (unconditional; no named Prop hypothesis).
#print axioms LeanDring.Even.markGhost_transitive
#print axioms LeanDring.Even.ghost_transitive_eq_zero_of_card_lt
#print axioms LeanDring.Even.ghost_transitive_self
#print axioms LeanDring.Even.peel

-- Even/BurnsideMarks.lean: marks of the transitive G-sets — the two fixed-point facts driving
-- the peel-off induction (unconditional).
#print axioms LeanDring.Even.mem_fixedPoints_coset_iff
#print axioms LeanDring.Even.fix_coset_eq_zero_of_forall
#print axioms LeanDring.Even.fix_coset_eq_zero_of_card_lt
#print axioms LeanDring.Even.fix_coset_self

-- Even/Cancellation.lean: the idempotent core of Müller's tensor cancellation (Satz 2.8.4) —
-- primitive idempotents in a product decomposition, and the tensor-to-product equivalence.
#print axioms LeanDring.Even.isIdempotentElem_pi_iff_of_trivial
#print axioms LeanDring.Even.idempotentEquivSet
#print axioms LeanDring.Even.card_eq_of_algEquiv_pi
#print axioms LeanDring.Even.IsPrimitiveIdem.map
#print axioms LeanDring.Even.isPrimitiveIdem_pi_iff
#print axioms LeanDring.Even.algEquivPiOfTensor

-- Even/CentralSylowTwo.lean: Theorem MC1 — a finite group with central Sylow 2-subgroup of
-- order 2 splits as C₂ × H, and what that gives for D ⇒ B.
#print axioms LeanDring.Even.directProduct_of_central_sylow_two
#print axioms LeanDring.Even.mulEquiv_of_card_two
#print axioms LeanDring.Even.mc1
#print axioms LeanDring.Even.dtoB_of_central_sylow_two

-- Even/ConductorAtSpecies.lean: Müller Satz 2.3.3, the conductor at a species. The largest
-- module of the layer: species of basis elements, good cosets, the pair normalizer count,
-- fusion counting, the twisted/induction/Mackey stack, and the Boltje reduction.
#print axioms LeanDring.Even.ringHom_eq_species
#print axioms LeanDring.Even.conductorPairDictionary_forward'
#print axioms LeanDring.Even.conductorPairDictionary'
#print axioms LeanDring.Even.intPoint_ext
#print axioms LeanDring.Even.conductorAtSpecies_trivial
#print axioms LeanDring.Even.species_basisElt_gen
#print axioms LeanDring.Even.species_basisElt_eq_zero_of_not_subconj
#print axioms LeanDring.Even.exists_conj_le_of_species_basisElt_ne_zero
#print axioms LeanDring.Even.species_sum_basisElt
#print axioms LeanDring.Even.isGoodCoset_iff_out_mem
#print axioms LeanDring.Even.isGoodCoset_iff_mem
#print axioms LeanDring.Even.out_mem_pairNormalizer
#print axioms LeanDring.Even.mem_fixCosetOf_of_mem_normalizer
#print axioms LeanDring.Even.goodOfMem_surjective
#print axioms LeanDring.Even.goodOfMem_eq_iff
#print axioms LeanDring.Even.card_pairNormalizer_eq_mul
#print axioms LeanDring.Even.isolates_of_witness
#print axioms LeanDring.Even.conductorAtSpecies_of
#print axioms LeanDring.Even.exists_sum_species_basisElt
#print axioms LeanDring.Even.speciesTotal_apply
#print axioms LeanDring.Even.exists_sum_species
#print axioms LeanDring.Even.dring_ringHom_ext
#print axioms LeanDring.Even.species_eq_of_mul_inv_mem_commutator
#print axioms LeanDring.Even.card_dvd_mul_fusionCount
#print axioms LeanDring.Even.pairNormalizer_top
#print axioms LeanDring.Even.species_top_eq_iff
#print axioms LeanDring.Even.speciesConductorLowerBound_top
#print axioms LeanDring.Even.commutator_le_self
#print axioms LeanDring.Even.card_fuses_left
#print axioms LeanDring.Even.isEmpty_fuses
#print axioms LeanDring.Even.card_fuses_right
#print axioms LeanDring.Even.card_fusionClass_mul_card_pairNormalizer
#print axioms LeanDring.Even.card_mul_card_pairNormalizer_dvd
#print axioms LeanDring.Even.speciesConductorLowerBound_of_selfNormalizing
#print axioms LeanDring.Even.exists_twistedSum_basisElt
#print axioms LeanDring.Even.exists_twistedSum
#print axioms LeanDring.Even.exists_twisted_fusion_sum
#print axioms LeanDring.Even.indChar_apply
#print axioms LeanDring.Even.indChar_one
#print axioms LeanDring.Even.isConjPair_map
#print axioms LeanDring.Even.indPair_congr
#print axioms LeanDring.Even.dringInd_basisElt
#print axioms LeanDring.Even.species_dringInd_basisElt
#print axioms LeanDring.Even.dringInd_basisElt_one
#print axioms LeanDring.Even.species_dringInd_eq_zero_of_not_subconj
#print axioms LeanDring.Even.mem_fixCoset_iff
#print axioms LeanDring.Even.sum_cosetSplit
#print axioms LeanDring.Even.sum_condWeight
#print axioms LeanDring.Even.species_dringInd_basisElt_mackey
#print axioms LeanDring.Even.species_dringInd
#print axioms LeanDring.Even.indSub_self_eq_top
#print axioms LeanDring.Even.species_dringInd_self
#print axioms LeanDring.Even.isolatingValue_zero
#print axioms LeanDring.Even.IsolatingValue.mul_left
#print axioms LeanDring.Even.isolates_of_isolatingValue
#print axioms LeanDring.Even.isolatingValue_of_isolates
#print axioms LeanDring.Even.isolatingValue_bot
#print axioms LeanDring.Even.boltjeIntegralityFor_of
#print axioms LeanDring.Even.speciesIsolatingWitness_of_boltje
#print axioms LeanDring.Even.speciesConductorLowerBound_of_boltje
#print axioms LeanDring.Even.conductorAtSpecies_of_boltje
#print axioms LeanDring.Even.conductorPairDictionary_of_boltje
#print axioms LeanDring.Even.isIndexValue_iff_of_boltje

-- Even/ConductorDictionary.lean: IsIndexValue in group-theoretic terms — the pair normalizer,
-- its commutator bound, and the index-value characterization.
#print axioms LeanDring.Even.conj_mem_commutator_of_mem_normalizer
#print axioms LeanDring.Even.le_pairNormalizer
#print axioms LeanDring.Even.commutator_le_pairNormalizer
#print axioms LeanDring.Even.card_commutator_dvd_card_pairNormalizer
#print axioms LeanDring.Even.pairNormalizer_bot
#print axioms LeanDring.Even.fullyFused_bot
#print axioms LeanDring.Even.isIndexValue_iff
#print axioms LeanDring.Even.isIndexValue_one
#print axioms LeanDring.Even.IsIndStarValue.transfer

-- Even/ConductorDictionaryGalois.lean: item (2), the analytic half — species values are
-- cyclotomic integers, integer points are rational species, rationality gives full fusion.
#print axioms LeanDring.MonGSet.fixedWeight_commutator
#print axioms LeanDring.MonGSet.speciesSum_mul_commutator
#print axioms LeanDring.map_commutator_subtype
#print axioms LeanDring.mem_commutator_of_coe
#print axioms LeanDring.MonRing.species_mul_commutator
#print axioms LeanDring.DRing.species_congr_coset
#print axioms LeanDring.isIntegral_speciesSum
#print axioms LeanDring.DRing.isIntegral_species
#print axioms LeanDring.exists_int_of_isIntegral_rat
#print axioms LeanDring.Even.species_exists_int
#print axioms LeanDring.Even.DRing.exists_intPoint_of_species_rat
#print axioms LeanDring.aeval_pow_eq_of_aeval_eq_rat
#print axioms LeanDring.sum_pow_eq_of_sum_eq_rat
#print axioms LeanDring.Even.fixedWeight_pow_card
#print axioms LeanDring.Even.speciesSum_sub_pow_eq_of_rat
#print axioms LeanDring.Even.species_pow_eq_of_rat_value
#print axioms LeanDring.Even.species_pow_eq_of_intPoint
#print axioms LeanDring.Even.fullyFused_of_intPoint
#print axioms LeanDring.Even.adamsStable_of_intPoint

-- Even/ConductorDictionaryProofs.lean: the ring-theoretic substrate of item (3) and the cheap
-- conductor bound — Isolates arithmetic, the trivial bound, Adams stability.
#print axioms LeanDring.Even.Isolates.add
#print axioms LeanDring.Even.Isolates.mul
#print axioms LeanDring.Even.Isolates.nsmul
#print axioms LeanDring.Even.Isolates.sub
#print axioms LeanDring.Even.conductor_dvd
#print axioms LeanDring.Even.dring_pointsSeparate
#print axioms LeanDring.Even.Isolates.unique
#print axioms LeanDring.Even.Isolates.mul_eq_nsmul
#print axioms LeanDring.Even.Isolates.mul_self
#print axioms LeanDring.Even.Isolates.nsmul_comm
#print axioms LeanDring.Even.MullerIsolation.weak
#print axioms LeanDring.Even.conductor_eq_card_of_trivialBound
#print axioms LeanDring.Even.mullerOrder_dring_eq_card'
#print axioms LeanDring.Even.orderTransfer_of_muller'
#print axioms LeanDring.Even.species_adamsStable_iff
#print axioms LeanDring.Even.IsIndexValue.pos
#print axioms LeanDring.Even.IsIndexValue.dvd_card

-- Even/CriterionT.lean: Criterion T in divisibility form — a transposition preserves a lattice
-- iff the dual pairing sees no obstruction; the ghost-lattice instance and the gauge it yields.
#print axioms LeanDring.Even.zpair
#print axioms LeanDring.Even.zpair_sub_right
#print axioms LeanDring.Even.zpair_zsmul_right
#print axioms LeanDring.Even.zpair_single
#print axioms LeanDring.Even.dualLat
#print axioms LeanDring.Even.mem_of_dual_pairing
#print axioms LeanDring.Even.mem_iff_dual_pairing
#print axioms LeanDring.Even.comp_swap_eq_sub
#print axioms LeanDring.Even.zpair_comp_swap
#print axioms LeanDring.Even.swap_preserves_iff
#print axioms LeanDring.Even.ghostLattice
#print axioms LeanDring.Even.mem_ghostLattice
#print axioms LeanDring.Even.ghost_swap_preserves_iff
#print axioms LeanDring.Even.ghostSwapGauge

-- Even/DedekindOdd.lean: Dedekind's theorem at odd order, reduced to p-groups — one of the four
-- external inputs, removed for the odd case (unconditional).
#print axioms LeanDring.Even.forall_normal_subgroupOf
#print axioms LeanDring.Even.dedekindOdd_of_pgroup
#print axioms LeanDring.Even.oddDedekind_of_pgroup

-- Even/DedekindOrderP.lean: in a Dedekind p-group every element of order p is central — the
-- conjugation-exponent computation behind DedekindOddPGroup (unconditional).
#print axioms LeanDring.Even.conj_pow_iterate
#print axioms LeanDring.Even.centralizes_of_orderOf_eq_prime
#print axioms LeanDring.Even.exists_conj_exponent_one_mod_prime

-- Even/Descent.lean: descent is well-definedness on shadow fibres; at odd order the Burnside
-- shadow is the identity, so descent is automatic.
#print axioms LeanDring.Even.shadowDescends_iff_congr
#print axioms LeanDring.Even.burnsideShadow_eq_id_of_odd
#print axioms LeanDring.Even.shadowDescends_of_odd

-- Even/Functorial.lean: functoriality of monomial G-sets and fibered Burnside rings — pullback
-- along a homomorphism, the congr isomorphism, its two commutation squares, and the sandwich
-- theorem (global and per-pair) deriving shadow recognition from 2-group rigidity.
#print axioms LeanDring.MonGSet.comap
#print axioms LeanDring.MonGSet.IsIso.comap
#print axioms LeanDring.MonGSet.comapSkelHom
#print axioms LeanDring.MonGSet.comap_comap_isIso
#print axioms LeanDring.MonGSet.comap_id_isIso
#print axioms LeanDring.MonGSet.skelCongr
#print axioms LeanDring.MonGSet.comapSkelHom_ofFinHom
#print axioms LeanDring.MonGSet.forgetHom_comapSkelHom
#print axioms LeanDring.MonRing.congr
#print axioms LeanDring.MonRing.congr_eta
#print axioms LeanDring.MonRing.forget_congr
#print axioms LeanDring.Even.burnsideShadow_intPointEquiv_congr
#print axioms LeanDring.Even.TwoGroupRigidity
#print axioms LeanDring.Even.shadowRecognition_of_rigidity
#print axioms LeanDring.Even.twoGroupDtoB_of_rigidity
#print axioms LeanDring.Even.exists_descending_identification_of_mulEquiv
#print axioms LeanDring.Even.shadowRecognition_pair_of_rigidity

-- Even/GaugeGroup.lean: the gauge group Γ(L) of a lattice, Theorem P (its dual characterization),
-- the transposition test, and the point-push / fixed-point-set recognition data.
#print axioms LeanDring.Even.zpair_comp_perm
#print axioms LeanDring.Even.comp_perm_pow_mem
#print axioms LeanDring.Even.comp_perm_symm_mem
#print axioms LeanDring.Even.latticePermGroup
#print axioms LeanDring.Even.mem_latticePermGroup
#print axioms LeanDring.Even.mem_latticePermGroup_iff_dual
#print axioms LeanDring.Even.swap_mem_latticePermGroup_iff
#print axioms LeanDring.Even.pointPush
#print axioms LeanDring.Even.fixedPointSet
#print axioms LeanDring.Even.intPointEquiv_mem_fixedPointSet

-- Even/Intrinsic.lean: aligned transport — a ring isomorphism carrying η(B(G)) onto η(B(H))
-- induces B(G) ≅ B(H); η-recognition implies D ⇒ B for 2-groups, and rigidity implies it.
#print axioms LeanDring.MonRing.burnsideEquivOfMapsEta
#print axioms LeanDring.Even.EtaRecognition
#print axioms LeanDring.Even.twoGroupDtoB_of_etaRecognition
#print axioms LeanDring.Even.etaRecognition_of_rigidity

-- Even/Linkage.lean: the linkage layer — integer points, the linkage subgroup and its transport,
-- higher-arity linkage, the rational kernel D_F, and the identification of D_F with the ghost
-- lattice together with the L1 mechanism turning a linkage-preserving permutation into an auto.
#print axioms LeanDring.Even.IntPoint
#print axioms LeanDring.Even.intPointEquiv
#print axioms LeanDring.Even.diffHom
#print axioms LeanDring.Even.linkSubgroup
#print axioms LeanDring.Even.mem_linkSubgroup
#print axioms LeanDring.Even.linkSubgroup_comm
#print axioms LeanDring.Even.linkSubgroup_intPointEquiv
#print axioms LeanDring.Even.exists_linkPreserving_bijection
#print axioms LeanDring.Even.sumHom
#print axioms LeanDring.Even.sumLinkSubgroup
#print axioms LeanDring.Even.sumLinkSubgroup_map
#print axioms LeanDring.Even.ratKernel
#print axioms LeanDring.Even.mem_ratKernel
#print axioms LeanDring.Even.ratKernel_comap
#print axioms LeanDring.Even.ratKernel_map
#print axioms LeanDring.Even.DF
#print axioms LeanDring.Even.dfCongr
#print axioms LeanDring.Even.ghost
#print axioms LeanDring.Even.ker_ghost
#print axioms LeanDring.Even.dfEquivGhostRange
#print axioms LeanDring.Even.reindex
#print axioms LeanDring.Even.ghostRangeAutoOfPreserving

-- Even/MarksSlice.lean: the collapse identity ψᴺ = η ∘ forget, the map B(G) → fixed slice, and
-- MarksOntoSlice for finite 2-groups — the capstone feeding Assembly's payoff.
#print axioms LeanDring.Even.psi_eq_eta_forget
#print axioms LeanDring.Even.symm_pointPush_psi_pow
#print axioms LeanDring.Even.burnsideToSlice
#print axioms LeanDring.Even.burnsideToSlice_injective
#print axioms LeanDring.Even.burnsideToSlice_surjective
#print axioms LeanDring.Even.marksOntoSlice_of_exponent
#print axioms LeanDring.Even.marksOntoSlice_of_isPGroup
#print axioms LeanDring.Even.burnsideNonempty_of_sliceRecognition_of_isPGroup

-- Even/MullerBound.lean: Müller Satz 2.3.1 proved — the triangularity/peel argument giving the
-- trivial-point bound MullerTrivialBound unconditionally, and order transfer from isolation.
#print axioms LeanDring.Even.regularGSet
#print axioms LeanDring.Even.fix_regularGSet_of_ne_bot
#print axioms LeanDring.Even.card_orbit_of_stabilizer_eq_bot
#print axioms LeanDring.Even.fix_orbit_eq_zero_of_stabilizer_eq_bot
#print axioms LeanDring.Even.exists_matched_point_ne_bot
#print axioms LeanDring.Even.dvd_card_sub_card_of_fix_eq
#print axioms LeanDring.Even.dvd_mark_bot_of_mark_eq_zero
#print axioms LeanDring.Even.trivialPoint
#print axioms LeanDring.Even.complexify_trivialPoint
#print axioms LeanDring.Even.species_ne_complexify_trivialPoint
#print axioms LeanDring.Even.dvd_of_isolates_trivialPoint
#print axioms LeanDring.Even.mullerTrivialBound
#print axioms LeanDring.Even.mullerOrder_dring_eq_card_of_isolation
#print axioms LeanDring.Even.orderTransfer_of_mullerIsolation

-- Even/MullerIsolation.lean: the trivial pair isolates |G|, the residual conductor bound, and
-- the species-isolation route to MullerIsolation and hence OrderTransfer.
#print axioms LeanDring.Even.regularClass
#print axioms LeanDring.Even.isolates_trivialPoint
#print axioms LeanDring.Even.conductor_trivialPoint
#print axioms LeanDring.Even.MullerConductorBound
#print axioms LeanDring.Even.mullerConductorBound_of_isolation
#print axioms LeanDring.Even.mullerOrder_eq_card_of_conductorBound
#print axioms LeanDring.Even.orderTransfer_of_conductorBound
#print axioms LeanDring.Even.SpeciesIsolation
#print axioms LeanDring.Even.mullerIsolation_of_speciesIsolation
#print axioms LeanDring.Even.orderTransfer_of_speciesIsolation

-- Even/OrderTransfer.lean: Müller's conductor and order — Isolates, conductor, mullerOrder and
-- its ring-isomorphism invariance, the two named Props, and order transfer from them.
#print axioms LeanDring.Even.complexify
#print axioms LeanDring.Even.Isolates
#print axioms LeanDring.Even.conductor
#print axioms LeanDring.Even.mullerOrder
#print axioms LeanDring.Even.Isolates.map
#print axioms LeanDring.Even.Isolates.comp_equiv
#print axioms LeanDring.Even.conductor_comp_equiv
#print axioms LeanDring.Even.mullerOrder_eq_of_ringEquiv
#print axioms LeanDring.Even.conductorMultiplicity
#print axioms LeanDring.Even.conductorMultiplicity_eq_of_ringEquiv
#print axioms LeanDring.Even.MullerIsolation
#print axioms LeanDring.Even.MullerTrivialBound
#print axioms LeanDring.Even.mullerOrder_dring_eq_card
#print axioms LeanDring.Even.orderTransfer_of_muller

-- Even/Profiles.lean: linkage profiles — the lattice reading of the linkage subgroup, its
-- transport, and the fibre-separating profile contract giving B(G) ≅ B(H) for 2-groups.
#print axioms LeanDring.Even.mem_linkSubgroup_iff_lattice
#print axioms LeanDring.Even.linkSubgroup_of_identifies
#print axioms LeanDring.Even.shadowDescends_of_profile
#print axioms LeanDring.Even.burnsideNonempty_of_profile

-- Even/Separation.lean: the extraspecial stratum — IsExtraspecial, the OrderTransfer and
-- RankSeparation Props, and recognition ⟹ D ⇒ B on that stratum.
#print axioms LeanDring.IsExtraspecial
#print axioms LeanDring.Even.OrderTransfer
#print axioms LeanDring.Even.RankSeparation
#print axioms LeanDring.Even.ExtraspecialRecognition
#print axioms LeanDring.Even.ExtraspecialRigidity
#print axioms LeanDring.Even.extraspecialRecognition_of_rankSeparation
#print axioms LeanDring.Even.dtoB_extraspecial_of_recognition

-- Even/Shadow.lean: the Burnside shadow — forget ∘ ψᵏ = forget, the idempotent projection on
-- integer points, point-level FIX-ψ², and slice recognition ⟹ D ⇒ B for 2-groups.
#print axioms LeanDring.Even.forget_psi
#print axioms LeanDring.Even.burnsideShadow
#print axioms LeanDring.Even.burnsideShadow_idempotent
#print axioms LeanDring.Even.pointPush_psi_eq_burnsideShadow
#print axioms LeanDring.Even.burnsideShadow_pointPush_psi
#print axioms LeanDring.Even.pointPush_psi_burnsideShadow
#print axioms LeanDring.Even.pointPush_psi_pow_fixed
#print axioms LeanDring.Even.pointPush_psi_two_fixed_iff
#print axioms LeanDring.Even.sliceFix_iff_comp_shadow
#print axioms LeanDring.Even.burnsideNonempty_of_exists_sliceIdentification
#print axioms LeanDring.Even.SliceRecognition
#print axioms LeanDring.Even.twoGroupDtoB_of_sliceRecognition

-- Even/SimpleRigidity.lean: the simple-group lane — the conductor reading of solvability
-- detection, the perfect self-normalizing class count, and the simple-group theorem.
#print axioms LeanDring.Even.card_perfectSelfNormalizingClass_eq_of_dringEquiv
#print axioms LeanDring.Even.solvabilityDetector_of_conductorDictionary
#print axioms LeanDring.Even.commutator_self_le
#print axioms LeanDring.Even.solvabilityDetector_of_pairDictionary
#print axioms LeanDring.Even.conductorMultiplicity_card_ne_zero
#print axioms LeanDring.Even.not_isSolvable_of_dringEquiv_of_simple
#print axioms LeanDring.Even.simpleDRigidity_of_exceptionSeparation
#print axioms LeanDring.Even.fittingFreeDetector_of_topConductor
#print axioms LeanDring.Even.fittingFreeOrderForcesSimple_of_card_sixty
#print axioms LeanDring.Even.twinSeparation_iff_forall
#print axioms LeanDring.Even.simpleGroupTheorem
#print axioms LeanDring.Even.simpleGroupTheorem_dtoB
#print axioms LeanDring.Even.simpleGroupTheorem_of_twinSeparationFor

-- Even/SpeciesRationality.lean: fully fused ⟹ rational, the backward half of
-- ConductorPairDictionary.
#print axioms LeanDring.rat_of_pow_twist_eq
#print axioms LeanDring.Even.species_congr_subgroup
#print axioms LeanDring.Even.species_conj_of_mem_normalizer
#print axioms LeanDring.Even.species_pow_eq_of_fullyFused
#print axioms LeanDring.Even.species_rat_of_fullyFused
#print axioms LeanDring.Even.exists_intPoint_of_fullyFused
#print axioms LeanDring.Even.fullyFused_iff_exists_intPoint
#print axioms LeanDring.Even.mark_eq_of_species_eq
#print axioms LeanDring.Even.conductorPairDictionary_backward
#print axioms LeanDring.Even.conductorPairDictionary_of

-- Even/SpeciesSeparation.lean: item (1) — SpeciesPairSeparation discharged: equal species force
-- N_G(H)-conjugacy modulo ⁅H, H⁆.
#print axioms LeanDring.Even.evalChar_injective
#print axioms LeanDring.Even.inv_out_mem_normalizer
#print axioms LeanDring.Even.one_mem_fixCoset
#print axioms LeanDring.Even.of_conjRep_one
#print axioms LeanDring.Even.species_basisElt_self
#print axioms LeanDring.Even.speciesPairSeparation
#print axioms LeanDring.Even.fullyFused_of_intPoint'

-- Even/SpeciesSurjectivity.lean: counting the points of D(G) — the basis/character-independence
-- upper bound and the forward direction of the conductor pair dictionary.
#print axioms LeanDring.Even.linearIndependent_coords
#print axioms LeanDring.Even.card_ringHom_le
#print axioms LeanDring.Even.eq_of_basis_indexed_family
#print axioms LeanDring.Even.ringHom_eq_species_of_enough
#print axioms LeanDring.Even.intPoint_eq_species_of_enough
#print axioms LeanDring.Even.card_species_le
#print axioms LeanDring.Even.conductorPairDictionary_forward

-- Even/SubgroupMoebius.lean: the Möbius function of the subgroup lattice, step one of the
-- Boltje programme (unconditional).
#print axioms LeanDring.Even.Subgroup.mu_self
#print axioms LeanDring.Even.Subgroup.sum_mu_Icc
#print axioms LeanDring.Even.Subgroup.sum_mu_Icc_of_ne

-- Even/TIR.lean: the shadow criterion — the slice condition holds iff the shadow descends; shadow
-- recognition ⟹ D ⇒ B for 2-groups.
#print axioms LeanDring.Even.burnsideShadow_eq_iff
#print axioms LeanDring.Even.ghost_eta_fixed
#print axioms LeanDring.Even.exists_ghost_eta_of_fixed
#print axioms LeanDring.Even.sliceCondition_iff_shadowDescends
#print axioms LeanDring.Even.ShadowRecognition
#print axioms LeanDring.Even.twoGroupDtoB_of_shadowRecognition

-- Even/Target.lean: the targets themselves — DtoBConjecture, TwoGroupDtoB, the proven odd instance,
-- rigidity ⟹ D ⇒ B, and the ψ²-transport engine behind the 2-group reduction.
#print axioms LeanDring.Even.exists_common_two_exponent
#print axioms LeanDring.Even.DtoBConjecture
#print axioms LeanDring.Even.TwoGroupDtoB
#print axioms LeanDring.Even.dtoB_of_odd
#print axioms LeanDring.Even.dtoB_of_rigidity
#print axioms LeanDring.Even.burnsideEquivOfPsiTwoConjugate
#print axioms LeanDring.Even.twoGroupDtoB_of_psiTwoRecognition

-- Even/Transport.lean: the transport chain — the exclusion principle, N2 in formal form,
-- IdentifiesLattices and the gauge torsor, and the slice where B lives.
#print axioms LeanDring.Even.not_mem_latticePermGroup_of_witness
#print axioms LeanDring.Even.not_mem_latticePermGroup_of_dual_witness
#print axioms LeanDring.Even.ghost_comp_intPointEquiv
#print axioms LeanDring.Even.comp_intPointEquiv_mem_ghostLattice
#print axioms LeanDring.Even.intPointEquiv_symm
#print axioms LeanDring.Even.comp_intPointEquiv_mem_ghostLattice_iff
#print axioms LeanDring.Even.IdentifiesLattices
#print axioms LeanDring.Even.identifiesLattices_intPointEquiv
#print axioms LeanDring.Even.identifies_symm_trans_mem
#print axioms LeanDring.Even.sliceFix
#print axioms LeanDring.Even.ghost_mem_sliceFix

-- Even/Triples.lean: primal and dual evaluation subgroups and their transport, plus the TCR
-- class-constancy identities for ghost vectors of Burnside elements.
#print axioms LeanDring.Even.ghostEvalSubgroup
#print axioms LeanDring.Even.ghostEvalSubgroup_of_identifies
#print axioms LeanDring.Even.dualEvalSubgroup
#print axioms LeanDring.Even.dualEvalSubgroup_of_identifies
#print axioms LeanDring.Even.ghost_eta_constantOnClasses
#print axioms LeanDring.Even.ghost_eta_comp_eq

-- Even/ZModUnitsPPow.lean: units of ZMod (p^k) of p-power order are ≡ 1 mod p — the Aut(C_{p^k})
-- input of DedekindOddPGroup (unconditional).
#print axioms LeanDring.Even.unitsReduce_eq_one_of_orderOf_eq_pow
