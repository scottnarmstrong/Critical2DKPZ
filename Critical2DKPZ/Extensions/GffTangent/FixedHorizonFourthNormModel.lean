/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthOperatorBounds
public import Critical2DKPZ.MomentBounds.CCR25BoundaryVectorBoundMain
public import Critical2DKPZ.MomentBounds.CCR25InteractingOperatorBound
public import Critical2DKPZ.MomentBounds.CCR25FreeOperatorBound
public import Critical2DKPZ.MomentBounds.AiiKCollisionWeight
public import Critical2DKPZ.MomentBounds.AiiKDisorderMoment
import Mathlib.Tactic

/-! # Actual exponential-weight operator bounds for the CCR remainder -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

attribute [local instance] Classical.propDecidable

/-- The universal fourth-order boundary constant from the proved CCR estimate. -/
def fourthBoundaryConstant : ℝ := Classical.choose (finiteLpNorm_hattedReplicaBoundaryVector_le 4 (by norm_num))
/-- The universal fourth-order interaction constant. -/
def fourthInteractionConstant : ℝ := Classical.choose (finiteLpNorm_weighted_hattedInteractingReplicaKernelAbs_le 4 (by norm_num))
/-- The universal fourth-order free transition constant. -/
def fourthFreeConstant : ℝ := Classical.choose (finiteLpNorm_weighted_hattedFreeReplicaKernel_le 4 (by norm_num))
/-- The universal collision-weight constant. -/
def fourthCollisionConstant : ℝ := Classical.choose finiteLpNorm_weight_mul_collisionIndicator_le
/-- The small-coupling threshold for all fourth-order partition moments. -/
def fourthMomentSigmaThreshold : ℝ := Classical.choose (abs_replicaPartitionDisorderMoment_le_sigmaSq 4)

/-- All chosen operator constants are at least one, and the threshold is positive. -/
theorem fourth_norm_constants_pos :
    1 ≤ fourthBoundaryConstant ∧ 1 ≤ fourthInteractionConstant ∧
      1 ≤ fourthFreeConstant ∧ 1 ≤ fourthCollisionConstant ∧ 0 < fourthMomentSigmaThreshold :=
  ⟨(Classical.choose_spec (finiteLpNorm_hattedReplicaBoundaryVector_le 4 (by norm_num))).1,
    (Classical.choose_spec (finiteLpNorm_weighted_hattedInteractingReplicaKernelAbs_le 4 (by norm_num))).1,
    (Classical.choose_spec (finiteLpNorm_weighted_hattedFreeReplicaKernel_le 4 (by norm_num))).1,
    (Classical.choose_spec finiteLpNorm_weight_mul_collisionIndicator_le).1,
    (Classical.choose_spec (abs_replicaPartitionDisorderMoment_le_sigmaSq 4)).1⟩

/-- The boundary cost at the exponential weight t. -/
def fourthBoundaryCost (t : ℝ) (L : ℕ) (S : Finset Site) (φ : Site → ℝ) : ℝ :=
  fourthBoundaryConstant * Real.exp (fourthBoundaryConstant * t ^ 2 * L) * 2 *
    (∑ y ∈ S, φ y * Real.exp (t * ‖siteToPlane y‖)) *
    finiteLpNorm S 2 (fun y => φ y * Real.exp (t * ‖siteToPlane y‖)) ^ 3

/-- The collision-vector cost at the exponential weight t. -/
def fourthCollisionCost (t : ℝ) : ℝ := (fourthCollisionConstant / t ^ 2) ^ ((3 : ℝ) / 2)

/-- The actual subcritical interacting-operator cost. -/
def fourthInteractionCost (t : ℝ) (L : ℕ) (β : ℝ) : ℝ :=
  1 + fourthInteractionConstant * Real.exp (fourthInteractionConstant * t ^ 2 * L) *
    (Polymer.sigmaSq β * replicaOverlap L / (1 - Polymer.sigmaSq β * replicaOverlap L))

/-- The free-operator cost at Holder exponents two and two. -/
def fourthFreeCost (t : ℝ) (L : ℕ) : ℝ :=
  4 * fourthFreeConstant * Real.exp (fourthFreeConstant * t ^ 2 * L)

/-- Zero Laplace damping recovers the actual overlap. -/
theorem dampedOverlap_zero_eq_replicaOverlap (L : ℕ) : dampedOverlap 0 L = replicaOverlap L := by
  simp only [dampedOverlap, replicaOverlap, zero_mul, neg_zero, Real.exp_zero, one_mul]

/-- The main library's proved finite operator estimates furnish the complete
fourth-word bound bundle for the actual boundary and collision vectors. -/
def fourthWordNormModel (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) (L : ℕ) (β : ℝ)
    (hσ : Polymer.sigmaSq β ≤ fourthMomentSigmaThreshold)
    (hgap : Polymer.sigmaSq β * replicaOverlap L < 1)
    (S : Finset Site) (φ : Site → ℝ) (hφ : ∀ y, 0 ≤ φ y)
    (s : Finset (LatticeConfiguration 4)) :
    FourthWordOperatorBounds s L β
      (fun I => hattedReplicaBoundaryVector L I S φ) collisionIndicator := by
  obtain ⟨hcB, hcI, hcQ, hcC, _⟩ := fourth_norm_constants_pos
  have hden : 0 < 1 - Polymer.sigmaSq β * replicaOverlap L := sub_pos.mpr hgap
  have hR : 0 ≤ replicaOverlap L := Finset.sum_nonneg (fun r _ => Critical2DKPZ.srwKernel_nonneg _ _)
  have hMom (I : ReplicaPartition 4) (hI : I ≠ ⊥) :
      |replicaPartitionDisorderMoment β I| ≤ Polymer.sigmaSq β :=
    (Classical.choose_spec (abs_replicaPartitionDisorderMoment_le_sigmaSq 4)).2 β hσ I hI
  refine {
    weight := replicaExponentialWeight t
    weight_pos := fun x _ => replicaExponentialWeight_pos t x
    interactionCost := fourthInteractionCost t L β
    freeCost := fourthFreeCost t L
    leftCost := fourthBoundaryCost t L S φ
    rightCost := fourthCollisionCost t
    interactionCost_nonneg := ?_
    freeCost_nonneg := ?_
    leftCost_nonneg := ?_
    rightCost_nonneg := ?_
    left_bound := ?_
    right_bound := ?_
    interaction_bound := ?_
    free_bound := ?_
    left_nonneg := fun I x => hattedReplicaBoundaryVector_nonneg L I S φ (fun y _ => hφ y) x
    right_nonneg := ?_ }
  · unfold fourthInteractionCost
    exact add_nonneg zero_le_one (mul_nonneg
      (mul_nonneg (zero_le_one.trans hcI) (Real.exp_nonneg _))
      (div_nonneg (mul_nonneg (sigmaSq_nonneg β) hR) hden.le))
  · unfold fourthFreeCost
    positivity
  · have hsum : 0 ≤ ∑ y ∈ S, φ y * Real.exp (t * ‖siteToPlane y‖) :=
      Finset.sum_nonneg (fun y _ => mul_nonneg (hφ y) (Real.exp_nonneg _))
    have hnorm := finiteLpNorm_nonneg S 2 (fun y => φ y * Real.exp (t * ‖siteToPlane y‖))
    unfold fourthBoundaryCost
    positivity
  · exact Real.rpow_nonneg (by positivity) _
  · intro I hI
    have h := (Classical.choose_spec (finiteLpNorm_hattedReplicaBoundaryVector_le 4 (by norm_num))).2
      t ht.le L 2 (by norm_num) S φ hφ s I hI
    simpa only [fourthBoundaryCost, fourthBoundaryConstant,
      show (2 : ℝ) / (2 - 1) = 2 by norm_num, show (4 - 1 : ℕ) = 3 by norm_num] using h
  · intro I hI
    have h := (Classical.choose_spec finiteLpNorm_weight_mul_collisionIndicator_le).2
      4 t ht ht1 2 (by norm_num) s I hI
    simpa only [fourthCollisionCost, fourthCollisionConstant, Nat.cast_ofNat,
      show (((4 : ℝ) - 1) / 2) = 3 / 2 by norm_num] using h
  · intro I hI f
    have h := (Classical.choose_spec (finiteLpNorm_weighted_hattedInteractingReplicaKernelAbs_le 4
      (by norm_num))).2 t ht.le L 0 β (le_refl 0) hMom
        (by simpa only [dampedOverlap_zero_eq_replicaOverlap] using hgap) 2 (by norm_num) s I hI f
    simpa only [ccr25LabelKernel, fourthInteractionCost, fourthInteractionConstant,
      dampedOverlap_zero_eq_replicaOverlap] using h
  · intro I J hI hJ hIJ f
    have h := (Classical.choose_spec (finiteLpNorm_weighted_hattedFreeReplicaKernel_le 4
      (by norm_num))).2 t ht.le L 2 (by norm_num) s I J hI hJ hIJ f
    apply h.trans_eq
    dsimp only [fourthFreeCost, fourthFreeConstant]
    norm_num
    ring_nf
    simp
  · intro I x
    unfold collisionIndicator
    split_ifs <;> norm_num

end Critical2DKPZ.Extensions.GffTangent
