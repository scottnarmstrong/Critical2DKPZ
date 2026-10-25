/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthMomentBound
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonFourthCostLimits
import Mathlib.Tactic

/-! # Quasi-critical normalization of the finite-volume fourth moment -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.MomentBounds
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- Scaling the finite entrance fluctuation scales every integral moment. -/
theorem integral_pow_finiteEntranceFluctuation_scale (β c : ℝ) (a n : ℕ)
    (S : Finset Site) (φ : Site → ℝ) (k : ℕ) :
    (∫ ω, finiteEntranceFluctuation β c a n S φ ω ^ k ∂disorderLaw) =
      c ^ k * ∫ ω, finiteEntranceFluctuation β 1 a n S φ ω ^ k ∂disorderLaw := by
  have he (ω : Disorder) : finiteEntranceFluctuation β c a n S φ ω =
      c * finiteEntranceFluctuation β 1 a n S φ ω := by
    simp only [finiteEntranceFluctuation, one_mul]
  simp_rw [he, mul_pow]
  exact integral_const_mul _ _

private theorem normalized_fourth_bound_algebra (l σ A U Q D H E : ℝ)
    (hl : l ≠ 0) :
    l ^ 2 * (D * A * σ ^ 2 +
      (2 : ℝ) ^ 32 * (σ ^ 2 * E + H * σ ^ 2 * Real.sqrt σ * (D * U ^ 2 * Q)) +
      D * A ^ 3 * Q ^ 2 * σ ^ 3 / (1 - (A * σ) * Q)) =
    (2 : ℝ) ^ 32 * (l * σ) ^ 2 * E +
      D * ((l * σ * A) * (l * σ) +
        (2 : ℝ) ^ 32 * H * (l * σ * U) ^ 2 * Real.sqrt σ * Q +
        ((l * σ * A) ^ 3 * Q ^ 2 / l) / (1 - (A * σ) * Q)) := by
  field_simp
  ring

/-- The complete scaled fourth-moment estimate, with the sharp leading
term separated from the explicit vanishing remainder coefficient. -/
theorem integral_fourth_sqrt_finiteEntranceFluctuation_le
    (N L : ℕ) (β l : ℝ) (hl : 0 < l)
    (S : Finset Site) (φ : Site → ℝ)
    (hφ : ∀ y, 0 ≤ φ y) (hS : ∀ w ∉ S, φ w = 0)
    {B : ℝ} (hB : 0 ≤ B) (hφB : ∀ y ∈ S, φ y ≤ B)
    (ht : 0 < fourthWeightScale N) (ht1 : fourthWeightScale N ≤ 1)
    (hσ : Polymer.sigmaSq β ≤ min 1 fourthMomentSigmaThreshold)
    (hgap : Polymer.sigmaSq β * replicaOverlap L < 1)
    (hsmall : (ccr25GaussianFiniteWordOperatorScale 4
      (fourthInteractionCost (fourthWeightScale N) L β) * Polymer.sigmaSq β) *
        fourthFreeCost (fourthWeightScale N) L < 1) :
    (∫ ω, finiteEntranceFluctuation β (Real.sqrt l) 0 L S φ ω ^ 4 ∂disorderLaw) ≤
      (2 : ℝ) ^ 32 * (l * Polymer.sigmaSq β * Renewal.freeSecondMoment β L) ^ 2 *
        (L : ℝ) ^ 2 * (B * ∑ y ∈ S, φ y) ^ 2 +
      (fourthBoundaryCost (fourthWeightScale N) L S φ *
        fourthCollisionCost (fourthWeightScale N)) * fourthRemainderCoefficient l β N L := by
  let b := fourthWordNormModel (fourthWeightScale N) ht ht1 L β
    (hσ.trans (min_le_right _ _)) hgap S φ hφ (configBox 4 S L)
  have h := integral_fourth_finiteEntranceFluctuation_le β L S φ hφ hS hB hφB b
    (hσ.trans (min_le_left _ _)) hsmall
  rw [integral_pow_finiteEntranceFluctuation_scale]
  have hsqrt : Real.sqrt l ^ 4 = l ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hl.le]
  rw [hsqrt]
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg l)).trans_eq
  dsimp only [b, fourthWordNormModel]
  have ha := normalized_fourth_bound_algebra l (Polymer.sigmaSq β)
    (ccr25GaussianFiniteWordOperatorScale 4 (fourthInteractionCost (fourthWeightScale N) L β))
    (fourthInteractionCost (fourthWeightScale N) L β)
    (fourthFreeCost (fourthWeightScale N) L)
    (fourthBoundaryCost (fourthWeightScale N) L S φ * fourthCollisionCost (fourthWeightScale N))
    ((max 1 (ccr25GaussianMomentUniformConstant 4)) ^ 8)
    ((L : ℝ) ^ 2 * Renewal.freeSecondMoment β L ^ 2 * (B * ∑ y ∈ S, φ y) ^ 2) hl.ne'
  dsimp only [fourthRemainderCoefficient]
  convert ha using 1 <;> ring

end Critical2DKPZ.Extensions.GffTangent
