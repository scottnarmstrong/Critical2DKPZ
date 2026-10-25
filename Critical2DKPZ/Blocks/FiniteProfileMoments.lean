/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.LastCollision
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Collision expansion for a finite signed initial profile -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Blocks


/-- The second moment of a finite signed-profile pairing expands over its first collision.
Integrability follows by summing `Collision.integrable_terminalPairProduct` over the profiles. -/
theorem finite_terminalProfile_sq_integral_firstCollision (β : ℝ) (a n : ℕ)
    (A : Finset Site) (ν f : Site → ℝ) :
    (∫ ω, (∑ w ∈ A, ν w * (∑' z, pointToPoint β a n w z ω * f z)) ^ 2 ∂disorderLaw) =
      (∑ w ∈ A, ν w * Collision.terminalWalkMean n w f) ^ 2 +
        Polymer.sigmaSq β * ∑ s ∈ Finset.Icc 1 n, ∑' x,
          Collision.heatEvolveFinite s A ν x ^ 2 *
            Collision.terminalPairMoment β (n - s) x x f f := by
  have hInt (w v : Site) : Integrable (fun ω =>
      (ν w * (∑' z, pointToPoint β a n w z ω * f z)) *
      (ν v * (∑' z, pointToPoint β a n v z ω * f z))) disorderLaw := by
    convert (Collision.integrable_terminalPairProduct β a n w v f f).const_mul (ν w * ν v)
      using 1
    funext ω
    ring
  have hmom :
      (∫ ω, (∑ w ∈ A, ν w * (∑' z, pointToPoint β a n w z ω * f z)) ^ 2 ∂disorderLaw) =
      ∑ w ∈ A, ∑ v ∈ A, (ν w * ν v) * Collision.terminalPairMoment β n w v f f := by
    simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [integral_finsetSum _ (fun w _ => integrable_finsetSum _ (fun v _ => hInt w v))]
    apply Finset.sum_congr rfl
    intro w _
    rw [integral_finsetSum _ (fun v _ => hInt w v)]
    apply Finset.sum_congr rfl
    intro v _
    rw [show (fun ω => (ν w * (∑' z, pointToPoint β a n w z ω * f z)) *
        (ν v * (∑' z, pointToPoint β a n v z ω * f z))) =
        (fun ω => (ν w * ν v) * ((∑' z, pointToPoint β a n w z ω * f z) *
          (∑' z, pointToPoint β a n v z ω * f z))) by funext ω; ring,
      integral_const_mul, Collision.terminalPairMoment_timeShift]
  have hfree : (∑ w ∈ A, ν w * Collision.terminalWalkMean n w f) ^ 2 =
      ∑ w ∈ A, ∑ v ∈ A, (ν w * ν v) *
        (Collision.terminalWalkMean n w f * Collision.terminalWalkMean n v f) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hcollision := Collision.terminalProfile_firstCollision_finite β n A ν f
  simp only [mul_sub, Finset.sum_sub_distrib] at hcollision
  rw [← hfree] at hcollision
  rw [hmom]
  linarith only [hcollision]

/-- The second moment of a finite signed-profile pairing expands over its first and last collisions. -/
theorem finite_terminalProfile_sq_integral_firstLastCollision (β : ℝ) (a n : ℕ)
    (A : Finset Site) (ν f : Site → ℝ) :
    (∫ ω, (∑ w ∈ A, ν w * (∑' z, pointToPoint β a n w z ω * f z)) ^ 2 ∂disorderLaw) =
      (∑ w ∈ A, ν w * Collision.terminalWalkMean n w f) ^ 2 +
        Polymer.sigmaSq β * ∑ s ∈ Finset.Icc 1 n, ∑' x,
          Collision.heatEvolveFinite s A ν x ^ 2 *
            (∑ r : Fin (n - s + 1), ∑' y,
              Collision.spatialRenewal (Polymer.sigmaSq β) r.val (y - x) *
                Collision.terminalWalkMean (n - s - r.val) y f ^ 2) := by
  rw [finite_terminalProfile_sq_integral_firstCollision]
  apply congrArg (fun z : ℝ => (∑ w ∈ A, ν w * Collision.terminalWalkMean n w f) ^ 2 +
    Polymer.sigmaSq β * z)
  apply Finset.sum_congr rfl
  intro s _
  apply tsum_congr
  intro x
  apply congrArg (fun z : ℝ => Collision.heatEvolveFinite s A ν x ^ 2 * z)
  simpa only [Collision.terminalPairMoment, pow_two] using
    terminalProfile_sq_integral_lastCollision_zeroIncluded β 0 (n - s) x f


end Critical2DKPZ.Blocks
