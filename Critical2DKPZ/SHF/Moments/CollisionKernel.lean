/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionExpansion
import Mathlib.Tactic

/-! # Finite collision-subset coefficients of polymer joint moments -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

/-- The independent-walk coefficient for a prescribed set of time/pair collisions. -/
def collisionSubsetCoefficient (n h : ℕ) (A : Finset (ℕ × CollisionPair h))
    (w z : Fin h → Site) : ℝ :=
  ∑ s : Fin h → Fin n → Fin 4,
    ((4 : ℝ)⁻¹ ^ n) ^ h * (∏ e ∈ A, edgeIndicator w s e) *
      ∏ i, if walkPosition (w i) (s i) n = z i then 1 else 0

/-- The coefficient of a prescribed finite collision subset is nonnegative. -/
theorem collisionSubsetCoefficient_nonneg (n h : ℕ) (A : Finset (ℕ × CollisionPair h))
    (w z : Fin h → Site) : 0 ≤ collisionSubsetCoefficient n h A w z := by
  unfold collisionSubsetCoefficient
  apply Finset.sum_nonneg
  intro s _
  apply mul_nonneg
  · exact mul_nonneg (by positivity)
      (Finset.prod_nonneg fun e _ => edgeIndicator_nonneg w s e)
  · exact Finset.prod_nonneg fun i _ => by split_ifs <;> norm_num

/-- The point-to-point joint moment equals its finite collision-subset expansion. -/
theorem pointToPoint_collision_expansion (β : ℝ) (a n h : ℕ) (w z : Fin h → Site) :
    (∫ ω, ∏ i, pointToPoint β a n (w i) (z i) ω ∂disorderLaw) =
      ∑ A ∈ (collisionEdges n h).powerset,
        sigmaSq β ^ A.card * collisionSubsetCoefficient n h A w z := by
  rw [pointToPoint_replica]
  simp_rw [replica_weight_collision_expansion, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A _
  rw [collisionSubsetCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The expansion has nonnegative coefficients for every real inverse temperature. -/
theorem collision_term_nonneg (β : ℝ) (n h : ℕ) (A : Finset (ℕ × CollisionPair h))
    (w z : Fin h → Site) : 0 ≤ sigmaSq β ^ A.card * collisionSubsetCoefficient n h A w z := by
  have hσ : 0 ≤ sigmaSq β := sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
  exact mul_nonneg (pow_nonneg hσ _) (collisionSubsetCoefficient_nonneg n h A w z)

end Critical2DKPZ.SHF.Moments
