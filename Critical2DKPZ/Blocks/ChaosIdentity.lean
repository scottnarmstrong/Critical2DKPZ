/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.ChaosIdentityMonotone
import Critical2DKPZ.Blocks.GridCongruence

/-! # Closed-discrepancy second moments

The second moment of a closed discrepancy equals a sum over collision strings with fixed first
and last collisions; its square is integrable by `integrable_sq_closedDiscrepancy`. -/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.Blocks

/-- The closed-discrepancy square moment is the first/last collision string sum. -/
theorem closedDiscrepancy_sq_integral_eq (β : ℝ) {t : ℕ → ℕ} {u v : ℕ}
    (ht : MonotoneOn t (Set.Iic v)) (hu : 1 ≤ u) (huv : u < v) :
    ∫ ω, closedDiscrepancy β t u v ω ^ 2 ∂disorderLaw =
      closedStringSum (Polymer.sigmaSq β) t u v := by
  let s : ℕ → ℕ := fun i => t (min i v)
  have hs : Monotone s := monotone_cappedGrid ht
  have heq (i : ℕ) (hi : i ≤ v) : t i = s i := by
    simp only [s, min_eq_left hi]
  rw [closedDiscrepancy_congr_below β t s hu huv.le heq,
    closedStringSum_congr_below (Polymer.sigmaSq β) t s huv.le heq]
  exact closedDiscrepancy_sq_integral_eq_monotone β s hs huv

end Critical2DKPZ.Blocks
