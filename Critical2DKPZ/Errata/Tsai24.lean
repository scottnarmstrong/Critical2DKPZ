/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs
public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks

/-! # Weighted planar kernels and index identities

These scalar examples concern the weighted kernel bounds and collision-index identities in Tsai24. -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Errata

/-- Multiplication by the inverse exponential weight preserves the weighted norm. -/
theorem tsai24_inverse_weight_norm {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (w f : X → ℝ) (p : ℝ≥0∞) :
    eLpNorm (fun x => (Real.exp (-w x) * f x) * Real.exp (w x)) p μ =
      eLpNorm f p μ := by
  congr 1
  funext x
  rw [mul_right_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

/-- Free spectator coordinates lie outside the union of both collision pairs. -/
theorem tsai24_swapping_active_spectator_factorization {n : ℕ}
    (α β : CollisionPair n) (t : ℝ) (y : FusedConfiguration α) (z : FusedConfiguration β) :
    let active : Finset (Fin n) := {α.1.1, α.1.2} ∪ {β.1.1, β.1.2}
    swappingKernel α β t y z =
      (∏ i ∈ active, heatKernel t (collisionEmbedding β z i - collisionEmbedding α y i)) *
      ∏ i ∈ activeᶜ, heatKernel t (collisionEmbedding β z i - collisionEmbedding α y i) := by
  dsimp only
  exact (Finset.prod_mul_prod_compl
    ({α.1.1, α.1.2} ∪ {β.1.1, β.1.2} : Finset (Fin n))
    (fun i : Fin n => heatKernel t (collisionEmbedding β z i - collisionEmbedding α y i))).symm

/-- For the collision sequence `01,12`, the successive covered sets intersect in two labels while the new pair meets the preceding set in one. -/
theorem tsai24_growth_intersection_counterexample :
    let η₁ : Finset (Fin 4) := {0, 1}
    let η₂ : Finset (Fin 4) := {1, 2}
    η₁ ⊂ η₁ ∪ η₂ ∧ (η₂ ∩ η₁).card = 1 ∧ ((η₁ ∪ η₂) ∩ η₁).card = 2 := by
  decide

end Critical2DKPZ.Errata

end
