/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedUniformSwapping
public import Critical2DKPZ.SHF.DeltaBose.PathKernel
import Mathlib.Tactic

/-! # Chosen uniform swapping constants in the conjugated Laplace chain -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- One swapping coefficient, chosen uniformly over all distinct pairs. -/
def conjugatedSwappingConstant (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) : ℝ :=
  Classical.choose (exists_uniform_conjugated_laplace_swapping n hp ha)

/-- One damping threshold for the uniformly chosen swapping coefficient. -/
def conjugatedSwappingThreshold (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) : ℝ :=
  Classical.choose (Classical.choose_spec (exists_uniform_conjugated_laplace_swapping n hp ha))

/-- Both chosen swapping constants are at least one. -/
theorem conjugatedSwappingConstants_ge_one (n : ℕ) {p a : ℝ} (hp : 1 < p) (ha : 0 ≤ a) :
    1 ≤ conjugatedSwappingConstant n hp ha ∧ 1 ≤ conjugatedSwappingThreshold n hp ha := by
  have h := Classical.choose_spec
    (Classical.choose_spec (exists_uniform_conjugated_laplace_swapping n hp ha))
  exact ⟨h.1, h.2.1⟩

/-- Every distinct-pair free strand satisfies the chosen uniform conjugated
swapping estimate above the common damping threshold. -/
theorem weightedFormBound_laplace_free_swapping_conj_uniform {n : ℕ} {p a rate : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) (α β : CollisionPair n) (hne : α ≠ β)
    (hrate : conjugatedSwappingThreshold n hp ha ≤ rate) :
    WeightedFormBound volume volume (fun y => -(a * fusedOneNorm α y))
      (fun z => a * fusedOneNorm β z) p (p / (p - 1))
      (laplaceTimeKernel rate (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β)))
      (ENNReal.ofReal (conjugatedSwappingConstant n hp ha)) :=
  (Classical.choose_spec
    (Classical.choose_spec (exists_uniform_conjugated_laplace_swapping n hp ha))).2.2 α β hne rate hrate

end Critical2DKPZ.SHF.Tsai

end
