/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.ConfigurationWeight

/-! # Measurability of the canonical configuration weights -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Flow

/-- The sum of the planar coordinate ℓ¹ norms is continuous on configuration space. -/
theorem continuous_configurationOneNorm (n : ℕ) : Continuous (@configurationOneNorm n) := by
  unfold configurationOneNorm planeOneNorm
  fun_prop

/-- The sum of the planar coordinate ℓ¹ norms is measurable on configuration space. -/
theorem measurable_configurationOneNorm (n : ℕ) : Measurable (@configurationOneNorm n) :=
  (continuous_configurationOneNorm n).measurable

/-- The fused configuration ℓ¹ weight is measurable. -/
theorem measurable_fusedOneNorm {n : ℕ} (α : CollisionPair n) : Measurable (fusedOneNorm α) := by
  have he : fusedOneNorm α = configurationOneNorm ∘ collisionEmbedding α := by
    funext z
    exact (configurationOneNorm_collisionEmbedding α z).symm
  rw [he]
  exact (measurable_configurationOneNorm n).comp (measurable_collisionEmbedding α)

end Critical2DKPZ.SHF.Flow

end
