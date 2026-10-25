/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.TwoParticleAction

/-! # The two-particle weighted smoothing cancellation bound

The correction has inverse-logarithmic norm decay. The two surrounding actions
are uniformly bounded, including at time zero where they are the identity.
All actions use the explicit positive moment and correction kernels.
-/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The weighted action–correction–action composition has an inverse-logarithmic bound on its squared integral, so finite quadratic input integrals give finite quadratic output integrals. -/
theorem exists_twoParticle_weighted_cancellation_bound (B a T : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (θ r t v : ℝ), θ ≤ B →
      0 ≤ r → r ≤ T → 0 ≤ t → t ≤ T → 0 < v → v ≤ 1 / 2 →
      ∀ f : Configuration 2 → ℝ≥0∞, Measurable f →
      (∫⁻ x : Configuration 2,
        twoParticleWeightedAction θ a r
          (twoParticleCorrectionWeightedAction θ a v (twoParticleWeightedAction θ a t f)) x ^ 2) ≤
        (C * ENNReal.ofReal (1 / (1 + Real.log v⁻¹))) ^ 2 * ∫⁻ y : Configuration 2, f y ^ 2 := by
  obtain ⟨D, hD, hQ⟩ := exists_twoParticleWeightedAction_l2_bound B a T ha
  obtain ⟨K, hK, hsmall⟩ := exists_diagramKernel_singleton_weighted_l2_log_bound 2 B a (1 / 2) ha
  refine ⟨D * K, ENNReal.mul_ne_top hD hK, fun θ r t v hθ hr hrT ht htT hv hvhalf f hf => ?_⟩
  have hQt := measurable_twoParticleWeightedAction θ a t hf
  have hKQt := measurable_twoParticleCorrectionWeightedAction θ a v hQt
  have hright := hQ θ t hθ ht htT f hf
  have hmiddle : (∫⁻ x : Configuration 2,
      twoParticleCorrectionWeightedAction θ a v (twoParticleWeightedAction θ a t f) x ^ 2) ≤
      (K * ENNReal.ofReal (1 / (1 + Real.log v⁻¹))) ^ 2 *
        ∫⁻ y : Configuration 2, twoParticleWeightedAction θ a t f y ^ 2 := by
    exact hsmall pairTwo θ v hθ hv hvhalf hvhalf (twoParticleWeightedAction θ a t f) hQt
  calc
    _ ≤ D * ∫⁻ x : Configuration 2,
        twoParticleCorrectionWeightedAction θ a v (twoParticleWeightedAction θ a t f) x ^ 2 :=
      hQ θ r hθ hr hrT _ hKQt
    _ ≤ D * ((K * ENNReal.ofReal (1 / (1 + Real.log v⁻¹))) ^ 2 *
        ∫⁻ y : Configuration 2, twoParticleWeightedAction θ a t f y ^ 2) :=
      mul_le_mul' le_rfl hmiddle
    _ ≤ D * ((K * ENNReal.ofReal (1 / (1 + Real.log v⁻¹))) ^ 2 *
        (D * ∫⁻ y : Configuration 2, f y ^ 2)) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl hright)
    _ = _ := by simp only [pow_two]; ac_rfl


end Critical2DKPZ.SHF.Flow

end
