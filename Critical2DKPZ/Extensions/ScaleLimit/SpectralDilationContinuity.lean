/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralDilationLp
import Mathlib.Tactic

/-! # Continuity of spectral Schwartz dilation in L2 -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Positive dilation is continuous in spectral L2, even after multiplication
by an arbitrary fixed measurable contraction. -/
theorem continuousAt_spectralMultipliedDilate (ν : Measure Plane) [ν.HasTemperateGrowth]
    (A : Plane → ℂ) (hAm : Measurable A) (hAn : ∀ ξ, ‖A ξ‖ ≤ 1)
    (m : SchwartzMap Plane ℂ) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (spectralMultipliedDilate ν A hAm hAn m) r := by
  let α := r / 2
  have hα : 0 < α := by dsimp [α]; positivity
  have hαr : α < r := by dsimp [α]; linarith
  obtain ⟨C, hC, henv⟩ := schwartz_scaled_decay_envelope m ν.integrablePower hα
  let B : Plane → ℝ := fun ξ => C / (1 + ‖ξ‖) ^ ν.integrablePower
  have hB0 (ξ : Plane) : 0 ≤ B ξ := by dsimp [B]; positivity
  have hB : Integrable (fun ξ => 4 * B ξ ^ 2) ν := (integrable_polynomial_envelope_sq ν hC).const_mul 4
  have hnorm (q : ℝ) (hq : α ≤ q) (ξ : Plane) : ‖A ξ * m (q • ξ)‖ ≤ B ξ := by
    rw [norm_mul]
    exact ((mul_le_mul_of_nonneg_right (hAn ξ) (norm_nonneg _)).trans_eq (one_mul _)).trans (henv q hq ξ)
  apply tendsto_L2_of_dominated_sq ν (spectralMultipliedDilate ν A hAm hAn m)
    (spectralMultipliedDilate ν A hAm hAn m r)
    (fun q ξ => A ξ * m (q • ξ)) (fun ξ => A ξ * m (r • ξ)) _
    (spectralMultipliedDilate_ae_eq ν A hAm hAn m hr.ne') hB _ _
  · filter_upwards [eventually_ge_nhds hαr] with q hq
    exact spectralMultipliedDilate_ae_eq ν A hAm hAn m (hα.trans_le hq).ne'
  · filter_upwards [eventually_ge_nhds hαr] with q hq
    exact Eventually.of_forall fun ξ => by
      have hh := (norm_sub_le (A ξ * m (q • ξ)) (A ξ * m (r • ξ))).trans
        (add_le_add (hnorm q hq ξ) (hnorm r hαr.le ξ))
      nlinarith only [hh, norm_nonneg (A ξ * m (q • ξ) - A ξ * m (r • ξ)), hB0 ξ]
  · exact Eventually.of_forall fun ξ =>
      (continuous_const.mul (m.continuous.comp (continuous_id.smul continuous_const))).continuousAt.tendsto

end Critical2DKPZ.Extensions.ScaleLimit
