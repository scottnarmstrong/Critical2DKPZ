/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.ThreeBlockSlice
import Mathlib.Tactic

/-! # Normalization of the three-block heat bound -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- Dividing the middle slice by the first outer mass bounds its heat-block average
by `(2πτ)⁻¹` times the last outer mass, including when the first mass is zero or infinite. -/
theorem lintegral_normalized_positiveChainBlockTest_three_heat_le
    (μ : ℕ → Measure (Plane × Plane)) [∀ k, SigmaFinite (μ k)]
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    (∫⁻ q, (∫⁻ p, f p.1 ∂μ 0)⁻¹ *
      positiveChainBlockTest 2 1 μ (fun _ => heatKernel ε)
        (fun p => f p.1 * g p.2) q ∂heatBlock τ) ≤
      ENNReal.ofReal ((2 * Real.pi * τ)⁻¹) * (∫⁻ p, g p.2 ∂μ 2) := by
  have hSlice : Measurable (positiveChainBlockTest 2 1 μ (fun _ => heatKernel ε)
      (fun p => f p.1 * g p.2)) :=
    measurable_positiveChainBlockTest_fixed μ 2 1 _ (fun _ => measurable_heatKernel ε) _
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd))
  rw [lintegral_const_mul _ hSlice]
  calc
    _ ≤ (∫⁻ p, f p.1 ∂μ 0)⁻¹ *
        (ENNReal.ofReal ((2 * Real.pi * τ)⁻¹) *
          (∫⁻ p, f p.1 ∂μ 0) * (∫⁻ p, g p.2 ∂μ 2)) := by
      gcongr
      exact lintegral_positiveChainBlockTest_three_heat_le μ f g hf hg hτ hε
    _ = ENNReal.ofReal ((2 * Real.pi * τ)⁻¹) *
        ((∫⁻ p, f p.1 ∂μ 0)⁻¹ * (∫⁻ p, f p.1 ∂μ 0)) * (∫⁻ p, g p.2 ∂μ 2) := by ac_rfl
    _ ≤ ENNReal.ofReal ((2 * Real.pi * τ)⁻¹) * 1 * (∫⁻ p, g p.2 ∂μ 2) := by
      gcongr
      exact ENNReal.inv_mul_le_one _
    _ = _ := by rw [mul_one]

/-- The normalized nonnegative three-block pairing equals the integral of the normalized middle slice. -/
theorem normalized_threeBlock_chain_eq_slice
    (μ : ℕ → Measure (Plane × Plane)) [∀ k, SigmaFinite (μ k)]
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (ε : ℝ) :
    (∫⁻ p, f p.1 * g p.2 ∂chainProduct μ (fun _ => heatKernel ε) 2) /
        (∫⁻ p, f p.1 ∂μ 0) =
      ∫⁻ q, (∫⁻ p, f p.1 ∂μ 0)⁻¹ *
        positiveChainBlockTest 2 1 μ (fun _ => heatKernel ε)
          (fun p => f p.1 * g p.2) q ∂μ 1 := by
  have hSlice : Measurable (positiveChainBlockTest 2 1 μ (fun _ => heatKernel ε)
      (fun p => f p.1 * g p.2)) :=
    measurable_positiveChainBlockTest_fixed μ 2 1 _ (fun _ => measurable_heatKernel ε) _
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd))
  rw [lintegral_const_mul _ hSlice,
    lintegral_chainProduct_eq_lintegral_blockTest μ (fun _ => measurable_heatKernel ε) 2 1
      (fun p : Plane × Plane => f p.1 * g p.2)
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd)), div_eq_mul_inv, mul_comm]
  rfl

end Critical2DKPZ.NonGaussian

end
