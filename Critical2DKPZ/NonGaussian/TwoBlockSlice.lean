/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.TwoBlockHeatBound
public import Critical2DKPZ.SHF.Tsai.PositiveChainBlockTests
import Critical2DKPZ.SHF.Tsai.MixedBlockJointMoments
import Mathlib.Tactic

/-! # Normalized final slices of Gaussian-smoothed two-block chains -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.NonGaussian

/-- The final slice of a two-block chain depends only on its first measure. -/
theorem positiveChainBlockTest_two_congr_first
    (μ ν : ℕ → Measure (Plane × Plane)) (h : μ 0 = ν 0)
    (w : ℕ → Plane → ℝ) (F : Plane × Plane → ℝ≥0∞) :
    positiveChainBlockTest 1 1 μ w F = positiveChainBlockTest 1 1 ν w F := by
  funext q
  unfold positiveChainBlockTest
  congr 1
  apply congrArg Measure.pi
  funext i
  fin_cases i
  exact h

/-- Heat averaging the final slice of a two-block chain bounds it by the
first mass whenever the final test is at most one. -/
theorem lintegral_positiveChainBlockTest_two_heat_le
    (μ : ℕ → Measure (Plane × Plane)) [∀ k, SigmaFinite (μ k)]
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (hg1 : ∀ y, g y ≤ 1)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    (∫⁻ q, positiveChainBlockTest 1 1 μ (fun _ => heatKernel ε)
      (fun p => f p.1 * g p.2) q ∂heatBlock τ) ≤ ∫⁻ p, f p.1 ∂μ 0 := by
  let ν : ℕ → Measure (Plane × Plane) := fun k => if k = 0 then μ 0 else heatBlock τ
  let : IsLocallyFiniteMeasure (heatBlock τ) := locallyFinite_heatBlock τ
  have hν (k : ℕ) : SigmaFinite (ν k) := by
    dsimp only [ν]
    split_ifs
    · infer_instance
    · infer_instance
  let : ∀ k, SigmaFinite (ν k) := hν
  have hSlice := positiveChainBlockTest_two_congr_first ν μ (by simp only [ν, ↓reduceIte])
    (fun _ => heatKernel ε) (fun p => f p.1 * g p.2)
  have hId := lintegral_chainProduct_eq_lintegral_blockTest ν (fun _ => measurable_heatKernel ε)
    1 1 (fun p : Plane × Plane => f p.1 * g p.2) ((hf.comp measurable_fst).mul (hg.comp measurable_snd))
  have hBound := lintegral_smoothedProduct_heatBlock_le (μ 0) f g hf hg hg1 hτ hε
  simpa [hSlice, chainProduct, ν] using
    hId.symm.trans_le hBound

/-- Normalizing the final slice by the first mass leaves the unit bound. -/
theorem lintegral_normalized_positiveChainBlockTest_two_heat_le
    (μ : ℕ → Measure (Plane × Plane)) [∀ k, SigmaFinite (μ k)]
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (hg1 : ∀ y, g y ≤ 1)
    {τ ε : ℝ} (hτ : 0 < τ) (hε : 0 < ε) :
    (∫⁻ q, (∫⁻ p, f p.1 ∂μ 0)⁻¹ * positiveChainBlockTest 1 1 μ (fun _ => heatKernel ε)
      (fun p => f p.1 * g p.2) q ∂heatBlock τ) ≤ 1 := by
  have hSlice : Measurable (positiveChainBlockTest 1 1 μ (fun _ => heatKernel ε)
      (fun p => f p.1 * g p.2)) :=
    measurable_positiveChainBlockTest_fixed μ 1 1 _ (fun _ => measurable_heatKernel ε) _
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd))
  rw [lintegral_const_mul _ hSlice]
  calc
    _ ≤ (∫⁻ p, f p.1 ∂μ 0)⁻¹ * (∫⁻ p, f p.1 ∂μ 0) := by
      gcongr 1
      exact lintegral_positiveChainBlockTest_two_heat_le μ f g hf hg hg1 hτ hε
    _ ≤ 1 := ENNReal.inv_mul_le_one _

/-- A normalized nonnegative two-block pairing equals the integral of its normalized final slice. -/
theorem normalized_twoBlock_chain_eq_slice
    (μ : ℕ → Measure (Plane × Plane)) [∀ k, SigmaFinite (μ k)]
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) (ε : ℝ) :
    (∫⁻ p, f p.1 * g p.2 ∂chainProduct μ (fun _ => heatKernel ε) 1) /
      (∫⁻ p, f p.1 ∂μ 0) =
      ∫⁻ q, (∫⁻ p, f p.1 ∂μ 0)⁻¹ * positiveChainBlockTest 1 1 μ (fun _ => heatKernel ε)
        (fun p => f p.1 * g p.2) q ∂μ 1 := by
  have hSlice : Measurable (positiveChainBlockTest 1 1 μ (fun _ => heatKernel ε)
      (fun p => f p.1 * g p.2)) :=
    measurable_positiveChainBlockTest_fixed μ 1 1 _ (fun _ => measurable_heatKernel ε) _
      ((hf.comp measurable_fst).mul (hg.comp measurable_snd))
  rw [lintegral_const_mul _ hSlice,
    lintegral_chainProduct_eq_lintegral_blockTest μ (fun _ => measurable_heatKernel ε) 1 1
      (fun p : Plane × Plane => f p.1 * g p.2) ((hf.comp measurable_fst).mul (hg.comp measurable_snd)),
    div_eq_mul_inv, mul_comm]
  rfl

end Critical2DKPZ.NonGaussian

end
