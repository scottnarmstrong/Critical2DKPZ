/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TensorComposition
public import Critical2DKPZ.SHF.Tsai.ChainLimitIdentification

/-! # Fourth-moment composition on all spatial L² tensors

The two consecutive increments are independent moment blocks. Their smoothed
product is Cauchy in `L⁴`; the composition axiom identifies its limit in measure.
Thus the actual tensor error converges in fourth moment.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- Approximate composition converges in fourth moment on arbitrary L² endpoint tensors. -/
theorem tendsto_integral_smoothedProduct_sub_pow_four_tensor (θ : ℝ) (D : Set ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    {t₀ t₁ t₂ : ℝ} (h₀ : t₀ ∈ D) (h₁ : t₁ ∈ D) (h₂ : t₂ ∈ D) (h₀₁ : t₀ < t₁) (h₁₂ : t₁ < t₂)
    (w : ℕ → Plane → ℝ) (hw : IsL2ApplicableMollifier w)
    (hwP : ∀ ℓ, ∀ᵐ ω ∂P, SmoothedProductWellDefined (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω))
    (hconv : ∀ f : C_c(Plane × Plane, ℝ),
      TendstoInMeasure P (fun ℓ ω => smoothedProductPairing (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω) f -
        ∫ p, f p ∂(Z t₀ t₂ ω)) atTop (fun _ => 0))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    (∀ ℓ, Integrable (fun ω => ((∫ p, g p.1 * g' p.2
      ∂smoothedProductMeasure (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)) -
        ∫ p, g p.1 * g' p.2 ∂Z t₀ t₂ ω) ^ 4) P) ∧
    Tendsto (fun ℓ => ∫ ω, ((∫ p, g p.1 * g' p.2
      ∂smoothedProductMeasure (Z t₀ t₁ ω) (w ℓ) (Z t₁ t₂ ω)) -
        ∫ p, g p.1 * g' p.2 ∂Z t₀ t₂ ω) ^ 4 ∂P) atTop (𝓝 0) := by
  classical
  let B (k : ℕ) := if k = 0 then Z t₀ t₁ else Z t₁ t₂
  let τ (k : ℕ) := if k = 0 then t₁ - t₀ else t₂ - t₁
  have hτ (k : ℕ) (_ : k ≤ 1) : 0 < τ k := by
    dsimp only [τ]
    split_ifs <;> linarith only [h₀₁, h₁₂]
  have hB (k : ℕ) (_ : k ≤ 1) : HasDeltaBoseMoments θ (τ k) P (B k) := by
    dsimp only [B, τ]
    split_ifs
    · exact hZ.hasDeltaBoseMoments h₀ h₁ h₀₁
    · exact hZ.hasDeltaBoseMoments h₁ h₂ h₁₂
  have hind : iIndepFun (fun k : Fin (1 + 1) => B k) P :=
    hZ.iIndepFun_twoConsecutive h₀ h₁ h₂ h₀₁ h₁₂
  have hprob := tendstoInMeasure_smoothedProductPairing_tensor θ D P Z hZ
    h₀ h₁ h₂ h₀₁ h₁₂ w hw hwP hconv g g' hg hg'
  have hprob' : TendstoInMeasure P (fun ℓ ω => ∫ p, g p.1 * g' p.2
      ∂chainProduct (fun k => B k ω) (fun _ => w ℓ) 1) atTop
      (fun ω => ∫ p, g p.1 * g' p.2 ∂Z t₀ t₂ ω) := by
    simpa only [tendstoInMeasure_iff_norm, Pi.zero_apply, sub_zero, chainProduct, B,
      ite_eq_left (show (0 : ℕ) = 0 from rfl), ite_eq_right (by norm_num : (1 : ℕ) ≠ 0)] using hprob
  have h := tendsto_integral_chainPairing_sub_pow_four_of_tendstoInMeasure 1 τ hτ B hB hind
    (fun _ => w) (fun _ => hw) g g' hg hg' _ hprob'
  simpa only [chainProduct, B, ite_eq_left (show (0 : ℕ) = 0 from rfl),
    ite_eq_right (by norm_num : (1 : ℕ) ≠ 0)] using h.2

end Critical2DKPZ.SHF.Tsai

end
