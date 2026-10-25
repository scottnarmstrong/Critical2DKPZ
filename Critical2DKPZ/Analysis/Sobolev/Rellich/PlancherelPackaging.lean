/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Defs
import Mathlib.Tactic.NormNum

/-! For integrable square-integrable functions, the pointwise Fourier integral represents the L² Fourier transform almost everywhere and their L² norms agree.

Adapted from A. Bou-Rabee's Lattice-Probability development (Apache-2.0). -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexInnerProductSpace ContDiff

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- On `L¹ ∩ L²` the `L²` Fourier transform is the pointwise Fourier integral, a.e. -/
theorem fourier_toLp_ae_eq {d : ℕ} {F : Space d → ℂ} (hF2 : MemLp F 2 volume)
    (hF1 : Integrable F) : ⇑(𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure (Space d)))
      =ᵐ[volume] 𝓕 F := by
  have hcont : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hF1
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num)) hcont.locallyIntegrable ?_
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := Complex.ofRealCLM.contDiff.comp hg
  set φ : 𝓢(Space d, ℂ) := hg₁.toSchwartzMap hg₂ with hφ
  have hφg : ∀ x, φ x = (g x : ℂ) := fun x => by simp [hφ]
  have e1 : ∫ x, g x • (𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure (Space d))) x
      = ∫ x, 𝓕 φ x • F x := by
    calc _ = ∫ x, φ x • (𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure (Space d))) x := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp [hφg, Complex.real_smul]
      _ = Lp.toTemperedDistribution
            (𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure (Space d))) φ :=
          (Lp.toTemperedDistribution_apply _ _).symm
      _ = 𝓕 (Lp.toTemperedDistribution (hF2.toLp F)) φ := by
          rw [Lp.fourier_toTemperedDistribution_eq]
      _ = ∫ x, 𝓕 φ x • (hF2.toLp F : Lp ℂ 2 (volume : Measure (Space d))) x := by
          rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
      _ = _ := by
          refine integral_congr_ae ?_
          filter_upwards [hF2.coeFn_toLp] with x hx
          rw [hx]
  have e2 : ∫ x, g x • 𝓕 F x = ∫ x, 𝓕 φ x • F x := by
    calc _ = ∫ ξ, 𝓕 F ξ • φ ξ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          simp [hφg, Complex.real_smul, mul_comm]
      _ = ∫ x, F x • 𝓕 φ x := by
          have := VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
            (L := innerₗ (Space d)) Real.continuous_fourierChar continuous_inner hF1 φ.integrable
          first | exact this | simpa using! this
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [mul_comm])
  rw [e1, e2]

/-- The squared spatial L² norm of an integrable square-integrable real function equals the nonnegative integral of its squared Fourier norm. -/
theorem abs_integral_mul_le_lintegral_fourier {d : ℕ} {f g : Space d → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (hf1 : Integrable f) (hg1 : Integrable g) :
    ENNReal.ofReal |∫ x, f x * g x| ≤ ∫⁻ ξ : Space d,
      ENNReal.ofReal (‖𝓕 (fun x => (f x : ℂ)) ξ‖
        * ‖𝓕 (fun x => (g x : ℂ)) ξ‖) := by
  have hF2 : MemLp (fun x => (f x : ℂ)) 2 volume := hf.ofReal
  have hG2 : MemLp (fun x => (g x : ℂ)) 2 volume := hg.ofReal
  set u := hF2.toLp (fun x => (f x : ℂ)) with hu
  set v := hG2.toLp (fun x => (g x : ℂ)) with hv
  have h1 : (((∫ x, f x * g x : ℝ)) : ℂ) = ⟪u, v⟫ := by
    rw [L2.inner_def, ← integral_complex_ofReal]
    refine integral_congr_ae ?_
    filter_upwards [hF2.coeFn_toLp, hG2.coeFn_toLp] with x hx hy
    rw [hx, hy]
    simp [mul_comm]
  have hb1 := fourier_toLp_ae_eq hF2 hf1.ofReal
  have hb2 := fourier_toLp_ae_eq hG2 hg1.ofReal
  calc ENNReal.ofReal |∫ x, f x * g x|
      = ‖(((∫ x, f x * g x : ℝ)) : ℂ)‖ₑ := by
        rw [← ofReal_norm]; simp
    _ = ‖⟪𝓕 u, 𝓕 v⟫‖ₑ := by rw [h1, Lp.inner_fourier_eq]
    _ = ‖∫ ξ, ⟪(𝓕 u : Lp ℂ 2 (volume : Measure (Space d))) ξ,
          (𝓕 v : Lp ℂ 2 (volume : Measure (Space d))) ξ⟫‖ₑ := by rw [L2.inner_def]
    _ ≤ ∫⁻ ξ, ‖⟪(𝓕 u : Lp ℂ 2 (volume : Measure (Space d))) ξ,
          (𝓕 v : Lp ℂ 2 (volume : Measure (Space d))) ξ⟫‖ₑ :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ _ := by
        refine lintegral_mono_ae ?_
        filter_upwards [hb1, hb2] with ξ h1 h2
        rw [← ofReal_norm, h1, h2]
        exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm _ _)

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
