/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Definitions.Plane
public import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.Fourier.FourierTransform

/-! For integrable square-integrable functions, the L² Fourier transform agrees almost everywhere with the pointwise Fourier integral.

Adapted from A. Bou-Rabee's Lattice-Probability development (Apache-2.0). -/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform SchwartzMap ComplexInnerProductSpace ContDiff

namespace Critical2DKPZ.Analysis.Sobolev

/-- The L² Fourier transform agrees almost everywhere with the pointwise Fourier integral on L¹ ∩ L². -/
theorem fourier_toLp_ae_eq {F : Plane → ℂ} (hF2 : MemLp F 2 volume) (hF1 : Integrable F) :
    ⇑(𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure Plane)) =ᵐ[volume] 𝓕 F := by
  have hcont : Continuous (𝓕 F) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hF1
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp _).locallyIntegrable (by norm_num)) hcont.locallyIntegrable ?_
  intro g hg hgc
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  have hg₂ : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := Complex.ofRealCLM.contDiff.comp hg
  let φ : 𝓢(Plane, ℂ) := hg₁.toSchwartzMap hg₂
  have hφg : ∀ x, φ x = (g x : ℂ) := fun _ => rfl
  have e1 : ∫ x, g x • (𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure Plane)) x =
      ∫ x, 𝓕 φ x • F x := by
    calc
      _ = ∫ x, φ x • (𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure Plane)) x := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [hφg, Complex.real_smul, smul_eq_mul]
      _ = Lp.toTemperedDistribution (𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure Plane)) φ :=
        (Lp.toTemperedDistribution_apply _ _).symm
      _ = 𝓕 (Lp.toTemperedDistribution (hF2.toLp F)) φ := by
        rw [Lp.fourier_toTemperedDistribution_eq]
      _ = ∫ x, 𝓕 φ x • (hF2.toLp F : Lp ℂ 2 (volume : Measure Plane)) x := by
        rw [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply]
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [hF2.coeFn_toLp] with x hx
        rw [hx]
  have e2 : ∫ x, g x • 𝓕 F x = ∫ x, 𝓕 φ x • F x := by
    calc
      _ = ∫ ξ, 𝓕 F ξ • φ ξ := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp only [hφg, Complex.real_smul, smul_eq_mul, mul_comm]
      _ = ∫ x, F x • 𝓕 φ x := by
        simpa only [flip_innerₗ, SchwartzMap.fourier_coe] using!
          VectorFourier.integral_fourierIntegral_smul_eq_flip (μ := volume) (ν := volume)
            (L := innerₗ Plane) Real.continuous_fourierChar continuous_inner hF1 φ.integrable
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun _ => by
        simp only [smul_eq_mul, mul_comm])
  rw [e1, e2]

/-- Pointwise Plancherel, expressed as equality of extended `L²` seminorms. -/
theorem eLpNorm_fourier_eq_of_integrable {F : Plane → ℂ}
    (hF2 : MemLp F 2 volume) (hF1 : Integrable F) : eLpNorm (𝓕 F) 2 volume = eLpNorm F 2 volume := by
  calc
    _ = eLpNorm (⇑(𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure Plane))) 2 volume :=
      (eLpNorm_congr_ae (fourier_toLp_ae_eq hF2 hF1)).symm
    _ = ‖(𝓕 (hF2.toLp F) : Lp ℂ 2 (volume : Measure Plane))‖ₑ := (Lp.enorm_def _).symm
    _ = ‖hF2.toLp F‖ₑ := by rw [← ofReal_norm, Lp.norm_fourier_eq, ofReal_norm]
    _ = eLpNorm F 2 volume := by
      rw [Lp.enorm_def]
      exact eLpNorm_congr_ae hF2.coeFn_toLp

end Critical2DKPZ.Analysis.Sobolev

end
