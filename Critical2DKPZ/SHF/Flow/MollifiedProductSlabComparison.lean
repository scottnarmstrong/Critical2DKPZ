/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSmoothedErrorCorrection
public import Critical2DKPZ.SHF.Flow.ThinSlabSmoothedCorrectionSmall
import all Critical2DKPZ.SHF.Flow.ThinSlabCompactCorrectionSmall
import all Critical2DKPZ.SHF.Flow.ThinSlabSeparatedKernelMeasure
import Mathlib.Tactic

/-! # Annealing a thin slab in a smoothed product -/

@[expose] public noncomputable section
open MeasureTheory Filter Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Tsai
open scoped CompactlySupported ENNReal Topology
namespace Critical2DKPZ.SHF.Flow


/-- The mean-square error from annealing a thin slab in a smoothed product vanishes uniformly over positive mollifier scales at most one; integrability is supplied by `integral_sq_sub_slabSmoothedProduct`. -/
theorem smoothedProduct_sub_slabProduct_sq_small_of (ϑ : ℝ) (hPolymerMomentInput : PolymerMomentLimit ϑ)
    (hFlatSixthMomentInput : FlatSixthMomentBound ϑ)
    (hSG : MomentKernelTwoSemigroup (ϑ - Real.eulerMascheroniConstant)) {s t u : ℝ} (hs : 0 ≤ s)
    (hst : s < t) (htu : t < u) (Φ : C_c(Plane × Plane, ℝ)) (w : Plane → ℝ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwc : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x) (hw1 : ∫ x, w x = 1) :
    ∀ ε > 0, ∃ v₀ > 0, ∀ v : ℝ, 0 < v → v < v₀ → ∀ e : ℝ, 0 < e → e ≤ 1 → ∀ᶠ N : ℕ in atTop,
      ∫ ω, (smoothedProductPairing (polymerMeasure ϑ N s t ω) (fun x => e⁻¹ ^ 2 * w (e⁻¹ • x))
          (polymerMeasure ϑ N t u ω) Φ -
        kernelProductPairing (polymerMeasure ϑ N s t ω)
          (fun a b => ∫ y, e⁻¹ ^ 2 * w (e⁻¹ • (a - y)) * slabMeanKernel ϑ N t (t + v) y b)
          (polymerMeasure ϑ N (t + v) u ω) Φ) ^ 2 ∂disorderLaw ≤ ε := by
  let θ := ϑ - Real.eulerMascheroniConstant
  let Ψ : C_c(Configuration 2 × Configuration 2, ℝ) := slabMomentBlockTensorTest (fun _ => Φ)
  obtain ⟨f, g, hf0, hg0, hmajor⟩ := exists_slabCompact_endpoint_majorant Ψ
  let fe : Configuration 2 → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  let ge : Configuration 2 → ℝ≥0∞ := fun x => ENNReal.ofReal (g x)
  have hfe : Measurable fe := f.continuous.measurable.ennreal_ofReal
  have hge : Measurable ge := g.continuous.measurable.ennreal_ofReal
  have hf2 : (∫⁻ x, fe x ^ 2) ≠ ⊤ := slabCompact_ofReal_square_integral_ne_top f hf0
  have hg2 : (∫⁻ x, ge x ^ 2) ≠ ⊤ := slabCompact_ofReal_square_integral_ne_top g hg0
  have hMajor (x z : Configuration 2) : ENNReal.ofReal (∏ i : Fin 2, Φ (x i, z i)) ≤ ge x * fe z := by
    change ENNReal.ofReal (Ψ (x, z)) ≤ ENNReal.ofReal (g x) * ENNReal.ofReal (f z)
    rw [← ENNReal.ofReal_mul (hg0 x)]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hmajor (x, z)))
  intro ε hε
  obtain ⟨v₁, hv₁, hsmall⟩ := slabPositiveCorrectionForm_uniformly_small θ (u - s) w hw.continuous hwc
    hfe hge hf2 hg2 (ε / 2) (half_pos hε)
  refine ⟨min v₁ (u - t), lt_min hv₁ (sub_pos.mpr htu), ?_⟩
  intro v hv hv₀ e he he1
  have hv₁' : v < v₁ := hv₀.trans_le (min_le_left _ _)
  have hvu : t + v < u := by
    have h := hv₀.trans_le (min_le_right v₁ (u - t))
    linarith only [h]
  have haT : t - s ≤ u - s := sub_le_sub_right htu.le s
  have hbT : u - (t + v) ≤ u - s :=
    sub_le_sub_left (hst.le.trans (le_add_of_nonneg_right hv.le)) u
  have hbound := hsmall θ (t - s) (u - (t + v)) v e le_rfl (sub_pos.mpr hst) haT
    (sub_pos.mpr hvu) hbT hv hv₁' he he1
    (fun x y => ENNReal.ofReal (∏ i : Fin 2, Φ (x i, y i))) hMajor
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  rw [ENNReal.toReal_ofReal (half_pos hε).le] at hreal
  have hL :
      (slabPositiveConnectorForm θ (t - s) (u - (t + v))
        (fun x y => ENNReal.ofReal (∏ i : Fin 2, Φ (x i, y i)))
        (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v))).toReal -
      (slabPositiveConnectorForm θ (t - s) (u - (t + v))
        (fun x y => ENNReal.ofReal (-(∏ i : Fin 2, Φ (x i, y i))))
        (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v))).toReal < ε := by
    have hnonneg : 0 ≤ (slabPositiveConnectorForm θ (t - s) (u - (t + v))
      (fun x y => ENNReal.ofReal (-(∏ i : Fin 2, Φ (x i, y i))))
      (spatialKernelComp volume (slabMollifierTensorKernel 2 e w) (twoParticleCorrection θ v))).toReal :=
      ENNReal.toReal_nonneg
    linarith only [hreal, hnonneg, hε]
  have hlimit := tendsto_slabSmoothedSlabError_correctionForm ϑ hPolymerMomentInput hFlatSixthMomentInput hSG hs hst hv hvu he he1
    Φ w hw.continuous hwc hw0 hw1
  filter_upwards [hlimit.eventually (Iio_mem_nhds hL)] with N hN
  exact hN.le

end Critical2DKPZ.SHF.Flow
end
