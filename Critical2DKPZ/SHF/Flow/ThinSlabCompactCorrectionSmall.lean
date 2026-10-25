/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabCorrectionEndpointMeasure
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Uniform smallness of the correction on general compact endpoint tests -/

@[expose] public noncomputable section

open MeasureTheory Filter Set Critical2DKPZ.DeltaBose
open scoped CompactlySupported ENNReal

namespace Critical2DKPZ.SHF.Flow

private theorem exists_slabCompact_endpoint_majorant
    (F : C_c(Configuration 2 × Configuration 2, ℝ)) :
    ∃ f g : C_c(Configuration 2, ℝ), (∀ x, 0 ≤ f x) ∧ (∀ x, 0 ≤ g x) ∧
      ∀ q, |F q| ≤ g q.1 * f q.2 := by
  obtain ⟨χ, hχone, hχc, _, hχ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (F.hasCompactSupport.image continuous_fst) isOpen_univ (subset_univ _)
  obtain ⟨ψ, hψone, hψc, _, hψ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen
      (F.hasCompactSupport.image continuous_snd) isOpen_univ (subset_univ _)
  obtain ⟨M, hMbound⟩ := F.continuous.bounded_above_of_compact_support F.hasCompactSupport
  have hM : 0 ≤ M := (norm_nonneg (F 0)).trans (hMbound 0)
  let f : C_c(Configuration 2, ℝ) := ⟨ψ, hψc⟩
  let g : C_c(Configuration 2, ℝ) :=
    ⟨⟨fun x => M * χ x, continuous_const.mul χ.continuous⟩, (show HasCompactSupport (χ : Configuration 2 → ℝ) from hχc).mul_left⟩
  refine ⟨f, g, fun x => (hψ01 x).1, fun x => mul_nonneg hM (hχ01 x).1, ?_⟩
  intro q
  by_cases hq : q ∈ tsupport (F : Configuration 2 × Configuration 2 → ℝ)
  · have hχq : χ q.1 = 1 := hχone ⟨q, hq, rfl⟩
    have hψq : ψ q.2 = 1 := hψone ⟨q, hq, rfl⟩
    change |F q| ≤ (M * χ q.1) * ψ q.2
    rw [hχq, hψq, mul_one, mul_one]
    simpa only [Real.norm_eq_abs, CompactlySupportedContinuousMap.coe_toContinuousMap] using hMbound q
  · have hzero : F q = 0 := image_eq_zero_of_notMem_tsupport hq
    rw [hzero, abs_zero]
    exact mul_nonneg (mul_nonneg hM (hχ01 _).1) (hψ01 _).1

private theorem slabCompact_ofReal_square_integral_ne_top
    (f : C_c(Configuration 2, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    (∫⁻ x : Configuration 2, ENNReal.ofReal (f x) ^ 2) ≠ ⊤ := by
  have hLp : MemLp (f : Configuration 2 → ℝ) 2 :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hEq := ofReal_integral_eq_lintegral_ofReal hLp.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg (f x))
  have hcast : (∫⁻ x : Configuration 2, ENNReal.ofReal (f x) ^ 2) =
      ENNReal.ofReal (∫ x : Configuration 2, f x ^ 2) := by
    rw [hEq]
    apply lintegral_congr
    intro x
    exact (ENNReal.ofReal_pow (hf x) 2).symm
  rw [hcast]
  exact ENNReal.ofReal_ne_top

/-- The correction integral of every compact signed endpoint test becomes small uniformly in
bounded outer durations. Its integrability is supplied by `integrable_slabEndpointMeasures`. -/
theorem integral_slabCorrectionEndpointMeasure_uniformly_small (B T : ℝ)
    (F : C_c(Configuration 2 × Configuration 2, ℝ)) :
    ∀ ε : ℝ, 0 < ε → ∃ v₀ > 0, ∀ θ a b v : ℝ, θ ≤ B →
      0 < a → a ≤ T → 0 < b → b ≤ T → 0 < v → v < v₀ →
      |∫ q, F q ∂slabCorrectionEndpointMeasure θ a v b| ≤ ε := by
  obtain ⟨f, g, hf0, hg0, hmajor⟩ := exists_slabCompact_endpoint_majorant F
  let fe : Configuration 2 → ℝ≥0∞ := fun x => ENNReal.ofReal (f x)
  let ge : Configuration 2 → ℝ≥0∞ := fun x => ENNReal.ofReal (g x)
  have hfe : Measurable fe := f.continuous.measurable.ennreal_ofReal
  have hge : Measurable ge := g.continuous.measurable.ennreal_ofReal
  have hf2 : (∫⁻ x, fe x ^ 2) ≠ ⊤ := slabCompact_ofReal_square_integral_ne_top f hf0
  have hg2 : (∫⁻ x, ge x ^ 2) ≠ ⊤ := slabCompact_ofReal_square_integral_ne_top g hg0
  intro ε hε
  obtain ⟨v₀, hv₀, hsmall⟩ :=
    slabMomentKernelTwo_correction_endpoint_uniformly_small B T hfe hge hf2 hg2 ε hε
  refine ⟨v₀, hv₀, ?_⟩
  intro θ a b v hθ ha haT hb hbT hv hv₀'
  have hI := (integrable_slabEndpointMeasures θ ha hv hb F).2.2
  have hbound : ENNReal.ofReal |∫ q, F q ∂slabCorrectionEndpointMeasure θ a v b| ≤
      slabMomentKernelTwoCorrectionEndpointForm θ a v b fe ge := by
    calc
      _ ≤ ENNReal.ofReal (∫ q, ‖F q‖ ∂slabCorrectionEndpointMeasure θ a v b) := by
        simpa only [Real.norm_eq_abs] using ENNReal.ofReal_le_ofReal (norm_integral_le_integral_norm (f := fun q => F q))
      _ = ∫⁻ q, ENNReal.ofReal ‖F q‖ ∂slabCorrectionEndpointMeasure θ a v b :=
        ofReal_integral_eq_lintegral_ofReal hI.norm (Eventually.of_forall fun q => norm_nonneg _)
      _ ≤ ∫⁻ q, ge q.1 * fe q.2 ∂slabCorrectionEndpointMeasure θ a v b := by
        apply lintegral_mono
        intro q
        change ENNReal.ofReal ‖F q‖ ≤ ENNReal.ofReal (g q.1) * ENNReal.ofReal (f q.2)
        rw [← ENNReal.ofReal_mul (hg0 _), Real.norm_eq_abs]
        exact ENNReal.ofReal_le_ofReal (hmajor q)
      _ = _ := lintegral_slabCorrectionEndpointMeasure_mul θ ha hb v hfe hge
  have hfinal := hbound.trans (hsmall θ a b v hθ ha.le haT hb.le hbT hv hv₀')
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hfinal

end Critical2DKPZ.SHF.Flow

end
