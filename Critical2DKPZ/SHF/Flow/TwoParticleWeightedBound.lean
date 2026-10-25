/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.WeightedDiagramBounds
public import Critical2DKPZ.SHF.Flow.KernelSumL2

/-! # Uniform weighted bounds for the full two-particle kernel -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The full two-particle kernel is the free kernel plus its one resummed diagram. -/
theorem momentKernel_two_eq_free_add_diagram (θ v : ℝ) (x y : Configuration 2) :
    momentKernel 2 θ v x y = ENNReal.ofReal (freeKernel 2 v x y) + diagramKernel θ [pairTwo] v x y := by
  rw [momentKernel_two]
  simp only [freeKernel, Fin.prod_univ_two, twoParticleCorrection]

/-- A uniform squared-operator bound over all positive times in a bounded window. -/
theorem exists_momentKernel_two_weighted_l2_bound (B a T : ℝ) (ha : 0 ≤ a) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ (θ v : ℝ), θ ≤ B → 0 < v → v ≤ T →
      ∀ f : Configuration 2 → ℝ≥0∞, Measurable f →
      (∫⁻ x : Configuration 2, (∫⁻ y : Configuration 2,
        expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
          (momentKernel 2 θ v) x y * f y) ^ 2) ≤ D * ∫⁻ y : Configuration 2, f y ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_diagramKernel_singleton_weighted_l2_bound 2 B a T ha
  let W : ℝ≥0∞ := ENNReal.ofReal (weightGrowth 2 a T)
  refine ⟨2 * (W ^ 2 + C ^ 2), ENNReal.mul_ne_top (by norm_num)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.pow_ne_top ENNReal.ofReal_ne_top, ENNReal.pow_ne_top hC⟩),
    fun θ v hθ hv hvT f hf => ?_⟩
  let A : Configuration 2 → ℝ := fun x => a * configurationOneNorm x
  have hA : Measurable A := measurable_const.mul (measurable_configurationOneNorm 2)
  have hFree : Measurable (Function.uncurry
      (fun x y : Configuration 2 => ENNReal.ofReal (freeKernel 2 v x y))) :=
    ((measurable_freeKernel 2).comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  have hDiag : Measurable (Function.uncurry (diagramKernel θ [pairTwo] v)) :=
    measurable_diagramKernel_comp [pairTwo] measurable_const measurable_const measurable_fst measurable_snd
  have hFreeBound : (∫⁻ x : Configuration 2, (∫⁻ y : Configuration 2,
      expConjugate A A (fun x y => ENNReal.ofReal (freeKernel 2 v x y)) x y * f y) ^ 2) ≤
        W ^ 2 * ∫⁻ y : Configuration 2, f y ^ 2 := by
    have h := freeKernel_weighted_l2_sq_le 2 ha hv hf
    have hcoef : ENNReal.ofReal (weightGrowth 2 a v) ^ 2 ≤ W ^ 2 :=
      pow_le_pow_left' (ENNReal.ofReal_le_ofReal (weightGrowth_mono 2 a hvT)) 2
    have h' := h.trans (mul_le_mul' hcoef le_rfl)
    simpa only [A, expConjugate_ofReal, ← mul_sub] using h'
  have hsum := kernelSum_l2_sq_le volume volume (measurable_expConjugate hA hA hFree)
    (measurable_expConjugate hA hA hDiag) hf hFreeBound (hbound pairTwo θ v hθ hv hvT f hf)
  simpa only [momentKernel_two_eq_free_add_diagram, expConjugate, add_mul, A] using hsum

end Critical2DKPZ.SHF.Flow

end
