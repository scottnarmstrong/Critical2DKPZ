/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedMomentBounds
public import Critical2DKPZ.SHF.Tsai.ConjugatedKernelApply
public import Critical2DKPZ.SHF.Tsai.WeightedCompactTensors
import Mathlib.Tactic

/-! # Uniform weighted moment-kernel bounds on compact tensors -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- For four particles, finite `p > 2`, and positive exponential weight, moment-semigroup actions on compact tensors have uniformly bounded weighted `Lᵖ` norms for `0 < τ ≤ T`, as in Tsai (2024), equation (2.16). Almost-everywhere row integrability follows from `WeightedFormBound.integrable_and_eLpNorm_configurationKernelAction_le`. -/
theorem exists_weighted_eLpNorm_momentKernel_apply_le (θ T : ℝ) {p : ℝ≥0∞} (hp : 2 < p) (hp' : p ≠ ⊤)
    {a : ℝ} (ha : 0 < a) (g : Fin 4 → C_c(Plane, ℝ)) :
    ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T →
      eLpNorm (fun x : Configuration 4 => Real.exp (a * configL1Norm x) *
        ∫ y, (momentKernel 4 θ τ x y).toReal * ∏ i, g i (y i)) p ≤ ENNReal.ofReal C := by
  let r : ℝ := p.toReal
  have hr : 1 < r := by
    have h : (1 : ℝ≥0∞).toReal < p.toReal :=
      (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp').mpr (lt_trans (by norm_num) hp)
    simpa only [ENNReal.toReal_one, r] using h
  obtain ⟨c, _hc, hBound⟩ := weightedFormBound_momentKernel_conj 4 θ T hr ha.le
  let F : Configuration 4 → ℝ := fun y => ∏ i, g i (y i)
  have hF : Measurable F :=
    (continuous_finsetProd _ (fun i _ => (g i).continuous.comp (continuous_apply i))).measurable
  have hWeightedF : MemLp (fun y => Real.exp (a * configurationOneNorm y) * F y) (ENNReal.ofReal r) := by
    simpa only [r, ENNReal.ofReal_toReal hp'] using memLp_exp_weighted_configurationTensor a p g
  let N : ℝ≥0∞ := eLpNorm (fun y => Real.exp (a * configurationOneNorm y) * F y) p
  let M : ℝ≥0∞ := ENNReal.ofReal c * N
  have hN : N ≠ ⊤ := by
    have h := hWeightedF.eLpNorm_lt_top
    simpa only [r, ENNReal.ofReal_toReal hp'] using h.ne
  have hM : M ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN
  refine ⟨M.toReal, ?_⟩
  intro τ hτ hτT
  have hK : Measurable (Function.uncurry (momentKernel 4 θ τ)) :=
    Measurable.comp
      (g := fun q : (ℝ × ℝ) × Configuration 4 × Configuration 4 =>
        momentKernel 4 q.1.1 q.1.2 q.2.1 q.2.2)
      (f := fun q : Configuration 4 × Configuration 4 => ((θ, τ), q))
      (measurable_momentKernel 4) (measurable_const.prodMk measurable_id)
  have hWeight : Measurable (fun x : Configuration 4 => a * configurationOneNorm x) :=
    measurable_const.mul (Flow.measurable_configurationOneNorm 4)
  have hApply := WeightedFormBound.integrable_and_eLpNorm_configurationKernelAction_le
    hr hWeight hK ENNReal.ofReal_ne_top (hBound τ hτ hτT) hF hWeightedF
  have hNorm : eLpNorm (fun x : Configuration 4 => Real.exp (a * configL1Norm x) *
      ∫ y, (momentKernel 4 θ τ x y).toReal * ∏ i, g i (y i)) p ≤ M := by
    simpa only [configurationKernelAction, r, ENNReal.ofReal_toReal hp'] using hApply.2
  exact hNorm.trans_eq (ENNReal.ofReal_toReal hM).symm

end Critical2DKPZ.SHF.Tsai

end
