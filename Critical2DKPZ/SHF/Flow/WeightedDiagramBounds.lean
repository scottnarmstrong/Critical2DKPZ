/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.WeightedDiagramAction

/-! # Uniform weighted collision bounds on bounded time windows -/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- A bounded parameter and time window give a uniform finite scalar collision mass. -/
theorem ofReal_integral_scalarDensity_Ioo_le {B θ v T : ℝ}
    (hθ : θ ≤ B) (hv : 0 < v) (hvT : v ≤ T) :
    IntegrableOn (scalarDensity θ) (Ioo 0 v) ∧
      ENNReal.ofReal (∫ s in Ioo 0 v, scalarDensity θ s) ≤
        ENNReal.ofReal (Real.exp (Real.exp (B + 1) * T)) := by
  have hj : IntegrableOn (scalarDensity θ) (Ioo 0 v) :=
    (integral_scalarDensity_Ioo_le_laplace (θ := θ) (v := v)
      (Real.exp_pos (θ + 1)) (by rw [Real.log_exp]; linarith)).1
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (0 : ℝ) v)] scalarDensity θ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact (scalarDensity_pos θ hs.1).le
  refine ⟨hj, ?_⟩
  rw [ofReal_integral_eq_lintegral_ofReal hj hn]
  calc
    _ ≤ ENNReal.ofReal (Real.exp (Real.exp (θ + 1) * v)) := lintegral_scalarDensity_Ioo_le
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul (Real.exp_le_exp.mpr (add_le_add hθ (le_refl (1 : ℝ)))) hvT hv.le (Real.exp_pos _).le))

/-- Uniform boundedness of the weighted single diagram throughout a bounded window. -/
theorem exists_diagramKernel_singleton_weighted_l2_bound (n : ℕ) (B a T : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (α : CollisionPair n) (θ v : ℝ),
      θ ≤ B → 0 < v → v ≤ T → ∀ f : Configuration n → ℝ≥0∞, Measurable f →
      (∫⁻ x : Configuration n, (∫⁻ y : Configuration n,
        expConjugate (fun x => a * configurationOneNorm x) (fun y => a * configurationOneNorm y)
          (diagramKernel θ [α] v) x y * f y) ^ 2) ≤ C ^ 2 * ∫⁻ y : Configuration n, f y ^ 2 := by
  let C := endpointBetaConstant * ENNReal.ofReal (weightGrowth n a T) ^ 3 *
    ENNReal.ofReal (Real.exp (Real.exp (B + 1) * T))
  have hC : C ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top endpointBetaConstant_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
    ENNReal.ofReal_ne_top
  refine ⟨C, hC, fun α θ v hθ hv hvT f hf => ?_⟩
  simp_rw [diagramKernel_singleton_weighted_action_eq α θ a v hf]
  have h := weightedCollisionTimeAction_l2_sq_le α θ (T := T) ha hvT hf
  exact h.trans (mul_le_mul' (pow_le_pow_left'
    (mul_le_mul' le_rfl (ofReal_integral_scalarDensity_Ioo_le hθ hv hvT).2) 2) le_rfl)

end Critical2DKPZ.SHF.Flow

end
