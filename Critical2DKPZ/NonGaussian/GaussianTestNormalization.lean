/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.KPZScalarMeasurability
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic

/-! # Normalizing nonnegative KPZ test functions -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Distributions ENNReal

namespace Critical2DKPZ.NonGaussian

/-- A Gaussian flat-initial KPZ pairing at a nonzero nonnegative test gives a Gaussian pairing
at the test normalized to have integral one, including when the variance is zero. -/
theorem exists_normalized_test_gaussian_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₀ : ψ ≠ 0)
    (hGauss : ∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) = gaussianReal m v) :
    ∃ φ : TestFn, (∀ x, 0 ≤ φ x) ∧ (∫ x, φ x) = 1 ∧
      ∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω φ) = gaussianReal m v := by
  have hψI : Integrable (ψ : Plane → ℝ) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hc : 0 < ∫ x, ψ x := by
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hψ₀
    have hxpos : 0 < ψ x := lt_of_le_of_ne (hψ x) (Ne.symm hx)
    apply (integral_pos_iff_support_of_nonneg hψ hψI).mpr
    have hOpen := (isOpen_lt continuous_const ψ.continuous).measure_pos volume ⟨x, hxpos⟩
    exact hOpen.trans_le (measure_mono fun y hy => ne_of_gt hy)
  let a : ℝ := (∫ x, ψ x)⁻¹
  let φ : TestFn := a • ψ
  have hφ : ∀ x, 0 ≤ φ x := by
    intro x
    change 0 ≤ a * ψ x
    exact mul_nonneg (inv_nonneg.mpr hc.le) (hψ x)
  have hφmean : (∫ x, φ x) = 1 := by
    change (∫ x, a * ψ x) = 1
    rw [integral_const_mul]
    exact inv_mul_cancel₀ hc.ne'
  obtain ⟨m, v, hlaw⟩ := hGauss
  have hmeas := aemeasurable_criticalKPZ_flat_pairing ϑ P Z hZ H hH ht ψ
  have hmap : P.map (fun ω => H t 0 ω φ) =
      (P.map (fun ω => H t 0 ω ψ)).map (fun z => a * z) := by
    have hMul : Measurable (fun z : ℝ => a * z) := measurable_const.mul measurable_id
    rw [AEMeasurable.map_map_of_aemeasurable (g := fun z : ℝ => a * z) hMul.aemeasurable hmeas]
    congr 1
    funext ω
    exact (H t 0 ω).map_smul a ψ
  refine ⟨φ, hφ, hφmean, a * m, NNReal.mk (a ^ 2) (sq_nonneg a) * v, ?_⟩
  rw [hmap, hlaw, gaussianReal_map_const_mul]

end Critical2DKPZ.NonGaussian

end
