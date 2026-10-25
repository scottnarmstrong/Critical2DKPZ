/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.L2CurvePrimitive
public import Critical2DKPZ.Extensions.ScaleLimit.RemainderWeights
import Mathlib.Tactic

/-! # Square-integrable envelopes for primitive random curves -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- A continuously differentiable L2 curve starting at zero has a continuous
version with an integrable square envelope. Its budget depends only on the
interval length and a uniform derivative norm bound. -/
theorem exists_L2_curve_square_envelope (F V : ℝ → Lp ℝ 2 P)
    (hV : Continuous V) (hF0 : F 0 = 0) {β K : ℝ} (hβ : 0 < β) (hK : 0 ≤ K)
    (hder : ∀ r ∈ Set.Icc 0 β, HasDerivAt F (V r) r)
    (hbound : ∀ r ∈ Set.Icc 0 β, ‖V r‖ ≤ K) :
    ∃ u : ℝ → Ω → ℝ, ∃ Z : Ω → ℝ,
      (∀ r ∈ Set.Icc 0 β, u r =ᵐ[P] (F r : Ω → ℝ)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun r => u r ω) (Set.Icc 0 β)) ∧
      Integrable Z P ∧ (∀ ω, 0 ≤ Z ω) ∧
      (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc 0 β, u r ω ^ 2 ≤ Z ω) ∧
      (∫ ω, Z ω ∂P) ≤ 2 * β ^ 2 * K ^ 2 := by
  obtain ⟨v, hvm, hrep⟩ := exists_real_joint_L2_version P V hV
  let u : ℝ → Ω → ℝ := fun r ω => F 0 ω + ∫ t in Set.Icc 0 r, v t ω
  let Z : Ω → ℝ := fun ω => 2 * β * ∫ t in Set.Icc 0 β, v t ω ^ 2
  have hs := integral_L2_version_sq_prod P V hV v hvm hrep 0 β
  have hv := integral_L2_version_prod P V hV v hvm hrep 0 β
  obtain ⟨hu, huc⟩ := L2_curve_primitive_version P F V hV 0 β hder v hvm hrep
  have hZi : Integrable Z P := hs.integral_prod_right.const_mul _
  refine ⟨u, Z, hu, huc, hZi, ?_, ?_, ?_⟩
  · intro ω
    exact mul_nonneg (by positivity) (integral_nonneg fun _ => sq_nonneg _)
  · have hzero : (F 0 : Ω → ℝ) =ᵐ[P] 0 := by rw [hF0]; exact Lp.coeFn_zero _ _ _
    filter_upwards [hv.prod_left_ae, hs.prod_left_ae, hzero] with ω hvi hsi h0
    change F 0 ω = 0 at h0
    have hzint : (∫ t in Set.Icc (0 : ℝ) 0, v t ω) = 0 := by simp
    intro r hr
    have hprim : ∀ q ∈ Set.Icc (0 : ℝ) β, u q ω = u 0 ω + ∫ t in Set.Icc 0 q, v t ω := by
      intro q _
      simp only [u, hzint, add_zero]
    have hG : (∫ _ : ℝ in Set.Icc 0 β, (1 : ℝ)) = β := by simp [hβ.le]
    have hh := primitive_sq_le_weighted (fun r => u r ω) (fun t => v t ω) (fun _ => 1)
      hprim hvi (integrableOn_const (by simp)) (hsi.div_const 1)
      (Eventually.of_forall fun _ => zero_lt_one) (by rw [hG]; exact hβ) hr
    change u r ω ^ 2 ≤ 2 * β * (∫ t in Set.Icc 0 β, v t ω ^ 2)
    simpa only [u, h0, hzint, add_zero, zero_add, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, hG, div_one] using hh
  · have heq (t : ℝ) : (∫ ω, v t ω ^ 2 ∂P) = ‖V t‖ ^ 2 := by
      rw [norm_Lp_two_sq]
      apply integral_congr_ae
      filter_upwards [hrep t] with ω hω
      rw [hω, Real.norm_eq_abs, sq_abs]
    calc
      (∫ ω, Z ω ∂P) = 2 * β * ∫ t in Set.Icc 0 β, ‖V t‖ ^ 2 := by
        have hswap : Integrable (fun q : Ω × ℝ => v q.2 q.1 ^ 2)
            (P.prod (volume.restrict (Set.Icc 0 β))) := hs.swap
        change (∫ ω, 2 * β * (∫ t in Set.Icc 0 β, v t ω ^ 2) ∂P) = _
        rw [integral_const_mul, integral_integral_swap (f := fun ω t => v t ω ^ 2) hswap]
        congr 1
        exact integral_congr_ae (Eventually.of_forall heq)
      _ ≤ 2 * β * ∫ _ : ℝ in Set.Icc 0 β, K ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply setIntegral_mono_on (hV.norm.pow 2).integrableOn_Icc (integrableOn_const (by simp))
          measurableSet_Icc
        intro t ht
        exact (sq_le_sq₀ (norm_nonneg _) hK).mpr (hbound t ht)
      _ = 2 * β ^ 2 * K ^ 2 := by simp [hβ.le]; ring

end Critical2DKPZ.Extensions.ScaleLimit
