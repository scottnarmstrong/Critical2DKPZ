/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.L2CurvePrimitive
public import Critical2DKPZ.Extensions.ScaleLimit.RemainderWeightInterval
import Mathlib.Tactic

/-! # Weighted square envelopes for high-frequency primitive curves -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

/-- A primitive curve with the high-frequency derivative decay has a square
envelope independent of the ratio of the endpoints. The weight is `a/r²`. -/
theorem exists_weighted_L2_curve_square_envelope (F V : ℝ → Lp ℝ 2 P)
    (hV : Continuous V) {a α β C N : ℝ} (ha : 0 < a) (hα : 0 < α) (hαβ : α < β)
    (hC : 0 ≤ C) (hN : 0 ≤ N)
    (hder : ∀ r ∈ Set.Icc α β, HasDerivAt F (V r) r)
    (hstart : ‖F α‖ ^ 2 ≤ C * (a / α) ^ 2 * N)
    (hbound : ∀ r ∈ Set.Icc α β, ‖V r‖ ^ 2 ≤ C * r⁻¹ ^ 2 * (a / r) ^ 2 * N) :
    ∃ u : ℝ → Ω → ℝ, ∃ Z : Ω → ℝ,
      (∀ r ∈ Set.Icc α β, u r =ᵐ[P] (F r : Ω → ℝ)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun r => u r ω) (Set.Icc α β)) ∧
      Integrable Z P ∧ (∀ ω, 0 ≤ Z ω) ∧
      (∀ᵐ ω ∂P, ∀ r ∈ Set.Icc α β, u r ω ^ 2 ≤ Z ω) ∧
      (∫ ω, Z ω ∂P) ≤ 4 * C * (a / α) ^ 2 * N := by
  obtain ⟨v, hvm, hrep⟩ := exists_real_joint_L2_version P V hV
  let G := ∫ r in Set.Icc α β, a / r ^ 2
  obtain ⟨hG0, hGa⟩ := remainder_weight_Icc_budget ha hα hαβ
  change 0 < G at hG0
  change G ≤ a / α at hGa
  have heq (t : ℝ) (ω : Ω) : v t ω ^ 2 / (a / t ^ 2) = (t ^ 2 / a) * v t ω ^ 2 := by
    rw [div_div_eq_mul_div]
    ring
  have hmean (t : ℝ) : (∫ ω, (t ^ 2 / a) * v t ω ^ 2 ∂P) = (t ^ 2 / a) * ‖V t‖ ^ 2 := by
    rw [integral_const_mul, norm_Lp_two_sq]
    congr 1
    apply integral_congr_ae
    filter_upwards [hrep t] with ω hω
    rw [hω, Real.norm_eq_abs, sq_abs]
  have hqm : Measurable (fun q : ℝ × Ω => (q.1 ^ 2 / a) * v q.1 q.2 ^ 2) :=
    ((measurable_fst.pow_const 2).div_const a).mul (hvm.pow_const 2)
  have hqprod : Integrable (fun q : ℝ × Ω => (q.1 ^ 2 / a) * v q.1 q.2 ^ 2)
      ((volume.restrict (Set.Icc α β)).prod P) := by
    apply (integrable_prod_iff hqm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun t =>
      (((memLp_congr_ae (hrep t)).mpr (Lp.memLp (V t))).integrable_sq).const_mul (t ^ 2 / a)), ?_⟩
    have heqm : (fun t : ℝ => ∫ ω, ‖(t ^ 2 / a) * v t ω ^ 2‖ ∂P) =
        fun t => (t ^ 2 / a) * ‖V t‖ ^ 2 := by
      funext t
      calc
        _ = ∫ ω, (t ^ 2 / a) * v t ω ^ 2 ∂P := by
          apply integral_congr_ae
          exact Eventually.of_forall fun ω => by
            change ‖(t ^ 2 / a) * v t ω ^ 2‖ = (t ^ 2 / a) * v t ω ^ 2
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) ha.le) (sq_nonneg _))]
        _ = _ := hmean t
    change Integrable (fun t : ℝ => ∫ ω, ‖(t ^ 2 / a) * v t ω ^ 2‖ ∂P) _
    rw [heqm]
    exact (((continuous_id.pow 2).div_const a).mul (hV.norm.pow 2)).integrableOn_Icc
  have hvprod := integral_L2_version_prod P V hV v hvm hrep α β
  let u : ℝ → Ω → ℝ := fun r ω => F α ω + ∫ t in Set.Icc α r, v t ω
  let Z : Ω → ℝ := fun ω => 2 * F α ω ^ 2 +
    2 * G * ∫ t in Set.Icc α β, (t ^ 2 / a) * v t ω ^ 2
  obtain ⟨hu, huc⟩ := L2_curve_primitive_version P F V hV α β hder v hvm hrep
  have hZi : Integrable Z P := ((Lp.memLp (F α)).integrable_sq.const_mul 2).add
    (hqprod.integral_prod_right.const_mul _)
  refine ⟨u, Z, hu, huc, hZi, ?_, ?_, ?_⟩
  · intro ω
    exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
      (mul_nonneg (by positivity) (integral_nonneg fun t =>
        mul_nonneg (div_nonneg (sq_nonneg _) ha.le) (sq_nonneg _)))
  · filter_upwards [hvprod.prod_left_ae, hqprod.prod_left_ae] with ω hvi hqi
    intro r hr
    have hq : IntegrableOn (fun t => v t ω ^ 2 / (a / t ^ 2)) (Set.Icc α β) := by
      exact hqi.congr (Eventually.of_forall fun t => (heq t ω).symm)
    have hua : u α ω = F α ω := by dsimp [u]; simp
    have hprim : ∀ q ∈ Set.Icc α β, u q ω = u α ω + ∫ t in Set.Icc α q, v t ω := by
      intro q _
      rw [hua]
    have hpos : ∀ᵐ t ∂volume.restrict (Set.Icc α β), 0 < a / t ^ 2 := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact div_pos ha (sq_pos_of_pos (hα.trans_le ht.1))
    have hh := primitive_sq_le_weighted (fun r => u r ω) (fun t => v t ω)
      (fun t => a / t ^ 2) hprim hvi (remainder_weight_Icc hα hαβ.le).1 hq hpos hG0 hr
    have hInt : (∫ t in Set.Icc α β, v t ω ^ 2 / (a / t ^ 2)) =
        ∫ t in Set.Icc α β, (t ^ 2 / a) * v t ω ^ 2 :=
      integral_congr_ae (Eventually.of_forall fun t => heq t ω)
    change u r ω ^ 2 ≤ 2 * F α ω ^ 2 + 2 * G * (∫ t in Set.Icc α β, (t ^ 2 / a) * v t ω ^ 2)
    rw [hua, hInt] at hh
    exact hh
  · have hFα : (∫ ω, F α ω ^ 2 ∂P) = ‖F α‖ ^ 2 := by
      rw [norm_Lp_two_sq]
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by
        change F α ω ^ 2 = ‖F α ω‖ ^ 2
        rw [Real.norm_eq_abs, sq_abs]
    have hswap : Integrable (fun q : Ω × ℝ => (q.2 ^ 2 / a) * v q.2 q.1 ^ 2)
        (P.prod (volume.restrict (Set.Icc α β))) := hqprod.swap
    have hQ : (∫ t in Set.Icc α β, (t ^ 2 / a) * ‖V t‖ ^ 2) ≤ C * N * G := by
      calc
        _ ≤ ∫ t in Set.Icc α β, (C * N) * (a / t ^ 2) := by
          apply setIntegral_mono_on
            ((((continuous_id.pow 2).div_const a).mul (hV.norm.pow 2)).integrableOn_Icc)
            ((remainder_weight_Icc hα hαβ.le).1.const_mul _) measurableSet_Icc
          intro t ht
          have ht0 : 0 < t := hα.trans_le ht.1
          calc
            _ ≤ (t ^ 2 / a) * (C * t⁻¹ ^ 2 * (a / t) ^ 2 * N) :=
              mul_le_mul_of_nonneg_left (hbound t ht) (div_nonneg (sq_nonneg _) ha.le)
            _ = _ := by field_simp
        _ = _ := by rw [integral_const_mul]
    have hGsq : G ^ 2 ≤ (a / α) ^ 2 := (sq_le_sq₀ hG0.le (div_pos ha hα).le).mpr hGa
    calc
      (∫ ω, Z ω ∂P) = 2 * ‖F α‖ ^ 2 + 2 * G *
          (∫ t in Set.Icc α β, (t ^ 2 / a) * ‖V t‖ ^ 2) := by
        rw [integral_add ((Lp.memLp (F α)).integrable_sq.const_mul 2)
          (hqprod.integral_prod_right.const_mul _), integral_const_mul, integral_const_mul, hFα,
          integral_integral_swap (f := fun ω t => (t ^ 2 / a) * v t ω ^ 2) hswap]
        congr 2
        exact integral_congr_ae (Eventually.of_forall hmean)
      _ ≤ 2 * (C * (a / α) ^ 2 * N) + 2 * G * (C * N * G) :=
        add_le_add (mul_le_mul_of_nonneg_left hstart (by norm_num))
          (mul_le_mul_of_nonneg_left hQ (by positivity))
      _ = 2 * (C * (a / α) ^ 2 * N) + (2 * C * N) * G ^ 2 := by ring
      _ ≤ 2 * (C * (a / α) ^ 2 * N) + (2 * C * N) * (a / α) ^ 2 :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hGsq (show 0 ≤ 2 * C * N by positivity))
      _ = _ := by ring

end Critical2DKPZ.Extensions.ScaleLimit
