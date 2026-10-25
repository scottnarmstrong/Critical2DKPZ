/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.LevyConvergence
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic

/-! # A uniform Lyapunov central limit estimate -/

@[expose] public section

namespace Critical2DKPZ.LogNormality

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BoundedContinuousFunction

private theorem abs_cos_sub_one_add_sq_le_three_mul_abs_cube (x : ℝ) :
    |Real.cos x - 1 + x ^ 2 / 2| ≤ 3 * |x| ^ 3 := by
  let y := x / 2
  have hcos : Real.cos x - 1 + x ^ 2 / 2 = 2 * (y ^ 2 - Real.sin y ^ 2) := by
    dsimp [y]
    have hcosTwo := Real.cos_two_mul (x / 2)
    have hx : 2 * (x / 2) = x := by ring
    rw [hx] at hcosTwo
    rw [hcosTwo]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have hsmall : |x| ≤ 1 → |Real.cos x - 1 + x ^ 2 / 2| ≤ 3 * |x| ^ 3 := by
    intro hx
    have hsin : |y - Real.sin y| ≤ |y| ^ 3 / 6 := Real.abs_sub_sin_le y
    have hsin' : |Real.sin y - y| ≤ |y| ^ 3 / 6 := by simpa [abs_sub_comm] using hsin
    have hsinabs : |Real.sin y| ≤ |y| := Real.abs_sin_le_abs (x := y)
    have hsum : |y + Real.sin y| ≤ 2 * |y| := by
      calc
        |y + Real.sin y| ≤ |y| + |Real.sin y| := abs_add_le _ _
        _ ≤ |y| + |y| := add_le_add le_rfl hsinabs
        _ = 2 * |y| := by ring
    have hfac : y ^ 2 - Real.sin y ^ 2 = (y - Real.sin y) * (y + Real.sin y) := by ring
    have hsmallcalc :
        |Real.cos x - 1 + x ^ 2 / 2| ≤ |x| ^ 4 / 24 := by
      rw [hcos, hfac, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul]
      calc
        2 * (|y - Real.sin y| * |y + Real.sin y|) ≤
            2 * ((|y| ^ 3 / 6) * (2 * |y|)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hsin hsum (abs_nonneg _) (by positivity)) (by norm_num)
        _ = |x| ^ 4 / 24 := by dsimp [y]; rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; ring
    have hx3 : |x| ^ 4 ≤ |x| ^ 3 := by
      calc
        |x| ^ 4 = |x| ^ 3 * |x| := by ring
        _ ≤ |x| ^ 3 * 1 := mul_le_mul_of_nonneg_left hx (pow_nonneg (abs_nonneg x) 3)
        _ = |x| ^ 3 := by ring
    have hdiv : |x| ^ 4 / 24 ≤ |x| ^ 3 / 24 := div_le_div_of_nonneg_right hx3 (by norm_num)
    have hsmall' : |x| ^ 3 / 24 ≤ 3 * |x| ^ 3 := by
      nlinarith [pow_nonneg (abs_nonneg x) 3]
    exact hsmallcalc.trans (hdiv.trans hsmall')
  by_cases hx : |x| ≤ 1
  · exact hsmall hx
  · have hxlarge : 1 ≤ |x| := le_of_not_ge hx
    have hrough : |Real.cos x - 1 + x ^ 2 / 2| ≤ 2 + |x| ^ 2 / 2 := by
      calc
        |Real.cos x - 1 + x ^ 2 / 2| ≤ |Real.cos x| + 1 + |x ^ 2 / 2| := by
          calc
            _ ≤ |Real.cos x - 1| + |x ^ 2 / 2| := abs_add_le _ _
            _ ≤ |Real.cos x| + 1 + |x ^ 2 / 2| := by
              have h := abs_sub_le (Real.cos x) 0 1
              simpa using add_le_add_right h |x ^ 2 / 2|
        _ ≤ 2 + |x| ^ 2 / 2 := by
          have hx2 : |x ^ 2 / 2| = |x| ^ 2 / 2 := by
            rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_nonneg (sq_nonneg x)]
            rw [sq_abs]
          rw [hx2]
          nlinarith [Real.abs_cos_le_one x]
    have hxlin : |x| ≤ |x| ^ 3 := by nlinarith [sq_nonneg (|x| - 1)]
    have hxconst : 1 ≤ |x| ^ 3 := by nlinarith [sq_nonneg (|x| - 1)]
    nlinarith

private theorem norm_exp_mul_I_sub_quadratic_le_four_mul_abs_cube (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
      (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ 4 * |x| ^ 3 := by
  have hsin : |Real.sin x - x| ≤ |x| ^ 3 / 6 := by
    simpa [abs_sub_comm] using Real.abs_sub_sin_le x
  have hcos := abs_cos_sub_one_add_sq_le_three_mul_abs_cube x
  have hrepr : Complex.exp ((x : ℂ) * Complex.I) -
      (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2) =
      (Real.cos x - 1 + x ^ 2 / 2 : ℝ) + (Real.sin x - x) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I]
    apply Complex.ext
    · simp
      ring
    · simp
      ring
  calc
    _ = ‖(Real.cos x - 1 + x ^ 2 / 2 : ℝ) + (Real.sin x - x) * Complex.I‖ := by rw [hrepr]
    _ ≤ |Real.cos x - 1 + x ^ 2 / 2| + |Real.sin x - x| := by
      have h := Complex.norm_le_abs_re_add_abs_im
        ((Real.cos x - 1 + x ^ 2 / 2 : ℝ) + (Real.sin x - x) * Complex.I)
      simpa only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        mul_one, zero_add, add_zero, sub_zero, zero_sub, Complex.cos_ofReal_re,
        Complex.sin_ofReal_re] using h
    _ ≤ 3 * |x| ^ 3 + |x| ^ 3 / 6 := add_le_add hcos hsin
    _ ≤ 4 * |x| ^ 3 := by nlinarith [pow_nonneg (abs_nonneg x) 3]

/-- An `L³` random variable has integrable first, second, and absolute third moments. -/
private theorem integrable_moments_of_memLp_three {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX3 : MemLp X 3 μ) :
    Integrable X μ ∧ Integrable (fun ω => X ω ^ 2) μ ∧
      Integrable (fun ω => |X ω| ^ 3) μ := by
  have hX2 : MemLp X 2 μ := hX3.mono_exponent (by norm_num)
  have hX1 : MemLp X 1 μ := hX2.mono_exponent (by norm_num)
  exact ⟨memLp_one_iff_integrable.1 hX1,
    (memLp_two_iff_integrable_sq hX3.aestronglyMeasurable).1 hX2,
    by simpa [Real.norm_eq_abs] using hX3.integrable_norm_pow'⟩


/-- The expected quadratic Taylor remainder of `exp (itX)` is bounded in norm by
`4 |t|³ E[|X|³]` for measurable `X ∈ L³`. -/
private theorem integral_exp_taylor_remainder_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX3 : MemLp X 3 μ) (t : ℝ) :
    ‖∫ ω, Complex.exp ((t * X ω : ℝ) * Complex.I) -
      (1 + (t * X ω : ℝ) * Complex.I - (t * X ω : ℝ) ^ 2 / 2) ∂μ‖ ≤
      (4 * |t| ^ 3) * ∫ ω, |X ω| ^ 3 ∂μ := by
  have hMom := integrable_moments_of_memLp_three μ X hX3
  have hXint := hMom.1
  have hXsqInt := hMom.2.1
  have hXcubeInt := hMom.2.2
  have hlin : Integrable (fun ω => (t * X ω : ℝ) * Complex.I) μ := by
    have h := hXint.ofReal.const_mul ((t : ℂ) * Complex.I)
    convert h using 1
    ext ω
    push_cast
    simp [mul_comm, mul_left_comm]
  have hquad : Integrable (fun ω => ((t * X ω : ℝ) ^ 2 / 2 : ℂ)) μ := by
    have h := hXsqInt.ofReal.const_mul (((t : ℝ) ^ 2 / 2 : ℝ) : ℂ)
    convert h using 1
    ext ω
    norm_cast
    push_cast
    field_simp
    rfl
  have hpoly : Integrable
      (fun ω => (1 : ℂ) + (t * X ω : ℝ) * Complex.I - (t * X ω : ℝ) ^ 2 / 2) μ := by
    exact (integrable_const (1 : ℂ)).add hlin |>.sub hquad
  have hexp : Integrable (fun ω => Complex.exp ((t * X ω : ℝ) * Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with ω
    rw [Complex.norm_exp_ofReal_mul_I]
  have hrem : Integrable
      (fun ω => Complex.exp ((t * X ω : ℝ) * Complex.I) -
        (1 + (t * X ω : ℝ) * Complex.I - (t * X ω : ℝ) ^ 2 / 2)) μ := hexp.sub hpoly
  have hboundInt : Integrable (fun ω => (4 * |t| ^ 3) * |X ω| ^ 3) μ := by
    have h := hXcubeInt.const_mul (4 * |t| ^ 3)
    convert h using 1
  have hbound (ω : Ω) :
      ‖Complex.exp ((t * X ω : ℝ) * Complex.I) -
        (1 + (t * X ω : ℝ) * Complex.I - (t * X ω : ℝ) ^ 2 / 2)‖ ≤
        (4 * |t| ^ 3) * |X ω| ^ 3 := by
    calc
      _ ≤ 4 * |t * X ω| ^ 3 := norm_exp_mul_I_sub_quadratic_le_four_mul_abs_cube (t * X ω)
      _ = (4 * |t| ^ 3) * |X ω| ^ 3 := by rw [abs_mul, mul_pow]; ring
  calc
    _ ≤ ∫ ω, ‖Complex.exp ((t * X ω : ℝ) * Complex.I) -
        (1 + (t * X ω : ℝ) * Complex.I - (t * X ω : ℝ) ^ 2 / 2)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ ω, (4 * |t| ^ 3) * |X ω| ^ 3 ∂μ := integral_mono hrem.norm hboundInt hbound
    _ = (4 * |t| ^ 3) * ∫ ω, |X ω| ^ 3 ∂μ := integral_const_mul _ _

/-- A centred real `L³` variable has characteristic function `1 - t² E[X²] / 2` up to an error
bounded by `4 |t|³ E[|X|³]`. -/
private theorem charFun_map_centered_quadratic_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    (hX3 : MemLp X 3 μ) (hmean : ∫ ω, X ω ∂μ = 0) (t : ℝ) :
    ‖charFun (μ.map X) t -
      (1 - ((t : ℂ) ^ 2 / 2) * ∫ ω, (X ω : ℂ) ^ 2 ∂μ)‖ ≤
      (4 * |t| ^ 3) * ∫ ω, |X ω| ^ 3 ∂μ := by
  have hMom := integrable_moments_of_memLp_three μ X hX3
  have hXint := hMom.1
  have hXsqInt := hMom.2.1
  have hchar : charFun (μ.map X) t =
      ∫ ω, Complex.exp ((t * X ω : ℝ) * Complex.I) ∂μ := by
    rw [MeasureTheory.charFun_apply_real]
    have hExpMap : Integrable (fun y : ℝ => Complex.exp (t * y * Complex.I)) (μ.map X) := by
      apply Integrable.of_bound (by fun_prop) 1
      filter_upwards [] with y
      simpa only [Complex.ofReal_mul] using (Complex.norm_exp_ofReal_mul_I (t * y)).le
    rw [integral_map hX.aemeasurable hExpMap.aestronglyMeasurable]
    apply integral_congr_ae
    filter_upwards [] with ω
    simp only [Complex.ofReal_mul]
  have hlin : ∫ ω, (t * X ω : ℝ) * Complex.I ∂μ =
      (t * Complex.I) * (∫ ω, (X ω : ℂ) ∂μ) := by
    calc
      _ = ∫ ω, (t * Complex.I) * (X ω : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        push_cast
        simp [mul_comm, mul_left_comm]
      _ = _ := integral_const_mul _ _
  have hmeanComplex : ∫ ω, (X ω : ℂ) ∂μ = 0 := by
    norm_cast
  have hquad : ∫ ω, ((t * X ω : ℝ) ^ 2 / 2 : ℂ) ∂μ =
      ((t : ℂ) ^ 2 / 2) * (∫ ω, (X ω : ℂ) ^ 2 ∂μ) := by
    calc
      _ = ∫ ω, ((t : ℂ) ^ 2 / 2) * (X ω : ℂ) ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with ω
        have hreal : (t * X ω) ^ 2 / 2 = (t ^ 2 / 2) * X ω ^ 2 := by ring
        simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
          Complex.ofReal_ofNat] using
          congrArg (fun r : ℝ => (r : ℂ)) hreal
      _ = _ := integral_const_mul _ _
  have hlinFunInt : Integrable (fun ω => (t * X ω : ℝ) * Complex.I) μ := by
    have h := hXint.ofReal.const_mul ((t : ℂ) * Complex.I)
    convert h using 1
    ext ω
    push_cast
    simp [mul_comm, mul_left_comm]
  have hquadFunInt : Integrable (fun ω => ((t * X ω : ℝ) ^ 2 / 2 : ℂ)) μ := by
    have h := hXsqInt.ofReal.const_mul (((t : ℝ) ^ 2 / 2 : ℝ) : ℂ)
    convert h using 1
    ext ω
    norm_cast
    push_cast
    field_simp
    rfl
  have hpolyInt : Integrable
      (fun ω => (1 : ℂ) + (t * X ω : ℝ) * Complex.I - (t * X ω : ℝ) ^ 2 / 2) μ :=
    (integrable_const (1 : ℂ)).add hlinFunInt |>.sub hquadFunInt
  have hpoly : ∫ ω, (1 : ℂ) + (t * X ω : ℝ) * Complex.I -
        (t * X ω : ℝ) ^ 2 / 2 ∂μ =
      (1 : ℂ) - ((t : ℂ) ^ 2 / 2) * ∫ ω, (X ω : ℂ) ^ 2 ∂μ := by
    calc
      _ = (∫ ω, (1 : ℂ) + (t * X ω : ℝ) * Complex.I ∂μ) -
          ∫ ω, ((t * X ω : ℝ) ^ 2 / 2 : ℂ) ∂μ :=
        integral_sub ((integrable_const (1 : ℂ)).add hlinFunInt) hquadFunInt
      _ = (∫ ω, (1 : ℂ) ∂μ + ∫ ω, (t * X ω : ℝ) * Complex.I ∂μ) -
          ∫ ω, ((t * X ω : ℝ) ^ 2 / 2 : ℂ) ∂μ := by
        rw [integral_add (integrable_const (1 : ℂ)) hlinFunInt]
      _ = _ := by
        rw [integral_const, probReal_univ, one_smul, hlin, hmeanComplex,
          mul_zero, add_zero, hquad]
  have hexp : Integrable (fun ω => Complex.exp ((t * X ω : ℝ) * Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with ω
    rw [Complex.norm_exp_ofReal_mul_I]
  have hrem := integral_exp_taylor_remainder_le μ X hX hX3 t
  calc
    _ = ‖(∫ ω, Complex.exp ((t * X ω : ℝ) * Complex.I) ∂μ) -
        ∫ ω, (1 : ℂ) + (t * X ω : ℝ) * Complex.I -
          (t * X ω : ℝ) ^ 2 / 2 ∂μ‖ := by rw [hchar, ← hpoly]
    _ = ‖∫ ω, Complex.exp ((t * X ω : ℝ) * Complex.I) -
        ((1 : ℂ) + (t * X ω : ℝ) * Complex.I -
          (t * X ω : ℝ) ^ 2 / 2) ∂μ‖ := by rw [← integral_sub hexp hpolyInt]
    _ ≤ _ := hrem

private theorem norm_finset_prod_sub_le_sum_norm_sub {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℂ)
    (ha : ∀ i ∈ s, ‖a i‖ ≤ 1) (hb : ∀ i ∈ s, ‖b i‖ ≤ 1) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ ≤ ∑ i ∈ s, ‖a i - b i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      have hprodA : ‖∏ j ∈ s, a j‖ ≤ 1 := by
        rw [norm_prod]
        apply Finset.prod_le_one₀
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          exact ha j (Finset.mem_insert_of_mem hj)
      have hprodB : ‖∏ j ∈ s, b j‖ ≤ 1 := by
        rw [norm_prod]
        apply Finset.prod_le_one₀
        · intro j hj
          exact norm_nonneg _
        · intro j hj
          exact hb j (Finset.mem_insert_of_mem hj)
      calc
        ‖a i * ∏ j ∈ s, a j - b i * ∏ j ∈ s, b j‖ =
            dist (a i * ∏ j ∈ s, a j) (b i * ∏ j ∈ s, b j) := by rw [dist_eq_norm]
        _ ≤ dist (a i * ∏ j ∈ s, a j) (b i * ∏ j ∈ s, a j) +
              dist (b i * ∏ j ∈ s, a j) (b i * ∏ j ∈ s, b j) := dist_triangle _ _ _
        _ = ‖a i - b i‖ * ‖∏ j ∈ s, a j‖ +
              ‖b i‖ * ‖∏ j ∈ s, a j - ∏ j ∈ s, b j‖ := by
          rw [dist_eq_norm, dist_eq_norm, ← sub_mul, norm_mul, ← mul_sub, norm_mul]
        _ ≤ ‖a i - b i‖ + ‖∏ j ∈ s, a j - ∏ j ∈ s, b j‖ := by
          have hdiff := norm_nonneg (a i - b i)
          have hsum := norm_nonneg (∏ j ∈ s, a j - ∏ j ∈ s, b j)
          calc
            _ ≤ ‖a i - b i‖ * 1 + 1 * ‖∏ j ∈ s, a j - ∏ j ∈ s, b j‖ := by
              exact add_le_add
                (mul_le_mul_of_nonneg_left hprodA hdiff)
                (mul_le_mul_of_nonneg_right (hb i (Finset.mem_insert_self i s)) hsum)
            _ = _ := by ring
        _ ≤ ‖a i - b i‖ + ∑ j ∈ s, ‖a j - b j‖ :=
          by
            simpa [add_comm] using add_le_add_right
              (ih (fun j hj => ha j (Finset.mem_insert_of_mem hj))
                (fun j hj => hb j (Finset.mem_insert_of_mem hj))) ‖a i - b i‖

private theorem norm_exp_neg_sub_one_add_le_square {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ‖Complex.exp (-(a : ℂ)) - (1 - (a : ℂ))‖ ≤ a ^ 2 := by
  have hnorm : ‖-(a : ℂ)‖ ≤ 1 := by
    simpa [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha] using ha1
  have h := Complex.norm_exp_sub_one_sub_id_le (x := -(a : ℂ)) hnorm
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

private theorem integral_sq_cube_interpolation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX3 : MemLp X 3 μ) :
    Integrable (fun ω => X ω ^ 2) μ ∧ Integrable (fun ω => |X ω| ^ 3) μ ∧
      (∫ ω, X ω ^ 2 ∂μ) ^ 3 ≤ (∫ ω, |X ω| ^ 3 ∂μ) ^ 2 := by
  have hX2 : MemLp X 2 μ := hX3.mono_exponent (by norm_num)
  have hXmeas : AEStronglyMeasurable X μ := hX3.aestronglyMeasurable
  let v : ℝ := ∫ ω, X ω ^ 2 ∂μ
  let r : ℝ := ∫ ω, |X ω| ^ 3 ∂μ
  have hv : 0 ≤ v := by
    dsimp [v]
    exact integral_nonneg (fun ω => sq_nonneg (X ω))
  have hr : 0 ≤ r := by
    dsimp [r]
    exact integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3)
  refine ⟨(memLp_two_iff_integrable_sq hXmeas).1 hX2, ?_, ?_⟩
  · simpa [Real.norm_eq_abs] using hX3.integrable_norm_pow'
  · have hLp : lpNorm X 2 μ ≤ lpNorm X 3 μ := by
      rw [← toReal_eLpNorm, ← toReal_eLpNorm]
      exact ENNReal.toReal_mono hX3.eLpNorm_ne_top
        (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))
    have hLp2 : lpNorm X 2 μ = v ^ (1 / 2 : ℝ) := by
      dsimp [v]
      rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hXmeas]
      simp [Real.norm_eq_abs, sq_abs]
    have hLp3 : lpNorm X 3 μ = r ^ (1 / 3 : ℝ) := by
      dsimp [r]
      rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hXmeas]
      simp [Real.norm_eq_abs]
    have hpow : (lpNorm X 2 μ) ^ 6 ≤ (lpNorm X 3 μ) ^ 6 :=
      pow_le_pow_left₀ (lpNorm_nonneg) hLp 6
    rw [hLp2, hLp3] at hpow
    have hroot2 : (v ^ (1 / 2 : ℝ)) ^ 2 = v := by
      rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hv (by norm_num)
    have hroot3 : (r ^ (1 / 3 : ℝ)) ^ 3 = r := by
      rw [show (1 / 3 : ℝ) = (3 : ℝ)⁻¹ by norm_num]
      exact Real.rpow_inv_natCast_pow hr (by norm_num)
    calc
      v ^ 3 = ((v ^ (1 / 2 : ℝ)) ^ 2) ^ 3 := by rw [hroot2]
      _ = (v ^ (1 / 2 : ℝ)) ^ 6 := by ring
      _ ≤ (r ^ (1 / 3 : ℝ)) ^ 6 := hpow
      _ = ((r ^ (1 / 3 : ℝ)) ^ 3) ^ 2 := by ring
      _ = r ^ 2 := by rw [hroot3]

private theorem sq_le_of_cube_sq_le {v r : ℝ} (hv : 0 ≤ v) (hr : 0 ≤ r)
    (hr1 : r ≤ 1) (hvr : v ^ 3 ≤ r ^ 2) : v ^ 2 ≤ r := by
  by_contra h
  have hrv : r < v ^ 2 := lt_of_not_ge h
  have hvr' : r < v := by
    by_contra hnot
    have hvle : v ≤ r := le_of_not_gt hnot
    have hv2 : v ^ 2 ≤ r ^ 2 := by
      calc
        v ^ 2 = v * v := by ring
        _ ≤ r * v := mul_le_mul_of_nonneg_right hvle hv
        _ ≤ r * r := mul_le_mul_of_nonneg_left hvle hr
        _ = r ^ 2 := by ring
    have hr2 : r ^ 2 ≤ r := by
      calc
        r ^ 2 = r * r := by ring
        _ ≤ 1 * r := mul_le_mul_of_nonneg_right hr1 hr
        _ = r := by ring
    exact (not_lt_of_ge (hv2.trans hr2)) hrv
  have hvpos : 0 < v := lt_of_le_of_lt hr hvr'
  have hprod1 : r ^ 2 ≤ v * r := by
    calc
      r ^ 2 = r * r := by ring
      _ ≤ v * r := mul_le_mul_of_nonneg_right hvr'.le hr
  have hprod2 : v * r < v ^ 3 := by
    calc
      v * r < v * (v ^ 2) := mul_lt_mul_of_pos_left hrv hvpos
      _ = v ^ 3 := by ring
  nlinarith

/-- The bounded exponential kernel used in characteristic functions is integrable under a
probability pushforward. -/
private theorem integrable_charFun_kernel {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (_hX : Measurable X) (t : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (t * x * Complex.I)) (μ.map X) := by
  apply Integrable.of_bound (by fun_prop) 1
  filter_upwards [] with x
  simpa only [Complex.ofReal_mul] using (Complex.norm_exp_ofReal_mul_I (t * x)).le

/-- The characteristic function of a real probability law has modulus at most one. -/
private theorem norm_charFun_map_le_one {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (_hX : Measurable X) (t : ℝ) :
    ‖charFun (μ.map X) t‖ ≤ 1 := by
  rw [MeasureTheory.charFun_apply_real]
  have hExp := integrable_charFun_kernel μ X _hX t
  calc
    ‖∫ x, Complex.exp (t * x * Complex.I) ∂(μ.map X)‖ ≤
        ∫ x, ‖Complex.exp (t * x * Complex.I)‖ ∂(μ.map X) :=
      norm_integral_le_integral_norm (fun x : ℝ => Complex.exp (t * x * Complex.I))
    _ = 1 := by
      have hnorm : (fun x : ℝ => ‖Complex.exp (t * x * Complex.I)‖) = fun _ => (1 : ℝ) := by
        funext x
        simpa only [Complex.ofReal_mul] using Complex.norm_exp_ofReal_mul_I (t * x)
      rw [hnorm, integral_const, probReal_univ]
      simp

private theorem charFun_map_eq_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X) (t : ℝ) :
    charFun (μ.map X) t = ∫ ω, Complex.exp ((t * X ω : ℝ) * Complex.I) ∂μ := by
  rw [MeasureTheory.charFun_apply_real]
  have hExp := integrable_charFun_kernel μ X hX t
  rw [integral_map hX.aemeasurable hExp.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [Complex.ofReal_mul]

private theorem charFun_add_perturbation_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Z : Ω → ℝ)
    (hX : Measurable X) (hZ : Measurable Z) (t ε : ℝ) (hε : 0 ≤ ε) :
    ‖charFun (μ.map (fun ω => X ω + Z ω)) t - charFun (μ.map X) t‖ ≤
      |t| * ε + 2 * μ.real {ω | ε ≤ |Z ω|} := by
  let E : Set Ω := {ω | ε ≤ |Z ω|}
  have hE : MeasurableSet E := by
    dsimp [E]
    exact measurableSet_le measurable_const (continuous_abs.measurable.comp hZ)
  have hEint : Integrable (E.indicator (1 : Ω → ℝ)) μ := by
    rw [integrable_indicator_iff hE]
    exact integrable_const 1
  have hEintVal : ∫ ω, E.indicator (1 : Ω → ℝ) ω ∂μ = μ.real E :=
    integral_indicator_one hE
  have hExp (F : Ω → ℝ) (hF : Measurable F) :
      Integrable (fun ω => Complex.exp ((t * F ω : ℝ) * Complex.I)) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with ω
    simpa only [Complex.ofReal_mul] using (Complex.norm_exp_ofReal_mul_I (t * F ω)).le
  have hExpX := hExp X hX
  have hExpXZ := hExp (fun ω => X ω + Z ω) (hX.add hZ)
  have hpoint (ω : Ω) :
      ‖Complex.exp ((t * (X ω + Z ω) : ℝ) * Complex.I) -
        Complex.exp ((t * X ω : ℝ) * Complex.I)‖ ≤
        |t| * ε + 2 * E.indicator (1 : Ω → ℝ) ω := by
    by_cases hω : ω ∈ E
    · have hrough :
          ‖Complex.exp ((t * (X ω + Z ω) : ℝ) * Complex.I) -
            Complex.exp ((t * X ω : ℝ) * Complex.I)‖ ≤ 2 := by
        calc
          _ ≤ ‖Complex.exp ((t * (X ω + Z ω) : ℝ) * Complex.I)‖ +
              ‖Complex.exp ((t * X ω : ℝ) * Complex.I)‖ := norm_sub_le _ _
          _ = 2 := by
            rw [Complex.norm_exp_ofReal_mul_I, Complex.norm_exp_ofReal_mul_I]
            norm_num
      simpa [E, hω] using (by linarith [hrough, mul_nonneg (abs_nonneg t) hε] :
          ‖Complex.exp ((t * (X ω + Z ω) : ℝ) * Complex.I) -
            Complex.exp ((t * X ω : ℝ) * Complex.I)‖ ≤ |t| * ε + 2)
    · have hZsmall : |Z ω| < ε := lt_of_not_ge (by simpa [E] using hω)
      have hfactor :
          Complex.exp ((t * (X ω + Z ω) : ℝ) * Complex.I) -
            Complex.exp ((t * X ω : ℝ) * Complex.I) =
          Complex.exp ((t * X ω : ℝ) * Complex.I) *
            (Complex.exp ((t * Z ω : ℝ) * Complex.I) - 1) := by
        have harg : (t * (X ω + Z ω) : ℝ) * Complex.I =
            (t * X ω : ℝ) * Complex.I + (t * Z ω : ℝ) * Complex.I := by
          push_cast
          ring
        rw [harg, Complex.exp_add]
        ring
      have hlin : ‖Complex.exp ((t * Z ω : ℝ) * Complex.I) - 1‖ ≤ |t| * ε := by
        calc
          _ ≤ ‖t * Z ω‖ := by
            simpa [mul_comm, Real.norm_eq_abs] using
              (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * Z ω))
          _ = |t| * |Z ω| := by rw [Real.norm_eq_abs, abs_mul]
          _ ≤ |t| * ε := mul_le_mul_of_nonneg_left hZsmall.le (abs_nonneg t)
      rw [hfactor, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      simpa [E, hω] using hlin
  have hMajor : Integrable
      (fun ω => |t| * ε + 2 * E.indicator (1 : Ω → ℝ) ω) μ := by
    exact (integrable_const _).add (hEint.const_mul 2)
  calc
    _ = ‖∫ ω, Complex.exp ((t * (X ω + Z ω) : ℝ) * Complex.I) -
        Complex.exp ((t * X ω : ℝ) * Complex.I) ∂μ‖ := by
          rw [charFun_map_eq_integral (μ := μ) (X := fun ω => X ω + Z ω)
              (hX.add hZ) t,
            charFun_map_eq_integral (μ := μ) (X := X) hX t,
            ← integral_sub hExpXZ hExpX]
    _ ≤ ∫ ω, ‖Complex.exp ((t * (X ω + Z ω) : ℝ) * Complex.I) -
        Complex.exp ((t * X ω : ℝ) * Complex.I)‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, |t| * ε + 2 * E.indicator (1 : Ω → ℝ) ω ∂μ :=
      integral_mono (hExpXZ.sub hExpX).norm hMajor hpoint
    _ = |t| * ε + 2 * μ.real E := by
      rw [integral_add (integrable_const _) (hEint.const_mul 2)]
      rw [integral_const, probReal_univ, integral_const_mul, hEintVal]
      simp

/-- Under the stated smallness assumptions, the characteristic function of a finite independent
centred sum differs from the matching Gaussian characteristic function by at most
`(4 |t|³ + t⁴ / 4) ∑ E[|Xᵢ|³]`. -/
private theorem charFun_finsetSum_close_exp_quadratic {Ω ι : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (I : Finset ι) (X : ι → Ω → ℝ) (t : ℝ)
    (hIndep : iIndepFun X μ) (hMeas : ∀ i ∈ I, Measurable (X i))
    (hMem : ∀ i ∈ I, MemLp (X i) 3 μ)
    (hMean : ∀ i ∈ I, ∫ ω, X i ω ∂μ = 0)
    (hThird : ∑ i ∈ I, ∫ ω, |X i ω| ^ 3 ∂μ ≤ 1)
    (hSmall : ∀ i ∈ I, t ^ 2 / 2 * ∫ ω, X i ω ^ 2 ∂μ ≤ 1) :
    ‖charFun (μ.map (fun ω => ∑ i ∈ I, X i ω)) t -
        Complex.exp (-((t : ℂ) ^ 2 / 2) *
          (∑ i ∈ I, ∫ ω, X i ω ^ 2 ∂μ : ℝ))‖ ≤
      (4 * |t| ^ 3 + t ^ 4 / 4) * ∑ i ∈ I, ∫ ω, |X i ω| ^ 3 ∂μ := by
  classical
  let v : ι → ℝ := fun i => ∫ ω, X i ω ^ 2 ∂μ
  let r : ι → ℝ := fun i => ∫ ω, |X i ω| ^ 3 ∂μ
  let a : ι → ℝ := fun i => t ^ 2 / 2 * v i
  have hrnonneg (i : ι) : 0 ≤ r i := by
    dsimp [r]
    exact integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3)
  have hrle (i : ι) (hi : i ∈ I) : r i ≤ 1 := by
    calc
      r i ≤ ∑ j ∈ I, r j := Finset.single_le_sum (fun j hj => hrnonneg j) hi
      _ ≤ 1 := by simpa [r] using hThird
  have hinterp (i : ι) (hi : i ∈ I) :
      Integrable (fun ω => X i ω ^ 2) μ ∧
        Integrable (fun ω => |X i ω| ^ 3) μ ∧ v i ^ 3 ≤ r i ^ 2 := by
    simpa [v, r] using integral_sq_cube_interpolation μ (X i) (hMem i hi)
  have hvnonneg (i : ι) : 0 ≤ v i := by
    dsimp [v]
    exact integral_nonneg (fun ω => sq_nonneg (X i ω))
  have hv2le (i : ι) (hi : i ∈ I) : v i ^ 2 ≤ r i :=
    sq_le_of_cube_sq_le (hvnonneg i) (hrnonneg i) (hrle i hi) (hinterp i hi).2.2
  have hvle (i : ι) (hi : i ∈ I) : v i ≤ 1 := by
    have hv2 : v i ^ 2 ≤ 1 := (hv2le i hi).trans (hrle i hi)
    nlinarith [sq_nonneg (v i - 1)]
  have hatnonneg (i : ι) : 0 ≤ a i := by
    dsimp [a]
    positivity
  have hatle (i : ι) (hi : i ∈ I) : a i ≤ 1 := by
    simpa [a, v] using hSmall i hi
  have hFactor (i : ι) (hi : i ∈ I) :
      ‖charFun (μ.map (X i)) t - Complex.exp (-(a i : ℂ))‖ ≤
        (4 * |t| ^ 3 + t ^ 4 / 4) * r i := by
    have hquad := charFun_map_centered_quadratic_bound μ (X i) (hMeas i hi)
      (hMem i hi) (hMean i hi) t
    have hcomplexSq : ∫ ω, (X i ω : ℂ) ^ 2 ∂μ = (v i : ℂ) := by
      dsimp [v]
      norm_cast
    have hpoly : 1 - ((t : ℂ) ^ 2 / 2) * ∫ ω, (X i ω : ℂ) ^ 2 ∂μ =
        1 - (a i : ℂ) := by
      rw [hcomplexSq]
      dsimp [a, v]
      push_cast
      ring
    have hchar : ‖charFun (μ.map (X i)) t - (1 - (a i : ℂ))‖ ≤
        (4 * |t| ^ 3) * r i := by
      rw [← hpoly]
      simpa [r] using hquad
    have hexp := norm_exp_neg_sub_one_add_le_square (hatnonneg i) (hatle i hi)
    have hexp' : ‖(1 - (a i : ℂ)) - Complex.exp (-(a i : ℂ))‖ ≤ a i ^ 2 := by
      simpa only [norm_sub_rev] using hexp
    have hsq : a i ^ 2 ≤ (t ^ 4 / 4) * r i := by
      dsimp [a]
      nlinarith [hv2le i hi, pow_nonneg (sq_nonneg t) (2 : ℕ)]
    calc
      _ ≤ ‖charFun (μ.map (X i)) t - (1 - (a i : ℂ))‖ +
          ‖(1 - (a i : ℂ)) - Complex.exp (-(a i : ℂ))‖ := by
            calc
              _ = ‖(charFun (μ.map (X i)) t - (1 - (a i : ℂ))) +
                  ((1 - (a i : ℂ)) - Complex.exp (-(a i : ℂ)))‖ := by congr 1; ring
              _ ≤ _ := norm_add_le _ _
      _ ≤ (4 * |t| ^ 3) * r i + a i ^ 2 := add_le_add hchar hexp'
      _ ≤ (4 * |t| ^ 3 + t ^ 4 / 4) * r i := by nlinarith [hrnonneg i]
  have hprodChar : charFun (μ.map (fun ω => ∑ i ∈ I, X i ω)) t =
      ∏ i ∈ I, charFun (μ.map (X i)) t := by
    have hprod := (hIndep.restrict I).charFun_map_fun_finsetSum_eq_prod
      (fun i hi => (hMeas i hi).aemeasurable)
    simpa only [Finset.prod_apply] using congrFun hprod t
  have hprodExp : ∏ i ∈ I, Complex.exp (-(a i : ℂ)) =
      Complex.exp (-((t : ℂ) ^ 2 / 2) * (∑ i ∈ I, v i : ℝ)) := by
    have hsum : ∑ i ∈ I, (-(a i : ℂ)) =
        -((t : ℂ) ^ 2 / 2) * (∑ i ∈ I, v i : ℝ) := by
      rw [Finset.sum_neg_distrib]
      simp [a, Finset.mul_sum]
    rw [← Complex.exp_sum, hsum]
  have hcharNorm (i : ι) (hi : i ∈ I) : ‖charFun (μ.map (X i)) t‖ ≤ 1 :=
    norm_charFun_map_le_one μ (X i) (hMeas i hi) t
  have hexpNorm (i : ι) : ‖Complex.exp (-(a i : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hatnonneg i))
  have hprodDiff := norm_finset_prod_sub_le_sum_norm_sub I
    (fun i => charFun (μ.map (X i)) t) (fun i => Complex.exp (-(a i : ℂ)))
    (fun i hi => hcharNorm i hi) (fun i hi => hexpNorm i)
  calc
    _ = ‖(∏ i ∈ I, charFun (μ.map (X i)) t) -
        ∏ i ∈ I, Complex.exp (-(a i : ℂ))‖ := by rw [hprodChar, hprodExp]
    _ ≤ ∑ i ∈ I, ‖charFun (μ.map (X i)) t - Complex.exp (-(a i : ℂ))‖ := hprodDiff
    _ ≤ ∑ i ∈ I, (4 * |t| ^ 3 + t ^ 4 / 4) * r i := by
      exact Finset.sum_le_sum fun i hi => hFactor i hi
    _ = (4 * |t| ^ 3 + t ^ 4 / 4) * ∑ i ∈ I, r i := by
      rw [Finset.mul_sum]
    _ = _ := by simp [r]

private theorem tendsto_charFun_finsetSum_of_lyapunov
    {Ω ι : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (μ : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (μ n)]
    (I : ∀ n, Finset (ι n)) (X : ∀ n, ι n → Ω n → ℝ)
    (hIndep : ∀ n, iIndepFun (X n) (μ n))
    (hMeas : ∀ n i, Measurable (X n i))
    (hMem : ∀ n i, i ∈ I n → MemLp (X n i) 3 (μ n))
    (hMean : ∀ n i, i ∈ I n → ∫ ω, X n i ω ∂(μ n) = 0)
    (hVar : Tendsto (fun n => ∑ i ∈ I n, ∫ ω, X n i ω ^ 2 ∂(μ n))
      atTop (𝓝 1))
    (hThird : Tendsto (fun n => ∑ i ∈ I n, ∫ ω, |X n i ω| ^ 3 ∂(μ n))
      atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => charFun ((μ n).map (fun ω => ∑ i ∈ I n, X n i ω)) t)
      atTop (𝓝 (Complex.exp (-((t : ℂ) ^ 2 / 2)))) := by
  classical
  let V : ℕ → ℝ := fun n => ∑ i ∈ I n, ∫ ω, X n i ω ^ 2 ∂(μ n)
  let R : ℕ → ℝ := fun n => ∑ i ∈ I n, ∫ ω, |X n i ω| ^ 3 ∂(μ n)
  let Y : ∀ n, ι n → Ω n → ℝ := fun n i ω => t * X n i ω
  have hV : Tendsto V atTop (𝓝 1) := by simpa [V] using hVar
  have hR : Tendsto R atTop (𝓝 0) := by simpa [R] using hThird
  have hRnonneg (n : ℕ) : 0 ≤ R n := by
    dsimp [R]
    apply Finset.sum_nonneg
    intro i hi
    exact integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3)
  have hRYeq (n : ℕ) :
      (∑ i ∈ I n, ∫ ω, |Y n i ω| ^ 3 ∂(μ n)) = |t| ^ 3 * R n := by
    calc
      _ = ∑ i ∈ I n, |t| ^ 3 * ∫ ω, |X n i ω| ^ 3 ∂(μ n) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfun : (fun ω => |Y n i ω| ^ 3) =
            fun ω => |t| ^ 3 * |X n i ω| ^ 3 := by
          funext ω
          simp [Y, abs_mul, mul_pow]
        rw [hfun, integral_const_mul]
      _ = |t| ^ 3 * R n := by rw [Finset.mul_sum]
  have hVYeq (n : ℕ) :
      (∑ i ∈ I n, ∫ ω, (Y n i ω) ^ 2 ∂(μ n)) = t ^ 2 * V n := by
    calc
      _ = ∑ i ∈ I n, t ^ 2 * ∫ ω, X n i ω ^ 2 ∂(μ n) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfun : (fun ω => (Y n i ω) ^ 2) =
            fun ω => t ^ 2 * X n i ω ^ 2 := by
          funext ω
          simp [Y, mul_pow]
        rw [hfun, integral_const_mul]
      _ = t ^ 2 * V n := by rw [Finset.mul_sum]
  have hVY : Tendsto (fun n => ∑ i ∈ I n, ∫ ω, (Y n i ω) ^ 2 ∂(μ n))
      atTop (𝓝 (t ^ 2)) := by
    simpa [hVYeq] using hV.const_mul (t ^ 2)
  let e : ℝ := 1 / (|t| ^ 3 + 1)
  have he : 0 < e := by dsimp [e]; positivity
  have hRsmall : ∀ᶠ n in atTop, R n < e := hR.eventually (Iio_mem_nhds he)
  have hRscaled_le_one : ∀ᶠ n in atTop, |t| ^ 3 * R n ≤ 1 := by
    filter_upwards [hRsmall] with n hn
    have ht3 : 0 ≤ |t| ^ 3 := pow_nonneg (abs_nonneg t) 3
    calc
      |t| ^ 3 * R n ≤ |t| ^ 3 * e := mul_le_mul_of_nonneg_left hn.le ht3
      _ ≤ 1 := by
        dsimp [e]
        calc
          |t| ^ 3 * (1 / (|t| ^ 3 + 1)) = |t| ^ 3 / (|t| ^ 3 + 1) := by ring
          _ ≤ 1 := (div_le_one₀ (by positivity : 0 < |t| ^ 3 + 1)).2 (by linarith)
  have hMemY (n : ℕ) (i : ι n) (hi : i ∈ I n) : MemLp (Y n i) 3 (μ n) := by
    simpa [Y] using (hMem n i hi).const_mul t
  have hMeanY (n : ℕ) (i : ι n) (hi : i ∈ I n) :
      ∫ ω, Y n i ω ∂(μ n) = 0 := by
    rw [show (fun ω => Y n i ω) = fun ω => t * X n i ω by rfl, integral_const_mul,
      hMean n i hi]
    simp
  have hIndepY (n : ℕ) : iIndepFun (Y n) (μ n) := by
    exact (hIndep n).comp (fun (_ : ι n) (x : ℝ) => t * x)
      (fun (_ : ι n) => by fun_prop)
  let S : ∀ n, Ω n → ℝ := fun n ω => ∑ i ∈ I n, X n i ω
  have hSmeas (n : ℕ) : Measurable (S n) := by
    dsimp [S]
    exact Finset.measurable_sum _ fun i hi => hMeas n i
  have hScaleSum (n : ℕ) : (fun ω => ∑ i ∈ I n, Y n i ω) = fun ω => t * S n ω := by
    funext ω
    simp [Y, S, Finset.mul_sum]
  have hCharScale (n : ℕ) :
      charFun ((μ n).map (fun ω => ∑ i ∈ I n, Y n i ω)) 1 =
        charFun ((μ n).map (S n)) t := by
    rw [hScaleSum, charFun_map_mul_comp (hSmeas n).aemeasurable t 1]
    simp
  have hsmallY (n : ℕ) (hn : |t| ^ 3 * R n ≤ 1) (i : ι n) (hi : i ∈ I n) :
      1 ^ 2 / 2 * ∫ ω, (Y n i ω) ^ 2 ∂(μ n) ≤ 1 := by
    let v : ℝ := ∫ ω, (Y n i ω) ^ 2 ∂(μ n)
    let r : ℝ := ∫ ω, |Y n i ω| ^ 3 ∂(μ n)
    have hinterp := integral_sq_cube_interpolation (μ n) (Y n i) (hMemY n i hi)
    have hrnonneg : 0 ≤ r := by
      dsimp [r]
      exact integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3)
    have hrle : r ≤ 1 := by
      calc
        r ≤ ∑ j ∈ I n, ∫ ω, |Y n j ω| ^ 3 ∂(μ n) := by
          change (∫ ω, |Y n i ω| ^ 3 ∂(μ n)) ≤ _
          exact Finset.single_le_sum (f := fun j => ∫ ω, |Y n j ω| ^ 3 ∂(μ n))
            (fun j hj => integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3)) hi
        _ = |t| ^ 3 * R n := hRYeq n
        _ ≤ 1 := hn
    have hvnonneg : 0 ≤ v := by
      dsimp [v]
      exact integral_nonneg (fun ω => sq_nonneg (Y n i ω))
    have hv2 : v ^ 2 ≤ r :=
      sq_le_of_cube_sq_le hvnonneg hrnonneg hrle hinterp.2.2
    have hvle : v ≤ 1 := by nlinarith [hv2]
    change 1 ^ 2 / 2 * v ≤ 1
    norm_num
    linarith
  have hrowBound : ∀ᶠ n in atTop,
      ‖charFun ((μ n).map (S n)) t -
          Complex.exp (-((t : ℂ) ^ 2 / 2) * (V n : ℂ))‖ ≤
        (17 / 4 : ℝ) * (|t| ^ 3 * R n) := by
    filter_upwards [hRscaled_le_one] with n hn
    have hrow := charFun_finsetSum_close_exp_quadratic (μ n) (I n) (Y n) 1
      (hIndepY n) (fun i hi => by fun_prop)
      (fun i hi => hMemY n i hi) (fun i hi => hMeanY n i hi)
      (by simpa [hRYeq n] using hn)
      (fun i hi => hsmallY n hn i hi)
    rw [hCharScale n, hVYeq n, hRYeq n] at hrow
    convert hrow using 1
    norm_num
    ring_nf
    ring
  let f : ℝ → ℂ := fun x => Complex.exp (-((t : ℂ) ^ 2 / 2) * (x : ℂ))
  have hfcont : Continuous f := by fun_prop
  have hExp : Tendsto (fun n => f (V n)) atTop (𝓝 (f 1)) :=
    hfcont.continuousAt.tendsto.comp hV
  have hErrorNorm : Tendsto
      (fun n => ‖charFun ((μ n).map (S n)) t - f (V n)‖) atTop (𝓝 0) := by
    have hBoundLim : Tendsto (fun n => (17 / 4 : ℝ) * (|t| ^ 3 * R n))
        atTop (𝓝 0) := by
      have hR' := hR.const_mul ((17 / 4 : ℝ) * |t| ^ 3)
      have hfun : (fun n => (17 / 4 : ℝ) * (|t| ^ 3 * R n)) =
          fun n => ((17 / 4 : ℝ) * |t| ^ 3) * R n := by
        funext n
        ring
      simpa only [hfun, mul_zero] using hR'
    apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
      hrowBound
    exact hBoundLim
  have hError : Tendsto
      (fun n => charFun ((μ n).map (S n)) t - f (V n)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hErrorNorm
  have hsum : (fun n => charFun ((μ n).map (S n)) t) =
      fun n => (charFun ((μ n).map (S n)) t - f (V n)) + f (V n) := by
    funext n
    ring
  rw [hsum]
  simpa [f] using hError.add hExp

open scoped BoundedContinuousFunction

private structure LyapunovRowData where
  Ω : Type
  ι : Type
  mΩ : MeasurableSpace Ω
  μ : @Measure Ω mΩ
  I : Finset ι
  X : ι → Ω → ℝ
  Z : Ω → ℝ
  s : ℝ

private def LyapunovRowData.good (h : ℝ →ᵇ ℝ) (η δ : ℝ)
    (d : LyapunovRowData) : Prop := by
  letI : MeasurableSpace d.Ω := d.mΩ
  exact IsProbabilityMeasure d.μ ∧ 0 < d.s ∧ iIndepFun d.X d.μ ∧
    (∀ i, Measurable (d.X i)) ∧ Measurable d.Z ∧
    (∀ i ∈ d.I, MemLp (d.X i) 3 d.μ) ∧
    (∀ i ∈ d.I, (∫ ω, d.X i ω ∂d.μ) = 0) ∧
    |(∑ i ∈ d.I, (∫ ω, d.X i ω ^ 2 ∂d.μ)) - d.s ^ 2| ≤ δ * d.s ^ 2 ∧
    (∑ i ∈ d.I, (∫ ω, |d.X i ω| ^ 3 ∂d.μ)) ≤ δ * d.s ^ 3 ∧
    (d.μ {ω | δ * d.s < |d.Z ω|}).toReal ≤ δ ∧
    η < |(∫ ω, h ((∑ i ∈ d.I, d.X i ω + d.Z ω) / d.s) ∂d.μ) -
      (∫ y, h y ∂(gaussianReal 0 1))|

set_option linter.style.haveILetI false in
/-- For finite independent centred sums, small normalized third moments and variance error imply
a uniform approximation by the standard Gaussian in a fixed bounded continuous test.
The approximation is stable under perturbations small in probability. -/
theorem exists_lyapunov_clt_bound (h : ℝ →ᵇ ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {Ω ι : Type} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] (I : Finset ι) (X : ι → Ω → ℝ) (Z : Ω → ℝ) (s : ℝ), 0 < s →
      iIndepFun X μ → (∀ i, Measurable (X i)) → Measurable Z →
      (∀ i ∈ I, MemLp (X i) 3 μ) → (∀ i ∈ I, (∫ ω, X i ω ∂μ) = 0) →
      |(∑ i ∈ I, (∫ ω, X i ω ^ 2 ∂μ)) - s ^ 2| ≤ δ * s ^ 2 →
      (∑ i ∈ I, (∫ ω, |X i ω| ^ 3 ∂μ)) ≤ δ * s ^ 3 →
      (μ {ω | δ * s < |Z ω|}).toReal ≤ δ →
      |(∫ ω, h ((∑ i ∈ I, X i ω + Z ω) / s) ∂μ) -
        (∫ y, h y ∂(gaussianReal 0 1))| ≤ η := by
  by_contra hno
  push Not at hno
  classical
  let δseq : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hδseq_pos (n : ℕ) : 0 < δseq n := by
    dsimp [δseq]
    positivity
  have hrows (n : ℕ) : ∃ d : LyapunovRowData,
      LyapunovRowData.good h η (δseq n) d := by
    rcases hno (δseq n) (hδseq_pos n) with
      ⟨Ω, ι, mΩ, μ, hμ, I, X, Z, s, hs, hIndep, hMeas, hZMeas,
        hMem, hMean, hVar, hThird, hTail, hBad⟩
    let d : LyapunovRowData := ⟨Ω, ι, mΩ, μ, I, X, Z, s⟩
    refine ⟨d, ?_⟩
    dsimp [LyapunovRowData.good, d]
    exact ⟨hμ, hs, hIndep, hMeas, hZMeas, hMem, hMean, hVar, hThird, hTail, hBad⟩
  let d : ℕ → LyapunovRowData := fun n => Classical.choose (hrows n)
  have hd (n : ℕ) : LyapunovRowData.good h η (δseq n) (d n) :=
    Classical.choose_spec (hrows n)
  have hδseq : Tendsto δseq atTop (𝓝 0) := by
    simpa [δseq] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  let Ωseq : ℕ → Type := fun n => (d n).Ω
  let ιseq : ℕ → Type := fun n => (d n).ι
  letI : ∀ n, MeasurableSpace (Ωseq n) := fun n => (d n).mΩ
  have hdata (n : ℕ) :
      IsProbabilityMeasure (d n).μ ∧ 0 < (d n).s ∧ iIndepFun (d n).X (d n).μ ∧
        (∀ i, Measurable ((d n).X i)) ∧ Measurable (d n).Z ∧
        (∀ i ∈ (d n).I, MemLp ((d n).X i) 3 (d n).μ) ∧
        (∀ i ∈ (d n).I, (∫ ω, (d n).X i ω ∂(d n).μ) = 0) ∧
        |(∑ i ∈ (d n).I, (∫ ω, (d n).X i ω ^ 2 ∂(d n).μ)) - (d n).s ^ 2| ≤
          δseq n * (d n).s ^ 2 ∧
        (∑ i ∈ (d n).I, (∫ ω, |(d n).X i ω| ^ 3 ∂(d n).μ)) ≤
          δseq n * (d n).s ^ 3 ∧
        ((d n).μ {ω | δseq n * (d n).s < |(d n).Z ω|}).toReal ≤ δseq n ∧
        η < |(∫ ω, h ((∑ i ∈ (d n).I, (d n).X i ω + (d n).Z ω) / (d n).s)
            ∂(d n).μ) - (∫ y, h y ∂(gaussianReal 0 1))| := by
    simpa [LyapunovRowData.good] using hd n
  let μseq : ∀ n, Measure (Ωseq n) := fun n => (d n).μ
  letI : ∀ n, IsProbabilityMeasure (μseq n) := fun n => (hdata n).1
  let Iseq : ∀ n, Finset (ιseq n) := fun n => (d n).I
  let Xraw : ∀ n, ιseq n → Ωseq n → ℝ := fun n i ω => (d n).X i ω
  let Zraw : ∀ n, Ωseq n → ℝ := fun n ω => (d n).Z ω
  let sseq : ℕ → ℝ := fun n => (d n).s
  let Xnorm : ∀ n, ιseq n → Ωseq n → ℝ := fun n i ω => Xraw n i ω / sseq n
  let Znorm : ∀ n, Ωseq n → ℝ := fun n ω => Zraw n ω / sseq n
  let Vraw : ℕ → ℝ := fun n => ∑ i ∈ Iseq n, ∫ ω, Xraw n i ω ^ 2 ∂(μseq n)
  let Rraw : ℕ → ℝ := fun n => ∑ i ∈ Iseq n, ∫ ω, |Xraw n i ω| ^ 3 ∂(μseq n)
  let Vnorm : ℕ → ℝ := fun n => ∑ i ∈ Iseq n, ∫ ω, Xnorm n i ω ^ 2 ∂(μseq n)
  let Rnorm : ℕ → ℝ := fun n => ∑ i ∈ Iseq n, ∫ ω, |Xnorm n i ω| ^ 3 ∂(μseq n)
  have hXmeas (n : ℕ) (i : ιseq n) : Measurable (Xraw n i) := (hdata n).2.2.2.1 i
  have hZmeas (n : ℕ) : Measurable (Zraw n) := (hdata n).2.2.2.2.1
  have hXmem (n : ℕ) (i : ιseq n) (hi : i ∈ Iseq n) : MemLp (Xraw n i) 3 (μseq n) :=
    (hdata n).2.2.2.2.2.1 i hi
  have hXmean (n : ℕ) (i : ιseq n) (hi : i ∈ Iseq n) :
      ∫ ω, Xraw n i ω ∂(μseq n) = 0 := (hdata n).2.2.2.2.2.2.1 i hi
  have hspos (n : ℕ) : 0 < sseq n := (hdata n).2.1
  have hIndep (n : ℕ) : iIndepFun (Xraw n) (μseq n) := (hdata n).2.2.1
  have hXnormMeas (n : ℕ) (i : ιseq n) : Measurable (Xnorm n i) := by
    exact (hXmeas n i).div_const (sseq n)
  have hXnormMem (n : ℕ) (i : ιseq n) (hi : i ∈ Iseq n) :
      MemLp (Xnorm n i) 3 (μseq n) := by
    simpa [Xnorm, div_eq_mul_inv, mul_comm] using (hXmem n i hi).const_mul (sseq n)⁻¹
  have hXnormMean (n : ℕ) (i : ιseq n) (hi : i ∈ Iseq n) :
      ∫ ω, Xnorm n i ω ∂(μseq n) = 0 := by
    rw [show (fun ω => Xnorm n i ω) = fun ω => (sseq n)⁻¹ * Xraw n i ω by
      funext ω
      simp [Xnorm, div_eq_mul_inv]; ring]
    rw [integral_const_mul, hXmean n i hi]
    simp
  have hIndepNorm (n : ℕ) : iIndepFun (Xnorm n) (μseq n) := by
    exact (hIndep n).comp (fun (_ : ιseq n) (x : ℝ) => x / sseq n)
      (fun (_ : ιseq n) => by fun_prop)
  have hVeq (n : ℕ) : Vnorm n = Vraw n / sseq n ^ 2 := by
    calc
      _ = ∑ i ∈ Iseq n, (∫ ω, Xraw n i ω ^ 2 ∂(μseq n)) / sseq n ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfun : (fun ω => Xnorm n i ω ^ 2) =
            fun ω => Xraw n i ω ^ 2 / sseq n ^ 2 := by
          funext ω
          simp [Xnorm, div_pow]
        rw [hfun, integral_div]
      _ = Vraw n / sseq n ^ 2 := by rw [← Finset.sum_div]
  have hReq (n : ℕ) : Rnorm n = Rraw n / sseq n ^ 3 := by
    calc
      _ = ∑ i ∈ Iseq n, (∫ ω, |Xraw n i ω| ^ 3 ∂(μseq n)) / sseq n ^ 3 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hfun : (fun ω => |Xnorm n i ω| ^ 3) =
            fun ω => |Xraw n i ω| ^ 3 / sseq n ^ 3 := by
          funext ω
          simp [Xnorm, abs_div, abs_of_pos (hspos n), div_pow]
        rw [hfun, integral_div]
      _ = Rraw n / sseq n ^ 3 := by rw [← Finset.sum_div]
  have hVbound (n : ℕ) : |Vnorm n - 1| ≤ δseq n := by
    rcases hdata n with ⟨_, hs, _, _, _, _, _, hv, _, _, _⟩
    have hs2 : 0 < sseq n ^ 2 := by positivity
    rw [hVeq n]
    have hident : Vraw n / sseq n ^ 2 - 1 =
        (Vraw n - sseq n ^ 2) / sseq n ^ 2 := by
      field_simp [ne_of_gt (hspos n)]
    rw [hident, abs_div, abs_of_pos hs2]
    apply (div_le_iff₀ hs2).2
    exact hv
  have hVnormErr : Tendsto (fun n => |Vnorm n - 1|) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
      (Eventually.of_forall hVbound) hδseq
  have hVnorm : Tendsto Vnorm atTop (𝓝 1) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simpa [Real.dist_eq] using hVnormErr
  have hRbound (n : ℕ) : Rnorm n ≤ δseq n := by
    rcases hdata n with ⟨_, hs, _, _, _, _, _, _, hr, _, _⟩
    rw [hReq n]
    apply (div_le_iff₀ (by positivity : 0 < sseq n ^ 3)).2
    exact hr
  have hRnonneg (n : ℕ) : 0 ≤ Rnorm n := by
    dsimp [Rnorm]
    apply Finset.sum_nonneg
    intro i hi
    exact integral_nonneg (fun ω => pow_nonneg (abs_nonneg _) 3)
  have hRnorm : Tendsto Rnorm atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall hRnonneg)
      (Eventually.of_forall hRbound) hδseq
  let S : ∀ n, Ωseq n → ℝ := fun n ω => ∑ i ∈ Iseq n, Xnorm n i ω
  let Y : ∀ n, Ωseq n → ℝ := fun n ω => S n ω + Znorm n ω
  have hSmeas (n : ℕ) : Measurable (S n) := by
    dsimp [S]
    exact Finset.measurable_fun_sum _ (fun i hi => hXnormMeas n i)
  have hZnormMeas (n : ℕ) : Measurable (Znorm n) :=
    (hZmeas n).div_const (sseq n)
  have hYmeas (n : ℕ) : Measurable (Y n) := (hSmeas n).add (hZnormMeas n)
  have hbaseCF (t : ℝ) :
      Tendsto (fun n => charFun ((μseq n).map (S n)) t) atTop
        (𝓝 (charFun (gaussianReal 0 1) t)) := by
    have h := tendsto_charFun_finsetSum_of_lyapunov μseq Iseq Xnorm
      hIndepNorm hXnormMeas hXnormMem hXnormMean hVnorm hRnorm t
    simpa [S, charFun_gaussianReal] using h
  have htailNorm (ε : ℝ) (hε : 0 < ε) :
      Tendsto (fun n => (μseq n {ω | ε ≤ |Znorm n ω|}).toReal) atTop (𝓝 0) := by
    have hδeventually : ∀ᶠ n in atTop, δseq n < ε :=
      hδseq.eventually (Iio_mem_nhds hε)
    have hbound : ∀ᶠ n in atTop,
        (μseq n {ω | ε ≤ |Znorm n ω|}).toReal ≤ δseq n := by
      filter_upwards [hδeventually] with n hn
      rcases hdata n with ⟨hμ, hs, hInd, hXm, hZm, hMem, hMean, hVar, hThird,
        hTail, hBad⟩
      have hsubset : {ω | ε ≤ |Znorm n ω|} ⊆
          {ω | δseq n * sseq n < |Zraw n ω|} := by
        intro ω hω
        have hdiv : ε ≤ |Zraw n ω| / sseq n := by
          simpa [Znorm, abs_div, abs_of_pos (hspos n)] using hω
        have hmul := (le_div_iff₀ (hspos n)).mp hdiv
        calc
          δseq n * sseq n < ε * sseq n := mul_lt_mul_of_pos_right hn (hspos n)
          _ ≤ |Zraw n ω| := hmul
      calc
        (μseq n {ω | ε ≤ |Znorm n ω|}).toReal ≤
            (μseq n {ω | δseq n * sseq n < |Zraw n ω|}).toReal :=
          measureReal_mono hsubset
        _ ≤ δseq n := by simpa [μseq, sseq, Zraw] using hTail
    exact squeeze_zero' (Eventually.of_forall fun n => ENNReal.toReal_nonneg)
      hbound hδseq
  have hperturbCF (t : ℝ) :
      Tendsto (fun n => charFun ((μseq n).map (Y n)) t) atTop
        (𝓝 (charFun (gaussianReal 0 1) t)) := by
    have hclose : Tendsto
        (fun n => charFun ((μseq n).map (Y n)) t -
          charFun ((μseq n).map (S n)) t) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine Metric.tendsto_nhds.mpr ?_
      intro ε hε
      let c : ℝ := ε / (4 * (|t| + 1))
      have hc : 0 < c := by dsimp [c]; positivity
      have hcprod : |t| * c ≤ ε / 4 := by
        have hratio : |t| / (4 * (|t| + 1)) ≤ (1 : ℝ) / 4 := by
          apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (|t| + 1))).2
          nlinarith [abs_nonneg t]
        calc
          |t| * c = ε * (|t| / (4 * (|t| + 1))) := by dsimp [c]; ring
          _ ≤ ε * ((1 : ℝ) / 4) := mul_le_mul_of_nonneg_left hratio (le_of_lt hε)
          _ = ε / 4 := by ring
      have htail := htailNorm c hc
      have htailSmall : ∀ᶠ n in atTop,
          (μseq n {ω | c ≤ |Znorm n ω|}).toReal < ε / 8 := by
        have h := Metric.tendsto_nhds.mp htail (ε / 8) (by positivity)
        filter_upwards [h] with n hn
        simpa [Real.dist_eq, abs_of_nonneg ENNReal.toReal_nonneg] using hn
      filter_upwards [htailSmall] with n hn
      have hcmp := charFun_add_perturbation_bound (μseq n) (S n) (Znorm n)
        (hSmeas n) (hZnormMeas n) t c (le_of_lt hc)
      have hnorm : ‖charFun ((μseq n).map (Y n)) t -
          charFun ((μseq n).map (S n)) t‖ ≤
          |t| * c + 2 * (μseq n {ω | c ≤ |Znorm n ω|}).toReal := by
        simpa [Y, measureReal_def] using hcmp
      have hlt : |t| * c + 2 * (μseq n {ω | c ≤ |Znorm n ω|}).toReal < ε := by
        nlinarith [hcprod, hn, hε]
      simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hnorm.trans_lt hlt
    have heq : (fun n => charFun ((μseq n).map (Y n)) t) =
        fun n => (charFun ((μseq n).map (S n)) t -
          charFun ((μseq n).map (S n)) t) +
          (charFun ((μseq n).map (Y n)) t -
            charFun ((μseq n).map (S n)) t) +
          charFun ((μseq n).map (S n)) t := by
      funext n
      ring
    rw [heq]
    simpa using (hclose.add (hbaseCF t))
  have hYdist : TendstoInDistribution Y atTop (fun x : ℝ => x) μseq
      (gaussianReal 0 1) := by
    apply TendstoInDistribution.of_tendsto_charFun
      (fun n => (hYmeas n).aemeasurable) (by fun_prop)
    intro t
    simpa using hperturbCF t
  have hYintegral : Tendsto
      (fun n => ∫ ω, h (Y n ω) ∂(μseq n)) atTop
      (𝓝 (∫ y, h y ∂(gaussianReal 0 1))) := by
    exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto
      (𝕜 := ℝ) (fun n => (hYmeas n).aemeasurable) (by fun_prop)).mp hYdist h
  have hYeq (n : ℕ) : Y n = fun ω =>
      ((∑ i ∈ Iseq n, Xraw n i ω + Zraw n ω) / sseq n) := by
    funext ω
    dsimp [Y, S, Znorm, Xnorm]
    calc
      (∑ i ∈ Iseq n, Xraw n i ω / sseq n) + Zraw n ω / sseq n =
          (∑ i ∈ Iseq n, Xraw n i ω) / sseq n + Zraw n ω / sseq n := by
        rw [← Finset.sum_div]
      _ = ((∑ i ∈ Iseq n, Xraw n i ω) + Zraw n ω) / sseq n := by
        rw [← add_div]
  have hbad (n : ℕ) : η <
      |∫ ω, h (Y n ω) ∂(μseq n) - ∫ y, h y ∂(gaussianReal 0 1)| := by
    rcases hdata n with ⟨hμ, hs, hInd, hXm, hZm, hMem, hMean, hVar, hThird,
      hTail, hBad⟩
    have hint : ∫ ω, h (Y n ω) ∂(μseq n) =
        ∫ ω, h ((∑ i ∈ (d n).I, (d n).X i ω + (d n).Z ω) / (d n).s)
          ∂(d n).μ := by
      rw [hYeq n]
    rw [hint]
    exact hBad
  have herror : Tendsto
      (fun n => |∫ ω, h (Y n ω) ∂(μseq n) - ∫ y, h y ∂(gaussianReal 0 1)|)
      atTop (𝓝 0) := by
    have hdiff := hYintegral.sub_const (∫ y, h y ∂(gaussianReal 0 1))
    simpa [Real.dist_eq] using hdiff.abs
  have hevent := herror.eventually (Iio_mem_nhds hη)
  obtain ⟨n, hn⟩ := (hevent.and (Filter.Eventually.of_forall hbad)).exists
  exact (not_lt_of_ge (le_of_lt hn.2)) (hn.1)

end Critical2DKPZ.LogNormality
