/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.Skewness.TwoCrossing
public import Critical2DKPZ.Extensions.Skewness.CubicComparison
import Critical2DKPZ.EhrhardType.NormalCDF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The cubic bound and its affine equality case -/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal

namespace Critical2DKPZ.Extensions.Skewness

/-- Zero residual means that the representative is affine with nonnegative slope. -/
theorem affine_of_residual_eq_zero {h : ℝ → ℝ} (hr : ∀ x, residual h x = 0) :
    ∃ a b : ℝ, 0 ≤ a ∧ ∀ x, h x = a * x + b := by
  refine ⟨stddev h, mean h, stddev_nonneg h, fun x => ?_⟩
  have hx := hr x
  dsimp [residual] at hx
  linarith only [hx]

/-- The zero-variance branch is constant everywhere, by continuity and full support. -/
theorem constant_of_stddev_eq_zero {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h)
    (hL3 : MemLp h 3 (gaussianReal 0 1)) (hσ : stddev h = 0) :
    ∀ x, h x = mean h := by
  have := EhrhardType.isOpenPosMeasure_gaussianReal 0 (v := 1) one_ne_zero
  have hv : variance h (gaussianReal 0 1) = 0 := by rw [← stddev_sq, hσ, zero_pow (by decide)]
  have heq := ae_eq_integral_of_variance_eq_zero (hL3.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)) hv
  exact congrFun (eq_of_ae_eq heq (continuousOn_univ.mp (hc.continuousOn isOpen_univ)) continuous_const)

/-- Both degenerate cases in the note are affine. -/
theorem affine_of_degenerate {h : ℝ → ℝ} (hc : ConvexOn ℝ univ h)
    (hL3 : MemLp h 3 (gaussianReal 0 1))
    (hd : stddev h = 0 ∨ ∀ x, residual h x = 0) :
    ∃ a b : ℝ, 0 ≤ a ∧ ∀ x, h x = a * x + b := by
  rcases hd with hs | hr
  · exact ⟨0, mean h, le_rfl, fun x => by rw [zero_mul, zero_add]; exact constant_of_stddev_eq_zero hc hL3 hs x⟩
  · exact affine_of_residual_eq_zero hr

/-- Mean, standard deviation and residual of any affine function with nonnegative slope. -/
theorem affine_moments {h : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hh : ∀ x, h x = a * x + b) :
    mean h = b ∧ stddev h = a ∧ ∀ x, residual h x = 0 := by
  have heq : h = fun x => a * x + b := funext hh
  have hId : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 3 (by norm_num)).integrable (by norm_num)
  have hm : mean h = b := by
    change (∫ x, h x ∂gaussianReal 0 1) = b
    rw [heq]
    change (∫ x, a * x + b ∂gaussianReal 0 1) = b
    rw [integral_add (hId.const_mul a) (integrable_const _), integral_const_mul, integral_id_gaussianReal]
    simp only [mul_zero, integral_const, probReal_univ, smul_eq_mul, one_mul, zero_add]
  have hs : stddev h = a := by
    rw [stddev, heq, variance_add_const (by fun_prop), variance_const_mul,
      variance_fun_id_gaussianReal, NNReal.coe_one, mul_one, Real.sqrt_sq ha]
  refine ⟨hm, hs, fun x => ?_⟩
  rw [residual, hh, hm, hs]
  ring

/-- An affine representative has vanishing third central moment. -/
theorem centralMoment_three_eq_zero_of_affine {h : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hh : ∀ x, h x = a * x + b) : centralMoment h 3 (gaussianReal 0 1) = 0 := by
  have hm := (affine_moments ha hh).1
  change (∫ x, (h x - mean h) ^ 3 ∂gaussianReal 0 1) = 0
  have hf : (fun x => (h x - mean h) ^ 3) = fun x => a ^ 3 * x ^ 3 := by
    funext x
    rw [hh, hm]
    ring
  rw [hf, integral_const_mul, integral_gaussian_odd.2.1, mul_zero]

/-- The crossing signs and monotonicity place the two values in one of the
three configurations of the scalar cubic comparison. -/
theorem crossing_configurations {h : ℝ → ℝ} (hm : Monotone h)
    {x₁ x₂ : ℝ} (hs : 0 < stddev h)
    (hneg : ∀ x, residual h x < 0 ↔ x ∈ Ioo x₁ x₂)
    (h₁ : residual h x₁ = 0) (h₂ : residual h x₂ = 0) (x : ℝ) :
    (stddev h * x ≤ h x - mean h ∧ h x - mean h ≤ stddev h * x₁) ∨
    (stddev h * x₁ ≤ h x - mean h ∧ h x - mean h ≤ stddev h * x ∧
      stddev h * x ≤ stddev h * x₂) ∨
    (stddev h * x₂ ≤ stddev h * x ∧ stddev h * x ≤ h x - mean h) := by
  have he₁ : h x₁ - mean h = stddev h * x₁ := sub_eq_zero.mp h₁
  have he₂ : h x₂ - mean h = stddev h * x₂ := sub_eq_zero.mp h₂
  by_cases hx₁ : x ≤ x₁
  · have hr : 0 ≤ residual h x :=
      le_of_not_gt (fun ht => hx₁.not_gt ((hneg x).mp ht).1)
    exact Or.inl ⟨sub_nonneg.mp hr, (sub_le_sub_right (hm hx₁) _).trans_eq he₁⟩
  by_cases hx₂ : x₂ ≤ x
  · have hr : 0 ≤ residual h x :=
      le_of_not_gt (fun ht => hx₂.not_gt ((hneg x).mp ht).2)
    exact Or.inr (Or.inr ⟨mul_le_mul_of_nonneg_left hx₂ hs.le, sub_nonneg.mp hr⟩)
  · have hr : residual h x < 0 := (hneg x).mpr ⟨lt_of_not_ge hx₁, lt_of_not_ge hx₂⟩
    exact Or.inr (Or.inl ⟨he₁.symm.trans_le (sub_le_sub_right (hm (le_of_not_ge hx₁)) _),
      (sub_neg.mp hr).le, mul_le_mul_of_nonneg_left (le_of_not_ge hx₂) hs.le⟩)

/-- The pointwise cubic inequality at the two crossing values. -/
theorem pointwise_cubic {h : ℝ → ℝ} (hm : Monotone h)
    {x₁ x₂ : ℝ} (hx : x₁ < x₂) (hs : 0 < stddev h)
    (hneg : ∀ x, residual h x < 0 ↔ x ∈ Ioo x₁ x₂)
    (h₁ : residual h x₁ = 0) (h₂ : residual h x₂ = 0) (x : ℝ) :
    1 / 2 * |residual h x| ^ 3 ≤
      cubicP (stddev h * x₁) (stddev h * x₂) (h x - mean h) -
        cubicP (stddev h * x₁) (stddev h * x₂) (stddev h * x) :=
  cubic_comparison (mul_lt_mul_of_pos_left hx hs)
    (crossing_configurations hm hs hneg h₁ h₂ x)

/-- The cubic comparison polynomial is integrable for every L³ argument. -/
theorem integrable_cubicP {g : ℝ → ℝ} (hg : MemLp g 3 (gaussianReal 0 1)) (a b : ℝ) :
    Integrable (fun x => cubicP a b (g x)) (gaussianReal 0 1) :=
  ((integrable_pow_of_memLp_three hg (n := 3) le_rfl).sub
    ((integrable_pow_of_memLp_three hg (n := 2) (by norm_num)).const_mul _)).add
      ((hg.integrable (by norm_num)).const_mul _)

/-- Integral expansion of the cubic, with all linearity premises supplied by L³. -/
theorem integral_cubicP {g : ℝ → ℝ} (hg : MemLp g 3 (gaussianReal 0 1)) (a b : ℝ) :
    (∫ x, cubicP a b (g x) ∂gaussianReal 0 1) =
      (∫ x, g x ^ 3 ∂gaussianReal 0 1) -
        3 / 2 * (a + b) * (∫ x, g x ^ 2 ∂gaussianReal 0 1) +
        3 * a * b * (∫ x, g x ∂gaussianReal 0 1) := by
  have h₃ := integrable_pow_of_memLp_three hg (n := 3) le_rfl
  have h₂ := integrable_pow_of_memLp_three hg (n := 2) (by norm_num)
  have h₁ := hg.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 3)
  have hsub : Integrable (fun x => g x ^ 3 - 3 / 2 * (a + b) * g x ^ 2) (gaussianReal 0 1) :=
    h₃.sub (h₂.const_mul _)
  unfold cubicP
  rw [integral_add hsub (h₁.const_mul _),
    integral_sub h₃ (h₂.const_mul _), integral_const_mul, integral_const_mul]

/-- Matching first and second moments cancels the lower-degree terms, while the
Gaussian cubic moment vanishes. -/
theorem integral_cubicP_gap {h : ℝ → ℝ} (hL3 : MemLp h 3 (gaussianReal 0 1)) (a b : ℝ) :
    (∫ x, cubicP a b (h x - mean h) - cubicP a b (stddev h * x) ∂gaussianReal 0 1) =
      centralMoment h 3 (gaussianReal 0 1) := by
  have hc := memLp_centered hL3
  have hId : MemLp (fun x : ℝ => x) 3 (gaussianReal 0 1) :=
    memLp_id_gaussianReal' 3 (by norm_num)
  have hl := hId.const_mul (stddev h)
  have hm : (∫ x, h x - mean h ∂gaussianReal 0 1) = 0 := by
    rw [integral_sub (hL3.integrable (by norm_num)) (integrable_const _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, mean, sub_self]
  have hmline : (∫ x, stddev h * x ∂gaussianReal 0 1) = 0 := by
    rw [integral_const_mul, integral_id_gaussianReal, mul_zero]
  have hs : (∫ x, (h x - mean h) ^ 2 ∂gaussianReal 0 1) = stddev h ^ 2 := by
    rw [stddev_sq, variance_eq_integral hL3.aemeasurable]
    rfl
  have hsline : (∫ x, (stddev h * x) ^ 2 ∂gaussianReal 0 1) = stddev h ^ 2 := by
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_gaussian_odd.2.2, mul_one]
  have hcline : (∫ x, (stddev h * x) ^ 3 ∂gaussianReal 0 1) = 0 := by
    simp_rw [mul_pow]
    rw [integral_const_mul, integral_gaussian_odd.2.1, mul_zero]
  rw [integral_sub (integrable_cubicP hc a b) (integrable_cubicP hl a b),
    integral_cubicP hc, integral_cubicP hl, hm, hmline, hs, hsline, hcline]
  change _ = ∫ x, (h x - mean h) ^ 3 ∂gaussianReal 0 1
  ring

/-- Proposition 3.1: the common-Gaussian cubic displacement is integrable and
bounded by twice the third central moment. -/
theorem integral_abs_sub_matching_gaussian_cube_le (h : ℝ → ℝ) (hmono : Monotone h)
    (hconv : ConvexOn ℝ univ h) (hL3 : MemLp h (3 : ℝ≥0∞) (gaussianReal 0 1)) :
    Integrable (fun x : ℝ => |h x - mean h - stddev h * x| ^ 3) (gaussianReal 0 1) ∧
      (∫ x : ℝ, |h x - mean h - stddev h * x| ^ 3 ∂gaussianReal 0 1) ≤
        2 * centralMoment h 3 (gaussianReal 0 1) := by
  classical
  have hi : Integrable (fun x => |residual h x| ^ 3) (gaussianReal 0 1) := by
    simpa only [Real.norm_eq_abs] using (memLp_residual hL3).integrable_norm_pow' (p := 3)
  refine ⟨hi, ?_⟩
  change (∫ x, |residual h x| ^ 3 ∂gaussianReal 0 1) ≤ _
  by_cases ha : ∃ a b : ℝ, 0 ≤ a ∧ ∀ x, h x = a * x + b
  · obtain ⟨a, b, ha, hh⟩ := ha
    have hr := (affine_moments ha hh).2.2
    simp only [hr, abs_zero, zero_pow (by decide : 3 ≠ 0), integral_zero,
      centralMoment_three_eq_zero_of_affine ha hh, mul_zero, le_refl]
  have hs : 0 < stddev h := lt_of_le_of_ne (stddev_nonneg h) (by
    intro hz
    exact ha (affine_of_degenerate hconv hL3 (Or.inl hz.symm)))
  have hr : ∃ x, residual h x ≠ 0 := by
    by_contra hn
    apply ha
    exact affine_of_residual_eq_zero (fun x => not_not.mp (fun hx => hn ⟨x, hx⟩))
  obtain ⟨x₁, x₂, hx, hneg, h₁, h₂⟩ := two_crossing hmono hconv hL3 hs hr
  have hl : MemLp (fun x => stddev h * x) 3 (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' 3 (by norm_num)).const_mul _
  have hp := integral_mono (hi.const_mul (1 / 2))
    ((integrable_cubicP (memLp_centered hL3) (stddev h * x₁) (stddev h * x₂)).sub
      (integrable_cubicP hl (stddev h * x₁) (stddev h * x₂)))
    (pointwise_cubic hmono hx hs hneg h₁ h₂)
  simp only [Pi.sub_apply] at hp
  rw [integral_const_mul, integral_cubicP_gap hL3] at hp
  linarith only [hp]

/-- A nondecreasing convex Gaussian transform has nonnegative third central moment. -/
theorem centralMoment_three_nonneg (h : ℝ → ℝ) (hm : Monotone h)
    (hc : ConvexOn ℝ univ h) (hL3 : MemLp h 3 (gaussianReal 0 1)) :
    0 ≤ centralMoment h 3 (gaussianReal 0 1) := by
  have hb := (integral_abs_sub_matching_gaussian_cube_le h hm hc hL3).2
  have hn : 0 ≤ ∫ x, |h x - mean h - stddev h * x| ^ 3 ∂gaussianReal 0 1 :=
    integral_nonneg (fun x => pow_nonneg (abs_nonneg _) _)
  linarith only [hb, hn]

/-- Proposition 3.1, strict equality characterization: the third central moment
is positive precisely when the representative is not affine. -/
theorem centralMoment_three_pos_iff_not_affine (h : ℝ → ℝ) (hmono : Monotone h)
    (hconv : ConvexOn ℝ univ h) (hL3 : MemLp h (3 : ℝ≥0∞) (gaussianReal 0 1)) :
    0 < centralMoment h 3 (gaussianReal 0 1) ↔
      ¬ ∃ a b : ℝ, 0 ≤ a ∧ ∀ x : ℝ, h x = a * x + b := by
  constructor
  · rintro hp ⟨a, b, ha, hh⟩
    rw [centralMoment_three_eq_zero_of_affine ha hh] at hp
    exact hp.false
  · intro hna
    have hn := centralMoment_three_nonneg h hmono hconv hL3
    apply lt_of_le_of_ne hn
    intro hz
    have hzero : centralMoment h 3 (gaussianReal 0 1) = 0 := hz.symm
    obtain ⟨hi, hb⟩ := integral_abs_sub_matching_gaussian_cube_le h hmono hconv hL3
    rw [hzero, mul_zero] at hb
    have hnn : ∀ x, 0 ≤ |h x - mean h - stddev h * x| ^ 3 :=
      fun x => pow_nonneg (abs_nonneg _) _
    have heq := (integral_eq_zero_iff_of_nonneg hnn hi).mp
      (le_antisymm hb (integral_nonneg hnn))
    have hr : residual h =ᵐ[gaussianReal 0 1] 0 := by
      filter_upwards [heq] with x hx
      exact abs_eq_zero.mp ((pow_eq_zero_iff (by decide : 3 ≠ 0)).mp hx)
    have := EhrhardType.isOpenPosMeasure_gaussianReal 0 (v := 1) one_ne_zero
    have hpoint : ∀ x, residual h x = 0 :=
      congrFun (eq_of_ae_eq hr (continuous_residual hconv) continuous_const)
    exact hna (affine_of_residual_eq_zero hpoint)

end Critical2DKPZ.Extensions.Skewness
