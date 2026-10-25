/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25FullSupportMoments
import Mathlib.Tactic

/-! # Gaussian disorder moment bounds for CCR25 -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- A global elementary estimate for the centered exponential. -/
theorem abs_exp_sub_one_le_two_mul_abs_mul_exp_abs (x : ℝ) :
    |Real.exp x - 1| ≤ 2 * |x| * Real.exp |x| := by
  by_cases hx : |x| ≤ 1
  · calc
      |Real.exp x - 1| ≤ 2 * |x| := Real.abs_exp_sub_one_le hx
      _ ≤ 2 * |x| * Real.exp |x| := by
        have hExp : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
        nlinarith [mul_nonneg (abs_nonneg x) (sub_nonneg.mpr hExp)]
  · have hx' : 1 < |x| := lt_of_not_ge hx
    have hExp : 1 ≤ Real.exp |x| := Real.one_le_exp (abs_nonneg x)
    have hAbs : |Real.exp x - 1| ≤ Real.exp |x| + 1 := by
      calc
        |Real.exp x - 1| = |Real.exp x + -1| := by congr 1
        _ ≤ |Real.exp x| + |-1| := abs_add_le _ _
        _ = Real.exp x + 1 := by simp
        _ ≤ Real.exp |x| + 1 := by gcongr; exact le_abs_self x
    calc
      |Real.exp x - 1| ≤ Real.exp |x| + 1 := hAbs
      _ ≤ 2 * Real.exp |x| := by linarith
      _ ≤ 2 * |x| * Real.exp |x| := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hx'.le) (Real.exp_nonneg |x|)]

/-- For small inverse temperature, a centered Gaussian disorder coordinate is
bounded by a linear factor in the Gaussian coordinate times an exponential. -/
theorem abs_xi_le_of_abs_beta_le_one (β : ℝ) (i : ℕ × Site)
    (ω : Disorder) (hβ : |β| ≤ 1) :
    |Critical2DKPZ.Polymer.xi β i ω| ≤
      2 * |β| * (|ω i| + 1) * Real.exp (|ω i| + 1) := by
  unfold Critical2DKPZ.Polymer.xi
  let u := β * ω i - β ^ 2 / 2
  have hβ0 : 0 ≤ |β| := abs_nonneg β
  have hω0 : 0 ≤ |ω i| := abs_nonneg (ω i)
  have hu : |u| ≤ |β| * (|ω i| + 1) := by
    dsimp [u]
    calc
      |β * ω i - β ^ 2 / 2| ≤ |β * ω i| + |β ^ 2 / 2| := abs_sub _ _
      _ = |β| * |ω i| + β ^ 2 / 2 := by
        rw [abs_mul, abs_div, abs_of_nonneg (sq_nonneg β),
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ |β| * |ω i| + |β| := by
        have hsq : β ^ 2 ≤ |β| := by nlinarith [sq_abs β, sq_nonneg (|β|)]
        nlinarith
      _ = |β| * (|ω i| + 1) := by ring
  have hu' : |u| ≤ |ω i| + 1 := by
    calc
      |u| ≤ |β| * (|ω i| + 1) := hu
      _ ≤ |ω i| + 1 := by
        exact mul_le_of_le_one_left (by positivity) hβ
  calc
    |Real.exp u - 1| ≤ 2 * |u| * Real.exp |u| :=
      abs_exp_sub_one_le_two_mul_abs_mul_exp_abs u
    _ ≤ 2 * (|β| * (|ω i| + 1)) * Real.exp (|ω i| + 1) := by
      gcongr
    _ = 2 * |β| * (|ω i| + 1) * Real.exp (|ω i| + 1) := by ring

/-- Polynomial Gaussian tails can be absorbed into one exponential. -/
theorem abs_xi_pow_le_exp_tail (β : ℝ) (i : ℕ × Site) (ω : Disorder)
    (k : ℕ) (hβ : |β| ≤ 1) :
    |Critical2DKPZ.Polymer.xi β i ω| ^ k ≤
      (2 : ℝ) ^ k * (Nat.factorial k : ℝ) * |β| ^ k *
        Real.exp (((k : ℝ) + 1) * (|ω i| + 1)) := by
  let y : ℝ := |ω i|
  have hxi := abs_xi_le_of_abs_beta_le_one β i ω hβ
  have hpoly : (y + 1) ^ k ≤ (Nat.factorial k : ℝ) * Real.exp (y + 1) := by
    have h := Real.pow_div_factorial_le_exp (y + 1) (by positivity) k
    have hfac : 0 < (Nat.factorial k : ℝ) := by positivity
    calc
      (y + 1) ^ k ≤ Real.exp (y + 1) * (Nat.factorial k : ℝ) :=
        (div_le_iff₀ hfac).mp h
      _ = (Nat.factorial k : ℝ) * Real.exp (y + 1) := by ring
  have hbase : 0 ≤ |Critical2DKPZ.Polymer.xi β i ω| := abs_nonneg _
  calc
    |Critical2DKPZ.Polymer.xi β i ω| ^ k ≤
        (2 * |β| * (y + 1) * Real.exp (y + 1)) ^ k := by
          apply pow_le_pow_left₀ hbase
          simpa [y, mul_assoc] using hxi
    _ = 2 ^ k * |β| ^ k * (y + 1) ^ k *
          Real.exp ((k : ℝ) * (y + 1)) := by
      rw [mul_pow, mul_pow, mul_pow, ← Real.exp_nat_mul]
    _ ≤ 2 ^ k * |β| ^ k * (Nat.factorial k : ℝ) * Real.exp (y + 1) *
          Real.exp ((k : ℝ) * (y + 1)) := by
      calc
        2 ^ k * |β| ^ k * (y + 1) ^ k * Real.exp ((k : ℝ) * (y + 1)) =
            (2 ^ k * |β| ^ k) *
              ((y + 1) ^ k * Real.exp ((k : ℝ) * (y + 1))) := by ring
        _ ≤ (2 ^ k * |β| ^ k) *
              ((Nat.factorial k : ℝ) * Real.exp (y + 1) *
                Real.exp ((k : ℝ) * (y + 1))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg _)) (by positivity)
        _ = 2 ^ k * |β| ^ k * (Nat.factorial k : ℝ) * Real.exp (y + 1) *
              Real.exp ((k : ℝ) * (y + 1)) := by ring
    _ = 2 ^ k * (Nat.factorial k : ℝ) * |β| ^ k *
          Real.exp (((k : ℝ) + 1) * (y + 1)) := by
      calc
        _ = 2 ^ k * |β| ^ k * (Nat.factorial k : ℝ) *
              (Real.exp (y + 1) * Real.exp ((k : ℝ) * (y + 1))) := by ring
        _ = 2 ^ k * |β| ^ k * (Nat.factorial k : ℝ) *
              Real.exp ((y + 1) + (k : ℝ) * (y + 1)) := by rw [← Real.exp_add]
        _ = 2 ^ k * (Nat.factorial k : ℝ) * |β| ^ k *
              Real.exp (((k : ℝ) + 1) * (y + 1)) := by congr 1 <;> ring_nf

/-- The exponential of an absolute Gaussian coordinate is bounded by its two
one-sided exponential moments. -/
theorem exp_mul_abs_le_sum_exp (a x : ℝ) :
    Real.exp (a * |x|) ≤ Real.exp (a * x) + Real.exp ((-a) * x) := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    exact le_add_of_nonneg_right (Real.exp_nonneg _)
  · rw [abs_of_neg (lt_of_not_ge hx)]
    rw [show a * -x = (-a) * x by ring]
    exact le_add_of_nonneg_left (Real.exp_nonneg _)

/-- Explicit uniform coordinate-moment constant for the Gaussian disorder. -/
def ccr25GaussianMomentConstant (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (k + 1) * (Nat.factorial k : ℝ) *
    Real.exp (((k : ℝ) + 1) + ((k : ℝ) + 1) ^ 2 / 2)

/-- The Gaussian moment constant is nonnegative. -/
theorem ccr25GaussianMomentConstant_nonneg (k : ℕ) :
    0 ≤ ccr25GaussianMomentConstant k := by
  unfold ccr25GaussianMomentConstant
  positivity

/-- Every fixed centered lognormal moment is bounded by a constant times the
corresponding power of the standard deviation, uniformly for `|β| ≤ 1`. -/
theorem abs_gaussianDisorderMoment_le_beta_pow (β : ℝ) (k : ℕ)
    (hβ : |β| ≤ 1) :
    |gaussianDisorderMoment β k| ≤ ccr25GaussianMomentConstant k * |β| ^ k := by
  change |∫ ω : Disorder,
      Critical2DKPZ.Polymer.xi β (0, 0) ω ^ k ∂disorderLaw| ≤
    ccr25GaussianMomentConstant k * |β| ^ k
  let z : ℕ × Site := (0, 0)
  let a : ℝ := (k : ℝ) + 1
  let D : ℝ := (2 : ℝ) ^ k * (Nat.factorial k : ℝ) * |β| ^ k * Real.exp a
  have hleft : Integrable (fun ω : Disorder =>
      |Critical2DKPZ.Polymer.xi β z ω| ^ k) disorderLaw := by
    have h := (Critical2DKPZ.Polymer.memLp_xi β z (k : ENNReal) (by simp)).integrable_norm_pow'
    simpa only [Real.norm_eq_abs] using h
  have hmoment : Integrable (fun ω : Disorder =>
      Critical2DKPZ.Polymer.xi β z ω ^ k) disorderLaw := by
    apply hleft.mono'
    · exact ((Critical2DKPZ.Polymer.measurable_xi β z).pow_const k).aestronglyMeasurable
    · filter_upwards [] with ω
      simp [Real.norm_eq_abs]
  have hplus : Integrable (fun ω : Disorder => Real.exp (a * ω z)) disorderLaw :=
    Integrable.of_integral_ne_zero (by
      rw [Critical2DKPZ.Polymer.integral_exp_coordinate]
      exact Real.exp_ne_zero _)
  have hminus : Integrable (fun ω : Disorder => Real.exp ((-a) * ω z)) disorderLaw :=
    Integrable.of_integral_ne_zero (by
      rw [Critical2DKPZ.Polymer.integral_exp_coordinate]
      exact Real.exp_ne_zero _)
  have hupper : Integrable (fun ω : Disorder =>
      D * (Real.exp (a * ω z) + Real.exp ((-a) * ω z))) disorderLaw :=
    (hplus.add hminus).const_mul D
  have hpoint (ω : Disorder) :
      |Critical2DKPZ.Polymer.xi β z ω| ^ k ≤
        D * (Real.exp (a * ω z) + Real.exp ((-a) * ω z)) := by
    have htail : Real.exp (a * (|ω z| + 1)) ≤
        Real.exp a * (Real.exp (a * ω z) + Real.exp ((-a) * ω z)) := by
      rw [mul_add, mul_one, Real.exp_add]
      calc
        Real.exp (a * |ω z|) * Real.exp a ≤
            (Real.exp (a * ω z) + Real.exp ((-a) * ω z)) * Real.exp a :=
          mul_le_mul_of_nonneg_right (exp_mul_abs_le_sum_exp a (ω z))
            (Real.exp_nonneg a)
        _ = Real.exp a * (Real.exp (a * ω z) + Real.exp ((-a) * ω z)) := by ring
    calc
      |Critical2DKPZ.Polymer.xi β z ω| ^ k ≤
          (2 : ℝ) ^ k * (Nat.factorial k : ℝ) * |β| ^ k *
            Real.exp (a * (|ω z| + 1)) := by
        simpa [a] using abs_xi_pow_le_exp_tail β z ω k hβ
      _ ≤ (2 : ℝ) ^ k * (Nat.factorial k : ℝ) * |β| ^ k *
            (Real.exp a * (Real.exp (a * ω z) + Real.exp ((-a) * ω z))) :=
        mul_le_mul_of_nonneg_left htail (by positivity)
      _ = D * (Real.exp (a * ω z) + Real.exp ((-a) * ω z)) := by
        dsimp [D]
        ring
  have hmono := integral_mono hleft hupper hpoint
  have hupperIntegral :
      (∫ ω : Disorder, D *
        (Real.exp (a * ω z) + Real.exp ((-a) * ω z)) ∂disorderLaw) =
        D * (Real.exp (a ^ 2 / 2) + Real.exp ((-a) ^ 2 / 2)) := by
    rw [integral_const_mul, integral_add hplus hminus,
      Critical2DKPZ.Polymer.integral_exp_coordinate,
      Critical2DKPZ.Polymer.integral_exp_coordinate]
  have hconst :
      D * (Real.exp (a ^ 2 / 2) + Real.exp ((-a) ^ 2 / 2)) =
        ccr25GaussianMomentConstant k * |β| ^ k := by
    dsimp [D, a, ccr25GaussianMomentConstant]
    rw [neg_sq, show Real.exp (((k : ℝ) + 1) ^ 2 / 2) +
      Real.exp (((k : ℝ) + 1) ^ 2 / 2) =
        2 * Real.exp (((k : ℝ) + 1) ^ 2 / 2) by ring]
    calc
      _ = (2 : ℝ) ^ k * 2 * (Nat.factorial k : ℝ) *
          (Real.exp ((k : ℝ) + 1) * Real.exp (((k : ℝ) + 1) ^ 2 / 2)) *
          |β| ^ k := by ring
      _ = (2 : ℝ) ^ k * 2 * (Nat.factorial k : ℝ) *
          Real.exp (((k : ℝ) + 1) + ((k : ℝ) + 1) ^ 2 / 2) *
          |β| ^ k := by rw [← Real.exp_add]
      _ = (2 : ℝ) ^ (k + 1) * (Nat.factorial k : ℝ) *
          Real.exp (((k : ℝ) + 1) + ((k : ℝ) + 1) ^ 2 / 2) *
          |β| ^ k := by rw [pow_succ]; ring
  have hbound :
      (∫ ω : Disorder, |Critical2DKPZ.Polymer.xi β z ω| ^ k ∂disorderLaw) ≤
        ccr25GaussianMomentConstant k * |β| ^ k := by
    calc
      (∫ ω : Disorder, |Critical2DKPZ.Polymer.xi β z ω| ^ k ∂disorderLaw) ≤
          ∫ ω : Disorder, D *
            (Real.exp (a * ω z) + Real.exp ((-a) * ω z)) ∂disorderLaw := hmono
      _ = ccr25GaussianMomentConstant k * |β| ^ k := by
        rw [hupperIntegral, hconst]
  calc
    |gaussianDisorderMoment β k| ≤
        ∫ ω : Disorder, |Critical2DKPZ.Polymer.xi β z ω ^ k| ∂disorderLaw :=
      abs_integral_le_integral_abs
    _ = ∫ ω : Disorder, |Critical2DKPZ.Polymer.xi β z ω| ^ k ∂disorderLaw := by
      congr 1
      funext ω
      rw [abs_pow]
    _ ≤ ccr25GaussianMomentConstant k * |β| ^ k := hbound

/-- The Gaussian variance parameter dominates the squared inverse temperature. -/
theorem beta_sq_le_sigmaSq (β : ℝ) :
    β ^ 2 ≤ Critical2DKPZ.Polymer.sigmaSq β := by
  unfold Critical2DKPZ.Polymer.sigmaSq
  have h := Real.add_one_le_exp (β ^ 2)
  linarith

/-- The Gaussian disorder variance parameter is nonnegative. -/
theorem sigmaSq_nonneg (β : ℝ) : 0 ≤ Critical2DKPZ.Polymer.sigmaSq β := by
  unfold Critical2DKPZ.Polymer.sigmaSq
  have h := Real.one_le_exp (sq_nonneg β)
  linarith

/-- A single fixed constant dominates all coordinate-moment constants up to
replica order `h`. -/
def ccr25GaussianMomentUniformConstant (h : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (h + 1), ccr25GaussianMomentConstant k


/-- The uniform Gaussian moment constant bounds every Gaussian moment constant of lower order. -/
theorem ccr25GaussianMomentUniformConstant_le_of_le {h k : ℕ} (hk : k ≤ h) :
    ccr25GaussianMomentConstant k ≤ ccr25GaussianMomentUniformConstant h := by
  unfold ccr25GaussianMomentUniformConstant
  apply Finset.single_le_sum
  · intro j hj
    exact ccr25GaussianMomentConstant_nonneg j
  · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hk)



end

end Critical2DKPZ.MomentBounds
