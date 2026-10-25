/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockCompositionProfile
public import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Shifted Gaussian sums for pair-block profiles -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Real Filter
open scoped Topology

/-- The untruncated sampled Gaussian profile on the full integer lattice. -/
def fullGaussianBlockWeight (m : ℕ) (k : ℤ) : ℝ :=
  Real.exp (-((2 * (k : ℝ) - (m : ℝ)) ^ 2) / (m : ℝ))

/-- Completing the square factors a two-block Gaussian convolution into the
Gaussian at the combined duration and one shifted theta sum. -/
theorem tsum_fullGaussianBlockWeight_convolution (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) (j : ℤ) :
    (∑' k : ℤ, fullGaussianBlockWeight m k *
      fullGaussianBlockWeight n (j - k)) =
      Real.exp (-((2 * (j : ℝ) - (m : ℝ) - (n : ℝ)) ^ 2) /
        ((m + n : ℕ) : ℝ)) *
        (∑' k : ℤ, Real.exp
          (-((4 * ((m + n : ℕ) : ℝ)) / ((m : ℝ) * (n : ℝ))) *
            ((k : ℝ) - (m : ℝ) * (j : ℝ) / ((m + n : ℕ) : ℝ)) ^ 2)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsumR : 0 < ((m + n : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < m + n by omega)
  have hprodR : 0 < (m : ℝ) * (n : ℝ) := mul_pos hmR hnR
  have hquad (k : ℤ) :
      ((2 * (k : ℝ) - (m : ℝ)) ^ 2) / (m : ℝ) +
          ((2 * ((j - k : ℤ) : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ) =
        ((2 * (j : ℝ) - (m : ℝ) - (n : ℝ)) ^ 2) /
            ((m + n : ℕ) : ℝ) +
          (4 * ((m + n : ℕ) : ℝ) / ((m : ℝ) * (n : ℝ))) *
            ((k : ℝ) - (m : ℝ) * (j : ℝ) / ((m + n : ℕ) : ℝ)) ^ 2 := by
    field_simp [hmR.ne', hnR.ne', hsumR.ne', hprodR.ne']
    push_cast
    ring
  have hterm (k : ℤ) :
      fullGaussianBlockWeight m k * fullGaussianBlockWeight n (j - k) =
        Real.exp (-((2 * (j : ℝ) - (m : ℝ) - (n : ℝ)) ^ 2) /
          ((m + n : ℕ) : ℝ)) *
          Real.exp (-((4 * ((m + n : ℕ) : ℝ)) / ((m : ℝ) * (n : ℝ))) *
            ((k : ℝ) - (m : ℝ) * (j : ℝ) / ((m + n : ℕ) : ℝ)) ^ 2) := by
    rw [fullGaussianBlockWeight, fullGaussianBlockWeight]
    calc
      _ = Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ) +
          -(2 * ((j - k : ℤ) : ℝ) - (n : ℝ)) ^ 2 / (n : ℝ)) := by
            rw [← Real.exp_add]
      _ = Real.exp (-(((2 * (k : ℝ) - (m : ℝ)) ^ 2) / (m : ℝ) +
          ((2 * ((j - k : ℤ) : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ))) := by
            congr 1
            ring
      _ = Real.exp (-(((2 * (j : ℝ) - (m : ℝ) - (n : ℝ)) ^ 2) /
          ((m + n : ℕ) : ℝ) +
          (4 * ((m + n : ℕ) : ℝ) / ((m : ℝ) * (n : ℝ))) *
            ((k : ℝ) - (m : ℝ) * (j : ℝ) / ((m + n : ℕ) : ℝ)) ^ 2)) := by
            rw [hquad]
      _ = Real.exp (-((2 * (j : ℝ) - (m : ℝ) - (n : ℝ)) ^ 2) /
          ((m + n : ℕ) : ℝ) +
          -((4 * ((m + n : ℕ) : ℝ)) / ((m : ℝ) * (n : ℝ))) *
            ((k : ℝ) - (m : ℝ) * (j : ℝ) / ((m + n : ℕ) : ℝ)) ^ 2) := by
            congr 1
            ring
      _ = _ := by rw [← Real.exp_add]
  calc
    _ = ∑' k : ℤ,
        Real.exp (-((2 * (j : ℝ) - (m : ℝ) - (n : ℝ)) ^ 2) /
          ((m + n : ℕ) : ℝ)) *
          Real.exp (-((4 * ((m + n : ℕ) : ℝ)) / ((m : ℝ) * (n : ℝ))) *
            ((k : ℝ) - (m : ℝ) * (j : ℝ) / ((m + n : ℕ) : ℝ)) ^ 2) :=
      tsum_congr hterm
    _ = _ := by rw [tsum_mul_left]

/-- Poisson summation expresses a shifted lattice Gaussian sum in terms of its dual Gaussian sum. -/
theorem tsum_complex_gaussian_shift {a : ℂ} (ha : 0 < a.re) (x : ℂ) :
    (∑' n : ℤ, Complex.exp (-π * a * ((n : ℂ) - x) ^ 2)) =
      1 / a ^ (1 / 2 : ℂ) *
        (∑' n : ℤ,
          Complex.exp (-π / a * (n : ℂ) ^ 2 - 2 * π * Complex.I * x * n)) := by
  have htheta := Complex.tsum_exp_neg_quadratic ha (a * x)
  have ha0 : a ≠ 0 := by
    intro hz
    subst a
    simp at ha
  have htheta' :
      (∑' n : ℤ,
        Complex.exp (-π * a * (n : ℂ) ^ 2 + 2 * π * a * x * n)) =
        1 / a ^ (1 / 2 : ℂ) *
          (∑' n : ℤ,
            Complex.exp (-π / a * ((n : ℂ) + Complex.I * (a * x)) ^ 2)) := by
    simpa [mul_assoc] using htheta
  calc
    _ = Complex.exp (-π * a * x ^ 2) *
        (∑' n : ℤ, Complex.exp (-π * a * (n : ℂ) ^ 2 + 2 * π * a * x * n)) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro n
          rw [← Complex.exp_add]
          congr 1
          ring
    _ = Complex.exp (-π * a * x ^ 2) *
        (1 / a ^ (1 / 2 : ℂ) *
          (∑' n : ℤ,
            Complex.exp (-π / a * ((n : ℂ) + Complex.I * (a * x)) ^ 2))) := by
          exact congrArg (fun z : ℂ => Complex.exp (-π * a * x ^ 2) * z) htheta'
    _ = _ := by
          calc
            _ = 1 / a ^ (1 / 2 : ℂ) *
                (Complex.exp (-π * a * x ^ 2) *
                  (∑' n : ℤ,
                    Complex.exp (-π / a * ((n : ℂ) + Complex.I * (a * x)) ^ 2))) := by ring
            _ = 1 / a ^ (1 / 2 : ℂ) *
                (∑' n : ℤ,
                  Complex.exp (-π * a * x ^ 2) *
                    Complex.exp (-π / a * ((n : ℂ) + Complex.I * (a * x)) ^ 2)) := by
                  rw [← tsum_mul_left]
            _ = 1 / a ^ (1 / 2 : ℂ) *
                (∑' n : ℤ,
                  Complex.exp (-π / a * (n : ℂ) ^ 2 - 2 * π * Complex.I * x * n)) := by
                  congr 1
                  apply tsum_congr
                  intro n
                  rw [← Complex.exp_add]
                  congr 1
                  have hI : (Complex.I * (a * x)) ^ 2 = -(a * x) ^ 2 := by
                    rw [mul_pow, Complex.I_sq]
                    ring
                  rw [show ((n : ℂ) + Complex.I * (a * x)) ^ 2 =
                    (n : ℂ) ^ 2 + 2 * (n : ℂ) * Complex.I * (a * x) +
                      (Complex.I * (a * x)) ^ 2 by ring, hI]
                  field_simp [ha0]
                  ring

/-- A Gaussian on the integer lattice is bounded by its first geometric
majorant. This gives a uniform summable tail for the nonzero dual modes. -/
theorem summable_exp_neg_int_sq (b : ℝ) (hb : 0 < b) :
    Summable (fun k : ℤ => Real.exp (-b * (k : ℝ) ^ 2)) := by
  have hnat : Summable (fun n : ℕ => Real.exp (-b * (n : ℝ) ^ 2)) := by
    apply Real.summable_exp_nat_mul_of_ge (by linarith)
    intro n
    have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · norm_num
      · have hone : 1 ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
    exact_mod_cast hn
  rw [summable_int_iff_summable_nat_and_neg]
  constructor
  · exact hnat
  · simpa [Int.cast_neg, mul_comm] using hnat

/-- The full-lattice block Gaussian is summable for every positive duration. -/
theorem summable_fullGaussianBlockWeight (m : ℕ) (hm : 0 < m) :
    Summable (fullGaussianBlockWeight m) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hbase := summable_exp_neg_int_sq (1 / (m : ℝ)) (by positivity)
  have hterm (k : ℤ) :
      fullGaussianBlockWeight m k ≤
        Real.exp (m : ℝ) * Real.exp (-(1 / (m : ℝ)) * (k : ℝ) ^ 2) := by
    have hquad :
        -((2 * (k : ℝ) - (m : ℝ)) ^ 2) / (m : ℝ) ≤
          (m : ℝ) - (k : ℝ) ^ 2 / (m : ℝ) := by
      rw [div_le_iff₀ hmR]
      field_simp [hmR.ne']
      nlinarith [sq_nonneg ((k : ℝ) - 2 * (m : ℝ) / 3)]
    rw [fullGaussianBlockWeight]
    calc
      Real.exp (-((2 * (k : ℝ) - (m : ℝ)) ^ 2) / (m : ℝ)) ≤
          Real.exp ((m : ℝ) - (k : ℝ) ^ 2 / (m : ℝ)) :=
        Real.exp_le_exp.mpr hquad
      _ = Real.exp (m : ℝ) * Real.exp (-(1 / (m : ℝ)) * (k : ℝ) ^ 2) := by
        rw [show (m : ℝ) - (k : ℝ) ^ 2 / (m : ℝ) =
          (m : ℝ) + (-(1 / (m : ℝ)) * (k : ℝ) ^ 2) by ring, Real.exp_add]
  apply Summable.of_nonneg_of_le (fun k => Real.exp_nonneg _)
    hterm (hbase.mul_left (Real.exp (m : ℝ)))

/-- The full-lattice mass is strictly positive. -/
theorem fullGaussianBlockMass_pos (m : ℕ) (hm : 0 < m) :
    0 < ∑' k : ℤ, fullGaussianBlockWeight m k := by
  apply Summable.tsum_pos (summable_fullGaussianBlockWeight m hm)
    (fun k => by
      unfold fullGaussianBlockWeight
      exact Real.exp_nonneg _) 0
  unfold fullGaussianBlockWeight
  exact Real.exp_pos _

/-- The normalized full-lattice discrete Gaussian of duration `m`. -/
def fullGaussianBlockProbability (m : ℕ) (k : ℤ) : ℝ :=
  fullGaussianBlockWeight m k / (∑' j : ℤ, fullGaussianBlockWeight m j)

/-- The continuous mass of a block Gaussian of duration `m`. -/
def fullGaussianBlockIntegralMass (m : ℕ) : ℝ :=
  Real.sqrt (Real.pi * (m : ℝ) / 4)

/-- Relative Poisson error for the full-lattice mass of a block Gaussian. -/
def fullGaussianBlockMassThetaError (m : ℕ) : ℝ :=
  2 * Real.exp (-Real.pi / ((4 / (m : ℝ)) / Real.pi)) /
    (1 - Real.exp (-Real.pi / ((4 / (m : ℝ)) / Real.pi)))

/-- The shifted Poisson error for the convolution of two full-lattice block
Gaussians. -/
def fullGaussianBlockPairShiftThetaError (m n : ℕ) : ℝ :=
  let s : ℕ := m + n
  let c : ℝ := (4 * (s : ℝ) / ((m : ℝ) * (n : ℝ))) / Real.pi
  2 * Real.exp (-Real.pi / c) / (1 - Real.exp (-Real.pi / c))

/-- The shifted theta error for two positive block lengths is strictly positive. -/
theorem fullGaussianBlockPairShiftThetaError_pos
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    0 < fullGaussianBlockPairShiftThetaError m n := by
  let c : ℝ := (4 * ((m + n : ℕ) : ℝ) / ((m : ℝ) * (n : ℝ))) / Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hexp : Real.exp (-Real.pi / c) < 1 :=
    Real.exp_lt_one_iff.mpr
      (div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) hc)
  have hden : 0 < 1 - Real.exp (-Real.pi / c) := sub_pos.mpr hexp
  unfold fullGaussianBlockPairShiftThetaError
  dsimp [c]
  positivity

/-- The shifted theta error decreases when both block durations increase. -/
theorem fullGaussianBlockPairShiftThetaError_antitone
    {M m n : ℕ} (hM : 0 < M) (hMm : M ≤ m) (hMn : M ≤ n) :
    fullGaussianBlockPairShiftThetaError m n ≤
      fullGaussianBlockPairShiftThetaError M M := by
  have hm : 0 < m := lt_of_lt_of_le hM hMm
  have hn : 0 < n := lt_of_lt_of_le hM hMn
  have hMR : 0 < (M : ℝ) := by exact_mod_cast hM
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsumR : 0 < (m : ℝ) + (n : ℝ) := add_pos hmR hnR
  have hMRm : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast hMm
  have hMRn : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hMn
  have hratio : (M : ℝ) / 2 ≤
      (m : ℝ) * (n : ℝ) / ((m : ℝ) + (n : ℝ)) := by
    have hMmprod : (M : ℝ) * (m : ℝ) ≤ (m : ℝ) * (n : ℝ) :=
      by simpa [mul_comm] using mul_le_mul_of_nonneg_right hMRn hmR.le
    have hMnprod : (M : ℝ) * (n : ℝ) ≤ (m : ℝ) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hMRm hnR.le
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hsumR]
    nlinarith
  let q : ℝ := Real.exp
    (-Real.pi / (((4 * ((m + n : ℕ) : ℝ)) /
      ((m : ℝ) * (n : ℝ))) / Real.pi))
  let q₀ : ℝ := Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ))
  have harg :
      -Real.pi / (((4 * ((m + n : ℕ) : ℝ)) /
        ((m : ℝ) * (n : ℝ))) / Real.pi) ≤
        -(Real.pi ^ 2 / 8) * (M : ℝ) := by
    have hsCast : ((m + n : ℕ) : ℝ) = (m : ℝ) + (n : ℝ) := by norm_cast
    rw [hsCast]
    have hcoef : 0 < Real.pi ^ 2 / 4 := by positivity
    have hidentity :
        -Real.pi / (((4 * ((m : ℝ) + (n : ℝ))) /
          ((m : ℝ) * (n : ℝ))) / Real.pi) =
          -(Real.pi ^ 2 / 4) *
            ((m : ℝ) * (n : ℝ) / ((m : ℝ) + (n : ℝ))) := by
      field_simp [hmR.ne', hnR.ne', hsumR.ne', Real.pi_ne_zero]
    rw [hidentity]
    have hscale := mul_le_mul_of_nonpos_left hratio
      (neg_nonpos.mpr hcoef.le)
    nlinarith
  have hq : q ≤ q₀ := by
    dsimp [q, q₀]
    exact Real.exp_le_exp.mpr harg
  have hqpos : 0 < q := by dsimp [q]; exact Real.exp_pos _
  have hq₀pos : 0 < q₀ := by dsimp [q₀]; exact Real.exp_pos _
  have hq_lt : q < 1 := by
    dsimp [q]
    apply Real.exp_lt_one_iff.mpr
    have hc : 0 < (((4 * ((m + n : ℕ) : ℝ)) /
        ((m : ℝ) * (n : ℝ))) / Real.pi) := by positivity
    have hargNeg : -Real.pi / (((4 * ((m + n : ℕ) : ℝ)) /
        ((m : ℝ) * (n : ℝ))) / Real.pi) < 0 :=
      div_neg_of_neg_of_pos (neg_neg_iff_pos.mpr Real.pi_pos) hc
    exact hargNeg
  have hq₀lt : q₀ < 1 := by
    dsimp [q₀]
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) hMR
  have hden : 0 < 1 - q := sub_pos.mpr hq_lt
  have hden₀ : 0 < 1 - q₀ := sub_pos.mpr hq₀lt
  have hfinal : 2 * q / (1 - q) ≤ 2 * q₀ / (1 - q₀) := by
    rw [div_le_div_iff₀ hden hden₀]
    nlinarith
  have hdiagarg :
      -Real.pi / (((4 * ((M : ℝ) + (M : ℝ))) /
        ((M : ℝ) * (M : ℝ))) / Real.pi) =
        -(Real.pi ^ 2 / 8) * (M : ℝ) := by
    field_simp [hMR.ne', Real.pi_ne_zero]
    ring
  have hleft : fullGaussianBlockPairShiftThetaError m n = 2 * q / (1 - q) := by
    simp [fullGaussianBlockPairShiftThetaError, q]
  have hright : fullGaussianBlockPairShiftThetaError M M = 2 * q₀ / (1 - q₀) := by
    simp [fullGaussianBlockPairShiftThetaError, q₀, hdiagarg, Nat.cast_add]
  rw [hleft, hright]
  exact hfinal


/-- Explicit exponential form of the full-lattice block mass error. -/
theorem fullGaussianBlockMassThetaError_eq_exp (m : ℕ) (hm : 0 < m) :
    fullGaussianBlockMassThetaError m =
      2 * Real.exp (-(Real.pi ^ 2 / 4) * (m : ℝ)) /
        (1 - Real.exp (-(Real.pi ^ 2 / 4) * (m : ℝ))) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have harg : -Real.pi / ((4 / (m : ℝ)) / Real.pi) =
      -(Real.pi ^ 2 / 4) * (m : ℝ) := by
    field_simp [hmR, Real.pi_ne_zero]
  unfold fullGaussianBlockMassThetaError
  rw [harg]

/-- Explicit exponential form of the equal-duration shifted theta error. -/
theorem fullGaussianBlockPairShiftThetaError_diag_eq_exp (m : ℕ) (hm : 0 < m) :
    fullGaussianBlockPairShiftThetaError m m =
      2 * Real.exp (-(Real.pi ^ 2 / 8) * (m : ℝ)) /
        (1 - Real.exp (-(Real.pi ^ 2 / 8) * (m : ℝ))) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have harg :
      -Real.pi / (((4 * ((m : ℝ) + (m : ℝ))) / ((m : ℝ) * (m : ℝ))) / Real.pi) =
        -(Real.pi ^ 2 / 8) * (m : ℝ) := by
    field_simp [hmR, Real.pi_ne_zero]
    ring
  unfold fullGaussianBlockPairShiftThetaError
  simp only [Nat.cast_add]
  rw [harg]

/-- The continuous Gaussian mass identity for the completed-square variance
of two pair-block marks. -/
theorem fullGaussianBlockPairIntegralMass_identity
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    1 / Real.sqrt
        (((4 * ((m + n : ℕ) : ℝ)) / ((m : ℝ) * (n : ℝ))) / Real.pi) *
      fullGaussianBlockIntegralMass (m + n) =
        fullGaussianBlockIntegralMass m * fullGaussianBlockIntegralMass n := by
  let s : ℕ := m + n
  let Ih : ℝ := 1 / Real.sqrt ((4 * (s : ℝ) / ((m : ℝ) * (n : ℝ))) / Real.pi)
  let Is : ℝ := fullGaussianBlockIntegralMass s
  let Im : ℝ := fullGaussianBlockIntegralMass m
  let In : ℝ := fullGaussianBlockIntegralMass n
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hspos : 0 < s := by dsimp [s]; omega
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hspos
  have hprodR : 0 < (m : ℝ) * (n : ℝ) := mul_pos hmR hnR
  have hIh : 0 < Ih := by dsimp [Ih]; positivity
  have hIs : 0 < Is := by dsimp [Is, fullGaussianBlockIntegralMass]; positivity
  have hIm : 0 < Im := by dsimp [Im, fullGaussianBlockIntegralMass]; positivity
  have hIn : 0 < In := by dsimp [In, fullGaussianBlockIntegralMass]; positivity
  have hIhSq : Ih ^ 2 = Real.pi * (m : ℝ) * (n : ℝ) / (4 * (s : ℝ)) := by
    dsimp [Ih]
    rw [one_div, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp [hmR.ne', hnR.ne', hsR.ne', hprodR.ne', Real.pi_ne_zero]
  have hIsSq : Is ^ 2 = Real.pi * (s : ℝ) / 4 := by
    dsimp [Is, fullGaussianBlockIntegralMass]
    rw [Real.sq_sqrt (by positivity)]
  have hImSq : Im ^ 2 = Real.pi * (m : ℝ) / 4 := by
    dsimp [Im, fullGaussianBlockIntegralMass]
    rw [Real.sq_sqrt (by positivity)]
  have hInSq : In ^ 2 = Real.pi * (n : ℝ) / 4 := by
    dsimp [In, fullGaussianBlockIntegralMass]
    rw [Real.sq_sqrt (by positivity)]
  have hsCast : (s : ℝ) = (m : ℝ) + (n : ℝ) := by
    dsimp [s]
    norm_cast
  have hsumRne : (m : ℝ) + (n : ℝ) ≠ 0 := ne_of_gt (add_pos hmR hnR)
  have hsq : (Ih * Is) ^ 2 = (Im * In) ^ 2 := by
    calc
      (Ih * Is) ^ 2 = Ih ^ 2 * Is ^ 2 := by rw [mul_pow]
      _ = Im ^ 2 * In ^ 2 := by
        rw [hIhSq, hIsSq, hImSq, hInSq, hsCast]
        field_simp [hsumRne]
      _ = (Im * In) ^ 2 := by rw [mul_pow]
  have heq : Ih * Is = Im * In := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with heq | heq
    · exact heq
    · have hleft : 0 < Ih * Is := mul_pos hIh hIs
      have hright : 0 < Im * In := mul_pos hIm hIn
      linarith
  simpa [s, Ih, Is, Im, In, fullGaussianBlockIntegralMass] using heq

/-- The relative Poisson error in the full-lattice Gaussian mass vanishes
as the block duration grows. -/
theorem tendsto_fullGaussianBlockMassThetaError :
    Tendsto (fun m : ℕ => fullGaussianBlockMassThetaError m) atTop (𝓝 0) := by
  let a : ℕ → ℝ := fun m => -Real.pi / ((4 / (m : ℝ)) / Real.pi)
  let q : ℕ → ℝ := fun m => Real.exp (a m)
  have hlinear : Tendsto (fun m : ℕ => -(Real.pi ^ 2 / 4) * (m : ℝ)) atTop atBot :=
    tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg
      (neg_lt_zero.mpr (by positivity))
  have ha : Tendsto a atTop atBot := by
    apply hlinear.congr'
    filter_upwards [eventually_gt_atTop 0] with m hm
    dsimp [a]
    have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    field_simp [hmR, Real.pi_ne_zero]
  have hq : Tendsto q atTop (𝓝 (0 : ℝ)) := by
    change Tendsto (fun m : ℕ => Real.exp (a m)) atTop (𝓝 0)
    exact Real.tendsto_exp_atBot.comp ha
  have hqsmall : ∀ᶠ m : ℕ in atTop, q m < 1 / 2 := by
    exact hq.eventually (Iio_mem_nhds (by norm_num))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds (by simpa using hq.const_mul (4 : ℝ))
  · filter_upwards [hqsmall] with m hsmall
    have hqpos : 0 < q m := by
      dsimp [q]
      exact Real.exp_pos _
    have hden : 0 < 1 - q m := by linarith
    have hden' : 0 < 1 - Real.exp (-Real.pi / ((4 / (m : ℝ)) / Real.pi)) := by
      simpa [q, a] using hden
    unfold fullGaussianBlockMassThetaError
    exact div_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _)) (le_of_lt hden')
  · filter_upwards [hqsmall] with m hsmall
    have hqpos : 0 < q m := by
      dsimp [q]
      exact Real.exp_pos _
    have hden : 0 < 1 - q m := by linarith
    have hbound : 2 * q m / (1 - q m) ≤ 4 * q m := by
      rw [div_le_iff₀ hden]
      nlinarith
    simpa [fullGaussianBlockMassThetaError, q, a] using hbound

/-- The normalized full-lattice Gaussian has total mass one. -/
theorem tsum_fullGaussianBlockProbability (m : ℕ) (hm : 0 < m) :
    ∑' k : ℤ, fullGaussianBlockProbability m k = 1 := by
  unfold fullGaussianBlockProbability
  rw [tsum_div_const]
  exact div_self (ne_of_gt (fullGaussianBlockMass_pos m hm))

/-- Summability of the normalized full-lattice Gaussian. -/
theorem summable_fullGaussianBlockProbability (m : ℕ) (hm : 0 < m) :
    Summable (fullGaussianBlockProbability m) := by
  have h := (summable_fullGaussianBlockWeight m hm).mul_right
    ((∑' j : ℤ, fullGaussianBlockWeight m j)⁻¹)
  change Summable (fun k : ℤ =>
    fullGaussianBlockWeight m k / (∑' j : ℤ, fullGaussianBlockWeight m j))
  simpa only [div_eq_mul_inv] using h

/-- Convolution of normalized full-lattice Gaussian blocks is the unnormalized
convolution divided by the two block masses. -/
theorem tsum_fullGaussianBlockProbability_convolution_eq
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (j : ℤ) :
    (∑' k : ℤ,
      fullGaussianBlockProbability m k * fullGaussianBlockProbability n (j - k)) =
      (∑' k : ℤ,
        fullGaussianBlockWeight m k * fullGaussianBlockWeight n (j - k)) /
        ((∑' k : ℤ, fullGaussianBlockWeight m k) *
          (∑' k : ℤ, fullGaussianBlockWeight n k)) := by
  let Zm : ℝ := ∑' k : ℤ, fullGaussianBlockWeight m k
  let Zn : ℝ := ∑' k : ℤ, fullGaussianBlockWeight n k
  have hZm : Zm ≠ 0 := (fullGaussianBlockMass_pos m hm).ne'
  have hZn : Zn ≠ 0 := (fullGaussianBlockMass_pos n hn).ne'
  calc
    _ = ∑' k : ℤ,
        (fullGaussianBlockWeight m k * fullGaussianBlockWeight n (j - k)) /
          (Zm * Zn) := by
          apply tsum_congr
          intro k
          simp only [fullGaussianBlockProbability, Zm, Zn]
          field_simp [hZm, hZn]
    _ = (∑' k : ℤ,
          fullGaussianBlockWeight m k * fullGaussianBlockWeight n (j - k)) /
          (Zm * Zn) := tsum_div_const
    _ = _ := by rfl

/-- The continuous mass factor for a full Gaussian block is `√(π m / 4)`. -/
theorem invSqrt_gaussianBlockScale_eq_sqrt (m : ℕ) (hm : 0 < m) :
    1 / Real.sqrt ((4 / (m : ℝ)) / Real.pi) =
      Real.sqrt (Real.pi * (m : ℝ) / 4) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  calc
    1 / Real.sqrt ((4 / (m : ℝ)) / Real.pi) =
        Real.sqrt (((4 / (m : ℝ)) / Real.pi)⁻¹) := by
          rw [Real.sqrt_inv]
          simp
    _ = Real.sqrt (Real.pi * (m : ℝ) / 4) := by
          congr 1
          field_simp [hmR, Real.pi_ne_zero]

/-- Bound the integer Gaussian sum by the corresponding geometric series. -/
theorem tsum_exp_neg_int_sq_le (b : ℝ) (hb : 0 < b) :
    (∑' k : ℤ, Real.exp (-b * (k : ℝ) ^ 2)) ≤
      1 + 2 * Real.exp (-b) / (1 - Real.exp (-b)) := by
  let f : ℤ → ℝ := fun k => Real.exp (-b * (k : ℝ) ^ 2)
  let q : ℝ := Real.exp (-b)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hint : Summable f := by
    simpa [f] using summable_exp_neg_int_sq b hb
  have hnat : Summable (fun n : ℕ => Real.exp (-b * (n : ℝ) ^ 2)) := by
    have hnat' := (summable_int_iff_summable_nat_and_neg.mp
      (summable_exp_neg_int_sq b hb)).1
    simpa using hnat'
  have heven : Function.Even f := by
    intro k
    simp [f]
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hint
  have hpos : Summable (fun n : ℕ =>
      Real.exp (-b * ((n + 1 : ℕ) : ℝ) ^ 2)) :=
    hnat.comp_injective Nat.succ_injective
  have hgeom : Summable (fun n : ℕ => q * q ^ n) := by
    exact (summable_geometric_of_lt_one hq0.le hq1).mul_left q
  have hterm (n : ℕ) :
      Real.exp (-b * ((n + 1 : ℕ) : ℝ) ^ 2) ≤ q * q ^ n := by
    have hn : (n : ℝ) + 1 ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by
      have hncast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_cast
      rw [hncast]
      nlinarith [sq_nonneg ((n : ℝ) + 1 - 1)]
    have hexp : -b * ((n + 1 : ℕ) : ℝ) ^ 2 ≤ -b * ((n : ℝ) + 1) :=
      mul_le_mul_of_nonpos_left hn (by linarith)
    calc
      _ ≤ Real.exp (-b * ((n : ℝ) + 1)) := Real.exp_monotone hexp
      _ = q * q ^ n := by
        dsimp [q]
        rw [show -b * ((n : ℝ) + 1) = -b + (n : ℝ) * (-b) by ring,
          Real.exp_add, Real.exp_nat_mul]
  have hpnatSucc (g : ℕ → ℝ) :
      (∑' n : ℕ+, g n) = ∑' n : ℕ, g (n + 1) := by
    simpa using (tsum_pnat_eq_tsum_succ (f := g))
  have hposBound :
      (∑' n : ℕ+, Real.exp (-b * (n : ℝ) ^ 2)) ≤ q / (1 - q) := by
    rw [hpnatSucc (fun n : ℕ => Real.exp (-b * (n : ℝ) ^ 2))]
    calc
      _ ≤ ∑' n : ℕ, q * q ^ n :=
        Summable.tsum_le_tsum (fun n => hterm n) hpos hgeom
      _ = q / (1 - q) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1]
        ring
  rw [show (∑' k : ℤ, Real.exp (-b * (k : ℝ) ^ 2)) = ∑' k : ℤ, f k by
    rfl, hsplit]
  have hzero : f 0 = 1 := by simp [f]
  rw [hzero]
  have hposBound' :
      (∑' n : ℕ+, f n) ≤ q / (1 - q) := by
    simpa [f] using hposBound
  have hmul := mul_le_mul_of_nonneg_left hposBound' (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ = 1 + 2 * (∑' n : ℕ+, f n) := by simp [nsmul_eq_mul]
    _ ≤ 1 + 2 * (q / (1 - q)) := by
      simpa [add_comm] using add_le_add_left hmul 1
    _ = 1 + 2 * Real.exp (-b) / (1 - Real.exp (-b)) := by simp [q]; ring

/-- The contribution of the nonzero integer modes is bounded by a geometric
tail, which tends to zero as the Gaussian becomes broad. -/
theorem tsum_exp_neg_int_sq_off_zero_le (b : ℝ) (hb : 0 < b) :
    (∑' k : ℤ, if k = 0 then (0 : ℝ) else Real.exp (-b * (k : ℝ) ^ 2)) ≤
      2 * Real.exp (-b) / (1 - Real.exp (-b)) := by
  let f : ℤ → ℝ := fun k => Real.exp (-b * (k : ℝ) ^ 2)
  let q : ℝ := Real.exp (-b)
  have hq0 : 0 < q := by dsimp [q]; positivity
  have hq1 : q < 1 := by
    dsimp [q]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hf : Summable f := by
    simpa [f] using summable_exp_neg_int_sq b hb
  have hsplit := hf.tsum_eq_add_tsum_ite (0 : ℤ)
  have hfull := tsum_exp_neg_int_sq_le b hb
  have hzero : f 0 = 1 := by simp [f]
  have hsplit' :
      (∑' k : ℤ, f k) = 1 +
        (∑' k : ℤ, if k = 0 then (0 : ℝ) else f k) := by
    simpa [f, hzero] using hsplit
  have htail :
      (∑' k : ℤ, if k = 0 then (0 : ℝ) else f k) ≤
        2 * q / (1 - q) := by
    have hfull' : (∑' k : ℤ, f k) ≤ 1 + 2 * q / (1 - q) := by
      simpa [f, q] using hfull
    rw [hsplit'] at hfull'
    linarith
  simpa [f, q] using htail

/-- The nonzero dual modes in Poisson summation are uniformly small, with no
dependence on the spatial shift. -/
theorem tsum_complex_gaussian_dual_sub_one_norm_le (a x : ℝ) (ha : 0 < a) :
    ‖(∑' k : ℤ,
        Complex.exp (-Real.pi / (a : ℂ) * (k : ℂ) ^ 2 -
          2 * Real.pi * Complex.I * (x : ℂ) * k)) - 1‖ ≤
      2 * Real.exp (-Real.pi / a) / (1 - Real.exp (-Real.pi / a)) := by
  let b : ℝ := Real.pi / a
  let g : ℤ → ℂ := fun k =>
    Complex.exp (-Real.pi / (a : ℂ) * (k : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * (x : ℂ) * k)
  have hb : 0 < b := by dsimp [b]; positivity
  have hnorm (k : ℤ) : ‖g k‖ = Real.exp (-b * (k : ℝ) ^ 2) := by
    change ‖Complex.exp (-Real.pi / (a : ℂ) * (k : ℂ) ^ 2 -
      2 * Real.pi * Complex.I * (x : ℂ) * k)‖ = _
    rw [Complex.norm_exp]
    simp [b, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [show (k : ℂ) ^ 2 = (((k : ℝ) ^ 2 : ℝ) : ℂ) by norm_cast,
      Complex.ofReal_re]
    ring
  have hnormSummable : Summable (fun k : ℤ => ‖g k‖) := by
    simpa [hnorm] using summable_exp_neg_int_sq b hb
  have hgsummable : Summable g := hnormSummable.of_norm
  have hzero : g 0 = 1 := by simp [g]
  have hsplit := hgsummable.tsum_eq_add_tsum_ite (0 : ℤ)
  have hsplit' :
      (∑' k : ℤ, g k) - 1 =
        ∑' k : ℤ, if k = 0 then (0 : ℂ) else g k := by
    rw [hsplit, hzero]
    ring
  have htailSummable : Summable (fun k : ℤ =>
      ‖if k = 0 then (0 : ℂ) else g k‖) := by
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun k => ?_) (summable_exp_neg_int_sq b hb)
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk, hnorm]
  have htailBound : ∀ k : ℤ,
      ‖if k = 0 then (0 : ℂ) else g k‖ ≤
        if k = 0 then (0 : ℝ) else Real.exp (-b * (k : ℝ) ^ 2) := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · simp [hk, hnorm]
  calc
    _ = ‖∑' k : ℤ, if k = 0 then (0 : ℂ) else g k‖ := by rw [← hsplit']
    _ ≤ ∑' k : ℤ, ‖if k = 0 then (0 : ℂ) else g k‖ :=
      norm_tsum_le_tsum_norm htailSummable
    _ ≤ ∑' k : ℤ,
        if k = 0 then (0 : ℝ) else Real.exp (-b * (k : ℝ) ^ 2) :=
      Summable.tsum_le_tsum htailBound htailSummable
        (by
          have h := summable_exp_neg_int_sq b hb
          exact h.of_nonneg_of_le
            (by
              intro k
              by_cases hk : k = 0
              · simp [hk]
              · simpa [hk] using (Real.exp_pos _).le)
            (by
              intro k
              by_cases hk : k = 0
              · simp [hk]
              · simp [hk]))
    _ ≤ 2 * Real.exp (-b) / (1 - Real.exp (-b)) :=
      tsum_exp_neg_int_sq_off_zero_le b hb
    _ = 2 * Real.exp (-Real.pi / a) / (1 - Real.exp (-Real.pi / a)) := by
      simp only [b]
      rw [← neg_div]

/-- Regard a real shifted Gaussian sum as the corresponding complex sum. -/
theorem ofReal_tsum_exp_neg_gaussian_shift (b x : ℝ) :
    ((∑' k : ℤ, Real.exp (-b * ((k : ℝ) - x) ^ 2) : ℝ) : ℂ) =
      ∑' k : ℤ, Complex.exp (-b * ((k : ℂ) - (x : ℂ)) ^ 2) := by
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  simp [Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg,
    Complex.ofReal_pow, Complex.ofReal_sub, Complex.ofReal_intCast]

/-- The shifted real Gaussian sum, written in Poisson-dual form. -/
theorem ofReal_tsum_exp_neg_gaussian_shift_eq_dual (b x : ℝ) (hb : 0 < b) :
    ((∑' k : ℤ, Real.exp (-b * ((k : ℝ) - x) ^ 2) : ℝ) : ℂ) =
      1 / ((b / Real.pi : ℝ) : ℂ) ^ (1 / 2 : ℂ) *
        ∑' k : ℤ,
          Complex.exp (-Real.pi / ((b / Real.pi : ℝ) : ℂ) * (k : ℂ) ^ 2 -
            2 * Real.pi * Complex.I * (x : ℂ) * k) := by
  rw [ofReal_tsum_exp_neg_gaussian_shift]
  calc
    _ = ∑' k : ℤ,
        Complex.exp (-Real.pi * ((b / Real.pi : ℝ) : ℂ) *
          ((k : ℂ) - (x : ℂ)) ^ 2) := by
          apply tsum_congr
          intro k
          congr 1
          push_cast
          field_simp [Real.pi_ne_zero]
    _ = _ := tsum_complex_gaussian_shift
      (a := ((b / Real.pi : ℝ) : ℂ))
      (by simp [Real.pi_pos]; positivity) (x : ℂ)

/-- A shifted lattice Gaussian differs from its continuous Gaussian integral by
the exponentially small nonzero Poisson modes. -/
theorem abs_tsum_exp_neg_gaussian_shift_sub_invSqrt_le (b x : ℝ) (hb : 0 < b) :
    |(∑' k : ℤ, Real.exp (-b * ((k : ℝ) - x) ^ 2)) -
        1 / Real.sqrt (b / Real.pi)| ≤
      (1 / Real.sqrt (b / Real.pi)) *
        (2 * Real.exp (-Real.pi / (b / Real.pi)) /
          (1 - Real.exp (-Real.pi / (b / Real.pi)))) := by
  let c : ℝ := b / Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hpois := ofReal_tsum_exp_neg_gaussian_shift_eq_dual b x hb
  have hdual := tsum_complex_gaussian_dual_sub_one_norm_le c x hc
  have hsqrt : ((Real.sqrt c : ℝ) : ℂ) = (c : ℂ) ^ (1 / 2 : ℂ) := by
    have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hhalf]
    rw [← Complex.ofReal_cpow hc.le, ← Real.sqrt_eq_rpow]
  have hcoef : ((1 / Real.sqrt c : ℝ) : ℂ) =
      1 / (c : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_one, hsqrt]
  have hdiff :
      ((∑' k : ℤ, Real.exp (-b * ((k : ℝ) - x) ^ 2) - 1 / Real.sqrt c : ℝ) : ℂ) =
        (1 / (c : ℂ) ^ (1 / 2 : ℂ)) *
          ((∑' k : ℤ,
            Complex.exp (-Real.pi / (c : ℂ) * (k : ℂ) ^ 2 -
              2 * Real.pi * Complex.I * (x : ℂ) * k)) - 1) := by
    rw [Complex.ofReal_sub, hpois, hcoef]
    ring
  have hnorm :
      |(∑' k : ℤ, Real.exp (-b * ((k : ℝ) - x) ^ 2)) - 1 / Real.sqrt c| =
        ‖(1 / (c : ℂ) ^ (1 / 2 : ℂ)) *
          ((∑' k : ℤ,
            Complex.exp (-Real.pi / (c : ℂ) * (k : ℂ) ^ 2 -
              2 * Real.pi * Complex.I * (x : ℂ) * k)) - 1)‖ := by
    have h := congrArg (fun z : ℂ => ‖z‖) hdiff
    rw [Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hcoefNorm : ‖1 / (c : ℂ) ^ (1 / 2 : ℂ)‖ = 1 / Real.sqrt c := by
    rw [← hcoef]
    simp
  calc
    |(∑' k : ℤ, Real.exp (-b * ((k : ℝ) - x) ^ 2)) - 1 / Real.sqrt c| =
        ‖(1 / (c : ℂ) ^ (1 / 2 : ℂ)) *
          ((∑' k : ℤ,
            Complex.exp (-Real.pi / (c : ℂ) * (k : ℂ) ^ 2 -
              2 * Real.pi * Complex.I * (x : ℂ) * k)) - 1)‖ := hnorm
    _ = (1 / Real.sqrt c) *
          ‖(∑' k : ℤ,
            Complex.exp (-Real.pi / (c : ℂ) * (k : ℂ) ^ 2 -
              2 * Real.pi * Complex.I * (x : ℂ) * k)) - 1‖ := by
      rw [norm_mul, hcoefNorm]
    _ ≤ (1 / Real.sqrt c) *
          (2 * Real.exp (-Real.pi / c) / (1 - Real.exp (-Real.pi / c))) :=
      mul_le_mul_of_nonneg_left hdual (by positivity)
    _ = _ := by simp [c]

/-- The full-lattice block Gaussian has the expected continuous mass up to its
Poisson tail. -/
theorem abs_tsum_fullGaussianBlockWeight_sub_invSqrt_le (m : ℕ) (hm : 0 < m) :
    |(∑' k : ℤ, fullGaussianBlockWeight m k) -
        1 / Real.sqrt ((4 / (m : ℝ)) / Real.pi)| ≤
      (1 / Real.sqrt ((4 / (m : ℝ)) / Real.pi)) *
        (2 * Real.exp (-Real.pi / ((4 / (m : ℝ)) / Real.pi)) /
          (1 - Real.exp (-Real.pi / ((4 / (m : ℝ)) / Real.pi)))) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hshift := abs_tsum_exp_neg_gaussian_shift_sub_invSqrt_le
    (4 / (m : ℝ)) ((m : ℝ) / 2) (by positivity)
  have hsum :
      (∑' k : ℤ, fullGaussianBlockWeight m k) =
        ∑' k : ℤ, Real.exp (-(4 / (m : ℝ)) * ((k : ℝ) - (m : ℝ) / 2) ^ 2) := by
    apply tsum_congr
    intro k
    rw [fullGaussianBlockWeight]
    congr 1
    field_simp [hmR.ne']
    ring
  rw [hsum]
  simpa using hshift

/-- The full-lattice mass is close to its continuous Gaussian integral. -/
theorem abs_tsum_fullGaussianBlockWeight_sub_sqrt_le (m : ℕ) (hm : 0 < m) :
    |(∑' k : ℤ, fullGaussianBlockWeight m k) -
        Real.sqrt (Real.pi * (m : ℝ) / 4)| ≤
      Real.sqrt (Real.pi * (m : ℝ) / 4) *
        (2 * Real.exp (-Real.pi / ((4 / (m : ℝ)) / Real.pi)) /
          (1 - Real.exp (-Real.pi / ((4 / (m : ℝ)) / Real.pi)))) := by
  simpa [invSqrt_gaussianBlockScale_eq_sqrt m hm] using
    abs_tsum_fullGaussianBlockWeight_sub_invSqrt_le m hm

/-- The full-lattice Gaussian mass error is nonnegative for a positive block length. -/
theorem fullGaussianBlockMassThetaError_nonneg (m : ℕ) (hm : 0 < m) :
    0 ≤ fullGaussianBlockMassThetaError m := by
  let c : ℝ := (4 / (m : ℝ)) / Real.pi
  have hc : 0 < c := by dsimp [c]; positivity
  have hexp : Real.exp (-Real.pi / c) < 1 :=
    Real.exp_lt_one_iff.mpr
      (div_neg_of_neg_of_pos (neg_neg_iff_pos.mpr Real.pi_pos) hc)
  have hden : 0 < 1 - Real.exp (-Real.pi / c) := sub_pos.mpr hexp
  unfold fullGaussianBlockMassThetaError
  exact (div_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _))
    (le_of_lt hden))

/-- The full-lattice mass Poisson error decreases with the block duration. -/
theorem fullGaussianBlockMassThetaError_antitone {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n) :
    fullGaussianBlockMassThetaError n ≤ fullGaussianBlockMassThetaError m := by
  have hn : 0 < n := lt_of_lt_of_le hm hmn
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  let qm : ℝ := Real.exp (-(Real.pi ^ 2 / 4) * (m : ℝ))
  let qn : ℝ := Real.exp (-(Real.pi ^ 2 / 4) * (n : ℝ))
  have hqm : qm < 1 := by
    dsimp [qm]
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) hmR
  have hqn : qn < 1 := by
    dsimp [qn]
    apply Real.exp_lt_one_iff.mpr
    exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) hnR
  have hqnonneg : 0 ≤ qn := by dsimp [qn]; exact Real.exp_nonneg _
  have hq : qn ≤ qm := by
    apply Real.exp_le_exp.mpr
    have hcoef : 0 < Real.pi ^ 2 / 4 := by positivity
    nlinarith
  have hform (k : ℕ) (hk : 0 < k) (q : ℝ)
      (hq : q = Real.exp (-(Real.pi ^ 2 / 4) * (k : ℝ))) :
      fullGaussianBlockMassThetaError k = 2 * q / (1 - q) := by
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
    unfold fullGaussianBlockMassThetaError
    have harg : -Real.pi / ((4 / (k : ℝ)) / Real.pi) =
        -(Real.pi ^ 2 / 4) * (k : ℝ) := by
      field_simp [hkR, Real.pi_ne_zero]
    rw [harg, hq]
  have hformN := hform n hn qn rfl
  have hformM := hform m hm qm rfl
  have hdenN : 0 < 1 - qn := sub_pos.mpr hqn
  have hdenM : 0 < 1 - qm := sub_pos.mpr hqm
  rw [hformN, hformM, div_le_div_iff₀ hdenN hdenM]
  nlinarith

/-- If a full Gaussian block's relative Poisson error is at most one half, its
lattice mass lies between one half and three halves of its continuous mass. -/
theorem fullGaussianBlockWeightMass_bounds_of_theta_small
    (m : ℕ) (hm : 0 < m)
    (hδ : fullGaussianBlockMassThetaError m ≤ 1 / 2) :
    Real.sqrt (Real.pi * (m : ℝ) / 4) / 2 ≤
        ∑' k : ℤ, fullGaussianBlockWeight m k ∧
      (∑' k : ℤ, fullGaussianBlockWeight m k) ≤
        3 * Real.sqrt (Real.pi * (m : ℝ) / 4) / 2 := by
  let Z : ℝ := ∑' k : ℤ, fullGaussianBlockWeight m k
  let I : ℝ := fullGaussianBlockIntegralMass m
  have hI : 0 < I := by dsimp [I, fullGaussianBlockIntegralMass]; positivity
  have herror : |Z - I| ≤ I * fullGaussianBlockMassThetaError m := by
    simpa [Z, I, fullGaussianBlockIntegralMass, fullGaussianBlockMassThetaError] using
      abs_tsum_fullGaussianBlockWeight_sub_sqrt_le m hm
  have hsmall : I * fullGaussianBlockMassThetaError m ≤ I / 2 := by
    have hδnonneg := fullGaussianBlockMassThetaError_nonneg m hm
    nlinarith [mul_le_mul_of_nonneg_left hδ (le_of_lt hI)]
  have hbounds := abs_le.mp herror
  have hresult : I / 2 ≤ Z ∧ Z ≤ 3 * I / 2 := by
    constructor <;> nlinarith
  simpa [Z, I, fullGaussianBlockIntegralMass] using hresult

/-- The product of the two continuous rotated-coordinate Gaussian profiles
is exactly the rescaled planar heat kernel on the reachable parity class. -/
theorem fullGaussianBlockPairContinuousDensity_eq_heatKernel
    (N n : ℕ) (hN : 0 < N) (hn : 0 < n) (z : Site) (j₁ j₂ : ℤ)
    (h₁ : 2 * j₁ = (n : ℤ) + z 0 + z 1)
    (h₂ : 2 * j₂ = (n : ℤ) + z 0 - z 1) :
    (N / 4 : ℝ) *
        (fullGaussianBlockWeight n j₁ / fullGaussianBlockIntegralMass n) *
        (fullGaussianBlockWeight n j₂ / fullGaussianBlockIntegralMass n) =
      heatKernel (n / (2 * N))
        ((Real.sqrt (N / 2))⁻¹ • siteToPlane z) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hD₁ : 2 * (j₁ : ℝ) - (n : ℝ) = (z 0 : ℝ) + (z 1 : ℝ) := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) h₁
    push_cast at h
    linarith
  have hD₂ : 2 * (j₂ : ℝ) - (n : ℝ) = (z 0 : ℝ) - (z 1 : ℝ) := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) h₂
    push_cast at h
    linarith
  have hsiteNorm : ‖siteToPlane z‖ ^ 2 = (z 0 : ℝ) ^ 2 + (z 1 : ℝ) ^ 2 :=
    Critical2DKPZ.norm_siteToPlane_sq z
  have hrot : (2 * (j₁ : ℝ) - (n : ℝ)) ^ 2 +
      (2 * (j₂ : ℝ) - (n : ℝ)) ^ 2 = 2 * ‖siteToPlane z‖ ^ 2 := by
    rw [hD₁, hD₂, hsiteNorm]
    ring
  have hscaleSq : ((Real.sqrt ((N : ℝ) / 2))⁻¹) ^ 2 = 2 / (N : ℝ) := by
    have hpos : 0 < (N : ℝ) / 2 := by positivity
    rw [inv_pow, Real.sq_sqrt hpos.le]
    field_simp [hNreal.ne']
  have hscaledNorm :
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ^ 2 =
        (2 / (N : ℝ)) * ‖siteToPlane z‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)), mul_pow, hscaleSq]
  have hIsq : fullGaussianBlockIntegralMass n ^ 2 = Real.pi * (n : ℝ) / 4 := by
    dsimp [fullGaussianBlockIntegralMass]
    rw [Real.sq_sqrt (by positivity)]
  have hexp :
      -((2 * (j₁ : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ) +
          -((2 * (j₂ : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ) =
        -‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ^ 2 /
          (2 * ((n : ℝ) / (2 * (N : ℝ)))) := by
    rw [← add_div, ← neg_add, hrot, hscaledNorm]
    field_simp [hnreal.ne', hNreal.ne']
  have hIpos : 0 < fullGaussianBlockIntegralMass n := by
    dsimp [fullGaussianBlockIntegralMass]
    positivity
  have hprodExp :
      Real.exp (-((2 * (j₁ : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ)) /
          fullGaussianBlockIntegralMass n *
        (Real.exp (-((2 * (j₂ : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ)) /
          fullGaussianBlockIntegralMass n) =
        Real.exp (-((2 * (j₁ : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ) +
          -((2 * (j₂ : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ)) /
          (fullGaussianBlockIntegralMass n * fullGaussianBlockIntegralMass n) := by
    field_simp [hIpos.ne']
    rw [← Real.exp_add]
    congr 1
    ring
  rw [fullGaussianBlockWeight, fullGaussianBlockWeight, heatKernel_eq_exp]
  have hcoeff : (N / 4 : ℝ) /
      (fullGaussianBlockIntegralMass n * fullGaussianBlockIntegralMass n) =
        (2 * Real.pi * ((n : ℝ) / (2 * (N : ℝ))))⁻¹ := by
    rw [← pow_two, hIsq]
    field_simp [hnreal.ne', hNreal.ne', Real.pi_ne_zero]
  have hexpHeat : -‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ^ 2 /
      (2 * ((n : ℝ) / (2 * (N : ℝ)))) =
        -(2 * ((n : ℝ) / (2 * (N : ℝ))))⁻¹ *
          ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ^ 2 := by
    have hu : 0 < (n : ℝ) / (2 * (N : ℝ)) := by positivity
    field_simp [hu.ne']
  calc
    _ = (N / 4 : ℝ) *
        ((Real.exp (-((2 * (j₁ : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ)) /
          fullGaussianBlockIntegralMass n) *
         (Real.exp (-((2 * (j₂ : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ)) /
          fullGaussianBlockIntegralMass n)) := by ring
    _ = (N / 4 : ℝ) *
        (Real.exp (-((2 * (j₁ : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ) +
          -((2 * (j₂ : ℝ) - (n : ℝ)) ^ 2) / (n : ℝ)) /
          (fullGaussianBlockIntegralMass n * fullGaussianBlockIntegralMass n)) := by
      rw [hprodExp]
    _ = (N / 4 : ℝ) *
        (Real.exp (-‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ^ 2 /
          (2 * ((n : ℝ) / (2 * (N : ℝ)))) ) /
          (fullGaussianBlockIntegralMass n * fullGaussianBlockIntegralMass n)) := by
      rw [hexp]
    _ = ((N / 4 : ℝ) /
        (fullGaussianBlockIntegralMass n * fullGaussianBlockIntegralMass n)) *
          Real.exp (-‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ^ 2 /
            (2 * ((n : ℝ) / (2 * (N : ℝ))))) := by ring
    _ = (2 * Real.pi * ((n : ℝ) / (2 * (N : ℝ))))⁻¹ *
          Real.exp (-(2 * ((n : ℝ) / (2 * (N : ℝ))))⁻¹ *
            ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ^ 2) := by
      rw [hcoeff, hexpHeat]

/-- A normalized full-lattice Gaussian block is pointwise close, relatively,
to its continuous Gaussian density. -/
theorem abs_fullGaussianBlockProbability_sub_continuousDensity_le
    (m : ℕ) (hm : 0 < m) (k : ℤ) :
    |fullGaussianBlockProbability m k -
        fullGaussianBlockWeight m k / fullGaussianBlockIntegralMass m| ≤
      fullGaussianBlockProbability m k * fullGaussianBlockMassThetaError m := by
  let Z : ℝ := ∑' j : ℤ, fullGaussianBlockWeight m j
  let I : ℝ := fullGaussianBlockIntegralMass m
  let η : ℝ := fullGaussianBlockMassThetaError m
  let G : ℝ := fullGaussianBlockWeight m k
  change |G / Z - G / I| ≤ G / Z * η
  have hZ : 0 < Z := by
    exact fullGaussianBlockMass_pos m hm
  have hI : 0 < I := by
    dsimp [I, fullGaussianBlockIntegralMass]
    positivity
  have hG : 0 ≤ G := by
    dsimp [G, fullGaussianBlockWeight]
    exact Real.exp_nonneg _
  have hmass : |Z - I| ≤ I * η := by
    dsimp [Z, I, η]
    simpa [fullGaussianBlockIntegralMass, fullGaussianBlockMassThetaError] using
      abs_tsum_fullGaussianBlockWeight_sub_sqrt_le m hm
  have hIZ : |I - Z| ≤ I * η := by
    simpa [abs_sub_comm] using hmass
  have hnum : G * |I - Z| ≤ G * (I * η) :=
    mul_le_mul_of_nonneg_left hIZ hG
  have hden : 0 < Z * I := mul_pos hZ hI
  have hform : |G / Z - G / I| = (G * |I - Z|) / (Z * I) := by
    have hsub : G / Z - G / I = G * (I - Z) / (Z * I) := by
      field_simp [hZ.ne', hI.ne']
    rw [hsub, abs_div, abs_mul, abs_of_nonneg hG, abs_of_pos hden]
  calc
    |G / Z - G / I| = (G * |I - Z|) / (Z * I) := hform
    _ ≤ (G * (I * η)) / (Z * I) :=
      div_le_div_of_nonneg_right hnum (le_of_lt hden)
    _ = G / Z * η := by
      field_simp [hZ.ne', hI.ne']


private theorem normalized_pair_convolution_error_of_mass_errors
    (G θ Ih Is Im In Zm Zn Zs δh δs δm δn : ℝ)
    (hG : 0 ≤ G)
    (hIh : 0 < Ih) (hIn : 0 < In)
    (hZm : 0 < Zm) (hZn : 0 < Zn) (hZs : 0 < Zs)
    (hθ : |θ - Ih| ≤ Ih * δh)
    (hZsErr : |Zs - Is| ≤ Is * δs)
    (hZmErr : |Zm - Im| ≤ Im * δm)
    (hZnErr : |Zn - In| ≤ In * δn)
    (hscale : Ih * Is = Im * In) :
    |G * θ / (Zm * Zn) - G / Zs| ≤
      G / (Zm * Zn * Zs) *
        (Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn) := by
  have hdecomp : θ * Zs - Zm * Zn =
      (θ - Ih) * Zs + Ih * (Zs - Is) + (Im - Zm) * In + Zm * (In - Zn) := by
    linear_combination hscale
  have hnum :
      |θ * Zs - Zm * Zn| ≤
        Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn := by
    have htri :
        |(θ - Ih) * Zs + Ih * (Zs - Is) + (Im - Zm) * In + Zm * (In - Zn)| ≤
          |(θ - Ih) * Zs| + |Ih * (Zs - Is)| +
            |(Im - Zm) * In| + |Zm * (In - Zn)| := by
      have hBCD := abs_add_le (Ih * (Zs - Is))
        ((Im - Zm) * In + Zm * (In - Zn))
      have hBCD' :
          |Ih * (Zs - Is) + (Im - Zm) * In + Zm * (In - Zn)| ≤
            |Ih * (Zs - Is)| + |(Im - Zm) * In + Zm * (In - Zn)| := by
        simpa only [add_assoc] using hBCD
      have hCD := abs_add_le ((Im - Zm) * In) (Zm * (In - Zn))
      calc
        |(θ - Ih) * Zs + Ih * (Zs - Is) + (Im - Zm) * In + Zm * (In - Zn)| =
            |(θ - Ih) * Zs +
              (Ih * (Zs - Is) + (Im - Zm) * In + Zm * (In - Zn))| := by
          congr 1
          ring
        _ ≤ |(θ - Ih) * Zs| +
            |Ih * (Zs - Is) + (Im - Zm) * In + Zm * (In - Zn)| :=
          abs_add_le _ _
        _ ≤ |(θ - Ih) * Zs| +
            (|Ih * (Zs - Is)| + |(Im - Zm) * In + Zm * (In - Zn)|) :=
          add_le_add (le_refl _) hBCD'
        _ ≤ |(θ - Ih) * Zs| +
            (|Ih * (Zs - Is)| + (|(Im - Zm) * In| + |Zm * (In - Zn)|)) := by
          have hInner := add_le_add_left hCD |Ih * (Zs - Is)|
          have hOuter := add_le_add_left hInner |(θ - Ih) * Zs|
          simpa [add_comm, add_left_comm, add_assoc] using hOuter
        _ = _ := by simp only [abs_mul, abs_of_pos hZs, abs_of_pos hIh,
          abs_of_pos hIn, abs_of_pos hZm, add_assoc]
    have hprod :
        |(θ - Ih) * Zs| + |Ih * (Zs - Is)| +
            |(Im - Zm) * In| + |Zm * (In - Zn)| =
          |θ - Ih| * Zs + Ih * |Zs - Is| +
            |Im - Zm| * In + Zm * |In - Zn| := by
      simp [abs_mul, abs_of_pos hZs, abs_of_pos hIh,
        abs_of_pos hIn, abs_of_pos hZm]
    rw [hprod] at htri
    have h₁ := mul_le_mul_of_nonneg_right hθ (le_of_lt hZs)
    have h₂ := mul_le_mul_of_nonneg_left hZsErr (le_of_lt hIh)
    have h₃ := mul_le_mul_of_nonneg_right hZmErr (le_of_lt hIn)
    have h₄ := mul_le_mul_of_nonneg_left hZnErr (le_of_lt hZm)
    calc
      |θ * Zs - Zm * Zn| =
          |(θ - Ih) * Zs + Ih * (Zs - Is) + (Im - Zm) * In + Zm * (In - Zn)| := by
            rw [hdecomp]
      _ ≤ |θ - Ih| * Zs + Ih * |Zs - Is| + |Im - Zm| * In + Zm * |In - Zn| := htri
      _ = |(θ - Ih) * Zs| + |Ih * (Zs - Is)| +
            |(Im - Zm) * In| + |Zm * (In - Zn)| := hprod.symm
      _ ≤ Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn := by
        have hleft :
            |θ - Ih| * Zs + Ih * |Zs - Is| ≤ Ih * δh * Zs + Ih * Is * δs := by
          simpa [mul_assoc] using add_le_add h₁ h₂
        have hright :
            |Im - Zm| * In + Zm * |In - Zn| ≤ Im * δm * In + Zm * In * δn := by
          simpa [mul_assoc, abs_sub_comm] using add_le_add h₃ h₄
        calc
          _ = (|θ - Ih| * Zs + Ih * |Zs - Is|) +
                (|Im - Zm| * In + Zm * |In - Zn|) := by
                  simpa only [add_assoc] using hprod
          _ ≤ (Ih * δh * Zs + Ih * Is * δs) +
                (Im * δm * In + Zm * In * δn) := add_le_add hleft hright
          _ = _ := by simp only [add_assoc]
  have hden : 0 < Zm * Zn * Zs := mul_pos (mul_pos hZm hZn) hZs
  have hform :
      G * θ / (Zm * Zn) - G / Zs =
        G * (θ * Zs - Zm * Zn) / (Zm * Zn * Zs) := by
    field_simp [hZm.ne', hZn.ne', hZs.ne']
  have habs :
      |G * θ / (Zm * Zn) - G / Zs| =
        (G * |θ * Zs - Zm * Zn|) / (Zm * Zn * Zs) := by
    rw [hform, abs_div, abs_mul, abs_of_nonneg hG, abs_of_pos hden]
  have hnum' := mul_le_mul_of_nonneg_left hnum hG
  calc
    |G * θ / (Zm * Zn) - G / Zs| =
        (G * |θ * Zs - Zm * Zn|) / (Zm * Zn * Zs) := habs
    _ ≤ (G * (Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn)) /
          (Zm * Zn * Zs) := div_le_div_of_nonneg_right hnum' hden.le
    _ = G / (Zm * Zn * Zs) *
          (Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn) := by
      field_simp [hden.ne']

/-- The convolution of two normalized lattice Gaussian blocks is close to the normalized Gaussian at their combined duration, with error controlled by shifted Poisson sums and the three normalization masses. -/
def fullGaussianBlockPairConvolutionError (m n : ℕ) (j : ℤ) : ℝ :=
  let s : ℕ := m + n
  let Zm : ℝ := ∑' k : ℤ, fullGaussianBlockWeight m k
  let Zn : ℝ := ∑' k : ℤ, fullGaussianBlockWeight n k
  let Zs : ℝ := ∑' k : ℤ, fullGaussianBlockWeight s k
  let b : ℝ := 4 * (s : ℝ) / ((m : ℝ) * (n : ℝ))
  let c : ℝ := b / Real.pi
  let Ih : ℝ := 1 / Real.sqrt c
  let Is : ℝ := fullGaussianBlockIntegralMass s
  let Im : ℝ := fullGaussianBlockIntegralMass m
  let In : ℝ := fullGaussianBlockIntegralMass n
  let δh : ℝ := 2 * Real.exp (-Real.pi / c) / (1 - Real.exp (-Real.pi / c))
  let δs : ℝ := fullGaussianBlockMassThetaError s
  let δm : ℝ := fullGaussianBlockMassThetaError m
  let δn : ℝ := fullGaussianBlockMassThetaError n
  fullGaussianBlockWeight s j / (Zm * Zn * Zs) *
    (Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn)

/-- The two-block Gaussian convolution differs from the combined block by at most its error envelope. -/
theorem abs_tsum_fullGaussianBlockProbability_pair_sub_le
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (j : ℤ) :
    |(∑' k : ℤ,
        fullGaussianBlockProbability m k * fullGaussianBlockProbability n (j - k)) -
      fullGaussianBlockProbability (m + n) j| ≤
      fullGaussianBlockPairConvolutionError m n j := by
  let s : ℕ := m + n
  let Zm : ℝ := ∑' k : ℤ, fullGaussianBlockWeight m k
  let Zn : ℝ := ∑' k : ℤ, fullGaussianBlockWeight n k
  let Zs : ℝ := ∑' k : ℤ, fullGaussianBlockWeight s k
  let b : ℝ := 4 * (s : ℝ) / ((m : ℝ) * (n : ℝ))
  let c : ℝ := b / Real.pi
  let Ih : ℝ := 1 / Real.sqrt c
  let Is : ℝ := fullGaussianBlockIntegralMass s
  let Im : ℝ := fullGaussianBlockIntegralMass m
  let In : ℝ := fullGaussianBlockIntegralMass n
  let δh : ℝ := 2 * Real.exp (-Real.pi / c) / (1 - Real.exp (-Real.pi / c))
  let δs : ℝ := fullGaussianBlockMassThetaError s
  let δm : ℝ := fullGaussianBlockMassThetaError m
  let δn : ℝ := fullGaussianBlockMassThetaError n
  let θ : ℝ := ∑' k : ℤ, Real.exp
    (-((4 * (s : ℝ) / ((m : ℝ) * (n : ℝ))) *
      ((k : ℝ) - (m : ℝ) * (j : ℝ) / (s : ℝ)) ^ 2))
  let G : ℝ := fullGaussianBlockWeight s j
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hspos : 0 < s := by dsimp [s]; omega
  have hsR : 0 < (s : ℝ) := by exact_mod_cast hspos
  have hb : 0 < b := by dsimp [b, s]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hexpC : Real.exp (-Real.pi / c) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_neg_of_pos Real.pi_pos) hc)
  have hdenC : 0 < 1 - Real.exp (-Real.pi / c) := sub_pos.mpr hexpC
  have hZm : 0 < Zm := by
    dsimp [Zm]
    exact fullGaussianBlockMass_pos m hm
  have hZn : 0 < Zn := by
    dsimp [Zn]
    exact fullGaussianBlockMass_pos n hn
  have hZs : 0 < Zs := by
    dsimp [Zs]
    exact fullGaussianBlockMass_pos s hspos
  have hIh : 0 < Ih := by dsimp [Ih]; positivity
  have hIs : 0 < Is := by
    dsimp [Is, fullGaussianBlockIntegralMass]
    exact Real.sqrt_pos.mpr (by positivity)
  have hIm : 0 < Im := by
    dsimp [Im, fullGaussianBlockIntegralMass]
    exact Real.sqrt_pos.mpr (by positivity)
  have hIn : 0 < In := by
    dsimp [In, fullGaussianBlockIntegralMass]
    exact Real.sqrt_pos.mpr (by positivity)
  have hθ : |θ - Ih| ≤ Ih * δh := by
    let x : ℝ := (m : ℝ) * (j : ℝ) / (s : ℝ)
    have h := abs_tsum_exp_neg_gaussian_shift_sub_invSqrt_le b x hb
    simpa [θ, Ih, δh, c, x] using h
  have hZsErr : |Zs - Is| ≤ Is * δs := by
    dsimp [Zs, Is, δs]
    exact abs_tsum_fullGaussianBlockWeight_sub_sqrt_le s hspos
  have hZmErr : |Zm - Im| ≤ Im * δm := by
    dsimp [Zm, Im, δm]
    exact abs_tsum_fullGaussianBlockWeight_sub_sqrt_le m hm
  have hZnErr : |Zn - In| ≤ In * δn := by
    dsimp [Zn, In, δn]
    exact abs_tsum_fullGaussianBlockWeight_sub_sqrt_le n hn
  have hIhSq : Ih ^ 2 = Real.pi * (m : ℝ) * (n : ℝ) / (4 * (s : ℝ)) := by
    dsimp [Ih, c, b, s]
    rw [one_div, inv_pow, Real.sq_sqrt (by positivity)]
    field_simp [hmR.ne', hnR.ne', hsR.ne', Real.pi_ne_zero]
  have hIsSq : Is ^ 2 = Real.pi * (s : ℝ) / 4 := by
    dsimp [Is, fullGaussianBlockIntegralMass]
    rw [Real.sq_sqrt (by positivity)]
  have hImSq : Im ^ 2 = Real.pi * (m : ℝ) / 4 := by
    dsimp [Im, fullGaussianBlockIntegralMass]
    rw [Real.sq_sqrt (by positivity)]
  have hInSq : In ^ 2 = Real.pi * (n : ℝ) / 4 := by
    dsimp [In, fullGaussianBlockIntegralMass]
    rw [Real.sq_sqrt (by positivity)]
  have hscale : Ih * Is = Im * In := by
    have hsCast : (s : ℝ) = (m : ℝ) + (n : ℝ) := by
      dsimp [s]
      norm_cast
    have hsumRne : (m : ℝ) + (n : ℝ) ≠ 0 := ne_of_gt (add_pos hmR hnR)
    have hsq : (Ih * Is) ^ 2 = (Im * In) ^ 2 := by
      calc
        (Ih * Is) ^ 2 = Ih ^ 2 * Is ^ 2 := by rw [mul_pow]
        _ = Im ^ 2 * In ^ 2 := by
          rw [hIhSq, hIsSq, hImSq, hInSq]
          rw [hsCast]
          field_simp [hsumRne]
        _ = (Im * In) ^ 2 := by rw [mul_pow]
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
    · exact h
    · have hl : 0 < Ih * Is := mul_pos hIh hIs
      have hr : 0 < Im * In := mul_pos hIm hIn
      linarith
  have hG : 0 ≤ G := by dsimp [G, fullGaussianBlockWeight]; positivity
  have hconv := normalized_pair_convolution_error_of_mass_errors
    G θ Ih Is Im In Zm Zn Zs δh δs δm δn hG hIh hIn
    hZm hZn hZs hθ hZsErr hZmErr hZnErr hscale
  have hraw :
      (∑' k : ℤ,
        fullGaussianBlockWeight m k * fullGaussianBlockWeight n (j - k)) = G * θ := by
    have hform := tsum_fullGaussianBlockWeight_convolution m n hm hn j
    have hG' : G = Real.exp (-((2 * (j : ℝ) - (m : ℝ) - (n : ℝ)) ^ 2) /
        ((m + n : ℕ) : ℝ)) := by
      change fullGaussianBlockWeight s j = _
      rw [fullGaussianBlockWeight]
      have hsCast : (s : ℝ) = (m : ℝ) + (n : ℝ) := by
        dsimp [s]
        norm_cast
      congr 1
      rw [hsCast]
      field_simp [hsR.ne']
      ring
    rw [hG']
    simpa [θ, b, s] using hform
  have hconvEq :
      (∑' k : ℤ,
        fullGaussianBlockProbability m k * fullGaussianBlockProbability n (j - k)) =
        G * θ / (Zm * Zn) := by
    rw [tsum_fullGaussianBlockProbability_convolution_eq m n hm hn j, hraw]
  change |(∑' k : ℤ,
      fullGaussianBlockProbability m k * fullGaussianBlockProbability n (j - k)) -
      fullGaussianBlockProbability (m + n) j| ≤ _
  rw [hconvEq]
  change |G * θ / (Zm * Zn) - G / Zs| ≤
    fullGaussianBlockPairConvolutionError m n j
  simpa [fullGaussianBlockPairConvolutionError, G, Zm, Zn, Zs, s, b, c,
    Ih, Is, Im, In, δh, δs, δm, δn, fullGaussianBlockMassThetaError,
    fullGaussianBlockIntegralMass, fullGaussianBlockWeight] using hconv


end Critical2DKPZ.SHF.Moments

end
