/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockGaussianTheta
import Mathlib.Tactic

/-! # Full-lattice Gaussian laws for pair-block compositions -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Filter

/-- The integer-valued law of the sum of independent full-lattice Gaussian
block marks. -/
def fullGaussianBlockListProbability : List ℕ → ℤ → ℝ
  | [], j => if j = 0 then 1 else 0
  | [m], j => fullGaussianBlockProbability m j
  | m :: n :: ms, j =>
      ∑' k : ℤ, fullGaussianBlockProbability m k *
        fullGaussianBlockListProbability (n :: ms) (j - k)

/-- The normalized pair-convolution error accumulated when a finite list of
Gaussian block laws is combined from left to right. -/
def fullGaussianBlockPairErrorMass (m n : ℕ) : ℝ :=
  ∑' j : ℤ, fullGaussianBlockPairConvolutionError m n j

private theorem fullGaussianBlockPairConvolutionError_nonneg
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (j : ℤ) :
    0 ≤ fullGaussianBlockPairConvolutionError m n j := by
  have h := abs_tsum_fullGaussianBlockProbability_pair_sub_le m n hm hn j
  exact le_trans (abs_nonneg _) h

/-- The pair convolution error at `j` is its value at `0` times the ratio of block weights
of duration `m + n` at `j` and at `0`. -/
theorem fullGaussianBlockPairConvolutionError_eq_const_mul_weight
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (j : ℤ) :
    fullGaussianBlockPairConvolutionError m n j =
      fullGaussianBlockPairConvolutionError m n 0 /
        fullGaussianBlockWeight (m + n) 0 *
          fullGaussianBlockWeight (m + n) j := by
  let Zm : ℝ := ∑' k : ℤ, fullGaussianBlockWeight m k
  let Zn : ℝ := ∑' k : ℤ, fullGaussianBlockWeight n k
  let Zs : ℝ := ∑' k : ℤ, fullGaussianBlockWeight (m + n) k
  let b : ℝ := 4 * ((m + n : ℕ) : ℝ) / ((m : ℝ) * (n : ℝ))
  let c : ℝ := b / Real.pi
  let Ih : ℝ := 1 / Real.sqrt c
  let Is : ℝ := fullGaussianBlockIntegralMass (m + n)
  let Im : ℝ := fullGaussianBlockIntegralMass m
  let In : ℝ := fullGaussianBlockIntegralMass n
  let δh : ℝ := 2 * Real.exp (-Real.pi / c) / (1 - Real.exp (-Real.pi / c))
  let δs : ℝ := fullGaussianBlockMassThetaError (m + n)
  let δm : ℝ := fullGaussianBlockMassThetaError m
  let δn : ℝ := fullGaussianBlockMassThetaError n
  let D : ℝ := Zm * Zn * Zs
  let B : ℝ := Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn
  have hD : D ≠ 0 := by
    dsimp [D, Zm, Zn, Zs]
    exact mul_ne_zero (mul_ne_zero
      (ne_of_gt (fullGaussianBlockMass_pos m hm))
      (ne_of_gt (fullGaussianBlockMass_pos n hn)))
      (ne_of_gt (fullGaussianBlockMass_pos (m + n) (by omega)))
  have hweight0 : fullGaussianBlockWeight (m + n) 0 ≠ 0 := by
    unfold fullGaussianBlockWeight
    exact ne_of_gt (Real.exp_pos _)
  have hrepr (q : ℤ) :
      fullGaussianBlockPairConvolutionError m n q =
        fullGaussianBlockWeight (m + n) q / D * B := by
    simp only [fullGaussianBlockPairConvolutionError]
    dsimp [D, B, Zm, Zn, Zs, b, c, Ih, Is, Im, In, δh, δs, δm, δn]
  rw [hrepr j, hrepr 0]
  field_simp [hD, hweight0]

private theorem summable_fullGaussianBlockPairConvolutionError
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Summable (fullGaussianBlockPairConvolutionError m n) := by
  let c : ℝ := fullGaussianBlockPairConvolutionError m n 0 /
    fullGaussianBlockWeight (m + n) 0
  have hs : Summable (fun j : ℤ => c * fullGaussianBlockWeight (m + n) j) := by
    exact (summable_fullGaussianBlockWeight (m + n) (by omega)).mul_left c
  have heq : (fun j : ℤ => fullGaussianBlockPairConvolutionError m n j) =
      fun j => c * fullGaussianBlockWeight (m + n) j := by
    funext j
    simpa [c] using fullGaussianBlockPairConvolutionError_eq_const_mul_weight m n hm hn j
  change Summable (fun j : ℤ => fullGaussianBlockPairConvolutionError m n j)
  rw [heq]
  exact hs

/-- The accumulated pair error mass is nonnegative for positive durations. -/
theorem fullGaussianBlockPairErrorMass_nonneg
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    0 ≤ fullGaussianBlockPairErrorMass m n := by
  unfold fullGaussianBlockPairErrorMass
  exact tsum_nonneg fun j => fullGaussianBlockPairConvolutionError_nonneg m n hm hn j

/-- The pair error mass is the error at `0` divided by the weight at `0`, times the total
weight of duration `m + n`. -/
theorem fullGaussianBlockPairErrorMass_eq_weightMass
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    fullGaussianBlockPairErrorMass m n =
      (fullGaussianBlockPairConvolutionError m n 0 /
        fullGaussianBlockWeight (m + n) 0) *
        (∑' j : ℤ, fullGaussianBlockWeight (m + n) j) := by
  unfold fullGaussianBlockPairErrorMass
  calc
    _ = ∑' j : ℤ,
        (fullGaussianBlockPairConvolutionError m n 0 /
          fullGaussianBlockWeight (m + n) 0) *
          fullGaussianBlockWeight (m + n) j := by
      apply tsum_congr
      intro j
      exact fullGaussianBlockPairConvolutionError_eq_const_mul_weight m n hm hn j
    _ = _ := tsum_mul_left

/-- The pair-error mass can be expressed through the Gaussian masses and relative Poisson errors at durations `m`, `n` and `m + n`. -/
theorem fullGaussianBlockPairErrorMass_eq_massCorrection
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
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
    fullGaussianBlockPairErrorMass m n =
      (Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn) /
        (Zm * Zn) := by
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
  let B : ℝ := Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn
  change fullGaussianBlockPairErrorMass m n = B / (Zm * Zn)
  have hZm : 0 < Zm := by
    dsimp [Zm]
    exact fullGaussianBlockMass_pos m hm
  have hZn : 0 < Zn := by
    dsimp [Zn]
    exact fullGaussianBlockMass_pos n hn
  have hZs : 0 < Zs := by
    dsimp [Zs, s]
    exact fullGaussianBlockMass_pos (m + n) (by omega)
  have hw0 : fullGaussianBlockWeight (m + n) 0 ≠ 0 := by
    unfold fullGaussianBlockWeight
    exact ne_of_gt (Real.exp_pos _)
  have herror0 : fullGaussianBlockPairConvolutionError m n 0 =
      fullGaussianBlockWeight (m + n) 0 / (Zm * Zn * Zs) * B := by
    simp only [fullGaussianBlockPairConvolutionError]
    dsimp [B, Zm, Zn, Zs, s, b, c, Ih, Is, Im, In, δh, δs, δm, δn]
  rw [fullGaussianBlockPairErrorMass_eq_weightMass m n hm hn, herror0]
  field_simp [hw0, hZm.ne', hZn.ne', hZs.ne']
  ring

/-- Once the three block masses are within one half of their continuous
Gaussian masses, the normalized pair-convolution error is controlled by the
four Poisson tails in the mass correction formula. -/
theorem fullGaussianBlockPairErrorMass_le_of_theta_small
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hδm : fullGaussianBlockMassThetaError m ≤ 1 / 2)
    (hδn : fullGaussianBlockMassThetaError n ≤ 1 / 2)
    (hδs : fullGaussianBlockMassThetaError (m + n) ≤ 1 / 2) :
    fullGaussianBlockPairErrorMass m n ≤
      6 * fullGaussianBlockPairShiftThetaError m n +
        4 * fullGaussianBlockMassThetaError (m + n) +
        4 * fullGaussianBlockMassThetaError m +
        2 * fullGaussianBlockMassThetaError n := by
  let Zm : ℝ := ∑' k : ℤ, fullGaussianBlockWeight m k
  let Zn : ℝ := ∑' k : ℤ, fullGaussianBlockWeight n k
  let Zs : ℝ := ∑' k : ℤ, fullGaussianBlockWeight (m + n) k
  let Im : ℝ := fullGaussianBlockIntegralMass m
  let In : ℝ := fullGaussianBlockIntegralMass n
  let Is : ℝ := fullGaussianBlockIntegralMass (m + n)
  let Ih : ℝ := 1 / Real.sqrt
    (((4 * ((m + n : ℕ) : ℝ)) / ((m : ℝ) * (n : ℝ))) / Real.pi)
  let δh : ℝ := fullGaussianBlockPairShiftThetaError m n
  let δm : ℝ := fullGaussianBlockMassThetaError m
  let δn : ℝ := fullGaussianBlockMassThetaError n
  let δs : ℝ := fullGaussianBlockMassThetaError (m + n)
  have hZm : 0 < Zm := by dsimp [Zm]; exact fullGaussianBlockMass_pos m hm
  have hZn : 0 < Zn := by dsimp [Zn]; exact fullGaussianBlockMass_pos n hn
  have hZs : 0 < Zs := by
    dsimp [Zs]
    exact fullGaussianBlockMass_pos (m + n) (by omega)
  have hIm : 0 < Im := by dsimp [Im, fullGaussianBlockIntegralMass]; positivity
  have hIn : 0 < In := by dsimp [In, fullGaussianBlockIntegralMass]; positivity
  have hIs : 0 < Is := by dsimp [Is, fullGaussianBlockIntegralMass]; positivity
  have hIh : 0 < Ih := by dsimp [Ih]; positivity
  have hδh : 0 ≤ δh := by
    dsimp [δh]
    exact le_of_lt (fullGaussianBlockPairShiftThetaError_pos m n hm hn)
  have hδm0 : 0 ≤ δm := by
    dsimp [δm]
    exact fullGaussianBlockMassThetaError_nonneg m hm
  have hδn0 : 0 ≤ δn := by
    dsimp [δn]
    exact fullGaussianBlockMassThetaError_nonneg n hn
  have hδs0 : 0 ≤ δs := by
    dsimp [δs]
    exact fullGaussianBlockMassThetaError_nonneg (m + n) (by omega)
  have hZmLo : Im / 2 ≤ Zm := by
    have h := fullGaussianBlockWeightMass_bounds_of_theta_small m hm hδm
    simpa [Im, Zm, fullGaussianBlockIntegralMass] using h.1
  have hZnLo : In / 2 ≤ Zn := by
    have h := fullGaussianBlockWeightMass_bounds_of_theta_small n hn hδn
    simpa [In, Zn, fullGaussianBlockIntegralMass] using h.1
  have hZsHi : Zs ≤ 3 * Is / 2 := by
    have h := fullGaussianBlockWeightMass_bounds_of_theta_small
      (m + n) (by omega) hδs
    simpa [Is, Zs, fullGaussianBlockIntegralMass] using h.2
  have hproductLo : Im * In / 4 ≤ Zm * Zn := by
    have h := mul_le_mul hZmLo hZnLo (by positivity : 0 ≤ In / 2)
      (by positivity : 0 ≤ Zm)
    nlinarith
  have hproductHi : Im * In ≤ 4 * (Zm * Zn) := by nlinarith [hproductLo]
  have hscale : Ih * Is = Im * In := by
    dsimp [Ih, Is, Im, In]
    exact fullGaussianBlockPairIntegralMass_identity m n hm hn
  have hnum1 : Ih * δh * Zs ≤ Ih * δh * (3 * Is / 2) :=
    mul_le_mul_of_nonneg_left hZsHi (mul_nonneg (le_of_lt hIh) hδh)
  have hterm1 : Ih * δh * Zs / (Zm * Zn) ≤ 6 * δh := by
    rw [div_le_iff₀ (mul_pos hZm hZn)]
    calc
      Ih * δh * Zs ≤ Ih * δh * (3 * Is / 2) := hnum1
      _ = (3 / 2 * δh) * (Im * In) := by rw [← hscale]; ring
      _ ≤ (3 / 2 * δh) * (4 * (Zm * Zn)) :=
        mul_le_mul_of_nonneg_left hproductHi (by positivity)
      _ = 6 * δh * (Zm * Zn) := by ring
  have hterm2 : Ih * Is * δs / (Zm * Zn) ≤ 4 * δs := by
    rw [div_le_iff₀ (mul_pos hZm hZn)]
    calc
      Ih * Is * δs = (Im * In) * δs := by rw [hscale]
      _ ≤ (4 * (Zm * Zn)) * δs :=
        mul_le_mul_of_nonneg_right hproductHi hδs0
      _ = 4 * δs * (Zm * Zn) := by ring
  have hterm3 : Im * δm * In / (Zm * Zn) ≤ 4 * δm := by
    rw [div_le_iff₀ (mul_pos hZm hZn)]
    calc
      Im * δm * In = (Im * In) * δm := by ring
      _ ≤ (4 * (Zm * Zn)) * δm :=
        mul_le_mul_of_nonneg_right hproductHi hδm0
      _ = 4 * δm * (Zm * Zn) := by ring
  have hInHi : In ≤ 2 * Zn := by nlinarith [hZnLo]
  have hterm4 : Zm * In * δn / (Zm * Zn) ≤ 2 * δn := by
    rw [div_le_iff₀ (mul_pos hZm hZn)]
    calc
      Zm * In * δn ≤ Zm * (2 * Zn) * δn :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hInHi
          (le_of_lt hZm)) hδn0
      _ = 2 * δn * (Zm * Zn) := by ring
  rw [fullGaussianBlockPairErrorMass_eq_massCorrection m n hm hn]
  change (Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn) /
      (Zm * Zn) ≤ 6 * δh + 4 * δs + 4 * δm + 2 * δn
  have hsum := add_le_add (add_le_add hterm1 hterm2) (add_le_add hterm3 hterm4)
  have hden : 0 ≤ Zm * Zn := le_of_lt (mul_pos hZm hZn)
  have hsum' : (Ih * δh * Zs + Ih * Is * δs + Im * δm * In + Zm * In * δn) /
        (Zm * Zn) ≤
      (6 * δh + 4 * δs + 4 * δm + 2 * δn) := by
    have := hsum
    rw [← add_div, ← add_div, ← add_div] at this
    simpa [add_assoc] using this
  simpa [δh, δs, δm, δn, fullGaussianBlockPairShiftThetaError] using hsum'


/-- An explicit exponential version of the uniform long-block pair error. -/
theorem fullGaussianBlockPairErrorMass_le_exp
    (M m n : ℕ) (hM : 0 < M) (hMm : M ≤ m) (hMn : M ≤ n)
    (hq : Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) ≤ 1 / 8) :
    fullGaussianBlockPairErrorMass m n ≤
      64 * Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) := by
  have hm : 0 < m := lt_of_lt_of_le hM hMm
  have hn : 0 < n := lt_of_lt_of_le hM hMn
  let q : ℝ := Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ))
  let r : ℝ := Real.exp (-(Real.pi ^ 2 / 4) * (M : ℝ))
  have hqpos : 0 < q := by dsimp [q]; exact Real.exp_pos _
  have hrpos : 0 < r := by dsimp [r]; exact Real.exp_pos _
  have hrleq : r ≤ q := by
    dsimp [r, q]
    apply Real.exp_le_exp.mpr
    have hcoef : 0 < Real.pi ^ 2 / 8 := by positivity
    have hMR : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hq' : q ≤ 1 / 8 := by simpa [q] using hq
  have hrhalf : r ≤ 1 / 2 := by linarith
  have hetaM : fullGaussianBlockMassThetaError M ≤ 4 * q := by
    rw [fullGaussianBlockMassThetaError_eq_exp M hM]
    have hden : 0 < 1 - r := by linarith
    have hrr : r ^ 2 ≤ r / 2 := by
      have := mul_le_mul_of_nonneg_left hrhalf hrpos.le
      nlinarith
    calc
      2 * r / (1 - r) ≤ 4 * r := by
        rw [div_le_iff₀ hden]
        nlinarith
      _ ≤ 4 * q := mul_le_mul_of_nonneg_left hrleq (by norm_num)
  have hfour : 4 * q ≤ 1 / 2 := by nlinarith
  have heta (k : ℕ) (hk : M ≤ k) :
      fullGaussianBlockMassThetaError k ≤ 4 * q := by
    calc
      _ ≤ fullGaussianBlockMassThetaError M :=
        fullGaussianBlockMassThetaError_antitone hM hk
      _ ≤ 4 * q := hetaM
  have hshiftDiag : fullGaussianBlockPairShiftThetaError M M ≤ 4 * q := by
    rw [fullGaussianBlockPairShiftThetaError_diag_eq_exp M hM]
    have hden : 0 < 1 - q := by linarith
    have hqq : q ^ 2 ≤ q / 2 := by
      have := mul_le_mul_of_nonneg_left hq' hqpos.le
      nlinarith
    calc
      2 * q / (1 - q) ≤ 4 * q := by
        rw [div_le_iff₀ hden]
        nlinarith
      _ = 4 * q := rfl
  have hshift (k l : ℕ) (hk : M ≤ k) (hl : M ≤ l) :
      fullGaussianBlockPairShiftThetaError k l ≤ 4 * q := by
    calc
      _ ≤ fullGaussianBlockPairShiftThetaError M M :=
        fullGaussianBlockPairShiftThetaError_antitone hM hk hl
      _ ≤ 4 * q := hshiftDiag
  have hδmHalf : fullGaussianBlockMassThetaError m ≤ 1 / 2 :=
    (heta m hMm).trans hfour
  have hδnHalf : fullGaussianBlockMassThetaError n ≤ 1 / 2 :=
    (heta n hMn).trans hfour
  have hδsHalf : fullGaussianBlockMassThetaError (m + n) ≤ 1 / 2 :=
    (heta (m + n) (by omega)).trans hfour
  have hbound := fullGaussianBlockPairErrorMass_le_of_theta_small m n hm hn
    hδmHalf hδnHalf hδsHalf
  have hshiftE := hshift m n hMm hMn
  have hδm := heta m hMm
  have hδn := heta n hMn
  have hδs := heta (m + n) (by omega)
  dsimp [q] at hshiftE hδm hδn hδs
  nlinarith [hbound]

/-- The accumulated full-lattice Gaussian convolution error for a list of
block durations. -/
def fullGaussianBlockListProfileError : List ℕ → ℝ
  | [] => 0
  | [_] => 0
  | m :: n :: ms => fullGaussianBlockListProfileError (n :: ms) +
      fullGaussianBlockPairErrorMass m (n + ms.sum)

/-- For lists whose durations all exceed `M`, the accumulated profile error
is bounded by the length times an explicit exponential tail. -/
theorem fullGaussianBlockListProfileError_le_exp
    (M : ℕ) (hM : 0 < M) (ms : List ℕ)
    (hcut : ∀ m ∈ ms, M ≤ m)
    (hq : Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) ≤ 1 / 8) :
    fullGaussianBlockListProfileError ms ≤
      (ms.length : ℝ) * (64 * Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ))) := by
  have hqpos : 0 < Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) := Real.exp_pos _
  induction ms with
  | nil => simp [fullGaussianBlockListProfileError]
  | cons m ms ih =>
      have hmcut : M ≤ m := hcut m (by simp)
      have htailcut : ∀ k ∈ ms, M ≤ k := by
        intro k hk
        exact hcut k (by simp [hk])
      cases ms with
      | nil => simp [fullGaussianBlockListProfileError]; positivity
      | cons n ms =>
          have hncut : M ≤ n := hcut n (by simp)
          have hpairTail : M ≤ n + ms.sum := by omega
          have hpair := fullGaussianBlockPairErrorMass_le_exp
            M m (n + ms.sum) hM hmcut hpairTail hq
          have htail := ih (by
            intro k hk
            exact hcut k (by simp [hk]))
          have hlen : (m :: n :: ms).length = (n :: ms).length + 1 := by simp
          simp only [fullGaussianBlockListProfileError]
          rw [hlen]
          simp only [Nat.cast_add, Nat.cast_one]
          calc
            _ ≤ ((n :: ms).length : ℝ) *
                (64 * Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ))) +
                  64 * Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) :=
              add_le_add htail hpair
            _ = (((n :: ms).length : ℝ) + 1) *
                (64 * Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ))) := by ring


/-- Each pair convolution error is bounded by the pair error mass. -/
theorem fullGaussianBlockPairConvolutionError_le_errorMass
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (j : ℤ) :
    fullGaussianBlockPairConvolutionError m n j ≤ fullGaussianBlockPairErrorMass m n := by
  unfold fullGaussianBlockPairErrorMass
  have h := (summable_fullGaussianBlockPairConvolutionError m n hm hn).sum_le_tsum
    {j} (fun k hk => fullGaussianBlockPairConvolutionError_nonneg m n hm hn k)
  simpa using h

/-- A single full-lattice Gaussian block probability lies in `[0, 1]`. -/
theorem fullGaussianBlockProbability_nonneg_le_one
    (m : ℕ) (hm : 0 < m) (j : ℤ) :
    0 ≤ fullGaussianBlockProbability m j ∧
      fullGaussianBlockProbability m j ≤ 1 := by
  have hnonneg : ∀ k : ℤ, 0 ≤ fullGaussianBlockProbability m k := by
    intro k
    unfold fullGaussianBlockProbability fullGaussianBlockWeight
    exact div_nonneg (Real.exp_nonneg _) (le_of_lt (fullGaussianBlockMass_pos m hm))
  have hupper := (summable_fullGaussianBlockProbability m hm).sum_le_tsum
    {j} (fun k hk => hnonneg k)
  rw [tsum_fullGaussianBlockProbability m hm] at hupper
  constructor
  · exact hnonneg j
  · simpa using hupper

private theorem fullGaussianBlockListProbability_properties (ms : List ℕ)
    (hms : ∀ m ∈ ms, 0 < m) :
    ∀ j, 0 ≤ fullGaussianBlockListProbability ms j ∧
      fullGaussianBlockListProbability ms j ≤ 1 := by
  induction ms with
  | nil =>
      intro j
      by_cases hj : j = 0 <;> simp [fullGaussianBlockListProbability, hj]
  | cons m ms ih =>
      have hm : 0 < m := hms m (by simp)
      have htail : ∀ k ∈ ms, 0 < k := by
        intro k hk
        exact hms k (by simp [hk])
      cases ms with
      | nil =>
          intro j
          exact fullGaussianBlockProbability_nonneg_le_one m hm j
      | cons n ms =>
          have htailBound : ∀ j, 0 ≤ fullGaussianBlockListProbability (n :: ms) j ∧
              fullGaussianBlockListProbability (n :: ms) j ≤ 1 := ih htail
          have hPnonneg (k : ℤ) : 0 ≤ fullGaussianBlockProbability m k := by
            unfold fullGaussianBlockProbability fullGaussianBlockWeight
            exact div_nonneg (Real.exp_nonneg _) (le_of_lt (fullGaussianBlockMass_pos m hm))
          have hPsum := tsum_fullGaussianBlockProbability m hm
          have hmassBound (j k : ℤ) :
              fullGaussianBlockProbability m k *
                fullGaussianBlockListProbability (n :: ms) (j - k) ≤
              fullGaussianBlockProbability m k := by
            calc
              _ ≤ fullGaussianBlockProbability m k * 1 :=
                mul_le_mul_of_nonneg_left (htailBound (j - k)).2 (hPnonneg k)
              _ = fullGaussianBlockProbability m k := by ring
          have htermSummable (j : ℤ) :
              Summable (fun k : ℤ => fullGaussianBlockProbability m k *
                fullGaussianBlockListProbability (n :: ms) (j - k)) := by
            have hPsumable : Summable (fullGaussianBlockProbability m) :=
              summable_fullGaussianBlockProbability m hm
            exact Summable.of_nonneg_of_le
              (fun k => mul_nonneg (hPnonneg k) (htailBound (j - k)).1)
              (fun k => hmassBound j k) hPsumable
          have hsumBound (j : ℤ) :
              (∑' k : ℤ, fullGaussianBlockProbability m k *
                fullGaussianBlockListProbability (n :: ms) (j - k)) ≤ 1 := by
            calc
              _ ≤ ∑' k : ℤ, fullGaussianBlockProbability m k :=
                (htermSummable j).tsum_le_tsum (fun k => hmassBound j k)
                  (summable_fullGaussianBlockProbability m hm)
              _ = 1 := hPsum
          intro j
          constructor
          · exact tsum_nonneg fun k => mul_nonneg (hPnonneg k)
              (htailBound (j - k)).1
          · exact hsumBound j

/-- For a list of positive durations, the composition law lies in `[0, 1]`. -/
theorem fullGaussianBlockListProbability_nonneg_le_one (ms : List ℕ)
    (hms : ∀ m ∈ ms, 0 < m) (j : ℤ) :
    0 ≤ fullGaussianBlockListProbability ms j ∧
      fullGaussianBlockListProbability ms j ≤ 1 :=
  fullGaussianBlockListProbability_properties ms hms j

/-- For a list of positive durations, the accumulated profile error is nonnegative. -/
theorem fullGaussianBlockListProfileError_nonneg (ms : List ℕ)
    (hms : ∀ m ∈ ms, 0 < m) :
    0 ≤ fullGaussianBlockListProfileError ms := by
  induction ms with
  | nil => simp [fullGaussianBlockListProfileError]
  | cons m ms ih =>
      cases ms with
      | nil => simp [fullGaussianBlockListProfileError]
      | cons n ms =>
          have hm : 0 < m := hms m (by simp)
          have hn : 0 < n := hms n (by simp)
          have htail : ∀ k ∈ n :: ms, 0 < k := by
            intro k hk
            exact hms k (by simp [hk])
          simpa [fullGaussianBlockListProfileError] using add_nonneg
            (ih htail) (fullGaussianBlockPairErrorMass_nonneg m (n + ms.sum) hm
              (by omega))

private theorem summable_fullGaussianBlockListPairTerm
    (m : ℕ) (hm : 0 < m) (ms : List ℕ)
    (hms : ∀ k ∈ ms, 0 < k) (j : ℤ) :
    Summable (fun k : ℤ => fullGaussianBlockProbability m k *
      fullGaussianBlockListProbability ms (j - k)) := by
  have htail := fullGaussianBlockListProbability_nonneg_le_one ms hms
  have hPnonneg (k : ℤ) : 0 ≤ fullGaussianBlockProbability m k :=
    (fullGaussianBlockProbability_nonneg_le_one m hm k).1
  have hPsum : Summable (fullGaussianBlockProbability m) :=
    summable_fullGaussianBlockProbability m hm
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (hPnonneg k) (htail (j - k)).1)
    (fun k => by
      calc
        _ ≤ fullGaussianBlockProbability m k * 1 :=
          mul_le_mul_of_nonneg_left (htail (j - k)).2 (hPnonneg k)
        _ = fullGaussianBlockProbability m k := by ring)
    hPsum

/-- The normalized full-lattice Gaussian law of a composition is uniformly
close to the full-lattice Gaussian at its total duration. The error is the sum
of the pair-convolution errors from successively combining its blocks. -/
theorem fullGaussianBlockListProbability_profileError_bound (ms : List ℕ)
    (hne : ms ≠ []) (hms : ∀ m ∈ ms, 0 < m) :
    ∀ j : ℤ, |fullGaussianBlockListProbability ms j -
      fullGaussianBlockProbability ms.sum j| ≤ fullGaussianBlockListProfileError ms := by
  intro j
  induction ms generalizing j with
  | nil => exact (hne rfl).elim
  | cons m ms ih =>
      have hm : 0 < m := hms m (by simp)
      have htail : ∀ k ∈ ms, 0 < k := by
        intro k hk
        exact hms k (by simp [hk])
      cases ms with
      | nil =>
          simp [fullGaussianBlockListProbability, fullGaussianBlockListProfileError]
      | cons n ms =>
          have htailne : n :: ms ≠ [] := by simp
          have htailProfile : ∀ q : ℤ,
              |fullGaussianBlockListProbability (n :: ms) q -
                fullGaussianBlockProbability (n + ms.sum) q| ≤
                  fullGaussianBlockListProfileError (n :: ms) := by
            intro q
            have htailSum : (n :: ms).sum = n + ms.sum := by simp
            simpa [htailSum] using ih htailne htail q
          have htailPositive : 0 < n + ms.sum := by
            have hn : 0 < n := hms n (by simp)
            omega
          have htailP (q : ℤ) :=
            fullGaussianBlockProbability_nonneg_le_one (n + ms.sum) htailPositive q
          have hPnonneg (k : ℤ) : 0 ≤ fullGaussianBlockProbability m k :=
            (fullGaussianBlockProbability_nonneg_le_one m hm k).1
          have hPsum : ∑' k : ℤ, fullGaussianBlockProbability m k = 1 :=
            tsum_fullGaussianBlockProbability m hm
          let f : ℤ → ℝ := fun k =>
            fullGaussianBlockProbability m k *
              fullGaussianBlockListProbability (n :: ms) (j - k)
          let g : ℤ → ℝ := fun k =>
            fullGaussianBlockProbability m k *
              fullGaussianBlockProbability (n + ms.sum) (j - k)
          have hf : Summable f := by
            simpa [f] using summable_fullGaussianBlockListPairTerm m hm (n :: ms)
              (by intro k hk; exact hms k (by simp [hk])) j
          have hg : Summable g := by
            have htemp := summable_fullGaussianBlockListPairTerm m hm [n + ms.sum]
              (by simp [htailPositive]) j
            simpa only [fullGaussianBlockListProbability, g] using htemp
          have hdiff : Summable (fun k : ℤ => f k - g k) := hf.sub hg
          have hdiffNorm : Summable (fun k : ℤ => ‖f k - g k‖) := hdiff.norm
          have hpoint (k : ℤ) : ‖f k - g k‖ ≤
              fullGaussianBlockProbability m k *
                fullGaussianBlockListProfileError (n :: ms) := by
            have hmul : f k - g k = fullGaussianBlockProbability m k *
                (fullGaussianBlockListProbability (n :: ms) (j - k) -
                  fullGaussianBlockProbability (n + ms.sum) (j - k)) := by
              simp [f, g]
              ring
            rw [hmul, Real.norm_eq_abs, abs_mul,
              abs_of_nonneg (hPnonneg k)]
            exact mul_le_mul_of_nonneg_left
              (htailProfile (j - k)) (hPnonneg k)
          have hsumDiff :
              ‖(∑' k : ℤ, f k) - (∑' k : ℤ, g k)‖ ≤
                fullGaussianBlockListProfileError (n :: ms) := by
            rw [← hf.tsum_sub hg]
            calc
              ‖∑' k : ℤ, (f k - g k)‖ ≤ ∑' k : ℤ, ‖f k - g k‖ :=
                norm_tsum_le_tsum_norm hdiffNorm
              _ ≤ ∑' k : ℤ,
                  fullGaussianBlockProbability m k *
                    fullGaussianBlockListProfileError (n :: ms) :=
                hdiffNorm.tsum_le_tsum hpoint
                  (summable_fullGaussianBlockProbability m hm |>.mul_right
                    (fullGaussianBlockListProfileError (n :: ms)))
              _ = fullGaussianBlockListProfileError (n :: ms) := by
                rw [tsum_mul_right, hPsum]
                ring
          have hpair := abs_tsum_fullGaussianBlockProbability_pair_sub_le
            m (n + ms.sum) hm htailPositive j
          have hpairError := fullGaussianBlockPairConvolutionError_le_errorMass
            m (n + ms.sum) hm htailPositive j
          have hpairBound :
              |(∑' k : ℤ,
                  fullGaussianBlockProbability m k *
                    fullGaussianBlockProbability (n + ms.sum) (j - k)) -
                fullGaussianBlockProbability (m + (n + ms.sum)) j| ≤
                fullGaussianBlockPairErrorMass m (n + ms.sum) := by
            exact hpair.trans hpairError
          have htriangle :
              |(∑' k : ℤ, f k) - fullGaussianBlockProbability (m + (n + ms.sum)) j| ≤
                fullGaussianBlockListProfileError (n :: ms) +
                  fullGaussianBlockPairErrorMass m (n + ms.sum) := by
            calc
              _ = |((∑' k : ℤ, f k) - (∑' k : ℤ, g k)) +
                  ((∑' k : ℤ, g k) -
                    fullGaussianBlockProbability (m + (n + ms.sum)) j)| := by
                    congr 1
                    ring
              _ ≤ |(∑' k : ℤ, f k) - (∑' k : ℤ, g k)| +
                    |(∑' k : ℤ, g k) -
                      fullGaussianBlockProbability (m + (n + ms.sum)) j| :=
                  abs_add_le _ _
              _ ≤ fullGaussianBlockListProfileError (n :: ms) +
                    fullGaussianBlockPairErrorMass m (n + ms.sum) := by
                  have hfirst : |(∑' k : ℤ, f k) - (∑' k : ℤ, g k)| ≤
                      fullGaussianBlockListProfileError (n :: ms) := by
                    simpa [Real.norm_eq_abs] using hsumDiff
                  exact add_le_add hfirst hpairBound
          have hlistSum : (m :: n :: ms).sum = m + (n + ms.sum) := by simp
          simpa [fullGaussianBlockListProbability, fullGaussianBlockListProfileError,
            f, hlistSum] using htriangle

/-- The two independent rotated coordinates of a full-Gaussian composition
have pair-profile error at most twice the one-coordinate error. -/
theorem fullGaussianBlockListPairProbability_profileError_bound
    (ms : List ℕ) (hne : ms ≠ []) (hms : ∀ m ∈ ms, 0 < m)
    (j₁ j₂ : ℤ) :
    |fullGaussianBlockListProbability ms j₁ * fullGaussianBlockListProbability ms j₂ -
        fullGaussianBlockProbability ms.sum j₁ * fullGaussianBlockProbability ms.sum j₂| ≤
      2 * fullGaussianBlockListProfileError ms := by
  let E := fullGaussianBlockListProfileError ms
  let a := fullGaussianBlockListProbability ms j₁
  let b := fullGaussianBlockListProbability ms j₂
  let c := fullGaussianBlockProbability ms.sum j₁
  let d := fullGaussianBlockProbability ms.sum j₂
  have hab := fullGaussianBlockListProbability_profileError_bound ms hne hms j₁
  have hbb := fullGaussianBlockListProbability_profileError_bound ms hne hms j₂
  have ha : 0 ≤ a ∧ a ≤ 1 := by
    simpa [a] using fullGaussianBlockListProbability_nonneg_le_one ms hms j₁
  have hb : 0 ≤ b ∧ b ≤ 1 := by
    simpa [b] using fullGaussianBlockListProbability_nonneg_le_one ms hms j₂
  have hsumPos : 0 < ms.sum := by
    cases ms with
    | nil => exact (hne rfl).elim
    | cons m ms =>
        have hm := hms m (by simp)
        simp
        omega
  have hc : 0 ≤ c ∧ c ≤ 1 := by
    simpa [c] using fullGaussianBlockProbability_nonneg_le_one ms.sum hsumPos j₁
  have hd : 0 ≤ d ∧ d ≤ 1 := by
    simpa [d] using fullGaussianBlockProbability_nonneg_le_one ms.sum hsumPos j₂
  have hE1 : |a - c| ≤ E := by simpa [a, c, E] using hab
  have hE2 : |b - d| ≤ E := by simpa [b, d, E] using hbb
  have hE0 : 0 ≤ E := by
    exact fullGaussianBlockListProfileError_nonneg ms hms
  have hdecomp : a * b - c * d = (a - c) * b + c * (b - d) := by ring
  rw [hdecomp]
  calc
    |(a - c) * b + c * (b - d)| ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * |b| + |c| * |b - d| := by rw [abs_mul, abs_mul]
    _ ≤ E + E := by
      apply add_le_add
      · have hAbsB : |b| ≤ 1 := by rw [abs_of_nonneg hb.1]; exact hb.2
        calc
          |a - c| * |b| ≤ E * 1 :=
            mul_le_mul hE1 hAbsB (abs_nonneg _) hE0
          _ = E := by ring
      · have hAbsC : |c| ≤ 1 := by rw [abs_of_nonneg hc.1]; exact hc.2
        calc
          |c| * |b - d| ≤ 1 * E :=
            mul_le_mul hAbsC hE2 (abs_nonneg _) (by norm_num)
          _ = E := by ring
    _ = 2 * E := by ring

/-- A composition of full-lattice Gaussian blocks has the heat-kernel profile
up to its accumulated convolution error and the one-block Poisson error. -/
theorem fullGaussianBlockListPair_heatKernel_error
    (N : ℕ) (hN : 0 < N) (ms : List ℕ) (hne : ms ≠ [])
    (hms : ∀ m ∈ ms, 0 < m) (z : Site) (j₁ j₂ : ℤ)
    (h₁ : 2 * j₁ = (ms.sum : ℤ) + z 0 + z 1)
    (h₂ : 2 * j₂ = (ms.sum : ℤ) + z 0 - z 1) :
    |(N / 4 : ℝ) * fullGaussianBlockListProbability ms j₁ *
        fullGaussianBlockListProbability ms j₂ -
      heatKernel (ms.sum / (2 * N))
        ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)| ≤
      (N / 2 : ℝ) * fullGaussianBlockListProfileError ms +
        (N / 4 : ℝ) *
          (2 * fullGaussianBlockMassThetaError ms.sum +
            fullGaussianBlockMassThetaError ms.sum ^ 2) := by
  have hsumPos : 0 < ms.sum := by
    cases ms with
    | nil => exact (hne rfl).elim
    | cons m ms =>
        have hm := hms m (by simp)
        simp
        omega
  let E := fullGaussianBlockListProfileError ms
  let θ := fullGaussianBlockMassThetaError ms.sum
  let P₁ := fullGaussianBlockListProbability ms j₁
  let P₂ := fullGaussianBlockListProbability ms j₂
  let Q₁ := fullGaussianBlockProbability ms.sum j₁
  let Q₂ := fullGaussianBlockProbability ms.sum j₂
  let G₁ := fullGaussianBlockWeight ms.sum j₁ /
    fullGaussianBlockIntegralMass ms.sum
  let G₂ := fullGaussianBlockWeight ms.sum j₂ /
    fullGaussianBlockIntegralMass ms.sum
  have hθ : 0 ≤ θ := by
    dsimp [θ]
    exact fullGaussianBlockMassThetaError_nonneg ms.sum hsumPos
  have hE : 0 ≤ E := by
    exact fullGaussianBlockListProfileError_nonneg ms hms
  have hpair := fullGaussianBlockListPairProbability_profileError_bound
    ms hne hms j₁ j₂
  have hpair' : |P₁ * P₂ - Q₁ * Q₂| ≤ 2 * E := by
    simpa [P₁, P₂, Q₁, Q₂, E] using hpair
  have hQ₁ := fullGaussianBlockProbability_nonneg_le_one ms.sum hsumPos j₁
  have hQ₂ := fullGaussianBlockProbability_nonneg_le_one ms.sum hsumPos j₂
  have hG₁ : 0 ≤ G₁ := by
    dsimp [G₁, fullGaussianBlockWeight, fullGaussianBlockIntegralMass]
    positivity
  have hG₂ : 0 ≤ G₂ := by
    dsimp [G₂, fullGaussianBlockWeight, fullGaussianBlockIntegralMass]
    positivity
  have hmass₁ := abs_fullGaussianBlockProbability_sub_continuousDensity_le
    ms.sum hsumPos j₁
  have hmass₂ := abs_fullGaussianBlockProbability_sub_continuousDensity_le
    ms.sum hsumPos j₂
  have hmass₁' : |Q₁ - G₁| ≤ θ := by
    have h := hmass₁
    dsimp [Q₁, G₁, θ] at h ⊢
    have hQ := (fullGaussianBlockProbability_nonneg_le_one ms.sum hsumPos j₁).2
    exact le_trans h (by nlinarith [mul_le_mul_of_nonneg_right hQ hθ])
  have hmass₂' : |Q₂ - G₂| ≤ θ := by
    have h := hmass₂
    dsimp [Q₂, G₂, θ] at h ⊢
    have hQ := (fullGaussianBlockProbability_nonneg_le_one ms.sum hsumPos j₂).2
    exact le_trans h (by nlinarith [mul_le_mul_of_nonneg_right hQ hθ])
  have hG₁bound : |G₁| ≤ 1 + θ := by
    rw [abs_of_nonneg hG₁]
    have hlow := (abs_le.mp hmass₁').1
    linarith
  have hcont : |Q₁ * Q₂ - G₁ * G₂| ≤ 2 * θ + θ ^ 2 := by
    have hdecomp : Q₁ * Q₂ - G₁ * G₂ =
        (Q₁ - G₁) * Q₂ + G₁ * (Q₂ - G₂) := by ring
    rw [hdecomp]
    calc
      |(Q₁ - G₁) * Q₂ + G₁ * (Q₂ - G₂)| ≤
          |(Q₁ - G₁) * Q₂| + |G₁ * (Q₂ - G₂)| := abs_add_le _ _
      _ = |Q₁ - G₁| * |Q₂| + |G₁| * |Q₂ - G₂| := by
        rw [abs_mul, abs_mul]
      _ ≤ θ * 1 + (1 + θ) * θ := by
        apply add_le_add
        · exact mul_le_mul hmass₁' (by
            rw [abs_of_nonneg hQ₂.1]
            exact hQ₂.2) (abs_nonneg _) hθ
        · exact mul_le_mul hG₁bound hmass₂' (abs_nonneg _) (by positivity)
      _ = 2 * θ + θ ^ 2 := by ring
  have htriangle : |P₁ * P₂ - G₁ * G₂| ≤
      2 * E + (2 * θ + θ ^ 2) := by
    calc
      _ = |(P₁ * P₂ - Q₁ * Q₂) + (Q₁ * Q₂ - G₁ * G₂)| := by
        congr 1
        ring
      _ ≤ |P₁ * P₂ - Q₁ * Q₂| + |Q₁ * Q₂ - G₁ * G₂| := abs_add_le _ _
      _ ≤ _ := add_le_add hpair' hcont
  have hheat := fullGaussianBlockPairContinuousDensity_eq_heatKernel
    N ms.sum hN hsumPos z j₁ j₂ h₁ h₂
  have hheat' : (N / 4 : ℝ) * (G₁ * G₂) =
      heatKernel (ms.sum / (2 * N))
        ((Real.sqrt (N / 2))⁻¹ • siteToPlane z) := by
    calc
      _ = (N / 4 : ℝ) * G₁ * G₂ := by ring
      _ = _ := by simpa [G₁, G₂] using hheat
  have hfactor : 0 ≤ (N / 4 : ℝ) := by positivity
  have hscaled : |(N / 4 : ℝ) * P₁ * P₂ - (N / 4 : ℝ) * (G₁ * G₂)| =
      (N / 4 : ℝ) * |P₁ * P₂ - G₁ * G₂| := by
    rw [show (N / 4 : ℝ) * P₁ * P₂ - (N / 4 : ℝ) * (G₁ * G₂) =
      (N / 4 : ℝ) * (P₁ * P₂ - G₁ * G₂) by ring, abs_mul,
      abs_of_nonneg hfactor]
  calc
    _ = |(N / 4 : ℝ) * P₁ * P₂ - (N / 4 : ℝ) * (G₁ * G₂)| := by
      rw [← hheat']
    _ = (N / 4 : ℝ) * |P₁ * P₂ - G₁ * G₂| := hscaled
    _ ≤ (N / 4 : ℝ) * (2 * E + (2 * θ + θ ^ 2)) :=
      mul_le_mul_of_nonneg_left htriangle hfactor
    _ = (N / 2 : ℝ) * E + (N / 4 : ℝ) * (2 * θ + θ ^ 2) := by ring

/-- For compositions with only long Gaussian blocks, the accumulated profile
error has an explicit exponential cutoff bound. -/
theorem fullGaussianBlockListPair_heatKernel_error_of_cutoff
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M)
    (hq : Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) ≤ 1 / 8)
    (ms : List ℕ) (hne : ms ≠ []) (hms : ∀ m ∈ ms, 0 < m)
    (hcut : ∀ m ∈ ms, M ≤ m) (z : Site) (j₁ j₂ : ℤ)
    (h₁ : 2 * j₁ = (ms.sum : ℤ) + z 0 + z 1)
    (h₂ : 2 * j₂ = (ms.sum : ℤ) + z 0 - z 1) :
    |(N / 4 : ℝ) * fullGaussianBlockListProbability ms j₁ *
        fullGaussianBlockListProbability ms j₂ -
      heatKernel (ms.sum / (2 * N))
        ((Real.sqrt (N / 2))⁻¹ • siteToPlane z)| ≤
      (N / 2 : ℝ) * (ms.length : ℝ) *
          (64 * Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ))) +
        (N / 4 : ℝ) *
          (2 * fullGaussianBlockMassThetaError ms.sum +
            fullGaussianBlockMassThetaError ms.sum ^ 2) := by
  have hsumPos : 0 < ms.sum := by
    cases ms with
    | nil => exact (hne rfl).elim
    | cons m ms =>
        have hm := hms m (by simp)
        simp
        omega
  have hprofile := fullGaussianBlockListProfileError_le_exp M hM ms hcut hq
  have hbase := fullGaussianBlockListPair_heatKernel_error
    N hN ms hne hms z j₁ j₂ h₁ h₂
  calc
    _ ≤ (N / 2 : ℝ) * fullGaussianBlockListProfileError ms +
        (N / 4 : ℝ) *
          (2 * fullGaussianBlockMassThetaError ms.sum +
            fullGaussianBlockMassThetaError ms.sum ^ 2) := hbase
    _ ≤ (N / 2 : ℝ) * ((ms.length : ℝ) *
          (64 * Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)))) +
        (N / 4 : ℝ) *
          (2 * fullGaussianBlockMassThetaError ms.sum +
            fullGaussianBlockMassThetaError ms.sum ^ 2) := by
      gcongr
    _ = _ := by ring

/-- The mass Poisson error at any duration above the cutoff is bounded by its
explicit Gaussian exponential tail. -/
theorem fullGaussianBlockMassThetaError_le_exp_of_cutoff
    (M n : ℕ) (hM : 0 < M) (hMn : M ≤ n)
    (hq : Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) ≤ 1 / 8) :
    fullGaussianBlockMassThetaError n ≤
      (16 / 7 : ℝ) * Real.exp (-(Real.pi ^ 2 / 4) * (n : ℝ)) := by
  have hn : 0 < n := lt_of_lt_of_le hM hMn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  let q : ℝ := Real.exp (-(Real.pi ^ 2 / 4) * (n : ℝ))
  have harg : -Real.pi / ((4 / (n : ℝ)) / Real.pi) =
      -(Real.pi ^ 2 / 4) * (n : ℝ) := by
    field_simp [hnR.ne', Real.pi_ne_zero]
  have hqsmall : q ≤ 1 / 8 := by
    have hnM : (M : ℝ) ≤ (n : ℝ) := by exact_mod_cast hMn
    have hargle : -(Real.pi ^ 2 / 4) * (n : ℝ) ≤
        -(Real.pi ^ 2 / 8) * (M : ℝ) := by
      have hcoef : 0 ≤ Real.pi ^ 2 / 8 := by positivity
      have hdiff : 0 ≤ (n : ℝ) - (M : ℝ) := sub_nonneg.mpr hnM
      nlinarith [mul_nonneg hcoef hdiff]
    have hq' : q ≤ Real.exp (-(Real.pi ^ 2 / 8) * (M : ℝ)) := by
      dsimp [q]
      exact Real.exp_le_exp.mpr hargle
    exact hq'.trans hq
  have hqpos : 0 < q := by dsimp [q]; exact Real.exp_pos _
  have hden : 0 < 1 - q := by linarith
  have hform : fullGaussianBlockMassThetaError n = 2 * q / (1 - q) := by
    unfold fullGaussianBlockMassThetaError
    rw [harg]
  rw [hform]
  have hbound : 2 * q / (1 - q) ≤ (16 / 7 : ℝ) * q := by
    rw [div_le_iff₀ hden]
    nlinarith
  simpa [q] using hbound

end Critical2DKPZ.SHF.Moments

end
