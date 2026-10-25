/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockIncrementProfile
import Mathlib.Tactic

/-! # Composition stability of the pair-block increment profile -/

@[expose] public section

noncomputable section

open Filter

namespace Critical2DKPZ.SHF.Moments

private theorem finiteProduct_abs_sub_le {α β : Type*} (A : Finset α) (B : Finset β)
    (p p' : α → ℝ) (q q' : β → ℝ)
    (hp' : ∀ a ∈ A, 0 ≤ p' a) (hq : ∀ b ∈ B, 0 ≤ q b)
    (hsq : ∑ b ∈ B, q b = 1) (hsp' : ∑ a ∈ A, p' a = 1) :
    (∑ a ∈ A, ∑ b ∈ B, |p a * q b - p' a * q' b|) ≤
      (∑ a ∈ A, |p a - p' a|) + (∑ b ∈ B, |q b - q' b|) := by
  calc
    _ ≤ ∑ a ∈ A, ∑ b ∈ B,
        (|p a - p' a| * q b + p' a * |q b - q' b|) := by
      apply Finset.sum_le_sum
      intro a ha
      apply Finset.sum_le_sum
      intro b hb
      calc
        |p a * q b - p' a * q' b| =
            |(p a - p' a) * q b + p' a * (q b - q' b)| := by congr 1; ring
        _ ≤ |(p a - p' a) * q b| + |p' a * (q b - q' b)| := abs_add_le _ _
        _ = |p a - p' a| * q b + p' a * |q b - q' b| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (hq b hb), abs_of_nonneg (hp' a ha)]
    _ = (∑ a ∈ A, |p a - p' a| * ∑ b ∈ B, q b) +
        (∑ a ∈ A, p' a * ∑ b ∈ B, |q b - q' b|) := by
      simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by rw [hsq, ← Finset.sum_mul, ← Finset.sum_mul, hsp']; simp

/-- A finite convolution on nonnegative integer marks, with the support bounds
kept explicit in its two duration parameters. -/
def finiteNaturalConvolution (m n : ℕ) (p q : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ ij ∈ (Finset.range (m + 1)).product (Finset.range (n + 1))
    with ij.1 + ij.2 = j, p ij.1 * q ij.2

private theorem finiteNaturalConvolution_eq_sum_right {m n : ℕ}
    (p q : ℕ → ℝ) (k : ℕ) :
    finiteNaturalConvolution m n p q k =
      ∑ j ∈ (Finset.range (n + 1)).filter (fun j => j ≤ k ∧ k - j ≤ m),
        p (k - j) * q j := by
  classical
  let A := Finset.range (m + 1)
  let B := Finset.range (n + 1)
  let F := (A.product B).filter (fun ij => ij.1 + ij.2 = k)
  let T := B.filter (fun j => j ≤ k ∧ k - j ≤ m)
  unfold finiteNaturalConvolution
  change (∑ ij ∈ F, p ij.1 * q ij.2) =
    ∑ j ∈ T, p (k - j) * q j
  refine Finset.sum_bij (s := F) (t := T) (fun ij _ => ij.2) ?_ ?_ ?_ ?_
  · intro ij hij
    have hmem := (Finset.mem_filter.mp hij).1
    have hsum := (Finset.mem_filter.mp hij).2
    have hpair := Finset.mem_product.mp hmem
    have hfst : ij.1 = k - ij.2 := by omega
    simp only [T, Finset.mem_filter]
    refine ⟨hpair.2, ?_⟩
    constructor
    · omega
    · have hi : ij.1 ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hpair.1)
      simpa [hfst] using hi
  · intro ij hij ij' hij' hmap
    have hsum := (Finset.mem_filter.mp hij).2
    have hsum' := (Finset.mem_filter.mp hij').2
    have hfst : ij.1 = ij'.1 := by omega
    exact Prod.ext hfst hmap
  · intro j hj
    have hj' : j ≤ n := by
      have := (Finset.mem_filter.mp hj).1
      simp only [B, Finset.mem_range] at this
      omega
    have hprops := (Finset.mem_filter.mp hj).2
    refine ⟨(k - j, j), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hprops.2),
          Finset.mem_range.mpr (Nat.lt_succ_of_le hj')⟩
      · exact Nat.sub_add_cancel hprops.1
    · rfl
  · intro ij hij
    have hsum := (Finset.mem_filter.mp hij).2
    have hfst : ij.1 = k - ij.2 := by omega
    rw [hfst]

/-- A pointwise bound on the first factor smooths the discrete convolution by
the `L¹` mass of the second factor. -/
theorem finiteNaturalConvolution_abs_le_leftPointwise {m n : ℕ}
    (p q : ℕ → ℝ) (B L : ℝ) (k : ℕ)
    (hB : 0 ≤ B)
    (hp : ∀ i ∈ Finset.range (m + 1), |p i| ≤ B)
    (hq : ∑ j ∈ Finset.range (n + 1), |q j| ≤ L) :
    |finiteNaturalConvolution m n p q k| ≤ B * L := by
  classical
  let T := (Finset.range (n + 1)).filter (fun j => j ≤ k ∧ k - j ≤ m)
  rw [finiteNaturalConvolution_eq_sum_right p q k]
  calc
    |∑ j ∈ T, p (k - j) * q j| ≤
        ∑ j ∈ T, |p (k - j) * q j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ T, |p (k - j)| * |q j| := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_mul]
    _ ≤ ∑ j ∈ T, B * |q j| := by
      apply Finset.sum_le_sum
      intro j hj
      have hjA : k - j ∈ Finset.range (m + 1) := by
        simp only [Finset.mem_range]
        exact Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2.2
      exact mul_le_mul_of_nonneg_right (hp _ hjA) (abs_nonneg _)
    _ = B * (∑ j ∈ T, |q j|) := by rw [Finset.mul_sum]
    _ ≤ B * (∑ j ∈ Finset.range (n + 1), |q j|) := by
      apply mul_le_mul_of_nonneg_left _ hB
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j hj _ => abs_nonneg _)
    _ ≤ B * L := mul_le_mul_of_nonneg_left hq hB

/-- A sufficiently long normalized sampled-Gaussian block has atoms bounded
at the one-dimensional local-CLT scale. -/
theorem exists_normalizedSampledHypergeometricGaussian_pointwise_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      ∀ k ∈ Finset.range (m + 1),
        |normalizedSampledHypergeometricGaussianWeight m k| ≤ C / Real.sqrt (m : ℝ) := by
  obtain ⟨Cp, hCp, mp, hpoint⟩ :=
    exists_hypergeometricWeight_normalizedGaussian_point_error
  have hlocal := eventually_hypergeometricWeight_localGaussian (ε := 1) (by norm_num)
  obtain ⟨mG, hmG⟩ := Filter.eventually_atTop.1 hlocal
  let m₀ := max mp mG
  let C : ℝ := 3 + Cp
  have hmp : mp ≤ m₀ := by simp [m₀]
  have hmGle : mG ≤ m₀ := by simp [m₀]
  refine ⟨C, ?_, m₀, ?_⟩
  · dsimp [C]
    positivity
  · intro m hm k hk
    have hdata := hpoint m (le_trans hmp hm)
    have hm1 : 1 ≤ m := hdata.1
    have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
    have hmsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
    let p : ℕ → ℝ := WalkTails.hypergeometricWeight m
    let q : ℕ → ℝ := normalizedSampledHypergeometricGaussianWeight m
    have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    have hlocalM :
        |Real.sqrt (m : ℝ) * p k -
          2 / Real.sqrt Real.pi *
            Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ))| < 1 := by
      simpa [p] using hmG m (le_trans hmGle hm) k hk'
    have hGupper :
        2 / Real.sqrt Real.pi *
          Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ)) ≤ 2 := by
      have hpiRoot : 1 ≤ Real.sqrt Real.pi := by
        calc
          1 = Real.sqrt 1 := by norm_num
          _ ≤ Real.sqrt Real.pi := Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
      have hcoef : 2 / Real.sqrt Real.pi ≤ 2 := by
        rw [div_le_iff₀ (Real.sqrt_pos.mpr Real.pi_pos)]
        nlinarith
      have harg : -(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ) ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · nlinarith [sq_nonneg (2 * (k : ℝ) - (m : ℝ))]
        · positivity
      calc
        _ ≤ 2 * Real.exp (-(2 * (k : ℝ) - (m : ℝ)) ^ 2 / (m : ℝ)) :=
          mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left
          (Real.exp_le_one_iff.mpr harg) (by norm_num)
        _ = 2 := by norm_num
    have hpUpper : p k ≤ 3 / Real.sqrt (m : ℝ) := by
      have hscaledUpper : Real.sqrt (m : ℝ) * p k ≤ 3 := by
        have hscaled := (abs_lt.mp hlocalM).2
        dsimp [p] at *
        linarith
      rw [le_div_iff₀ hmsqrt]
      simpa [mul_comm] using hscaledUpper
    have hpointK : |p k - q k| ≤ Cp / (m : ℝ) := by
      simpa [p, q] using hdata.2 k hk'
    have hqnonneg : 0 ≤ q k := by
      dsimp [q, normalizedSampledHypergeometricGaussianWeight,
        sampledHypergeometricGaussianWeight]
      positivity
    have hqle : q k ≤ p k + Cp / (m : ℝ) := by
      have hrev : q k - p k ≤ |p k - q k| := by
        rw [abs_sub_comm]
        exact le_abs_self _
      linarith
    have hrootOne : 1 ≤ Real.sqrt (m : ℝ) := by
      calc
        1 = Real.sqrt 1 := by norm_num
        _ ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hm1)
    have hrootle : Real.sqrt (m : ℝ) ≤ (m : ℝ) := by
      calc
        Real.sqrt (m : ℝ) = 1 * Real.sqrt (m : ℝ) := by ring
        _ ≤ Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) :=
          mul_le_mul_of_nonneg_right hrootOne (Real.sqrt_nonneg _)
        _ = (m : ℝ) := by nlinarith [Real.sq_sqrt hmR.le]
    have hCpdiv : Cp / (m : ℝ) ≤ Cp / Real.sqrt (m : ℝ) :=
      div_le_div_of_nonneg_left hCp.le hmsqrt hrootle
    rw [abs_of_nonneg hqnonneg]
    calc
      q k ≤ p k + Cp / (m : ℝ) := hqle
      _ ≤ 3 / Real.sqrt (m : ℝ) + Cp / Real.sqrt (m : ℝ) :=
        add_le_add hpUpper hCpdiv
      _ = C / Real.sqrt (m : ℝ) := by dsimp [C]; ring



private theorem finiteNaturalConvolution_sum_map {m n : ℕ} (p q : ℕ → ℝ) :
    (∑ j ∈ Finset.range (m + n + 1), finiteNaturalConvolution m n p q j) =
      (∑ i ∈ Finset.range (m + 1), p i) *
        (∑ j ∈ Finset.range (n + 1), q j) := by
  let A := Finset.range (m + 1)
  let B := Finset.range (n + 1)
  let AB := A.product B
  have hmap : ∀ ij ∈ AB, ij.1 + ij.2 ∈ Finset.range (m + n + 1) := by
    intro ij hij
    have hij' : ij.1 ≤ m ∧ ij.2 ≤ n := by simpa [AB, A, B] using hij
    have hi : ij.1 < m + 1 := by omega
    have hj : ij.2 < n + 1 := by omega
    simp only [Finset.mem_range]
    omega
  calc
    _ = ∑ j ∈ Finset.range (m + n + 1),
        ∑ ij ∈ AB with ij.1 + ij.2 = j, p ij.1 * q ij.2 := by
      apply Finset.sum_congr rfl
      intro j hj
      simp [finiteNaturalConvolution, AB, A, B]
    _ = ∑ ij ∈ AB, p ij.1 * q ij.2 :=
      Finset.sum_fiberwise_of_maps_to hmap _
    _ = _ := by
      dsimp [AB, A, B]
      rw [Finset.sum_product]
      calc
        (∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (n + 1), p i * q j) =
            ∑ i ∈ Finset.range (m + 1), p i *
              (∑ j ∈ Finset.range (n + 1), q j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
        _ = _ := by rw [Finset.sum_mul]

/-- Convolution preserves unit mass for probability weights supported on the
two duration intervals. -/
theorem finiteNaturalConvolution_sum_one {m n : ℕ} (p q : ℕ → ℝ)
    (hp : ∑ i ∈ Finset.range (m + 1), p i = 1)
    (hq : ∑ j ∈ Finset.range (n + 1), q j = 1) :
    ∑ j ∈ Finset.range (m + n + 1), finiteNaturalConvolution m n p q j = 1 := by
  rw [finiteNaturalConvolution_sum_map, hp, hq]
  norm_num

private theorem finiteNaturalConvolution_nonneg {m n : ℕ} (p q : ℕ → ℝ)
    (hp : ∀ i ∈ Finset.range (m + 1), 0 ≤ p i)
    (hq : ∀ j ∈ Finset.range (n + 1), 0 ≤ q j) (k : ℕ) :
    0 ≤ finiteNaturalConvolution m n p q k := by
  unfold finiteNaturalConvolution
  apply Finset.sum_nonneg
  intro ij hij
  have hij' : ij.1 ∈ Finset.range (m + 1) ∧ ij.2 ∈ Finset.range (n + 1) := by
    have hprod := (Finset.mem_filter.mp hij).1
    exact Finset.mem_product.mp hprod
  exact mul_nonneg (hp ij.1 hij'.1) (hq ij.2 hij'.2)

/-- Convolution contracts the discrete `L¹` distance between probability
weights. -/
theorem finiteNaturalConvolution_L1_le {m n : ℕ}
    (p p' q q' : ℕ → ℝ)
    (hp' : ∀ i ∈ Finset.range (m + 1), 0 ≤ p' i)
    (hq : ∀ j ∈ Finset.range (n + 1), 0 ≤ q j)
    (hqsum : ∑ j ∈ Finset.range (n + 1), q j = 1)
    (hp'sum : ∑ i ∈ Finset.range (m + 1), p' i = 1) :
    (∑ k ∈ Finset.range (m + n + 1),
      |finiteNaturalConvolution m n p q k - finiteNaturalConvolution m n p' q' k|) ≤
      (∑ i ∈ Finset.range (m + 1), |p i - p' i|) +
        (∑ j ∈ Finset.range (n + 1), |q j - q' j|) := by
  let A := Finset.range (m + 1)
  let B := Finset.range (n + 1)
  let AB := A.product B
  let f : ℕ × ℕ → ℕ := fun ij => ij.1 + ij.2
  have hmap : ∀ ij ∈ AB, f ij ∈ Finset.range (m + n + 1) := by
    intro ij hij
    have hij' : ij.1 ≤ m ∧ ij.2 ≤ n := by simpa [AB, A, B] using hij
    have hi : ij.1 < m + 1 := by omega
    have hj : ij.2 < n + 1 := by omega
    simp only [f, Finset.mem_range]
    omega
  have hprod := finiteProduct_abs_sub_le A B p p' q q' hp' hq hqsum hp'sum
  have hfiber (k : ℕ) :
      finiteNaturalConvolution m n p q k - finiteNaturalConvolution m n p' q' k =
        ∑ ij ∈ AB with f ij = k, (p ij.1 * q ij.2 - p' ij.1 * q' ij.2) := by
    dsimp [finiteNaturalConvolution, AB, A, B, f]
    rw [← Finset.sum_sub_distrib]
  have hcontract :
      (∑ k ∈ Finset.range (m + n + 1),
        |finiteNaturalConvolution m n p q k -
          finiteNaturalConvolution m n p' q' k|) ≤
        ∑ ij ∈ AB, |p ij.1 * q ij.2 - p' ij.1 * q' ij.2| := by
    calc
      _ = ∑ k ∈ Finset.range (m + n + 1),
          |∑ ij ∈ AB with f ij = k, (p ij.1 * q ij.2 - p' ij.1 * q' ij.2)| := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hfiber]
      _ ≤ ∑ k ∈ Finset.range (m + n + 1),
          ∑ ij ∈ AB with f ij = k, |p ij.1 * q ij.2 - p' ij.1 * q' ij.2| := by
        apply Finset.sum_le_sum
        intro k hk
        exact Finset.abs_sum_le_sum_abs _ _
      _ = _ := Finset.sum_fiberwise_of_maps_to hmap _
  have hconvert :
      (∑ ij ∈ AB, |p ij.1 * q ij.2 - p' ij.1 * q' ij.2|) =
        ∑ i ∈ A, ∑ j ∈ B, |p i * q j - p' i * q' j| := by
    dsimp [AB, A, B]
    rw [Finset.sum_product]
  exact hcontract.trans (hconvert.le.trans hprod)

/-- Exact law of the sum of independent squared-binomial increment marks for
a finite list of block durations. -/
def hypergeometricBlockListLaw : List ℕ → ℕ → ℝ
  | [], j => if j = 0 then 1 else 0
  | m :: ms, j => finiteNaturalConvolution m ms.sum
      (WalkTails.hypergeometricWeight m) (hypergeometricBlockListLaw ms) j

/-- Gaussian comparison law for a finite list of block durations, using the
normalized sampled profile at each block. -/
def normalizedGaussianBlockListLaw : List ℕ → ℕ → ℝ
  | [], j => if j = 0 then 1 else 0
  | m :: ms, j => finiteNaturalConvolution m ms.sum
      (normalizedSampledHypergeometricGaussianWeight m)
      (normalizedGaussianBlockListLaw ms) j

/-- The convolution law of a list of hypergeometric blocks has total mass one. -/
theorem hypergeometricBlockListLaw_sum_one (ms : List ℕ) :
    ∑ j ∈ Finset.range (ms.sum + 1), hypergeometricBlockListLaw ms j = 1 := by
  induction ms with
  | nil => simp [hypergeometricBlockListLaw]
  | cons m ms ih =>
      simpa [hypergeometricBlockListLaw, List.sum_cons] using
        (finiteNaturalConvolution_sum_one
          (WalkTails.hypergeometricWeight m) (hypergeometricBlockListLaw ms)
          (WalkTails.sum_hypergeometricWeight m) ih)

/-- The convolution law of hypergeometric blocks is nonnegative. -/
theorem hypergeometricBlockListLaw_nonneg (ms : List ℕ) :
    ∀ j, 0 ≤ hypergeometricBlockListLaw ms j := by
  induction ms with
  | nil =>
      intro j
      by_cases hj : j = 0 <;> simp [hypergeometricBlockListLaw, hj]
  | cons m ms ih =>
      intro j
      apply finiteNaturalConvolution_nonneg
      · intro i hi
        exact WalkTails.hypergeometricWeight_nonneg m i
      · intro k hk
        exact ih k

private theorem normalizedGaussianWeight_nonneg_of_large
    {C : ℝ} {m : ℕ}
    (hprofile :
      1 ≤ m ∧ 0 < (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) ∧
      (∑ k ∈ Finset.range (m + 1), normalizedSampledHypergeometricGaussianWeight m k) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k|) ≤ C / Real.sqrt (m : ℝ)) :
    ∀ k ∈ Finset.range (m + 1),
      0 ≤ normalizedSampledHypergeometricGaussianWeight m k := by
  intro k hk
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hprofile.1)
  have hroot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
  have hden : 0 < ∑ j ∈ Finset.range (m + 1), sampledHypergeometricGaussianWeight m j := hprofile.2.1
  unfold normalizedSampledHypergeometricGaussianWeight
  exact div_nonneg (by unfold sampledHypergeometricGaussianWeight; positivity)
    (le_of_lt hden)




/-- Replace a block by its normalized sampled Gaussian when its duration is
above `m₀`, and retain the exact law for shorter blocks. -/
def largeBlockGaussianWeight (m₀ m k : ℕ) : ℝ :=
  if m₀ ≤ m then normalizedSampledHypergeometricGaussianWeight m k
  else WalkTails.hypergeometricWeight m k

/-- The composition law obtained by Gaussianizing only the blocks above a
fixed duration threshold. -/
def largeBlockGaussianListLaw (m₀ : ℕ) : List ℕ → ℕ → ℝ
  | [], j => if j = 0 then 1 else 0
  | m :: ms, j => finiteNaturalConvolution m ms.sum
      (largeBlockGaussianWeight m₀ m) (largeBlockGaussianListLaw m₀ ms) j

private theorem largeBlockGaussianWeight_sum_one {C : ℝ} {m₀ m : ℕ}
    (hprofile : ∀ m : ℕ, m₀ ≤ m →
      1 ≤ m ∧ 0 < (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) ∧
      (∑ k ∈ Finset.range (m + 1), normalizedSampledHypergeometricGaussianWeight m k) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k|) ≤ C / Real.sqrt (m : ℝ)) :
    ∑ k ∈ Finset.range (m + 1), largeBlockGaussianWeight m₀ m k = 1 := by
  by_cases hm : m₀ ≤ m
  · have hsum := (hprofile m hm).2.2.1
    simpa [largeBlockGaussianWeight, hm] using hsum
  · simpa [largeBlockGaussianWeight, hm] using WalkTails.sum_hypergeometricWeight m

private theorem largeBlockGaussianWeight_nonneg {C : ℝ} {m₀ m : ℕ}
    (hprofile : ∀ m : ℕ, m₀ ≤ m →
      1 ≤ m ∧ 0 < (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) ∧
      (∑ k ∈ Finset.range (m + 1), normalizedSampledHypergeometricGaussianWeight m k) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k|) ≤ C / Real.sqrt (m : ℝ))
    (k : ℕ) (hk : k ∈ Finset.range (m + 1)) :
    0 ≤ largeBlockGaussianWeight m₀ m k := by
  by_cases hm : m₀ ≤ m
  · have hsingle := hprofile m hm
    have hnonneg := normalizedGaussianWeight_nonneg_of_large hsingle
    simpa [largeBlockGaussianWeight, hm] using hnonneg k hk
  · unfold largeBlockGaussianWeight
    simpa [largeBlockGaussianWeight, hm] using WalkTails.hypergeometricWeight_nonneg m k

private theorem largeBlockGaussianWeight_L1_error {C : ℝ} {m₀ m : ℕ}
    (hprofile : ∀ m : ℕ, m₀ ≤ m →
      1 ≤ m ∧ 0 < (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) ∧
      (∑ k ∈ Finset.range (m + 1), normalizedSampledHypergeometricGaussianWeight m k) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k|) ≤ C / Real.sqrt (m : ℝ)) :
    (∑ k ∈ Finset.range (m + 1),
      |WalkTails.hypergeometricWeight m k - largeBlockGaussianWeight m₀ m k|) ≤
      if m₀ ≤ m then C / Real.sqrt (m : ℝ) else 0 := by
  by_cases hm : m₀ ≤ m
  · have hbound := (hprofile m hm).2.2.2
    simpa [largeBlockGaussianWeight, hm] using hbound
  · simp [largeBlockGaussianWeight, hm]

/-- Replacing large hypergeometric blocks by normalized Gaussian profiles preserves total mass one. -/
theorem largeBlockGaussianListLaw_sum_one {C : ℝ} {m₀ : ℕ}
    (hprofile : ∀ m : ℕ, m₀ ≤ m →
      1 ≤ m ∧ 0 < (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) ∧
      (∑ k ∈ Finset.range (m + 1), normalizedSampledHypergeometricGaussianWeight m k) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k|) ≤ C / Real.sqrt (m : ℝ))
    (ms : List ℕ) :
    ∑ j ∈ Finset.range (ms.sum + 1), largeBlockGaussianListLaw m₀ ms j = 1 := by
  induction ms with
  | nil => simp [largeBlockGaussianListLaw]
  | cons m ms ih =>
      simpa [largeBlockGaussianListLaw, List.sum_cons] using
        (finiteNaturalConvolution_sum_one
          (largeBlockGaussianWeight m₀ m) (largeBlockGaussianListLaw m₀ ms)
          (largeBlockGaussianWeight_sum_one hprofile)
          (ih))

/-- The law with Gaussian replacements on large blocks is nonnegative. -/
theorem largeBlockGaussianListLaw_nonneg {C : ℝ} {m₀ : ℕ}
    (hprofile : ∀ m : ℕ, m₀ ≤ m →
      1 ≤ m ∧ 0 < (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) ∧
      (∑ k ∈ Finset.range (m + 1), normalizedSampledHypergeometricGaussianWeight m k) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k|) ≤ C / Real.sqrt (m : ℝ))
    (ms : List ℕ) : ∀ j, 0 ≤ largeBlockGaussianListLaw m₀ ms j := by
  induction ms with
  | nil =>
      intro j
      by_cases hj : j = 0 <;> simp [largeBlockGaussianListLaw, hj]
  | cons m ms ih =>
      intro j
      apply finiteNaturalConvolution_nonneg
      · intro k hk
        exact largeBlockGaussianWeight_nonneg (m := m) hprofile k hk
      · intro k hk
        exact ih k

/-- For every finite composition, replacing each sufficiently long increment
by its normalized Gaussian profile has error bounded by the sum of those
one-block errors; short increments remain exact. -/
theorem exists_hypergeometricBlockListLaw_hybrid_L1_error :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ mCut : ℕ, m₀ ≤ mCut → ∀ ms : List ℕ,
      (∑ j ∈ Finset.range (ms.sum + 1),
        |hypergeometricBlockListLaw ms j - largeBlockGaussianListLaw mCut ms j|) ≤
      (ms.map fun m => if mCut ≤ m then C / Real.sqrt (m : ℝ) else 0).sum := by
  obtain ⟨C, hC, m₀, hprofile⟩ :=
    exists_normalized_hypergeometricGaussian_L1_error
  refine ⟨C, hC, m₀, ?_⟩
  intro mCut hmCut ms
  have hprofileCut : ∀ m : ℕ, mCut ≤ m →
      1 ≤ m ∧ 0 < (∑ k ∈ Finset.range (m + 1),
        sampledHypergeometricGaussianWeight m k) ∧
      (∑ k ∈ Finset.range (m + 1), normalizedSampledHypergeometricGaussianWeight m k) = 1 ∧
      (∑ k ∈ Finset.range (m + 1),
        |WalkTails.hypergeometricWeight m k -
          normalizedSampledHypergeometricGaussianWeight m k|) ≤ C / Real.sqrt (m : ℝ) := by
    intro m hm
    exact hprofile m (le_trans hmCut hm)
  induction ms with
  | nil => simp [hypergeometricBlockListLaw, largeBlockGaussianListLaw]
  | cons m ms ih =>
      have htailL1 := ih
      have htailMass := hypergeometricBlockListLaw_sum_one ms
      have htailNonneg : ∀ k ∈ Finset.range (ms.sum + 1),
          0 ≤ hypergeometricBlockListLaw ms k := by
        intro k hk
        exact hypergeometricBlockListLaw_nonneg ms k
      have hmMass := largeBlockGaussianWeight_sum_one hprofileCut (m := m)
      have hmL1 := largeBlockGaussianWeight_L1_error hprofileCut (m := m)
      have hmNonneg : ∀ k ∈ Finset.range (m + 1),
          0 ≤ largeBlockGaussianWeight mCut m k := by
        intro k hk
        exact largeBlockGaussianWeight_nonneg (m := m) hprofileCut k hk
      have hconv := finiteNaturalConvolution_L1_le
        (WalkTails.hypergeometricWeight m) (largeBlockGaussianWeight mCut m)
        (hypergeometricBlockListLaw ms) (largeBlockGaussianListLaw mCut ms)
        hmNonneg htailNonneg htailMass hmMass
      have htailBound :
          (∑ k ∈ Finset.range (ms.sum + 1),
            |hypergeometricBlockListLaw ms k - largeBlockGaussianListLaw mCut ms k|) ≤
            (ms.map fun k => if mCut ≤ k then C / Real.sqrt (k : ℝ) else 0).sum :=
        htailL1
      have hbound :
          (∑ j ∈ Finset.range (m + ms.sum + 1),
            |finiteNaturalConvolution m ms.sum
                (WalkTails.hypergeometricWeight m) (hypergeometricBlockListLaw ms) j -
              finiteNaturalConvolution m ms.sum
                (largeBlockGaussianWeight mCut m) (largeBlockGaussianListLaw mCut ms) j|) ≤
            (if mCut ≤ m then C / Real.sqrt (m : ℝ) else 0) +
              (ms.map fun k => if mCut ≤ k then C / Real.sqrt (k : ℝ) else 0).sum :=
        hconv.trans (add_le_add hmL1 htailBound)
      simpa [hypergeometricBlockListLaw, largeBlockGaussianListLaw,
        List.sum_cons, List.map_cons] using hbound

/-- For a composition with at most `K` blocks, the hybrid approximation error
is `O(K / √mCut)` uniformly in the chosen cutoff. -/
theorem exists_hypergeometricBlockListLaw_hybrid_L1_error_of_length :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ mCut : ℕ, m₀ ≤ mCut → 0 < mCut →
      ∀ ms : List ℕ,
        (∑ j ∈ Finset.range (ms.sum + 1),
          |hypergeometricBlockListLaw ms j - largeBlockGaussianListLaw mCut ms j|) ≤
          (ms.length : ℝ) * (C / Real.sqrt (mCut : ℝ)) := by
  obtain ⟨C, hC, m₀, herror⟩ := exists_hypergeometricBlockListLaw_hybrid_L1_error
  refine ⟨C, hC, m₀, ?_⟩
  intro mCut hmCut hmCutPos ms
  have hrootCut : 0 < Real.sqrt (mCut : ℝ) := by
    exact Real.sqrt_pos.mpr (by exact_mod_cast hmCutPos)
  have hterm : ∀ m ∈ ms,
      (if mCut ≤ m then C / Real.sqrt (m : ℝ) else 0) ≤
        C / Real.sqrt (mCut : ℝ) := by
    intro m hm
    by_cases hlarge : mCut ≤ m
    · have hmPos : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le hmCutPos hlarge)
      have hroot : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmPos
      have hrootLe : Real.sqrt (mCut : ℝ) ≤ Real.sqrt (m : ℝ) :=
        Real.sqrt_le_sqrt (by exact_mod_cast hlarge)
      have hite : (if mCut ≤ m then C / Real.sqrt (m : ℝ) else 0) =
          C / Real.sqrt (m : ℝ) := ite_eq_left hlarge
      rw [hite]
      rw [div_le_div_iff₀ hroot hrootCut]
      exact mul_le_mul_of_nonneg_left hrootLe (le_of_lt hC)
    · have hite : (if mCut ≤ m then C / Real.sqrt (m : ℝ) else 0) = 0 :=
        ite_eq_right hlarge
      rw [hite]
      exact div_nonneg hC.le hrootCut.le
  have hsum :
      (ms.map fun m => if mCut ≤ m then C / Real.sqrt (m : ℝ) else 0).sum ≤
        (ms.length : ℝ) * (C / Real.sqrt (mCut : ℝ)) := by
    calc
      _ ≤ (ms.map fun _ : ℕ => C / Real.sqrt (mCut : ℝ)).sum :=
        List.sum_le_sum hterm
      _ = (ms.length : ℝ) * (C / Real.sqrt (mCut : ℝ)) := by
        simp [nsmul_eq_mul]
  exact (herror mCut hmCut ms).trans hsum

/-- If the first block is long enough to have the local-Gaussian atom bound,
its convolution smooths the `L¹` hybrid error in an arbitrary remaining
composition. -/
theorem exists_hypergeometricBlockListLaw_cons_pointwise_hybrid_error :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ mCut m : ℕ, m₀ ≤ mCut → 0 < mCut →
      mCut ≤ m → ∀ ms : List ℕ, ∀ j : ℕ,
        |hypergeometricBlockListLaw (m :: ms) j -
          largeBlockGaussianListLaw mCut (m :: ms) j| ≤
            C / (m : ℝ) + C * (ms.length : ℝ) /
              (Real.sqrt (m : ℝ) * Real.sqrt (mCut : ℝ)) := by
  obtain ⟨Cp, hCp, mp, hpoint⟩ :=
    exists_hypergeometricWeight_normalizedGaussian_point_error
  obtain ⟨Cq, hCq, mq, hq⟩ :=
    exists_normalizedSampledHypergeometricGaussian_pointwise_bound
  obtain ⟨Cl, hCl, ml, hL1⟩ :=
    exists_hypergeometricBlockListLaw_hybrid_L1_error_of_length
  let m₀ := max mp (max mq ml)
  let C : ℝ := Cp + Cq * Cl
  have hmp : mp ≤ m₀ := by simp [m₀]
  have hmq : mq ≤ m₀ := by simp [m₀]
  have hml : ml ≤ m₀ := by simp [m₀]
  refine ⟨C, ?_, m₀, ?_⟩
  · dsimp [C]
    positivity
  · intro mCut m hm₀cut hmCutPos hmCutm ms j
    have hmLarge : m₀ ≤ m := le_trans hm₀cut hmCutm
    have hmData := hpoint m (le_trans hmp hmLarge)
    have hm1 : 1 ≤ m := hmData.1
    have hmR : 0 < (m : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hm1)
    have hcutR : 0 < (mCut : ℝ) := by exact_mod_cast hmCutPos
    have hmsqrt : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hmR
    have hcutsqrt : 0 < Real.sqrt (mCut : ℝ) := Real.sqrt_pos.mpr hcutR
    let p : ℕ → ℝ := WalkTails.hypergeometricWeight m
    let q : ℕ → ℝ := normalizedSampledHypergeometricGaussianWeight m
    let r : ℕ → ℝ := hypergeometricBlockListLaw ms
    let s : ℕ → ℝ := largeBlockGaussianListLaw mCut ms
    have hpq : ∀ k ∈ Finset.range (m + 1), |p k - q k| ≤ Cp / (m : ℝ) := by
      intro k hk
      have hk' : k ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      simpa [p, q] using hmData.2 k hk'
    have hqPoint : ∀ k ∈ Finset.range (m + 1),
        |q k| ≤ Cq / Real.sqrt (m : ℝ) := by
      intro k hk
      exact hq m (le_trans hmq hmLarge) k hk
    have hrMass : ∑ k ∈ Finset.range (ms.sum + 1), r k = 1 := by
      simpa [r] using hypergeometricBlockListLaw_sum_one ms
    have hrNonneg : ∀ k ∈ Finset.range (ms.sum + 1), 0 ≤ r k := by
      intro k hk
      exact hypergeometricBlockListLaw_nonneg ms k
    have hrAbs : ∑ k ∈ Finset.range (ms.sum + 1), |r k| = 1 := by
      calc
        _ = ∑ k ∈ Finset.range (ms.sum + 1), r k := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [abs_of_nonneg (hrNonneg k hk)]
        _ = 1 := hrMass
    have hrest := hL1 mCut (le_trans hml hm₀cut) hmCutPos ms
    have hrestL1 :
        ∑ k ∈ Finset.range (ms.sum + 1), |r k - s k| ≤
          (ms.length : ℝ) * (Cl / Real.sqrt (mCut : ℝ)) := by
      simpa [r, s] using hrest
    have hdecomp :
        hypergeometricBlockListLaw (m :: ms) j -
            largeBlockGaussianListLaw mCut (m :: ms) j =
          finiteNaturalConvolution m ms.sum (fun k => p k - q k) r j +
            finiteNaturalConvolution m ms.sum q (fun k => r k - s k) j := by
      have hexact : hypergeometricBlockListLaw (m :: ms) j =
          finiteNaturalConvolution m ms.sum p r j := rfl
      have hhybrid : largeBlockGaussianListLaw mCut (m :: ms) j =
          finiteNaturalConvolution m ms.sum q s j := by
        change finiteNaturalConvolution m ms.sum (largeBlockGaussianWeight mCut m)
          (largeBlockGaussianListLaw mCut ms) j =
          finiteNaturalConvolution m ms.sum q s j
        have hweight : largeBlockGaussianWeight mCut m =
            normalizedSampledHypergeometricGaussianWeight m := by
          funext k
          simp [largeBlockGaussianWeight, hmCutm]
        rw [hweight]
      rw [hexact, hhybrid]
      let F := ((Finset.range (m + 1)).product (Finset.range (ms.sum + 1))).filter
        (fun ij => ij.1 + ij.2 = j)
      change (∑ ij ∈ F, p ij.1 * r ij.2) -
          (∑ ij ∈ F, q ij.1 * s ij.2) =
        (∑ ij ∈ F, (p ij.1 - q ij.1) * r ij.2) +
          (∑ ij ∈ F, q ij.1 * (r ij.2 - s ij.2))
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro ij hij
      ring
    have hterm1 := finiteNaturalConvolution_abs_le_leftPointwise
      (fun k => p k - q k) r (Cp / (m : ℝ)) 1 j (by positivity) hpq hrAbs.le
    have hterm2 := finiteNaturalConvolution_abs_le_leftPointwise
      q (fun k => r k - s k) (Cq / Real.sqrt (m : ℝ))
      ((ms.length : ℝ) * (Cl / Real.sqrt (mCut : ℝ))) j
      (by positivity) hqPoint hrestL1
    have hCpt : Cp ≤ C := by dsimp [C]; nlinarith [hCp.le, hCq.le, hCl.le]
    have hCprod : Cq * Cl ≤ C := by dsimp [C]; nlinarith
    have hterm1' :
        |finiteNaturalConvolution m ms.sum (fun k => p k - q k) r j| ≤
          C / (m : ℝ) := by
      calc
        _ ≤ Cp / (m : ℝ) := by simpa using hterm1
        _ ≤ C / (m : ℝ) := div_le_div_of_nonneg_right hCpt (by positivity)
    have hterm2' :
        |finiteNaturalConvolution m ms.sum q (fun k => r k - s k) j| ≤
          C * (ms.length : ℝ) /
            (Real.sqrt (m : ℝ) * Real.sqrt (mCut : ℝ)) := by
      have hnum : Cq * Cl * (ms.length : ℝ) ≤ C * (ms.length : ℝ) :=
        mul_le_mul_of_nonneg_right hCprod (Nat.cast_nonneg _)
      have hraw :
          (Cq / Real.sqrt (m : ℝ)) *
              ((ms.length : ℝ) * (Cl / Real.sqrt (mCut : ℝ))) =
            (Cq * Cl * (ms.length : ℝ)) /
              (Real.sqrt (m : ℝ) * Real.sqrt (mCut : ℝ)) := by ring
      calc
        _ ≤ (Cq / Real.sqrt (m : ℝ)) *
            ((ms.length : ℝ) * (Cl / Real.sqrt (mCut : ℝ))) := hterm2
        _ = (Cq * Cl * (ms.length : ℝ)) /
            (Real.sqrt (m : ℝ) * Real.sqrt (mCut : ℝ)) := hraw
        _ ≤ C * (ms.length : ℝ) /
            (Real.sqrt (m : ℝ) * Real.sqrt (mCut : ℝ)) :=
          div_le_div_of_nonneg_right hnum (by positivity)
    have htriangle :
        |hypergeometricBlockListLaw (m :: ms) j -
          largeBlockGaussianListLaw mCut (m :: ms) j| ≤
        |finiteNaturalConvolution m ms.sum (fun k => p k - q k) r j| +
          |finiteNaturalConvolution m ms.sum q (fun k => r k - s k) j| := by
      rw [hdecomp]
      exact abs_add_le _ _
    exact htriangle.trans (add_le_add hterm1' hterm2')




/-- The two rotated mark coordinates of a pair block are represented by the
product of two copies of the one-dimensional composition law. -/
def hypergeometricBlockListPairLaw (ms : List ℕ) (j₁ j₂ : ℕ) : ℝ :=
  hypergeometricBlockListLaw ms j₁ * hypergeometricBlockListLaw ms j₂

/-- The product comparison law for the two rotated pair-block coordinates. -/
def largeBlockGaussianListPairLaw (mCut : ℕ) (ms : List ℕ) (j₁ j₂ : ℕ) : ℝ :=
  largeBlockGaussianListLaw mCut ms j₁ * largeBlockGaussianListLaw mCut ms j₂




end Critical2DKPZ.SHF.Moments

end
