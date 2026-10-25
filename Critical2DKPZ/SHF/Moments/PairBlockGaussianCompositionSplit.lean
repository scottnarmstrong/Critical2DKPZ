/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockCompositionProfile
import Mathlib.Tactic

/-! # Exact short and long block splitting -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

/-- The probability generating polynomial of one hybrid Gaussian block. -/
def largeBlockGaussianPolynomial (mCut m : ℕ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (m + 1),
    Polynomial.C (largeBlockGaussianWeight mCut m k) * Polynomial.X ^ k

/-- The generating polynomial of a finite hybrid composition. -/
def largeBlockGaussianListPolynomial (mCut : ℕ) (ms : List ℕ) : Polynomial ℝ :=
  (ms.map (largeBlockGaussianPolynomial mCut)).prod

/-- The coefficient of `X ^ j` in `largeBlockGaussianPolynomial mCut m` is
the weight for `j ≤ m` and `0` otherwise. -/
theorem largeBlockGaussianPolynomial_coeff
    (mCut m j : ℕ) :
    (largeBlockGaussianPolynomial mCut m).coeff j =
      if j ≤ m then largeBlockGaussianWeight mCut m j else 0 := by
  classical
  simp only [largeBlockGaussianPolynomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul_X_pow]
  by_cases hjm : j ≤ m
  · have hjmem : j ∈ Finset.range (m + 1) := by simp [hjm]
    rw [Finset.sum_eq_single j]
    · simp [hjm]
    · intro k hk hkj
      simp [hkj.symm]
    · intro hnot
      exact (hnot hjmem).elim
  · have hjnot : j ∉ Finset.range (m + 1) := by
      simp only [Finset.mem_range]
      omega
    rw [Finset.sum_eq_zero]
    · simp [hjm]
    · intro k hk
      have hne : j ≠ k := by
        intro hEq
        subst k
        exact hjnot hk
      simp [hne]

private theorem largeBlockGaussianListLaw_eq_zero_of_gt
    (mCut : ℕ) (ms : List ℕ) (j : ℕ) (hj : ms.sum < j) :
    largeBlockGaussianListLaw mCut ms j = 0 := by
  induction ms generalizing j with
  | nil =>
      unfold largeBlockGaussianListLaw
      split_ifs with h
      · omega
      · rfl
  | cons m ms ih =>
      unfold largeBlockGaussianListLaw
      unfold finiteNaturalConvolution
      apply Finset.sum_eq_zero
      intro ij hij
      have hsum := (Finset.mem_filter.mp hij).2
      have hmem := Finset.mem_product.mp (Finset.mem_filter.mp hij).1
      have hfirst : ij.1 ≤ m := by
        have hlt : ij.1 < Nat.succ m := by simpa using Finset.mem_range.mp hmem.1
        exact Nat.le_of_lt_succ hlt
      have hsecond : ij.2 ≤ ms.sum := by
        have hlt : ij.2 < Nat.succ ms.sum := by
          simpa using Finset.mem_range.mp hmem.2
        exact Nat.le_of_lt_succ hlt
      have htail : largeBlockGaussianListLaw mCut ms ij.2 = 0 := by
        apply ih ij.2
        have hj' : m + ms.sum < j := by simpa using hj
        omega
      simp [htail]

private theorem coeff_mul_eq_finiteNaturalConvolution
    {m n j : ℕ} (p q : Polynomial ℝ) (f g : ℕ → ℝ)
    (hp : ∀ i, p.coeff i = if i ≤ m then f i else 0)
    (hq : ∀ i, q.coeff i = if i ≤ n then g i else 0) :
    (p * q).coeff j = finiteNaturalConvolution m n f g j := by
  classical
  let A : Finset (ℕ × ℕ) := Finset.HasAntidiagonal.antidiagonal j
  let B := ((Finset.range (m + 1)).product (Finset.range (n + 1))).filter
    (fun ij => ij.1 + ij.2 = j)
  have hsub : B ⊆ A := by
    intro ij hij
    simp only [A, Finset.HasAntidiagonal.mem_antidiagonal]
    exact (Finset.mem_filter.mp hij).2
  have hzero : ∀ ij ∈ A, ij ∉ B →
      p.coeff ij.1 * q.coeff ij.2 = 0 := by
    intro ij hij hnot
    have hsum : ij.1 + ij.2 = j := by
      simpa [A, Finset.HasAntidiagonal.mem_antidiagonal] using hij
    have hnotRange : ¬ (ij.1 ≤ m ∧ ij.2 ≤ n) := by
      intro hle
      apply hnot
      simp [B, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        hle, hsum]
    rcases not_and_or.mp hnotRange with hi | hi
    · rw [hp]
      simp [not_le_of_gt (by omega : m < ij.1)]
    · rw [hq]
      simp [not_le_of_gt (by omega : n < ij.2)]
  calc
    _ = ∑ ij ∈ A, p.coeff ij.1 * q.coeff ij.2 := by rw [Polynomial.coeff_mul]
    _ = ∑ ij ∈ B, p.coeff ij.1 * q.coeff ij.2 :=
      (Finset.sum_subset hsub hzero).symm
    _ = finiteNaturalConvolution m n f g j := by
      unfold finiteNaturalConvolution
      simp only [B]
      apply Finset.sum_congr rfl
      intro ij hij
      rw [hp, hq]
      have hle : ij.1 ≤ m ∧ ij.2 ≤ n := by
        have hmem := (Finset.mem_filter.mp hij).1
        simpa [Finset.mem_product, Finset.mem_range, Nat.lt_succ_iff] using hmem
      simp [hle]

/-- `largeBlockGaussianListLaw mCut ms j` is the `j`-th coefficient of
`largeBlockGaussianListPolynomial mCut ms`. -/
theorem largeBlockGaussianListLaw_eq_polynomial_coeff
    (mCut : ℕ) (ms : List ℕ) (j : ℕ) :
    (largeBlockGaussianListPolynomial mCut ms).coeff j =
      largeBlockGaussianListLaw mCut ms j := by
  induction ms generalizing j with
  | nil => simp [largeBlockGaussianListPolynomial, largeBlockGaussianListLaw,
      Polynomial.coeff_one]
  | cons m ms ih =>
      have hp (i : ℕ) :
          (largeBlockGaussianPolynomial mCut m).coeff i =
            if i ≤ m then largeBlockGaussianWeight mCut m i else 0 :=
        largeBlockGaussianPolynomial_coeff mCut m i
      have hq (i : ℕ) :
          (largeBlockGaussianListPolynomial mCut ms).coeff i =
            if i ≤ ms.sum then largeBlockGaussianListLaw mCut ms i else 0 := by
        by_cases hi : i ≤ ms.sum
        · simpa [hi] using ih i
        · have hzero := largeBlockGaussianListLaw_eq_zero_of_gt
            mCut ms i (Nat.lt_of_not_ge hi)
          rw [ih i]
          simp [hi, hzero]
      rw [largeBlockGaussianListPolynomial, List.map_cons, List.prod_cons]
      have hconv := coeff_mul_eq_finiteNaturalConvolution (j := j)
        (largeBlockGaussianPolynomial mCut m)
        (largeBlockGaussianListPolynomial mCut ms)
        (largeBlockGaussianWeight mCut m)
        (largeBlockGaussianListLaw mCut ms) hp hq
      simpa [largeBlockGaussianListPolynomial, List.map_cons, List.prod_cons,
        largeBlockGaussianListLaw] using hconv

/-- Filtering by a threshold partitions a list into its short and long blocks. -/
theorem filter_short_append_long_perm
    (mCut : ℕ) (ms : List ℕ) :
    List.Perm (ms.filter (fun m => m < mCut) ++
      ms.filter (fun m => mCut ≤ m)) ms := by
  induction ms with
  | nil => simp
  | cons m ms ih =>
      by_cases hm : m < mCut
      · simpa [hm] using ih.cons m
      · have hm' : mCut ≤ m := Nat.le_of_not_gt hm
        have hmove (xs ys : List ℕ) :
            List.Perm (xs ++ m :: ys) (m :: xs ++ ys) := by
          induction xs with
          | nil => simp
          | cons a xs ihx =>
              exact (ihx.cons a).trans (List.Perm.swap _ _ _)
        have hstep : List.Perm
            (ms.filter (fun k => k < mCut) ++ m ::
              ms.filter (fun k => mCut ≤ k)) (m :: ms) :=
          (hmove _ _).trans (ih.cons m)
        simpa [hm, hm'] using hstep

private theorem listPolynomial_eq_of_perm
    (mCut : ℕ) {xs ys : List ℕ} (h : List.Perm xs ys) :
    largeBlockGaussianListPolynomial mCut xs =
      largeBlockGaussianListPolynomial mCut ys := by
  have hmap := h.map (largeBlockGaussianPolynomial mCut)
  have hfold :
      List.foldl (fun a b : Polynomial ℝ => a * b) 1
          (xs.map (largeBlockGaussianPolynomial mCut)) =
        List.foldl (fun a b : Polynomial ℝ => a * b) 1
          (ys.map (largeBlockGaussianPolynomial mCut)) := by
    apply hmap.foldl_eq'
    · intro x hx y hy z
      simp only [mul_assoc]
      rw [mul_comm x y]
  simpa [largeBlockGaussianListPolynomial, List.prod_eq_foldl] using hfold

/-- The hybrid composition law factors exactly into the convolution of its
short exact blocks and its long Gaussianized blocks. -/
theorem largeBlockGaussianListLaw_eq_short_long_convolution
    (mCut : ℕ) (ms : List ℕ) (j : ℕ) :
    largeBlockGaussianListLaw mCut ms j =
      finiteNaturalConvolution
        (ms.filter (fun m => m < mCut)).sum
        (ms.filter (fun m => mCut ≤ m)).sum
        (largeBlockGaussianListLaw mCut (ms.filter (fun m => m < mCut)))
        (largeBlockGaussianListLaw mCut (ms.filter (fun m => mCut ≤ m))) j := by
  let short := ms.filter (fun m => m < mCut)
  let long := ms.filter (fun m => mCut ≤ m)
  have hperm : List.Perm (short ++ long) ms := by
    simpa [short, long] using filter_short_append_long_perm mCut ms
  have hpoly : largeBlockGaussianListPolynomial mCut ms =
      largeBlockGaussianListPolynomial mCut short *
        largeBlockGaussianListPolynomial mCut long := by
    calc
      _ = largeBlockGaussianListPolynomial mCut (short ++ long) :=
        (listPolynomial_eq_of_perm mCut hperm).symm
      _ = _ := by simp [largeBlockGaussianListPolynomial, short, long]
  have hcoeffSupport (xs : List ℕ) (i : ℕ) :
      (largeBlockGaussianListPolynomial mCut xs).coeff i =
        if i ≤ xs.sum then largeBlockGaussianListLaw mCut xs i else 0 := by
    by_cases hi : i ≤ xs.sum
    · rw [largeBlockGaussianListLaw_eq_polynomial_coeff]
      simp [hi]
    · rw [largeBlockGaussianListLaw_eq_polynomial_coeff]
      simp [hi, largeBlockGaussianListLaw_eq_zero_of_gt mCut xs i
        (Nat.lt_of_not_ge hi)]
  have hconv := coeff_mul_eq_finiteNaturalConvolution
    (m := short.sum) (n := long.sum) (j := j)
    (largeBlockGaussianListPolynomial mCut short)
    (largeBlockGaussianListPolynomial mCut long)
    (largeBlockGaussianListLaw mCut short)
    (largeBlockGaussianListLaw mCut long)
    (hcoeffSupport short) (hcoeffSupport long)
  calc
    largeBlockGaussianListLaw mCut ms j =
        (largeBlockGaussianListPolynomial mCut ms).coeff j :=
      (largeBlockGaussianListLaw_eq_polynomial_coeff mCut ms j).symm
    _ = (largeBlockGaussianListPolynomial mCut short *
        largeBlockGaussianListPolynomial mCut long).coeff j := by rw [hpoly]
    _ = _ := by simpa [short, long] using hconv

end Critical2DKPZ.SHF.Moments

end
