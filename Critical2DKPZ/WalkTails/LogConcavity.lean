/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.WalkTails.DiscreteConvolution
public import Critical2DKPZ.WalkTails.Hypergeometric

/-! # Log-concavity and finite walk-law convolution

Repeated convolution with the coefficient sequence of `1+x` gives the binomial coefficients.
Nonnegative Toeplitz minors are preserved by this convolution and imply log-concavity of the
squared-binomial laws.
-/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.WalkTails

/-- The two-point coefficient sequence of `1 + x`. -/
def unitBernoulliCoeff (z : ℤ) : ℝ := if z = 0 ∨ z = 1 then 1 else 0

/-- The point mass at zero, used as the initial binomial coefficient sequence. -/
def deltaCoeff (z : ℤ) : ℝ := if z = 0 then 1 else 0

/-- The unit Bernoulli coefficient sequence is nonnegative. -/
theorem unitBernoulliCoeff_nonneg (z : ℤ) : 0 ≤ unitBernoulliCoeff z := by
  unfold unitBernoulliCoeff
  split <;> positivity

/-- The unit Bernoulli coefficient sequence has nonnegative Toeplitz minors of order two. -/
theorem unitBernoulliCoeff_toeplitzTP2 : toeplitzTP2 unitBernoulliCoeff := by
  intro i j k l hij hkl
  have hsecond : unitBernoulliCoeff (l - i) * unitBernoulliCoeff (k - j) = 0 := by
    by_cases hL : l - i = 0 ∨ l - i = 1
    · by_cases hK : k - j = 0 ∨ k - j = 1
      · exfalso
        rcases hL with hL | hL <;> rcases hK with hK | hK <;> omega
      · simp [unitBernoulliCoeff, hL, hK]
    · simp [unitBernoulliCoeff, hL]
  have hfirst : 0 ≤ unitBernoulliCoeff (k - i) * unitBernoulliCoeff (l - j) :=
    mul_nonneg (unitBernoulliCoeff_nonneg _) (unitBernoulliCoeff_nonneg _)
  rw [hsecond, sub_zero]
  exact hfirst

/-- The point-mass coefficient sequence has nonnegative Toeplitz minors of order two. -/
theorem deltaCoeff_toeplitzTP2 : toeplitzTP2 deltaCoeff := by
  intro i j k l hij hkl
  have hsecond : deltaCoeff (l - i) * deltaCoeff (k - j) = 0 := by
    by_cases hL : l - i = 0
    · by_cases hK : k - j = 0
      · exfalso
        omega
      · simp [deltaCoeff, hL, hK]
    · simp [deltaCoeff, hL]
  have hfirst : 0 ≤ deltaCoeff (k - i) * deltaCoeff (l - j) := by
    unfold deltaCoeff
    split <;> split <;> positivity
  rw [hsecond, sub_zero]
  exact hfirst

/-- Convolution with the coefficient sequence of `1+x` adds adjacent coefficients. -/
theorem finiteConvolution_unitBernoulli (f : ℤ → ℝ) (z : ℤ) :
    finiteConvolution ({0, 1} : Finset ℤ) unitBernoulliCoeff f z =
      f z + f (z - 1) := by
  classical
  simp [finiteConvolution, unitBernoulliCoeff]

/-- Binomial coefficients extended to the integers have nonnegative Toeplitz minors of order two. -/
theorem binomZ_toeplitzTP2 (m : ℕ) : toeplitzTP2 (LatticeProb.binomZ m) := by
  induction m with
  | zero =>
      have hzero : LatticeProb.binomZ 0 = deltaCoeff := by
        funext z
        rcases lt_trichotomy z 0 with hz | hz | hz
        · simp [LatticeProb.binomZ, deltaCoeff, not_le.mpr (by omega : z < 0),
            ne_of_lt hz]
        · subst z
          simp [LatticeProb.binomZ, deltaCoeff]
        · have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
          have hnat : 0 < z.toNat := by omega
          simp [LatticeProb.binomZ, deltaCoeff, show 0 ≤ z by omega,
            Nat.choose_eq_zero_of_lt hnat, ne_of_gt hz]
      rw [hzero]
      exact deltaCoeff_toeplitzTP2
  | succ m ih =>
      have hconv :
          finiteConvolution ({0, 1} : Finset ℤ) unitBernoulliCoeff
            (LatticeProb.binomZ m) = LatticeProb.binomZ (m + 1) := by
        funext z
        rw [finiteConvolution_unitBernoulli]
        rw [LatticeProb.binomZ_succ]
        ring
      rw [← hconv]
      apply finiteConvolution_toeplitzTP2
        (s := ({0, 1} : Finset ℤ))
        (f := unitBernoulliCoeff) (g := LatticeProb.binomZ m)
      · intro a ha
        have ha0 : a ≠ 0 := by
          intro h
          apply ha
          simp [h]
        have ha1 : a ≠ 1 := by
          intro h
          apply ha
          simp [h]
        simp [unitBernoulliCoeff, ha0, ha1]
      · exact unitBernoulliCoeff_toeplitzTP2
      · exact ih

/-- A sequence is discretely log-concave when each squared value dominates the product of its neighbors. -/
def discreteLogConcave (f : ℤ → ℝ) : Prop :=
  ∀ k : ℤ, f k ^ 2 ≥ f (k - 1) * f (k + 1)

/-- Nonnegative Toeplitz minors of order two imply discrete log-concavity. -/
theorem toeplitzTP2_logConcave {f : ℤ → ℝ} (hf : toeplitzTP2 f) :
    discreteLogConcave f := by
  intro k
  have h := hf (i := 0) (j := 1) (k := k) (l := k + 1) (by omega) (by omega)
  simpa [discreteLogConcave, pow_two, mul_comm] using h


/-- Pointwise squaring preserves nonnegative Toeplitz minors for a nonnegative sequence. -/
theorem pointwiseSquare_toeplitzTP2 {f : ℤ → ℝ} (hf : toeplitzTP2 f)
    (hfnonneg : ∀ z, 0 ≤ f z) : toeplitzTP2 (fun z => f z ^ 2) := by
  intro i j k l hij hkl
  have hminor := hf hij hkl
  have hfirst : 0 ≤ f (k - i) * f (l - j) :=
    mul_nonneg (hfnonneg _) (hfnonneg _)
  have hsecond : 0 ≤ f (l - i) * f (k - j) :=
    mul_nonneg (hfnonneg _) (hfnonneg _)
  have hcmp : f (l - i) * f (k - j) ≤ f (k - i) * f (l - j) := by
    linarith
  have hsquare := mul_self_le_mul_self hsecond hcmp
  have hsquare' : (f (l - i) * f (k - j)) ^ 2 ≤
      (f (k - i) * f (l - j)) ^ 2 := by
    simpa [pow_two] using hsquare
  calc
    0 ≤ (f (k - i) * f (l - j)) ^ 2 -
        (f (l - i) * f (k - j)) ^ 2 := sub_nonneg.mpr hsquare'
    _ = (f (k - i) ^ 2) * (f (l - j) ^ 2) -
        (f (l - i) ^ 2) * (f (k - j) ^ 2) := by ring

/-- Multiplication by a real scalar preserves nonnegative Toeplitz minors of order two. -/
theorem scalarMul_toeplitzTP2 {f : ℤ → ℝ} (a : ℝ)
    (hf : toeplitzTP2 f) : toeplitzTP2 (fun z => a * f z) := by
  intro i j k l hij hkl
  have hminor := hf hij hkl
  have hEq :
      (a * f (k - i)) * (a * f (l - j)) -
          (a * f (l - i)) * (a * f (k - j)) =
        a ^ 2 * (f (k - i) * f (l - j) - f (l - i) * f (k - j)) := by ring
  rw [hEq]
  exact mul_nonneg (sq_nonneg a) hminor

/-- The squared-binomial probability mass, extended by zero to all of `ℤ`. -/
def hypergeometricIntWeight (m : ℕ) (z : ℤ) : ℝ :=
  (LatticeProb.binomZ m z) ^ 2 / (Nat.choose (2 * m) m : ℝ)

/-- The integer hypergeometric weight is nonnegative. -/
theorem hypergeometricIntWeight_nonneg (m : ℕ) (z : ℤ) :
    0 ≤ hypergeometricIntWeight m z := by
  unfold hypergeometricIntWeight
  positivity

/-- The squared-binomial law is strictly positive on its full interval
support. -/
theorem hypergeometricIntWeight_pos_of_mem {m : ℕ} {z : ℤ}
    (hz : z ∈ Finset.Icc (0 : ℤ) m) : 0 < hypergeometricIntWeight m z := by
  have hz0 : 0 ≤ z := (Finset.mem_Icc.mp hz).1
  have hzm : z ≤ (m : ℤ) := (Finset.mem_Icc.mp hz).2
  have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  have hzm' : (z.toNat : ℤ) ≤ m := by rw [hzcast]; exact hzm
  have hnat : z.toNat ≤ m := by exact_mod_cast hzm'
  rw [← hzcast]
  unfold hypergeometricIntWeight
  rw [LatticeProb.binomZ_natCast]
  have hchoose : 0 < (Nat.choose m z.toNat : ℝ) := by
    exact_mod_cast Nat.choose_pos hnat
  have hden : 0 < (Nat.choose (2 * m) m : ℝ) := hypergeometric_denominator_pos m
  positivity

private theorem sum_int_interval_eq_sum_range (m : ℕ) (f : ℤ → ℝ) :
    (∑ z ∈ Finset.Icc (0 : ℤ) m, f z) =
      ∑ j ∈ Finset.range (m + 1), f (j : ℤ) := by
  classical
  symm
  apply Finset.sum_bij (s := Finset.range (m + 1))
    (t := Finset.Icc (0 : ℤ) m) (fun j _ => (j : ℤ))
  · intro j hj
    simp only [Finset.mem_range] at hj
    simp only [Finset.mem_Icc]
    constructor
    · exact_mod_cast Nat.zero_le j
    · exact_mod_cast (Nat.lt_succ_iff.mp hj)
  · intro j hj k hk hjk
    exact_mod_cast hjk
  · intro z hz
    have hz0 : 0 ≤ z := (Finset.mem_Icc.mp hz).1
    have hzm : z ≤ (m : ℤ) := (Finset.mem_Icc.mp hz).2
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    have hnat : z.toNat ≤ m := by
      have : (z.toNat : ℤ) ≤ m := by simpa [hzcast] using hzm
      exact_mod_cast this
    refine ⟨z.toNat, Finset.mem_range.mpr (Nat.lt_succ_of_le hnat), ?_⟩
    exact hzcast
  · intro j hj
    rfl

/-- The integer hypergeometric weight agrees with its natural-index expression on nonnegative indices. -/
theorem hypergeometricIntWeight_eq_nat (m j : ℕ) :
    hypergeometricIntWeight m (j : ℤ) = hypergeometricWeight m j := by
  rw [hypergeometricIntWeight, LatticeProb.binomZ_natCast]
  rfl

/-- The integer-indexed extension of a squared-binomial law has total mass one. -/
theorem sum_hypergeometricIntWeight (m : ℕ) :
    ∑ z ∈ Finset.Icc (0 : ℤ) m, hypergeometricIntWeight m z = 1 := by
  rw [sum_int_interval_eq_sum_range]
  calc
    (∑ j ∈ Finset.range (m + 1), hypergeometricIntWeight m (j : ℤ)) =
        ∑ j ∈ Finset.range (m + 1), hypergeometricWeight m j := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [hypergeometricIntWeight, LatticeProb.binomZ_natCast]
          rfl
    _ = 1 := sum_hypergeometricWeight m

/-- The integer-indexed squared-binomial law is centered at `m / 2`. -/
theorem hypergeometricIntWeight_centered_firstMoment (m : ℕ) :
    (∑ z ∈ Finset.Icc (0 : ℤ) m,
      hypergeometricIntWeight m z * (2 * (z : ℝ) - (m : ℝ))) = 0 := by
  rw [sum_int_interval_eq_sum_range]
  calc
    _ = ∑ j ∈ Finset.range (m + 1),
          hypergeometricWeight m j * hypergeometricIncrement m j := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hypergeometricIntWeight_eq_nat]
            simp [hypergeometricIncrement]
    _ = 0 := hypergeometricIncrement_firstMoment m

/-- The second moment of `2j-m` under the integer-indexed squared-binomial law is `m²/(2m-1)`. -/
theorem hypergeometricIntWeight_centered_secondMoment (m : ℕ) :
    (∑ z ∈ Finset.Icc (0 : ℤ) m,
      hypergeometricIntWeight m z * (2 * (z : ℝ) - (m : ℝ)) ^ 2) =
      (m : ℝ) ^ 2 / (2 * (m : ℝ) - 1) := by
  rw [sum_int_interval_eq_sum_range]
  calc
    _ = ∑ j ∈ Finset.range (m + 1),
          hypergeometricWeight m j * hypergeometricIncrement m j ^ 2 := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hypergeometricIntWeight_eq_nat]
            simp [hypergeometricIncrement]
    _ = _ := hypergeometricIncrement_secondMoment m

/-- Integer hypergeometric weights have nonnegative Toeplitz minors of order two. -/
theorem hypergeometricIntWeight_toeplitzTP2 (m : ℕ) :
    toeplitzTP2 (hypergeometricIntWeight m) := by
  have hsquare := pointwiseSquare_toeplitzTP2 (binomZ_toeplitzTP2 m)
    (fun z => LatticeProb.binomZ_nonneg m z)
  have hden : 0 < (Nat.choose (2 * m) m : ℝ) :=
    hypergeometric_denominator_pos m
  have hscale : 0 ≤ ((Nat.choose (2 * m) m : ℝ)⁻¹) := by positivity
  have heq : hypergeometricIntWeight m =
      (fun z => ((Nat.choose (2 * m) m : ℝ)⁻¹) *
        (LatticeProb.binomZ m z) ^ 2) := by
    funext z
    unfold hypergeometricIntWeight
    rw [div_eq_mul_inv]
    ring
  rw [heq]
  exact scalarMul_toeplitzTP2 _ hsquare

/-- The integer-indexed squared-binomial law is symmetric about `m/2`. -/
theorem hypergeometricIntWeight_symm (m : ℕ) (z : ℤ) :
    hypergeometricIntWeight m ((m : ℤ) - z) = hypergeometricIntWeight m z := by
  unfold hypergeometricIntWeight
  rw [LatticeProb.binomZ_symm]

/-- The integer hypergeometric weight vanishes outside its finite support interval. -/
theorem hypergeometricIntWeight_eq_zero_of_notMem {m : ℕ} {z : ℤ}
    (hz : z ∉ Finset.Icc (0 : ℤ) m) : hypergeometricIntWeight m z = 0 := by
  have hz' : z < 0 ∨ (m : ℤ) < z := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hz
    exact hz
  unfold hypergeometricIntWeight
  rcases hz' with hneg | hlarge
  · rw [LatticeProb.binomZ_of_neg hneg]
    simp
  · rw [LatticeProb.binomZ_of_lt hlarge]
    simp



/-- The finite convolution law of a list of squared-binomial increments. -/
def squaredBinomialConvolution : List ℕ → ℤ → ℝ
  | [] => deltaCoeff
  | m :: ms => finiteConvolution (Finset.Icc (0 : ℤ) m)
      (hypergeometricIntWeight m) (squaredBinomialConvolution ms)

/-- Finite convolutions of squared-binomial laws have nonnegative Toeplitz minors of size two. -/
theorem squaredBinomialConvolution_toeplitzTP2 (ms : List ℕ) :
    toeplitzTP2 (squaredBinomialConvolution ms) := by
  induction ms with
  | nil => exact deltaCoeff_toeplitzTP2
  | cons m ms ih =>
      apply finiteConvolution_toeplitzTP2
        (s := Finset.Icc (0 : ℤ) m)
        (f := hypergeometricIntWeight m)
        (g := squaredBinomialConvolution ms)
      · intro z hz
        exact hypergeometricIntWeight_eq_zero_of_notMem hz
      · exact hypergeometricIntWeight_toeplitzTP2 m
      · exact ih

/-- A squared-binomial convolution is log-concave. -/
theorem squaredBinomialConvolution_logConcave (ms : List ℕ) :
    discreteLogConcave (squaredBinomialConvolution ms) :=
  toeplitzTP2_logConcave (squaredBinomialConvolution_toeplitzTP2 ms)

/-- Every finite squared-binomial convolution is nonnegative. -/
theorem squaredBinomialConvolution_nonneg (ms : List ℕ) (z : ℤ) :
    0 ≤ squaredBinomialConvolution ms z := by
  induction ms generalizing z with
  | nil =>
      unfold squaredBinomialConvolution deltaCoeff
      split_ifs <;> positivity
  | cons m ms ih =>
      change 0 ≤ finiteConvolution (Finset.Icc (0 : ℤ) m)
        (hypergeometricIntWeight m) (squaredBinomialConvolution ms) z
      unfold finiteConvolution
      apply Finset.sum_nonneg
      intro a ha
      exact mul_nonneg (hypergeometricIntWeight_nonneg m a) (ih (z - a))

/-- A finite squared-binomial convolution vanishes outside its summed
support interval. -/
theorem squaredBinomialConvolution_eq_zero_of_notMem {ms : List ℕ} {z : ℤ}
    (hz : z ∉ Finset.Icc (0 : ℤ) ms.sum) : squaredBinomialConvolution ms z = 0 := by
  induction ms generalizing z with
  | nil =>
      have hz' : z ≠ 0 := by
        intro hz0
        apply hz
        simp [hz0]
      simp [squaredBinomialConvolution, deltaCoeff, hz']
  | cons m ms ih =>
      have hres : ∀ a ∈ Finset.Icc (0 : ℤ) m,
          z - a ∉ Finset.Icc (0 : ℤ) ms.sum := by
        intro a ha hmem
        apply hz
        simp only [List.sum_cons, Nat.cast_add, Finset.mem_Icc] at ha hmem hz ⊢
        constructor <;> omega
      change finiteConvolution (Finset.Icc (0 : ℤ) m)
        (hypergeometricIntWeight m) (squaredBinomialConvolution ms) z = 0
      unfold finiteConvolution
      apply Finset.sum_eq_zero
      intro a ha
      rw [ih (z := z - a) (hres a ha)]
      simp

/-- Every integer in the summed support interval has strictly positive mass. -/
theorem squaredBinomialConvolution_pos (ms : List ℕ) (z : ℤ)
    (hz : z ∈ Finset.Icc (0 : ℤ) ms.sum) : 0 < squaredBinomialConvolution ms z := by
  induction ms generalizing z with
  | nil =>
      have hz0 : z = 0 := by
        have hz' := Finset.mem_Icc.mp hz
        simp only [List.sum_nil] at hz'
        omega
      subst z
      simp [squaredBinomialConvolution, deltaCoeff]
  | cons m ms ih =>
      have hzmem : 0 ≤ z ∧ z ≤ ((m + ms.sum : ℕ) : ℤ) := by
        simpa only [List.sum_cons, Nat.cast_add, Finset.mem_Icc] using hz
      have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzmem.1
      have hznat' : (z.toNat : ℤ) ≤ ((m + ms.sum : ℕ) : ℤ) := by
        rw [hzcast]
        exact hzmem.2
      have hznat : z.toNat ≤ m + ms.sum := by exact_mod_cast hznat'
      let a : ℤ := (min z.toNat m : ℕ)
      have ha0 : 0 ≤ a := by
        dsimp [a]
        positivity
      have ham : a ≤ (m : ℤ) := by
        dsimp [a]
        exact_mod_cast Nat.min_le_right z.toNat m
      have ha : a ∈ Finset.Icc (0 : ℤ) m := Finset.mem_Icc.mpr ⟨ha0, ham⟩
      have hres : z - a ∈ Finset.Icc (0 : ℤ) ms.sum := by
        have hmin_le : min z.toNat m ≤ z.toNat := Nat.min_le_left _ _
        have hmin_le_cast : a ≤ z := by
          dsimp [a]
          calc
            ((min z.toNat m : ℕ) : ℤ) ≤ (z.toNat : ℤ) := by exact_mod_cast hmin_le
            _ = z := hzcast
        by_cases hcase : z.toNat ≤ m
        · have hamin : a = z := by
            dsimp [a]
            rw [Nat.min_eq_left hcase, hzcast]
          rw [Finset.mem_Icc]
          rw [hamin]
          constructor
          · simp
          · have hsum_nonneg : (0 : ℤ) ≤ (ms.sum : ℤ) := by
              exact_mod_cast Nat.zero_le ms.sum
            simpa using hsum_nonneg
        · have hamin : a = (m : ℤ) := by
            dsimp [a]
            rw [Nat.min_eq_right (Nat.le_of_not_ge hcase)]
          rw [Finset.mem_Icc]
          have hmlt : (m : ℤ) < z := by
            have hnatlt : m < z.toNat := Nat.lt_of_not_ge hcase
            have hcastlt : (m : ℤ) < (z.toNat : ℤ) := by exact_mod_cast hnatlt
            rwa [hzcast] at hcastlt
          have hleInt : z ≤ ((m + ms.sum : ℕ) : ℤ) := by
            calc
              z = (z.toNat : ℤ) := hzcast.symm
              _ ≤ ((m + ms.sum : ℕ) : ℤ) := by exact_mod_cast hznat
          rw [hamin]
          constructor <;> omega
      have hterm : 0 <
          hypergeometricIntWeight m a * squaredBinomialConvolution ms (z - a) :=
        mul_pos (hypergeometricIntWeight_pos_of_mem ha) (ih (z - a) hres)
      have hsum : 0 <
          ∑ b ∈ Finset.Icc (0 : ℤ) m,
            hypergeometricIntWeight m b * squaredBinomialConvolution ms (z - b) :=
        lt_of_lt_of_le hterm (Finset.single_le_sum
          (f := fun b => hypergeometricIntWeight m b * squaredBinomialConvolution ms (z - b))
          (fun b hb => mul_nonneg (hypergeometricIntWeight_nonneg m b)
            (squaredBinomialConvolution_nonneg ms (z - b))) ha)
      change 0 < finiteConvolution (Finset.Icc (0 : ℤ) m)
        (hypergeometricIntWeight m) (squaredBinomialConvolution ms) z
      simpa [finiteConvolution] using hsum

private theorem sum_Icc_translate_of_supported {m n : ℕ} {a : ℤ}
    (ha : a ∈ Finset.Icc (0 : ℤ) m) (f : ℤ → ℝ)
    (hfzero : ∀ z, z ∉ Finset.Icc (0 : ℤ) n → f z = 0) :
    (∑ z ∈ Finset.Icc (0 : ℤ) (m + n), f (z - a)) =
      ∑ z ∈ Finset.Icc (0 : ℤ) n, f z := by
  classical
  let s : Finset ℤ := Finset.Icc 0 (m + n)
  let t : Finset ℤ := Finset.Icc (-a) ((m + n : ℕ) - a)
  have hmem : ∀ z ∈ s, z - a ∈ t := by
    intro z hz
    have ha' := Finset.mem_Icc.mp ha
    simp only [s, t, Finset.mem_Icc] at hz ⊢
    omega
  have hsub : Finset.Icc (0 : ℤ) n ⊆ t := by
    intro z hz
    have haz := Finset.mem_Icc.mp ha
    have hzz := Finset.mem_Icc.mp hz
    simp only [t, Finset.mem_Icc, Nat.cast_add] at ⊢
    omega
  calc
    (∑ z ∈ Finset.Icc (0 : ℤ) (m + n), f (z - a)) = ∑ z ∈ t, f z := by
      change ∑ z ∈ s, f (z - a) = ∑ z ∈ t, f z
      refine Finset.sum_bij (s := s) (t := t)
        (f := fun z => f (z - a)) (g := f) (fun z _ => z - a) ?_ ?_ ?_ ?_
      · exact hmem
      · intro z hz z' hz' hEq
        omega
      · intro z hz
        refine ⟨z + a, ?_, ?_⟩
        · have haz := Finset.mem_Icc.mp ha
          have hzz := Finset.mem_Icc.mp hz
          simp only [s, Finset.mem_Icc]
          omega
        · omega
      · intro z hz
        rfl
    _ = ∑ z ∈ Finset.Icc (0 : ℤ) n, f z :=
      (Finset.sum_subset hsub (fun z hz hnot => hfzero z hnot)).symm

private theorem finiteConvolution_weighted_sum {m n : ℕ} (f g φ : ℤ → ℝ)
    (hgzero : ∀ z, z ∉ Finset.Icc (0 : ℤ) n → g z = 0) :
    (∑ z ∈ Finset.Icc (0 : ℤ) (m + n),
      finiteConvolution (Finset.Icc (0 : ℤ) m) f g z * φ z) =
      ∑ a ∈ Finset.Icc (0 : ℤ) m,
        f a * ∑ b ∈ Finset.Icc (0 : ℤ) n, g b * φ (a + b) := by
  classical
  unfold finiteConvolution
  calc
    _ = ∑ z ∈ Finset.Icc (0 : ℤ) (m + n),
          ∑ a ∈ Finset.Icc (0 : ℤ) m,
            f a * (g (z - a) * φ z) := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro a ha
              ring
    _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
          ∑ z ∈ Finset.Icc (0 : ℤ) (m + n),
            f a * (g (z - a) * φ z) := by rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
          f a * ∑ z ∈ Finset.Icc (0 : ℤ) (m + n),
            g (z - a) * φ z := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
    _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
          f a * ∑ b ∈ Finset.Icc (0 : ℤ) n, g b * φ (a + b) := by
              apply Finset.sum_congr rfl
              intro a ha
              have htranslate := sum_Icc_translate_of_supported
                (m := m) (n := n) (a := a) ha
                (fun b => g b * φ (b + a))
                (by
                  intro b hb
                  rw [hgzero b hb]
                  simp)
              congr 1
              calc
                (∑ z ∈ Finset.Icc (0 : ℤ) (m + n),
                    g (z - a) * φ z) =
                    ∑ z ∈ Finset.Icc (0 : ℤ) (m + n),
                      g (z - a) * φ ((z - a) + a) := by
                        apply Finset.sum_congr rfl
                        intro z hz
                        congr 2
                        omega
                _ = ∑ b ∈ Finset.Icc (0 : ℤ) n,
                      g b * φ (a + b) := by simpa [add_comm] using htranslate

/-- The finite squared-binomial convolution is a probability mass function on
its exact support interval. -/
theorem squaredBinomialConvolution_sum_one (ms : List ℕ) :
    ∑ z ∈ Finset.Icc (0 : ℤ) ms.sum, squaredBinomialConvolution ms z = 1 := by
  classical
  induction ms with
  | nil =>
      simp [squaredBinomialConvolution, deltaCoeff]
  | cons m ms ih =>
      change (∑ z ∈ Finset.Icc (0 : ℤ) (m + ms.sum),
        finiteConvolution (Finset.Icc (0 : ℤ) m)
          (hypergeometricIntWeight m) (squaredBinomialConvolution ms) z) = 1
      unfold finiteConvolution
      calc
        _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
            ∑ z ∈ Finset.Icc (0 : ℤ) (m + ms.sum),
              hypergeometricIntWeight m a * squaredBinomialConvolution ms (z - a) := by
                rw [Finset.sum_comm]
        _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
            hypergeometricIntWeight m a *
              (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
                squaredBinomialConvolution ms z) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [← Finset.mul_sum]
                rw [sum_Icc_translate_of_supported (m := m) (n := ms.sum) (a := a) ha
                  (squaredBinomialConvolution ms)
                  (fun z hz => squaredBinomialConvolution_eq_zero_of_notMem hz)]
        _ = ∑ a ∈ Finset.Icc (0 : ℤ) m, hypergeometricIntWeight m a := by
              rw [ih]
              simp
        _ = 1 := sum_hypergeometricIntWeight m

/-- The finite convolution is centered at half its total duration. -/
theorem squaredBinomialConvolution_centered_firstMoment (ms : List ℕ) :
    (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
      squaredBinomialConvolution ms z *
        (2 * (z : ℝ) - (ms.sum : ℝ))) = 0 := by
  induction ms with
  | nil =>
      simp [squaredBinomialConvolution, deltaCoeff]
  | cons m ms ih =>
      change
        (∑ z ∈ Finset.Icc (0 : ℤ) (m + ms.sum),
          finiteConvolution (Finset.Icc (0 : ℤ) m)
            (hypergeometricIntWeight m) (squaredBinomialConvolution ms) z *
              (2 * (z : ℝ) - ((m + ms.sum : ℕ) : ℝ))) = 0
      rw [finiteConvolution_weighted_sum
        (f := hypergeometricIntWeight m)
        (g := squaredBinomialConvolution ms)
        (φ := fun z => 2 * (z : ℝ) - ((m + ms.sum : ℕ) : ℝ))
        (hgzero := fun z hz => squaredBinomialConvolution_eq_zero_of_notMem hz)]
      have hsplit (a b : ℤ) :
          2 * ((a + b : ℤ) : ℝ) - ((m + ms.sum : ℕ) : ℝ) =
            (2 * (a : ℝ) - (m : ℝ)) +
              (2 * (b : ℝ) - (ms.sum : ℝ)) := by
        push_cast
        ring
      have hsumChild := squaredBinomialConvolution_sum_one ms
      have hinner (a : ℤ) :
          (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
            squaredBinomialConvolution ms b *
              (2 * ((a + b : ℤ) : ℝ) - ((m + ms.sum : ℕ) : ℝ))) =
            (2 * (a : ℝ) - (m : ℝ)) := by
        calc
          _ = ∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                squaredBinomialConvolution ms b *
                  ((2 * (a : ℝ) - (m : ℝ)) +
                    (2 * (b : ℝ) - (ms.sum : ℝ))) := by
                apply Finset.sum_congr rfl
                intro b hb
                rw [hsplit]
          _ = (2 * (a : ℝ) - (m : ℝ)) *
                (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                  squaredBinomialConvolution ms b) +
              (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                squaredBinomialConvolution ms b *
                  (2 * (b : ℝ) - (ms.sum : ℝ))) := by
                calc
                  _ = ∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                        (squaredBinomialConvolution ms b *
                            (2 * (a : ℝ) - (m : ℝ)) +
                          squaredBinomialConvolution ms b *
                            (2 * (b : ℝ) - (ms.sum : ℝ))) := by
                          apply Finset.sum_congr rfl
                          intro b hb
                          ring
                  _ = _ := by
                    rw [Finset.sum_add_distrib, ← Finset.sum_mul]
                    ring
          _ = 2 * (a : ℝ) - (m : ℝ) := by
                rw [hsumChild, ih]
                ring
      calc
        _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
              hypergeometricIntWeight m a * (2 * (a : ℝ) - (m : ℝ)) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [hinner]
        _ = 0 := hypergeometricIntWeight_centered_firstMoment m

/-- The exact centered second moment of a finite squared-binomial convolution
is the sum of the component second moments. -/
theorem squaredBinomialConvolution_centered_secondMoment (ms : List ℕ) :
    (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
      squaredBinomialConvolution ms z *
        (2 * (z : ℝ) - (ms.sum : ℝ)) ^ 2) =
      (ms.map fun r => (r : ℝ) ^ 2 / (2 * (r : ℝ) - 1)).sum := by
  induction ms with
  | nil => simp [squaredBinomialConvolution, deltaCoeff]
  | cons m ms ih =>
      change
        (∑ z ∈ Finset.Icc (0 : ℤ) (m + ms.sum),
          finiteConvolution (Finset.Icc (0 : ℤ) m)
            (hypergeometricIntWeight m) (squaredBinomialConvolution ms) z *
              (2 * (z : ℝ) - ((m + ms.sum : ℕ) : ℝ)) ^ 2) = _
      rw [finiteConvolution_weighted_sum
        (f := hypergeometricIntWeight m)
        (g := squaredBinomialConvolution ms)
        (φ := fun z => (2 * (z : ℝ) - ((m + ms.sum : ℕ) : ℝ)) ^ 2)
        (hgzero := fun z hz => squaredBinomialConvolution_eq_zero_of_notMem hz)]
      let A : ℤ → ℝ := fun a => 2 * (a : ℝ) - (m : ℝ)
      let B : ℤ → ℝ := fun b => 2 * (b : ℝ) - (ms.sum : ℝ)
      have hsplit (a b : ℤ) :
          2 * ((a + b : ℤ) : ℝ) - ((m + ms.sum : ℕ) : ℝ) = A a + B b := by
        dsimp [A, B]
        push_cast
        ring
      have hsumChild := squaredBinomialConvolution_sum_one ms
      have hmeanChild := squaredBinomialConvolution_centered_firstMoment ms
      have hsecondChild := ih
      have hinner (a : ℤ) :
          (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
            squaredBinomialConvolution ms b *
              (2 * ((a + b : ℤ) : ℝ) - ((m + ms.sum : ℕ) : ℝ)) ^ 2) =
            A a ^ 2 *
                (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                  squaredBinomialConvolution ms b) +
              2 * A a *
                (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                  squaredBinomialConvolution ms b * B b) +
              (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                squaredBinomialConvolution ms b * B b ^ 2) := by
        calc
          _ = ∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                squaredBinomialConvolution ms b * (A a + B b) ^ 2 := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  rw [hsplit]
          _ = ∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                (squaredBinomialConvolution ms b * A a ^ 2 +
                  squaredBinomialConvolution ms b * (2 * A a * B b) +
                  squaredBinomialConvolution ms b * B b ^ 2) := by
                  apply Finset.sum_congr rfl
                  intro b hb
                  ring
          _ = (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                  squaredBinomialConvolution ms b * A a ^ 2) +
                (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                  squaredBinomialConvolution ms b * (2 * A a * B b)) +
                (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                  squaredBinomialConvolution ms b * B b ^ 2) := by
                  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          _ = _ := by
                have hA :
                    (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                      squaredBinomialConvolution ms b * A a ^ 2) =
                      A a ^ 2 * (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                        squaredBinomialConvolution ms b) := by
                  calc
                    _ = (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                          squaredBinomialConvolution ms b) * A a ^ 2 := by
                            rw [Finset.sum_mul]
                    _ = _ := by ring
                have hcross :
                    (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                      squaredBinomialConvolution ms b * (2 * A a * B b)) =
                      2 * A a *
                        (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                          squaredBinomialConvolution ms b * B b) := by
                  calc
                    _ = ∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                          (2 * A a) *
                            (squaredBinomialConvolution ms b * B b) := by
                              apply Finset.sum_congr rfl
                              intro b hb
                              ring
                    _ = _ := by rw [Finset.mul_sum]
                rw [hA, hcross]
      have hinner' (a : ℤ) :
          (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
            squaredBinomialConvolution ms b *
              (2 * ((a + b : ℤ) : ℝ) - ((m + ms.sum : ℕ) : ℝ)) ^ 2) =
            A a ^ 2 +
              (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                squaredBinomialConvolution ms b * B b ^ 2) := by
        rw [hinner a, hsumChild, hmeanChild]
        ring
      have hcomponent :
          (∑ a ∈ Finset.Icc (0 : ℤ) m,
            hypergeometricIntWeight m a * A a ^ 2) =
            (m : ℝ) ^ 2 / (2 * (m : ℝ) - 1) := by
        simpa [A] using hypergeometricIntWeight_centered_secondMoment m
      calc
        _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
              hypergeometricIntWeight m a *
                (A a ^ 2 +
                  (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                    squaredBinomialConvolution ms b * B b ^ 2)) := by
                apply Finset.sum_congr rfl
                intro a ha
                rw [hinner']
        _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
              (hypergeometricIntWeight m a * A a ^ 2 +
                hypergeometricIntWeight m a *
                  (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                    squaredBinomialConvolution ms b * B b ^ 2)) := by
                apply Finset.sum_congr rfl
                intro a ha
                ring
        _ = (∑ a ∈ Finset.Icc (0 : ℤ) m,
                hypergeometricIntWeight m a * A a ^ 2) +
              ∑ a ∈ Finset.Icc (0 : ℤ) m,
                hypergeometricIntWeight m a *
                  (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                    squaredBinomialConvolution ms b * B b ^ 2) := by
                rw [Finset.sum_add_distrib]
        _ = (m : ℝ) ^ 2 / (2 * (m : ℝ) - 1) +
              (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                squaredBinomialConvolution ms b * B b ^ 2) := by
                rw [hcomponent]
                have hfactor :
                    (∑ a ∈ Finset.Icc (0 : ℤ) m,
                      hypergeometricIntWeight m a) = 1 :=
                    sum_hypergeometricIntWeight m
                rw [← Finset.sum_mul, hfactor]
                ring
        _ = _ := by
              rw [hsecondChild]
              rfl

private theorem sum_map_natCast_div_two (ms : List ℕ) :
    (ms.map fun r => (r : ℝ) / 2).sum = (ms.sum : ℝ) / 2 := by
  induction ms with
  | nil => norm_num
  | cons r ms ih =>
      change (r : ℝ) / 2 + (ms.map fun s => (s : ℝ) / 2).sum =
        ((r + ms.sum : ℕ) : ℝ) / 2
      rw [ih]
      push_cast
      ring

private theorem sum_map_component_variance_lower (ms : List ℕ) :
    (ms.map fun r => (r : ℝ) / 2).sum ≤
      (ms.map fun r => (r : ℝ) ^ 2 / (2 * (r : ℝ) - 1)).sum := by
  have hcomponentLower : ∀ r : ℕ,
      (r : ℝ) / 2 ≤ (r : ℝ) ^ 2 / (2 * (r : ℝ) - 1) := by
    intro r
    by_cases hr0 : r = 0
    · subst r
      norm_num
    · have hrpos : 0 < (r : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hr0
      have hrone : 1 ≤ (r : ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr0)
      have hden : 0 < 2 * (r : ℝ) - 1 := by nlinarith
      apply (le_div_iff₀ hden).2
      nlinarith [hrone]
  induction ms with
  | nil => exact le_rfl
  | cons r ms ih =>
      change (r : ℝ) / 2 + (ms.map fun s => (s : ℝ) / 2).sum ≤
        (r : ℝ) ^ 2 / (2 * (r : ℝ) - 1) +
          (ms.map fun s => (s : ℝ) ^ 2 / (2 * (s : ℝ) - 1)).sum
      exact add_le_add (hcomponentLower r) ih

/-- The centered variance of a finite squared-binomial convolution is at least
one eighth of its total duration. -/
theorem squaredBinomialConvolution_centered_secondMoment_lower (ms : List ℕ) :
    (ms.sum : ℝ) / 8 ≤
      (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
        squaredBinomialConvolution ms z *
          ((z : ℝ) - (ms.sum : ℝ) / 2) ^ 2) := by
  have hsumLower := sum_map_component_variance_lower ms
  have hsumCast := sum_map_natCast_div_two ms
  have hdouble := squaredBinomialConvolution_centered_secondMoment ms
  have hscale :
      (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
        squaredBinomialConvolution ms z *
          (2 * (z : ℝ) - (ms.sum : ℝ)) ^ 2) =
      4 * (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
        squaredBinomialConvolution ms z *
          ((z : ℝ) - (ms.sum : ℝ) / 2) ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    ring
  rw [← hdouble, hscale] at hsumLower
  rw [hsumCast] at hsumLower
  nlinarith [hsumLower]

/-- A squared-binomial convolution is symmetric. -/
theorem squaredBinomialConvolution_symm (ms : List ℕ) (z : ℤ) :
    squaredBinomialConvolution ms ((ms.sum : ℕ) - z) =
      squaredBinomialConvolution ms z := by
  induction ms generalizing z with
  | nil =>
      simp [squaredBinomialConvolution, deltaCoeff]
  | cons m ms ih =>
      classical
      let s : Finset ℤ := Finset.Icc 0 m
      change finiteConvolution s (hypergeometricIntWeight m)
          (squaredBinomialConvolution ms) ((m + ms.sum : ℕ) - z) = _
      change finiteConvolution s (hypergeometricIntWeight m)
          (squaredBinomialConvolution ms) ((m + ms.sum : ℕ) - z) =
        finiteConvolution s (hypergeometricIntWeight m)
          (squaredBinomialConvolution ms) z
      unfold finiteConvolution
      have hbij : ∀ a ∈ s, m - a ∈ s := by
        intro a ha
        simp only [s, Finset.mem_Icc] at ha ⊢
        omega
      refine Finset.sum_bij (s := s) (t := s)
        (f := fun a => hypergeometricIntWeight m a *
          squaredBinomialConvolution ms ((m + ms.sum : ℕ) - z - a))
        (g := fun b => hypergeometricIntWeight m b *
          squaredBinomialConvolution ms (z - b))
        (fun a _ => m - a) ?_ ?_ ?_ ?_
      · intro a ha
        exact hbij a ha
      · intro a ha b hb hab
        omega
      · intro b hb
        refine ⟨m - b, hbij b hb, ?_⟩
        omega
      · intro a ha
        rw [hypergeometricIntWeight_symm]
        have harg : (m + ms.sum : ℕ) - z - a =
            (ms.sum : ℤ) - (z - ((m : ℤ) - a)) := by push_cast; ring
        rw [harg, ih]

end Critical2DKPZ.WalkTails

end
