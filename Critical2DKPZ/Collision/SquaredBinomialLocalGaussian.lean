/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.WalkTails.LogConcavity
public import Critical2DKPZ.WalkTails.SquaredBinomialMGF
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Int.Interval
public import Critical2DKPZ.WalkTails.SymmetricMaxAtom
import Mathlib.Tactic

/-! # A composition-uniform local Gaussian bound for squared-binomial laws -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.Collision

open Critical2DKPZ.WalkTails

private def squaredBinomialGaussianDecay : ℝ := min ((1 / 6 : ℝ) / 32) 1

private def squaredBinomialGaussianAmplitude : ℝ :=
  Real.sqrt (487 * 8 : ℝ) * Real.exp (16 * squaredBinomialGaussianDecay) + 2

private def squaredBinomialGaussianFinalDecay : ℝ := squaredBinomialGaussianDecay / 8

private def squaredBinomialGaussianFinalAmplitude : ℝ :=
  squaredBinomialGaussianAmplitude * Real.exp (squaredBinomialGaussianDecay / 8)

private theorem shiftedSquareExponent_le (k : ℕ) (d : ℝ) (hd : 0 ≤ d) :
    (d / 8) * (2 * (k : ℝ) + 1) ^ 2 - d * (k : ℝ) ^ 2 ≤ d / 8 := by
  by_cases hk0 : k = 0
  · have hkR : (k : ℝ) = 0 := by exact_mod_cast hk0
    rw [hkR]
    nlinarith
  · have hk1 : 1 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk0)
    have hkRnonneg : 0 ≤ (k : ℝ) := by positivity
    have hprod : 0 ≤ (k : ℝ) * ((k : ℝ) - 1) :=
      mul_nonneg hkRnonneg (by linarith)
    have hpoly : (2 * (k : ℝ) + 1) ^ 2 - 8 * (k : ℝ) ^ 2 ≤ 1 := by
      nlinarith [hprod]
    have hd8 : 0 ≤ d / 8 := by positivity
    have hmul := mul_le_mul_of_nonneg_left hpoly hd8
    nlinarith [hmul]

private theorem sum_Icc_translate_of_supported_local {m n : ℕ} {a : ℤ}
    (ha : a ∈ Finset.Icc (0 : ℤ) m) (f : ℤ → ℝ)
    (hfzero : ∀ z, z ∉ Finset.Icc (0 : ℤ) n → f z = 0) :
    (∑ z ∈ Finset.Icc (0 : ℤ) (m + n), f (z - a)) =
      ∑ z ∈ Finset.Icc (0 : ℤ) n, f z := by
  classical
  let s : Finset ℤ := Finset.Icc (0 : ℤ) (m + n)
  let t : Finset ℤ := Finset.Icc (-a) ((m + n : ℕ) - a)
  have hmem : ∀ z ∈ s, z - a ∈ t := by
    intro z hz
    have haz := Finset.mem_Icc.mp ha
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

private theorem sum_int_interval_eq_sum_range_local (m : ℕ) (f : ℤ → ℝ) :
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

private theorem squaredBinomialConvolution_weighted_sum {m n : ℕ}
    (f g φ : ℤ → ℝ)
    (hgzero : ∀ z, z ∉ Finset.Icc (0 : ℤ) n → g z = 0) :
    (∑ z ∈ Finset.Icc (0 : ℤ) (m + n),
      WalkTails.finiteConvolution (Finset.Icc (0 : ℤ) m) f g z * φ z) =
      ∑ a ∈ Finset.Icc (0 : ℤ) m,
        f a * ∑ b ∈ Finset.Icc (0 : ℤ) n, g b * φ (a + b) := by
  classical
  unfold WalkTails.finiteConvolution
  calc
    _ = ∑ z ∈ Finset.Icc (0 : ℤ) (m + n),
          ∑ a ∈ Finset.Icc (0 : ℤ) m, f a * (g (z - a) * φ z) := by
              apply Finset.sum_congr rfl
              intro z hz
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro a ha
              ring
    _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
          ∑ z ∈ Finset.Icc (0 : ℤ) (m + n), f a * (g (z - a) * φ z) := by
              rw [Finset.sum_comm]
    _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
          f a * ∑ z ∈ Finset.Icc (0 : ℤ) (m + n), g (z - a) * φ z := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
    _ = ∑ a ∈ Finset.Icc (0 : ℤ) m,
          f a * ∑ b ∈ Finset.Icc (0 : ℤ) n, g b * φ (a + b) := by
              apply Finset.sum_congr rfl
              intro a ha
              have htranslate := sum_Icc_translate_of_supported_local
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
                      g b * φ (a + b) := by
                        simpa [add_comm] using htranslate

private theorem squaredBinomialConvolution_oneStep_expMoment_le
    (m : ℕ) (t : ℝ) :
    (∑ z ∈ Finset.Icc (0 : ℤ) m,
      WalkTails.hypergeometricIntWeight m z *
        Real.exp (t * (2 * (z : ℝ) - (m : ℝ)))) ≤
      Real.exp ((3 / 2 : ℝ) * (m : ℝ) * t ^ 2) := by
  have hsum :
      (∑ z ∈ Finset.Icc (0 : ℤ) m,
        WalkTails.hypergeometricIntWeight m z *
          Real.exp (t * (2 * (z : ℝ) - (m : ℝ)))) =
      ∑ j ∈ Finset.range (m + 1),
        WalkTails.hypergeometricWeight m j *
          Real.exp (t * WalkTails.hypergeometricIncrement m j) := by
    rw [sum_int_interval_eq_sum_range_local]
    apply Finset.sum_congr rfl
    intro j hj
    rw [WalkTails.hypergeometricIntWeight_eq_nat]
    simp [WalkTails.hypergeometricIncrement]
  rw [hsum]
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    WalkTails.hypergeometricExpMoment_le m t

private theorem squaredBinomialConvolution_expMoment_le
    (ms : List ℕ) (t : ℝ) :
    (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
      WalkTails.squaredBinomialConvolution ms z *
        Real.exp (t * (2 * (z : ℝ) - (ms.sum : ℝ)))) ≤
      Real.exp ((3 / 2 : ℝ) * (ms.sum : ℝ) * t ^ 2) := by
  classical
  induction ms with
  | nil =>
      simp [WalkTails.squaredBinomialConvolution, WalkTails.deltaCoeff]
  | cons m ms ih =>
      rw [show (m :: ms).sum = m + ms.sum by simp]
      change (∑ z ∈ Finset.Icc (0 : ℤ) (m + ms.sum),
        WalkTails.finiteConvolution (Finset.Icc (0 : ℤ) m)
          (WalkTails.hypergeometricIntWeight m)
          (WalkTails.squaredBinomialConvolution ms) z *
          Real.exp (t * (2 * (z : ℝ) - ((m + ms.sum : ℕ) : ℝ)))) ≤ _
      rw [squaredBinomialConvolution_weighted_sum
        (m := m) (n := ms.sum)
        (WalkTails.hypergeometricIntWeight m)
        (WalkTails.squaredBinomialConvolution ms)
        (fun z => Real.exp (t * (2 * (z : ℝ) - ((m + ms.sum : ℕ) : ℝ))))
        (fun z hz => WalkTails.squaredBinomialConvolution_eq_zero_of_notMem hz)]
      calc
        (∑ a ∈ Finset.Icc (0 : ℤ) m,
          WalkTails.hypergeometricIntWeight m a *
            ∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
              WalkTails.squaredBinomialConvolution ms b *
                Real.exp (t * (2 * ((a + b : ℤ) : ℝ) -
                  ((m + ms.sum : ℕ) : ℝ)))) ≤
          ∑ a ∈ Finset.Icc (0 : ℤ) m,
            WalkTails.hypergeometricIntWeight m a *
              (Real.exp (t * (2 * (a : ℝ) - (m : ℝ))) *
                Real.exp ((3 / 2 : ℝ) * (ms.sum : ℝ) * t ^ 2)) := by
                apply Finset.sum_le_sum
                intro a ha
                apply mul_le_mul_of_nonneg_left _
                  (WalkTails.hypergeometricIntWeight_nonneg m a)
                calc
                  (∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                      WalkTails.squaredBinomialConvolution ms b *
                        Real.exp (t * (2 * ((a + b : ℤ) : ℝ) -
                          ((m + ms.sum : ℕ) : ℝ)))) =
                    ∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                      Real.exp (t * (2 * (a : ℝ) - (m : ℝ))) *
                        (WalkTails.squaredBinomialConvolution ms b *
                          Real.exp (t * (2 * (b : ℝ) - (ms.sum : ℝ)))) := by
                            apply Finset.sum_congr rfl
                            intro b hb
                            have he : Real.exp (t * (2 * ((a + b : ℤ) : ℝ) -
                                ((m + ms.sum : ℕ) : ℝ))) =
                                Real.exp (t * (2 * (a : ℝ) - (m : ℝ))) *
                                  Real.exp (t * (2 * (b : ℝ) - (ms.sum : ℝ))) := by
                              rw [← Real.exp_add]
                              congr 1
                              push_cast
                              ring
                            rw [he]
                            ring
                  _ = Real.exp (t * (2 * (a : ℝ) - (m : ℝ))) *
                      ∑ b ∈ Finset.Icc (0 : ℤ) ms.sum,
                        WalkTails.squaredBinomialConvolution ms b *
                          Real.exp (t * (2 * (b : ℝ) - (ms.sum : ℝ))) := by
                            rw [Finset.mul_sum]
                  _ ≤ Real.exp (t * (2 * (a : ℝ) - (m : ℝ))) *
                      Real.exp ((3 / 2 : ℝ) * (ms.sum : ℝ) * t ^ 2) :=
                    mul_le_mul_of_nonneg_left (ih) (le_of_lt (Real.exp_pos _))
        _ = Real.exp ((3 / 2 : ℝ) * (ms.sum : ℝ) * t ^ 2) *
              ∑ a ∈ Finset.Icc (0 : ℤ) m,
                WalkTails.hypergeometricIntWeight m a *
                  Real.exp (t * (2 * (a : ℝ) - (m : ℝ))) := by
                calc
                  _ = (∑ a ∈ Finset.Icc (0 : ℤ) m,
                      WalkTails.hypergeometricIntWeight m a *
                        Real.exp (t * (2 * (a : ℝ) - (m : ℝ)))) *
                        Real.exp ((3 / 2 : ℝ) * (ms.sum : ℝ) * t ^ 2) := by
                          rw [Finset.sum_mul]
                          apply Finset.sum_congr rfl
                          intro a ha
                          ring
                  _ = _ := by ring
        _ ≤ Real.exp ((3 / 2 : ℝ) * (ms.sum : ℝ) * t ^ 2) *
              Real.exp ((3 / 2 : ℝ) * (m : ℝ) * t ^ 2) :=
                mul_le_mul_of_nonneg_left (squaredBinomialConvolution_oneStep_expMoment_le m t)
                  (le_of_lt (Real.exp_pos _))
        _ = Real.exp ((3 / 2 : ℝ) * (m + ms.sum : ℕ) * t ^ 2) := by
              rw [← Real.exp_add]
              congr 1
              push_cast
              ring

private theorem squaredBinomialConvolution_upperTail_le
    (ms : List ℕ) (hn : 0 < ms.sum) (r : ℝ) (hr : 0 ≤ r) :
    (∑ z ∈ (Finset.Icc (0 : ℤ) ms.sum).filter
      (fun (z : ℤ) => r ≤ 2 * (z : ℝ) - (ms.sum : ℝ)),
      squaredBinomialConvolution ms z) ≤
      Real.exp (-r ^ 2 / (6 * (ms.sum : ℝ))) := by
  have hV : 0 < 3 * (ms.sum : ℝ) := by positivity
  have h := finite_exp_upperTail_le
    (Finset.Icc (0 : ℤ) ms.sum) (squaredBinomialConvolution ms)
    (fun z => 2 * (z : ℝ) - (ms.sum : ℝ))
    (3 * (ms.sum : ℝ)) r hV hr
    (fun z hz => squaredBinomialConvolution_nonneg ms z)
    (fun t => by
      calc
        (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
          squaredBinomialConvolution ms z *
            Real.exp (t * (2 * (z : ℝ) - (ms.sum : ℝ)))) ≤
            Real.exp ((3 / 2 : ℝ) * (ms.sum : ℝ) * t ^ 2) :=
              squaredBinomialConvolution_expMoment_le ms t
        _ = Real.exp ((3 * (ms.sum : ℝ)) * t ^ 2 / 2) := by
              congr 1
              ring)
  simpa only [show 2 * (3 * (ms.sum : ℝ)) = 6 * (ms.sum : ℝ) by ring] using h


private theorem sum_Icc_nat_shift_to_int_local {r N a : ℕ} (f : ℤ → ℝ) :
    (∑ k ∈ Finset.Icc r N, f ((a + k : ℕ) : ℤ)) =
      ∑ z ∈ Finset.Icc ((a + r : ℕ) : ℤ) ((a + N : ℕ) : ℤ), f z := by
  classical
  refine Finset.sum_bij (s := Finset.Icc r N)
    (t := Finset.Icc ((a + r : ℕ) : ℤ) ((a + N : ℕ) : ℤ))
    (fun k _ => ((a + k : ℕ) : ℤ)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    constructor <;> exact_mod_cast (by omega)
  · intro k hk k' hk' hEq
    have hNat : a + k = a + k' := by exact_mod_cast hEq
    omega
  · intro z hz
    have hz0 : 0 ≤ z := by
      have := (Finset.mem_Icc.mp hz).1
      exact le_trans (by exact_mod_cast Nat.zero_le (a + r)) this
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    have hzlo : a + r ≤ z.toNat := by
      have hzlo' : ((a + r : ℕ) : ℤ) ≤ z := (Finset.mem_Icc.mp hz).1
      have hzlo'' : ((a : ℤ) + (r : ℤ)) ≤ z := by simpa using hzlo'
      have hzloInt : ((a + r : ℕ) : ℤ) ≤ ((z.toNat : ℕ) : ℤ) := by
        simpa [Nat.cast_add, hzcast] using hzlo''
      exact_mod_cast hzloInt
    have hzhi : z.toNat ≤ a + N := by
      have hzhi' : z ≤ ((a + N : ℕ) : ℤ) := (Finset.mem_Icc.mp hz).2
      exact_mod_cast (by simpa [hzcast] using hzhi')
    refine ⟨z.toNat - a, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · have hnat : a + (z.toNat - a) = z.toNat := by omega
      rw [hnat, hzcast]
  · intro k hk
    rfl

private theorem sum_int_Icc_eq_range_local (N : ℕ) (f : ℤ → ℝ) :
    (∑ z ∈ Finset.Icc (0 : ℤ) N, f z) =
      ∑ j ∈ Finset.range (N + 1), f (j : ℤ) := by
  classical
  symm
  apply Finset.sum_bij (s := Finset.range (N + 1))
    (t := Finset.Icc (0 : ℤ) N) (fun j _ => (j : ℤ))
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
    have hzN : z ≤ (N : ℤ) := (Finset.mem_Icc.mp hz).2
    have hzcast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
    have hzNat : z.toNat ≤ N := by
      have h : (z.toNat : ℤ) ≤ N := by simpa [hzcast] using hzN
      exact_mod_cast h
    exact ⟨z.toNat, Finset.mem_range.mpr (Nat.lt_succ_of_le hzNat), hzcast⟩
  · intro j hj
    rfl

private theorem symmetricEven_range_sum_local (N : ℕ) (f : ℤ → ℝ)
    (hsymm : ∀ z, f ((2 * N : ℕ) - z) = f z) :
    (∑ j ∈ Finset.range (2 * N + 1), f (j : ℤ)) =
      f (N : ℤ) + 2 * (∑ k ∈ Finset.range N,
        f ((N + k + 1 : ℕ) : ℤ)) := by
  classical
  let g : ℕ → ℝ := fun j => f (j : ℤ)
  have hsplit : 2 * N + 1 = (N + 1) + N := by omega
  have hsplitSum :
      (∑ j ∈ Finset.range (2 * N + 1), g j) =
        (∑ j ∈ Finset.range (N + 1), g j) +
          ∑ k ∈ Finset.range N, g (N + 1 + k) := by
    rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ j ∈ Finset.range (N + 1), g j) =
        (∑ k ∈ Finset.range N, g k) + g N := by
    rw [Finset.sum_range_succ]
  have hmirror :
      (∑ k ∈ Finset.range N, g k) =
        ∑ k ∈ Finset.range N, g (N + 1 + k) := by
    apply Finset.sum_bij (s := Finset.range N) (t := Finset.range N)
      (fun j _ => N - 1 - j)
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi j hj hij
      simp only [Finset.mem_range] at hi hj
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      exact ⟨N - 1 - k, by omega, by omega⟩
    · intro j hj
      have hjlt : j < N := Finset.mem_range.mp hj
      have hidx : N + 1 + (N - 1 - j) = 2 * N - j := by omega
      have hidx' : ((N + 1 + (N - 1 - j) : ℕ) : ℤ) =
          (2 * N : ℕ) - (j : ℤ) := by
        push_cast
        omega
      change f (j : ℤ) = f ((N + 1 + (N - 1 - j : ℕ) : ℕ) : ℤ)
      rw [hidx']
      exact (hsymm (j : ℤ)).symm
  rw [hsplitSum, hfirst, hmirror]
  simp only [g]
  ring_nf

private theorem symmetricOdd_range_sum_local (N : ℕ) (f : ℤ → ℝ)
    (hsymm : ∀ z, f ((2 * N + 1 : ℕ) - z) = f z) :
    (∑ j ∈ Finset.range (2 * N + 2), f (j : ℤ)) =
      2 * (∑ k ∈ Finset.range (N + 1), f ((N + k + 1 : ℕ) : ℤ)) := by
  classical
  let g : ℕ → ℝ := fun j => f (j : ℤ)
  have hsplit : 2 * N + 2 = (N + 1) + (N + 1) := by omega
  have hsplitSum :
      (∑ j ∈ Finset.range (2 * N + 2), g j) =
        (∑ j ∈ Finset.range (N + 1), g j) +
          ∑ k ∈ Finset.range (N + 1), g (N + 1 + k) := by
    rw [hsplit, Finset.sum_range_add]
  have hmirror :
      (∑ j ∈ Finset.range (N + 1), g j) =
        ∑ k ∈ Finset.range (N + 1), g (N + 1 + k) := by
    apply Finset.sum_bij (s := Finset.range (N + 1)) (t := Finset.range (N + 1))
      (fun j _ => N - j)
    · intro j hj
      simp only [Finset.mem_range] at hj ⊢
      omega
    · intro i hi j hj hij
      simp only [Finset.mem_range] at hi hj
      omega
    · intro k hk
      simp only [Finset.mem_range] at hk ⊢
      exact ⟨N - k, by omega, by omega⟩
    · intro j hj
      have hjle : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hidx : N + 1 + (N - j) = 2 * N + 1 - j := by omega
      have hidx' : ((N + 1 + (N - j) : ℕ) : ℤ) =
          (2 * N + 1 : ℕ) - (j : ℤ) := by
        push_cast
        omega
      change f (j : ℤ) = f ((N + 1 + (N - j) : ℕ) : ℤ)
      rw [hidx']
      exact (hsymm (j : ℤ)).symm
  rw [hsplitSum, hmirror]
  simp only [g]
  ring_nf

private theorem squaredBinomial_even_moment_profile_eq
    (ms : List ℕ) (N : ℕ) (hN : ms.sum = 2 * N) :
    (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
      squaredBinomialConvolution ms z * ((z : ℝ) - (N : ℝ)) ^ 2) =
      2 * (∑ k ∈ Finset.range N,
        ((k + 1 : ℕ) : ℝ) ^ 2 *
          squaredBinomialConvolution ms ((N + k + 1 : ℕ) : ℤ)) := by
  let g : ℤ → ℝ := fun z =>
    squaredBinomialConvolution ms z * ((z : ℝ) - (N : ℝ)) ^ 2
  have hsymm : ∀ z, g ((2 * N : ℕ) - z) = g z := by
    intro z
    dsimp [g]
    have hf := squaredBinomialConvolution_symm ms z
    rw [hN] at hf
    push_cast at hf
    rw [hf]
    push_cast
    ring
  have hsum :
      (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum, g z) =
        ∑ j ∈ Finset.range (2 * N + 1), g (j : ℤ) := by
    simpa [hN, g] using sum_int_Icc_eq_range_local (2 * N) g
  calc
    _ = ∑ j ∈ Finset.range (2 * N + 1), g (j : ℤ) := hsum
    _ = g (N : ℤ) + 2 * (∑ k ∈ Finset.range N,
          g ((N + k + 1 : ℕ) : ℤ)) := symmetricEven_range_sum_local N g hsymm
    _ = 2 * (∑ k ∈ Finset.range N,
          ((k + 1 : ℕ) : ℝ) ^ 2 *
            squaredBinomialConvolution ms ((N + k + 1 : ℕ) : ℤ)) := by
          rw [show g (N : ℤ) = 0 by simp [g]]
          simp only [zero_add]
          apply congrArg (fun x : ℝ => 2 * x)
          apply Finset.sum_congr rfl
          intro k hk
          simp only [g]
          push_cast
          ring

private theorem squaredBinomial_odd_moment_profile_eq
    (ms : List ℕ) (N : ℕ) (hN : ms.sum = 2 * N + 1) :
    (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
      squaredBinomialConvolution ms z *
        ((z : ℝ) - (ms.sum : ℝ) / 2) ^ 2) =
      2 * (∑ k ∈ Finset.range (N + 1),
        ((k : ℝ) + 1 / 2) ^ 2 *
          squaredBinomialConvolution ms ((N + k + 1 : ℕ) : ℤ)) := by
  let g : ℤ → ℝ := fun z =>
    squaredBinomialConvolution ms z * ((z : ℝ) - (ms.sum : ℝ) / 2) ^ 2
  have hsymm : ∀ z, g ((2 * N + 1 : ℕ) - z) = g z := by
    intro z
    dsimp [g]
    have hf := squaredBinomialConvolution_symm ms z
    rw [hN] at hf
    push_cast at hf
    rw [hf]
    rw [hN]
    push_cast
    ring
  have hsum :
      (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum, g z) =
        ∑ j ∈ Finset.range (2 * N + 2), g (j : ℤ) := by
    simpa [hN, g] using sum_int_Icc_eq_range_local (2 * N + 1) g
  calc
    _ = ∑ j ∈ Finset.range (2 * N + 2), g (j : ℤ) := hsum
    _ = 2 * (∑ k ∈ Finset.range (N + 1),
          g ((N + k + 1 : ℕ) : ℤ)) := symmetricOdd_range_sum_local N g hsymm
    _ = 2 * (∑ k ∈ Finset.range (N + 1),
          ((k : ℝ) + 1 / 2) ^ 2 *
            squaredBinomialConvolution ms ((N + k + 1 : ℕ) : ℤ)) := by
          apply congrArg (fun x : ℝ => 2 * x)
          apply Finset.sum_congr rfl
          intro k hk
          simp only [g]
          rw [hN]
          push_cast
          ring

private theorem squaredBinomialConvolution_upperInterval_even_le
    (ms : List ℕ) (N r : ℕ) (hN : ms.sum = 2 * N)
    (hr : 1 ≤ r) (hrN : r ≤ N) :
    (∑ z ∈ Finset.Icc ((N + r : ℕ) : ℤ) ((2 * N : ℕ) : ℤ),
      squaredBinomialConvolution ms z) ≤
      Real.exp (-((2 * (r : ℝ)) ^ 2) / (6 * (ms.sum : ℝ))) := by
  have hfilter :
      (Finset.Icc (0 : ℤ) ms.sum).filter
        (fun (z : ℤ) => 2 * (r : ℝ) ≤ 2 * (z : ℝ) - (ms.sum : ℝ)) =
        Finset.Icc ((N + r : ℕ) : ℤ) ((2 * N : ℕ) : ℤ) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [hN]
    push_cast
    constructor
    · rintro ⟨⟨hz0, hzn⟩, hthr⟩
      have hthr' : 2 * (r : ℤ) ≤ 2 * z - 2 * (N : ℤ) := by exact_mod_cast hthr
      constructor <;> omega
    · rintro ⟨hlo, hhi⟩
      constructor
      · constructor <;> omega
      · exact_mod_cast (show 2 * (r : ℤ) ≤ 2 * z - 2 * (N : ℤ) by omega)
  have hn : 0 < ms.sum := by rw [hN]; omega
  have htail := squaredBinomialConvolution_upperTail_le ms
    hn (2 * (r : ℝ)) (by positivity)
  rw [← hfilter]
  simpa [hN] using htail

private theorem squaredBinomialConvolution_upperInterval_odd_le
    (ms : List ℕ) (N r : ℕ) (hN : ms.sum = 2 * N + 1) :
    (∑ z ∈ Finset.Icc ((N + r + 1 : ℕ) : ℤ) ((2 * N + 1 : ℕ) : ℤ),
      squaredBinomialConvolution ms z) ≤
      Real.exp (-((2 * (r : ℝ) + 1) ^ 2) / (6 * (ms.sum : ℝ))) := by
  have hfilter :
      (Finset.Icc (0 : ℤ) ms.sum).filter
        (fun (z : ℤ) => 2 * (r : ℝ) + 1 ≤ 2 * (z : ℝ) - (ms.sum : ℝ)) =
        Finset.Icc ((N + r + 1 : ℕ) : ℤ) ((2 * N + 1 : ℕ) : ℤ) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_Icc]
    rw [hN]
    push_cast
    constructor
    · rintro ⟨⟨hz0, hzn⟩, hthr⟩
      have hthr' : 2 * (r : ℤ) + 1 ≤ 2 * z - (2 * (N : ℤ) + 1) := by
        exact_mod_cast hthr
      constructor <;> omega
    · rintro ⟨hlo, hhi⟩
      constructor
      · constructor <;> omega
      · exact_mod_cast (show 2 * (r : ℤ) + 1 ≤ 2 * z - (2 * (N : ℤ) + 1) by omega)
  have hn : 0 < ms.sum := by rw [hN]; positivity
  have htail := squaredBinomialConvolution_upperTail_le ms
    hn (2 * (r : ℝ) + 1) (by positivity)
  rw [← hfilter]
  simpa [hN] using htail

private theorem sum_Icc_mul_le_sum_of_antitone_local {R r k : ℕ} (f : ℕ → ℝ)
    (hkR : k ≤ R)
    (hmono : ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ R → f j ≤ f i) :
    ((Finset.Icc r k).card : ℝ) * f k ≤ ∑ j ∈ Finset.Icc r k, f j := by
  calc
    ((Finset.Icc r k).card : ℝ) * f k = ∑ j ∈ Finset.Icc r k, f k := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.Icc r k, f j := Finset.sum_le_sum fun j hj =>
      hmono (Finset.mem_Icc.mp hj).2 hkR

private theorem icc_card_double_ge_local {r k : ℕ}
    (hr : r = k / 2) : k ≤ 2 * (Finset.Icc r k).card := by
  rw [hr]
  simp
  omega

private theorem finite_radial_localGaussian_explicit
    {R n : ℕ} (f : ℕ → ℝ) (A B b : ℝ)
    (hn : 0 < n) (hA : 0 < A) (hB : 0 ≤ B) (hb : 0 < b)
    (hnonneg : ∀ k ≤ R, 0 ≤ f k)
    (hmono : ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ R → f j ≤ f i)
    (hatom : ∀ k ≤ R, f k ≤ A / Real.sqrt (n : ℝ))
    (htail : ∀ r ≤ R, 1 ≤ r →
      2 * (∑ j ∈ Finset.Icc r R, f j) ≤
        B * Real.exp (-b * (r : ℝ) ^ 2 / (n : ℝ))) :
    let c : ℝ := min (b / 32) 1
    let C : ℝ := A * Real.exp (16 * c) + B
    0 < C ∧ 0 < c ∧ ∀ k ≤ R,
      f k ≤ C / Real.sqrt (n : ℝ) *
        Real.exp (-c * (k : ℝ) ^ 2 / (n : ℝ)) := by
  let c : ℝ := min (b / 32) 1
  let C : ℝ := A * Real.exp (16 * c) + B
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hcB : c ≤ b / 16 := by
    dsimp [c]
    have hmin : min (b / 32) 1 ≤ b / 32 := min_le_left _ _
    linarith
  refine ⟨hCpos, hcpos, ?_⟩
  intro k hkR
  by_cases hsmall : (k : ℝ) ^ 2 ≤ 16 * (n : ℝ)
  · have hsmallExp :
        Real.exp (-c * (k : ℝ) ^ 2 / (n : ℝ)) ≥ Real.exp (-16 * c) := by
      apply Real.exp_le_exp.mpr
      apply (le_div_iff₀ (by exact_mod_cast hn : (0 : ℝ) < n)).2
      have hmul := mul_le_mul_of_nonneg_left hsmall hcpos.le
      nlinarith
    have hAtom := hatom k hkR
    have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have hscale : A / Real.sqrt (n : ℝ) ≤
        C / Real.sqrt (n : ℝ) * Real.exp (-c * (k : ℝ) ^ 2 / (n : ℝ)) := by
      have heq : Real.exp (16 * c) * Real.exp (-16 * c) = 1 := by
        rw [← Real.exp_add]
        calc
          Real.exp (16 * c + -16 * c) = Real.exp 0 := by congr 1; ring
          _ = 1 := Real.exp_zero
      have hprod : A ≤ C * Real.exp (-16 * c) := by
        dsimp [C]
        calc
          A = A * 1 := by ring
          _ = A * (Real.exp (16 * c) * Real.exp (-16 * c)) := by rw [heq]
          _ = A * Real.exp (16 * c) * Real.exp (-16 * c) := by ring
          _ ≤ (A * Real.exp (16 * c) + B) * Real.exp (-16 * c) := by
            have hterm : 0 ≤ B * Real.exp (-16 * c) :=
              mul_nonneg hB (le_of_lt (Real.exp_pos _))
            nlinarith
      have hscaledExp := mul_le_mul_of_nonneg_left hsmallExp
        (div_nonneg (le_of_lt hCpos) hsqrt.le)
      calc
        A / Real.sqrt (n : ℝ) = A * (Real.sqrt (n : ℝ))⁻¹ := by rw [div_eq_mul_inv]
        _ ≤ C * Real.exp (-16 * c) * (Real.sqrt (n : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hprod (inv_nonneg.mpr hsqrt.le)
        _ = C / Real.sqrt (n : ℝ) * Real.exp (-16 * c) := by
          rw [div_eq_mul_inv]
          ring
        _ ≤ C / Real.sqrt (n : ℝ) *
            Real.exp (-c * (k : ℝ) ^ 2 / (n : ℝ)) := hscaledExp
    exact hAtom.trans hscale
  · have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hklarge : 4 ≤ k := by
      by_contra h
      have hklt : k < 4 := by omega
      have hkltR : (k : ℝ) < 4 := by exact_mod_cast hklt
      have hlarge : 16 * (n : ℝ) < (k : ℝ) ^ 2 := lt_of_not_ge hsmall
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.one_le_of_lt hn)
      nlinarith
    let r := k / 2
    have hrpos : 1 ≤ r := by dsimp [r]; omega
    have hrle : r ≤ R := by dsimp [r]; omega
    have hsumLower := sum_Icc_mul_le_sum_of_antitone_local (r := r) f hkR hmono
    have hcard := icc_card_double_ge_local (r := r) (k := k) rfl
    have hsubset : Finset.Icc r k ⊆ Finset.Icc r R := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
        (Finset.mem_Icc.mp hj).2.trans hkR⟩
    have hsumSub := Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun j hj _ =>
      hnonneg j (Finset.mem_Icc.mp hj).2)
    have htail' := htail r hrle hrpos
    have hpoint : (k : ℝ) * f k ≤
        B * Real.exp (-b * (r : ℝ) ^ 2 / (n : ℝ)) := by
      have hcardR : (k : ℝ) ≤ 2 * (Finset.Icc r k).card := by exact_mod_cast hcard
      have hfnonneg := hnonneg k hkR
      calc
        (k : ℝ) * f k ≤ (2 * (Finset.Icc r k).card) * f k :=
          mul_le_mul_of_nonneg_right hcardR hfnonneg
        _ ≤ 2 * (∑ j ∈ Finset.Icc r k, f j) := by nlinarith [hsumLower]
        _ ≤ 2 * (∑ j ∈ Finset.Icc r R, f j) := by nlinarith [hsumSub]
        _ ≤ _ := htail'
    have hrLower : (k : ℝ) / 4 ≤ (r : ℝ) := by
      dsimp [r]
      have hmod := Nat.mod_lt k (by norm_num : 0 < 2)
      have hdecomp := Nat.mod_add_div k 2
      have hcast : ((k % 2 : ℕ) : ℝ) + 2 * ((k / 2 : ℕ) : ℝ) = k := by
        exact_mod_cast hdecomp
      have hrem : ((k % 2 : ℕ) : ℝ) < 2 := by exact_mod_cast hmod
      have hkR' : (4 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hklarge
      nlinarith [hcast, hrem, hkR']
    have hexpSmall :
        Real.exp (-b * (r : ℝ) ^ 2 / (n : ℝ)) ≤
          Real.exp (-c * (k : ℝ) ^ 2 / (n : ℝ)) := by
      apply Real.exp_le_exp.mpr
      have hr2 : ((k : ℝ) / 4) ^ 2 ≤ (r : ℝ) ^ 2 := by
        nlinarith [hrLower, (sq_nonneg ((k : ℝ) / 4))]
      apply (div_le_div_iff₀ hnR hnR).2
      have hmul := mul_le_mul_of_nonneg_left hr2 hb.le
      have hcscaled := mul_le_mul_of_nonneg_right hcB (sq_nonneg (k : ℝ))
      nlinarith
    have hkLargeReal : Real.sqrt (n : ℝ) ≤ k := by
      apply Real.sqrt_le_iff.mpr
      constructor
      · positivity
      · have hlarge : 16 * (n : ℝ) < (k : ℝ) ^ 2 := lt_of_not_ge hsmall
        nlinarith
    have hkposR : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hklarge)
    have hfbound : f k ≤ B / (k : ℝ) *
        Real.exp (-b * (r : ℝ) ^ 2 / (n : ℝ)) := by
      have hdiv : f k ≤
          (B * Real.exp (-b * (r : ℝ) ^ 2 / (n : ℝ))) / (k : ℝ) := by
        apply (le_div_iff₀ hkposR).2
        simpa [mul_comm] using hpoint
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv
    have hrecip : (k : ℝ)⁻¹ ≤ (Real.sqrt (n : ℝ))⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le (Real.sqrt_pos.mpr hnR) hkLargeReal
    have hfinal : f k ≤ B / Real.sqrt (n : ℝ) *
        Real.exp (-c * (k : ℝ) ^ 2 / (n : ℝ)) := by
      calc
        f k ≤ B / (k : ℝ) *
            Real.exp (-b * (r : ℝ) ^ 2 / (n : ℝ)) := hfbound
        _ ≤ B / Real.sqrt (n : ℝ) *
            Real.exp (-c * (k : ℝ) ^ 2 / (n : ℝ)) := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hrecip hB
              · exact hexpSmall
              · positivity
              · positivity
    have hC : B ≤ C := by
      dsimp [C]
      have hterm : 0 ≤ A * Real.exp (16 * c) := mul_nonneg hA.le (Real.exp_nonneg _)
      linarith
    have hscale : B / Real.sqrt (n : ℝ) *
        Real.exp (-c * (k : ℝ) ^ 2 / (n : ℝ)) ≤
        C / Real.sqrt (n : ℝ) *
          Real.exp (-c * (k : ℝ) ^ 2 / (n : ℝ)) := by
      gcongr
    exact hfinal.trans hscale

private theorem finite_symmetricProfile_localGaussian_explicit
    {N n : ℕ} (p : ℕ → ℝ) (M : ℝ)
    (hn : 0 < n) (hM : 0 < M) (hp0 : p 0 = M)
    (hpos : ∀ k ≤ N, 0 < p k) (hzero : ∀ k, N < k → p k = 0)
    (hcenter : p 1 ≤ p 0)
    (hlc : ∀ k, 0 < k → k + 1 ≤ N → p k ^ 2 ≥ p (k - 1) * p (k + 1))
    (hnorm : M + 2 * (∑ k ∈ Finset.range N, p (k + 1)) = 1)
    (hvariance : (n : ℝ) / 8 ≤
      2 * (∑ k ∈ Finset.range N, ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)))
    (htail : ∀ r ≤ N, 1 ≤ r →
      2 * (∑ j ∈ Finset.Icc r N, p j) ≤
        2 * Real.exp (-(1 / 6 : ℝ) * (r : ℝ) ^ 2 / (n : ℝ))) :
    0 < squaredBinomialGaussianAmplitude ∧ 0 < squaredBinomialGaussianDecay ∧
      ∀ k ≤ N, p k ≤ squaredBinomialGaussianAmplitude / Real.sqrt (n : ℝ) *
        Real.exp (-squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (n : ℝ)) := by
  have hpeak := symmetricProfile_maxAtom_le_of_logConcave p M hM hp0
    hpos hzero hcenter hlc hnorm
  let V : ℝ := 2 * (∑ k ∈ Finset.range N,
    ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1))
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun k hk =>
      mul_nonneg (sq_nonneg _) (le_of_lt (hpos (k + 1) (by simpa using Finset.mem_range.mp hk)))
  have hMscale : M ^ 2 * (n : ℝ) ≤ 487 * 8 := by
    have hle : (n : ℝ) / 8 ≤ 1 + V := by dsimp [V]; linarith [hvariance]
    have h := mul_le_mul_of_nonneg_left hle (sq_nonneg M)
    change M ^ 2 * (1 + V) ≤ 487 at hpeak
    nlinarith [hpeak]
  have hsqrtNpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hApos : 0 < Real.sqrt (487 * 8 : ℝ) := by positivity
  have hrootSq : (M * Real.sqrt (n : ℝ)) ^ 2 ≤ (Real.sqrt (487 * 8 : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ)),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 487 * 8)]
    nlinarith [hMscale]
  have hroot : M * Real.sqrt (n : ℝ) ≤ Real.sqrt (487 * 8 : ℝ) :=
    (sq_le_sq₀ (mul_nonneg hM.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp hrootSq
  have hAtom : M ≤ Real.sqrt (487 * 8 : ℝ) / Real.sqrt (n : ℝ) :=
    (le_div_iff₀ hsqrtNpos).2 (by simpa [mul_comm] using hroot)
  have hmonoAdj := symmetricProfile_antitone_of_logConcave p hpos hzero hcenter hlc
  have hmono : ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ N → p j ≤ p i := by
    intro i j hij hjN
    exact symmetricProfile_antitone_of_adjacent hmonoAdj hij
  exact finite_radial_localGaussian_explicit p (Real.sqrt (487 * 8 : ℝ)) 2 (1 / 6)
    hn hApos (by norm_num) (by norm_num)
    (fun k hk => le_of_lt (hpos k hk)) hmono
    (fun k hk => by
      calc
        p k ≤ p 0 := symmetricProfile_antitone_of_adjacent hmonoAdj (Nat.zero_le k)
        _ = M := hp0
        _ ≤ Real.sqrt (487 * 8 : ℝ) / Real.sqrt (n : ℝ) := hAtom)
    (by simpa using htail)

private theorem finite_symmetricHalfProfile_localGaussian_explicit
    {N n : ℕ} (p : ℕ → ℝ) (M : ℝ)
    (hn : 0 < n) (hM : 0 < M) (hp0 : p 0 = M)
    (hpos : ∀ k ≤ N, 0 < p k) (hzero : ∀ k, N < k → p k = 0)
    (hmono : ∀ k, p (k + 1) ≤ p k)
    (hlc : ∀ k, 0 < k → k + 1 ≤ N → p k ^ 2 ≥ p (k - 1) * p (k + 1))
    (hnorm : 2 * (∑ k ∈ Finset.range (N + 1), p k) = 1)
    (hvariance : (n : ℝ) / 8 ≤
      2 * (∑ k ∈ Finset.range (N + 1), (((k : ℝ) + 1 / 2) ^ 2) * p k))
    (htail : ∀ r ≤ N, 1 ≤ r →
      2 * (∑ j ∈ Finset.Icc r N, p j) ≤
        2 * Real.exp (-(1 / 6 : ℝ) * (r : ℝ) ^ 2 / (n : ℝ))) :
    0 < squaredBinomialGaussianAmplitude ∧ 0 < squaredBinomialGaussianDecay ∧
      ∀ k ≤ N, p k ≤ squaredBinomialGaussianAmplitude / Real.sqrt (n : ℝ) *
        Real.exp (-squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (n : ℝ)) := by
  have hpeak := symmetricHalfProfile_maxAtom_le p M hM hp0 hpos hzero hmono hlc hnorm
  let V : ℝ := 2 * (∑ k ∈ Finset.range (N + 1),
    (((k : ℝ) + 1 / 2) ^ 2) * p k)
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun k hk =>
      mul_nonneg (sq_nonneg _) (le_of_lt (hpos k (by simpa using Finset.mem_range.mp hk)))
  have hMscale : M ^ 2 * (n : ℝ) ≤ 487 * 8 := by
    have hle : (n : ℝ) / 8 ≤ 1 + V := by dsimp [V]; linarith [hvariance]
    have h := mul_le_mul_of_nonneg_left hle (sq_nonneg M)
    change M ^ 2 * (1 + V) ≤ 487 at hpeak
    nlinarith [hpeak]
  have hsqrtNpos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hApos : 0 < Real.sqrt (487 * 8 : ℝ) := by positivity
  have hrootSq : (M * Real.sqrt (n : ℝ)) ^ 2 ≤ (Real.sqrt (487 * 8 : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (n : ℝ)),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 487 * 8)]
    nlinarith [hMscale]
  have hroot : M * Real.sqrt (n : ℝ) ≤ Real.sqrt (487 * 8 : ℝ) :=
    (sq_le_sq₀ (mul_nonneg hM.le (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)).mp hrootSq
  have hAtom : M ≤ Real.sqrt (487 * 8 : ℝ) / Real.sqrt (n : ℝ) :=
    (le_div_iff₀ hsqrtNpos).2 (by simpa [mul_comm] using hroot)
  have hmono' : ∀ ⦃i j : ℕ⦄, i ≤ j → j ≤ N → p j ≤ p i := by
    intro i j hij hjN
    exact symmetricProfile_antitone_of_adjacent hmono hij
  exact finite_radial_localGaussian_explicit p (Real.sqrt (487 * 8 : ℝ)) 2 (1 / 6)
    hn hApos (by norm_num) (by norm_num)
    (fun k hk => le_of_lt (hpos k hk)) hmono'
    (fun k hk => by
      calc
        p k ≤ p 0 := symmetricProfile_antitone_of_adjacent hmono (Nat.zero_le k)
        _ = M := hp0
        _ ≤ Real.sqrt (487 * 8 : ℝ) / Real.sqrt (n : ℝ) := hAtom)
    (by simpa using htail)


private theorem squaredBinomialConvolution_even_profile_localGaussian
    (ms : List ℕ) (N : ℕ) (hN : ms.sum = 2 * N) (hn : 0 < ms.sum) :
    0 < squaredBinomialGaussianAmplitude ∧
    0 < squaredBinomialGaussianDecay ∧
    ∀ k ≤ N,
      squaredBinomialConvolution ms ((N + k : ℕ) : ℤ) ≤
        squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) *
          Real.exp (-squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ)) := by
  let f : ℤ → ℝ := squaredBinomialConvolution ms
  let p : ℕ → ℝ := fun k => f ((N + k : ℕ) : ℤ)
  let M : ℝ := f (N : ℤ)
  have hfpos : ∀ z ∈ Finset.Icc (0 : ℤ) (2 * N), 0 < f z := by
    intro z hz
    apply squaredBinomialConvolution_pos ms z
    simpa [hN] using hz
  have hfzero : ∀ z, z ∉ Finset.Icc (0 : ℤ) (2 * N) → f z = 0 := by
    intro z hz
    apply squaredBinomialConvolution_eq_zero_of_notMem
    simpa [hN] using hz
  have hsymm : ∀ z, f ((2 * N : ℕ) - z) = f z := by
    intro z
    simpa [f, hN] using squaredBinomialConvolution_symm ms z
  have hM : 0 < M := by
    apply hfpos
    simp only [Finset.mem_Icc]
    constructor
    · exact_mod_cast Nat.zero_le N
    · exact_mod_cast (show N ≤ 2 * N by omega)
  have hp0 : p 0 = M := by simp [p, M]
  have hpos : ∀ k ≤ N, 0 < p k := by
    intro k hk
    apply hfpos
    simp only [Finset.mem_Icc]
    constructor
    · exact_mod_cast Nat.zero_le (N + k)
    · exact_mod_cast (by omega : N + k ≤ 2 * N)
  have hzero : ∀ k, N < k → p k = 0 := by
    intro k hk
    apply hfzero
    simp only [Finset.mem_Icc]
    push_cast
    omega
  have hcenter : p 1 ≤ p 0 := by
    by_cases hN0 : N = 0
    · subst N
      have hp1 : p 1 = 0 := hzero 1 (by omega)
      rw [hp1]
      exact le_of_lt (by simpa [p, M] using hM)
    · have hNpos : 0 < N := Nat.pos_of_ne_zero hN0
      have hmirrorIndex :
          ((2 * N : ℕ) : ℤ) - ((N + 1 : ℕ) : ℤ) = (N : ℤ) - 1 := by
        push_cast
        omega
      have hmirror := hsymm ((N + 1 : ℕ) : ℤ)
      rw [hmirrorIndex] at hmirror
      have hLC := squaredBinomialConvolution_logConcave ms (N : ℤ)
      have hsq : f ((N + 1 : ℕ) : ℤ) ^ 2 ≤ f (N : ℤ) ^ 2 := by
        have hLC' := hLC
        have hmirror' : squaredBinomialConvolution ms ((N : ℤ) - 1) =
            squaredBinomialConvolution ms ((N + 1 : ℕ) : ℤ) := by simpa [f] using hmirror
        rw [hmirror'] at hLC'
        simpa [f, pow_two] using hLC'
      have hp1nonneg : 0 ≤ p 1 := le_of_lt (hpos 1 (by omega))
      have hp0nonneg : 0 ≤ p 0 := le_of_lt (hpos 0 (by omega))
      exact (sq_le_sq₀ hp1nonneg hp0nonneg).mp (by simpa [p, M] using hsq)
  have hlcProfile : ∀ k, 0 < k → k + 1 ≤ N →
      p k ^ 2 ≥ p (k - 1) * p (k + 1) := by
    intro k hk hkN
    have h := squaredBinomialConvolution_logConcave ms ((N + k : ℕ) : ℤ)
    have hminus : ((N + k : ℕ) : ℤ) - 1 = ((N + (k - 1) : ℕ) : ℤ) := by
      simp only [Nat.cast_add]
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      omega
    have hplus : ((N + k : ℕ) : ℤ) + 1 = ((N + (k + 1) : ℕ) : ℤ) := by
      simp only [Nat.cast_add]
      push_cast
      omega
    rw [hminus, hplus] at h
    simpa [p, f, discreteLogConcave] using h
  have hnormRange :
      (∑ j ∈ Finset.range (2 * N + 1), f (j : ℤ)) = 1 := by
    calc
      _ = ∑ z ∈ Finset.Icc (0 : ℤ) (2 * N), f z :=
        (sum_int_Icc_eq_range_local (2 * N) f).symm
      _ = 1 := by simpa [f, hN] using squaredBinomialConvolution_sum_one ms
  have hnormProfile : M + 2 * (∑ k ∈ Finset.range N, p (k + 1)) = 1 := by
    rw [symmetricEven_range_sum_local N f hsymm] at hnormRange
    simpa [p, M, Nat.cast_add, Nat.cast_one, add_assoc] using hnormRange
  have hmoment :
      (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
        f z * ((z : ℝ) - (ms.sum : ℝ) / 2) ^ 2) =
        2 * (∑ k ∈ Finset.range N,
          ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) := by
    simpa [f, p, hN, Nat.cast_add, Nat.cast_one, add_assoc] using
      squaredBinomial_even_moment_profile_eq ms N hN
  have hvariance : (ms.sum : ℝ) / 8 ≤
      2 * (∑ k ∈ Finset.range N,
        ((k + 1 : ℕ) : ℝ) ^ 2 * p (k + 1)) := by
    rw [← hmoment]
    exact squaredBinomialConvolution_centered_secondMoment_lower ms
  have htail : ∀ r ≤ N, 1 ≤ r →
      2 * (∑ j ∈ Finset.Icc r N, p j) ≤
        2 * Real.exp (-(1 / 6 : ℝ) * (r : ℝ) ^ 2 / (ms.sum : ℝ)) := by
    intro r hrN hr
    have hshift := sum_Icc_nat_shift_to_int_local (r := r) (N := N) (a := N) f
    have hprofileSum :
        (∑ j ∈ Finset.Icc r N, p j) =
          ∑ z ∈ Finset.Icc ((N + r : ℕ) : ℤ) ((2 * N : ℕ) : ℤ), f z := by
      simpa [p, show N + N = 2 * N by omega] using hshift
    have hupper := squaredBinomialConvolution_upperInterval_even_le ms N r hN hr hrN
    have hnR : 0 < (ms.sum : ℝ) := by exact_mod_cast hn
    have harg : -((2 * (r : ℝ)) ^ 2) / (6 * (ms.sum : ℝ)) ≤
        -(1 / 6 : ℝ) * (r : ℝ) ^ 2 / (ms.sum : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * (ms.sum : ℝ)) hnR).2
      nlinarith [sq_nonneg (r : ℝ)]
    calc
      2 * (∑ j ∈ Finset.Icc r N, p j) ≤
          2 * Real.exp (-((2 * (r : ℝ)) ^ 2) / (6 * (ms.sum : ℝ))) := by
            rw [hprofileSum]
            exact mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ ≤ 2 * Real.exp (-(1 / 6 : ℝ) * (r : ℝ) ^ 2 / (ms.sum : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
  exact finite_symmetricProfile_localGaussian_explicit p M hn hM hp0 hpos hzero
    hcenter hlcProfile hnormProfile hvariance htail

private theorem squaredBinomialConvolution_odd_profile_localGaussian
    (ms : List ℕ) (N : ℕ) (hN : ms.sum = 2 * N + 1) (hn : 0 < ms.sum) :
    0 < squaredBinomialGaussianAmplitude ∧
    0 < squaredBinomialGaussianDecay ∧
    ∀ k ≤ N,
      squaredBinomialConvolution ms ((N + k + 1 : ℕ) : ℤ) ≤
        squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) *
          Real.exp (-squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ)) := by
  let f : ℤ → ℝ := squaredBinomialConvolution ms
  let p : ℕ → ℝ := fun k => f ((N + k + 1 : ℕ) : ℤ)
  let M : ℝ := f ((N + 1 : ℕ) : ℤ)
  have hfpos : ∀ z ∈ Finset.Icc (0 : ℤ) (2 * N + 1), 0 < f z := by
    intro z hz
    apply squaredBinomialConvolution_pos ms z
    simpa [hN] using hz
  have hfzero : ∀ z, z ∉ Finset.Icc (0 : ℤ) (2 * N + 1) → f z = 0 := by
    intro z hz
    apply squaredBinomialConvolution_eq_zero_of_notMem
    simpa [hN] using hz
  have hsymm : ∀ z, f ((2 * N + 1 : ℕ) - z) = f z := by
    intro z
    simpa [f, hN] using squaredBinomialConvolution_symm ms z
  have hM : 0 < M := by
    apply hfpos
    simp only [Finset.mem_Icc]
    constructor
    · exact_mod_cast Nat.zero_le (N + 1)
    · exact_mod_cast (show N + 1 ≤ 2 * N + 1 by omega)
  have hp0 : p 0 = M := by simp [p, M]
  have hpos : ∀ k ≤ N, 0 < p k := by
    intro k hk
    apply hfpos
    simp only [Finset.mem_Icc]
    constructor
    · exact_mod_cast Nat.zero_le (N + k + 1)
    · exact_mod_cast (show N + k + 1 ≤ 2 * N + 1 by omega)
  have hzero : ∀ k, N < k → p k = 0 := by
    intro k hk
    apply hfzero
    simp only [Finset.mem_Icc]
    push_cast
    omega
  have hcenterSymm : f (N : ℤ) = f ((N + 1 : ℕ) : ℤ) := by
    have h := hsymm (N : ℤ)
    have hindex : ((2 * N + 1 : ℕ) : ℤ) - (N : ℤ) = ((N + 1 : ℕ) : ℤ) := by
      push_cast
      omega
    rw [hindex] at h
    exact h.symm
  have hlcProfile : ∀ k, 0 < k → k + 1 ≤ N →
      p k ^ 2 ≥ p (k - 1) * p (k + 1) := by
    intro k hk hkN
    have h := squaredBinomialConvolution_logConcave ms ((N + k + 1 : ℕ) : ℤ)
    have hminus : ((N + k + 1 : ℕ) : ℤ) - 1 =
        ((N + (k - 1) + 1 : ℕ) : ℤ) := by
      simp only [Nat.cast_add]
      rw [Nat.cast_sub (by omega : 1 ≤ k)]
      omega
    have hplus : ((N + k + 1 : ℕ) : ℤ) + 1 =
        ((N + (k + 1) + 1 : ℕ) : ℤ) := by
      simp only [Nat.cast_add]
      push_cast
      omega
    rw [hminus, hplus] at h
    simpa [p, f, discreteLogConcave] using h
  have hcenter : p 1 ≤ p 0 := by
    have hLC := squaredBinomialConvolution_logConcave ms ((N + 1 : ℕ) : ℤ)
    have hLC' : f ((N + 1 : ℕ) : ℤ) ^ 2 ≥
        f (N : ℤ) * f ((N + 2 : ℕ) : ℤ) := by
      have hminus : ((N + 1 : ℕ) : ℤ) - 1 = (N : ℤ) := by
        push_cast
        omega
      have hplus : ((N + 1 : ℕ) : ℤ) + 1 = ((N + 2 : ℕ) : ℤ) := by
        push_cast
        omega
      simpa [discreteLogConcave, hminus, hplus, Nat.cast_add,
        Nat.cast_ofNat, add_assoc] using hLC
    rw [hcenterSymm] at hLC'
    have hmul : M * p 1 ≤ M * M := by
      simpa [p, M, pow_two, Nat.cast_add, Nat.cast_ofNat, add_assoc] using hLC'
    exact (mul_le_mul_iff_of_pos_left hM).mp hmul
  have hmono := symmetricProfile_antitone_of_logConcave p hpos hzero hcenter hlcProfile
  have hnormRange :
      (∑ j ∈ Finset.range (2 * N + 2), f (j : ℤ)) = 1 := by
    calc
      _ = ∑ z ∈ Finset.Icc (0 : ℤ) (2 * N + 1), f z :=
        (sum_int_Icc_eq_range_local (2 * N + 1) f).symm
      _ = 1 := by simpa [f, hN] using squaredBinomialConvolution_sum_one ms
  have hnormProfile : 2 * (∑ k ∈ Finset.range (N + 1), p k) = 1 := by
    rw [symmetricOdd_range_sum_local N f hsymm] at hnormRange
    simpa [p] using hnormRange
  have hmoment :
      (∑ z ∈ Finset.Icc (0 : ℤ) ms.sum,
        f z * ((z : ℝ) - (ms.sum : ℝ) / 2) ^ 2) =
        2 * (∑ k ∈ Finset.range (N + 1),
          ((k : ℝ) + 1 / 2) ^ 2 * p k) := by
    simpa [f, p, hN, Nat.cast_add, Nat.cast_one, add_assoc] using
      squaredBinomial_odd_moment_profile_eq ms N hN
  have hvariance : (ms.sum : ℝ) / 8 ≤
      2 * (∑ k ∈ Finset.range (N + 1),
        ((k : ℝ) + 1 / 2) ^ 2 * p k) := by
    rw [← hmoment]
    exact squaredBinomialConvolution_centered_secondMoment_lower ms
  have htail : ∀ r ≤ N, 1 ≤ r →
      2 * (∑ j ∈ Finset.Icc r N, p j) ≤
        2 * Real.exp (-(1 / 6 : ℝ) * (r : ℝ) ^ 2 / (ms.sum : ℝ)) := by
    intro r hrN hr
    have hshift := sum_Icc_nat_shift_to_int_local (r := r) (N := N) (a := N + 1) f
    have hshift' := hshift
    rw [show N + 1 + N = 2 * N + 1 by omega] at hshift'
    have hprofileSum :
        (∑ j ∈ Finset.Icc r N, p j) =
          ∑ z ∈ Finset.Icc ((N + r + 1 : ℕ) : ℤ) ((2 * N + 1 : ℕ) : ℤ), f z := by
      simpa [p, Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using hshift'
    have hupper := squaredBinomialConvolution_upperInterval_odd_le ms N r hN
    have hnR : 0 < (ms.sum : ℝ) := by exact_mod_cast hn
    have harg : -((2 * (r : ℝ) + 1) ^ 2) / (6 * (ms.sum : ℝ)) ≤
        -(1 / 6 : ℝ) * (r : ℝ) ^ 2 / (ms.sum : ℝ) := by
      apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 6 * (ms.sum : ℝ)) hnR).2
      have hrR : 0 ≤ (r : ℝ) := by positivity
      have hpoly : -((2 * (r : ℝ) + 1) ^ 2) ≤ -(1 / 6 : ℝ) * (r : ℝ) ^ 2 * 6 := by
        nlinarith [sq_nonneg (r : ℝ), hrR]
      have hscaled := mul_le_mul_of_nonneg_right hpoly hnR.le
      nlinarith [hscaled]
    calc
      2 * (∑ j ∈ Finset.Icc r N, p j) ≤
          2 * Real.exp (-((2 * (r : ℝ) + 1) ^ 2) / (6 * (ms.sum : ℝ))) := by
            rw [hprofileSum]
            exact mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ ≤ 2 * Real.exp (-(1 / 6 : ℝ) * (r : ℝ) ^ 2 / (ms.sum : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
  exact finite_symmetricHalfProfile_localGaussian_explicit p M hn hM hp0 hpos hzero
    hmono hlcProfile hnormProfile hvariance htail

private theorem squaredBinomialConvolution_even_pointwise_localGaussian
    (ms : List ℕ) (N : ℕ) (hN : ms.sum = 2 * N) (hn : 0 < ms.sum) (j : ℤ) :
    squaredBinomialConvolution ms j ≤
      squaredBinomialGaussianFinalAmplitude / Real.sqrt (ms.sum : ℝ) *
        Real.exp (-squaredBinomialGaussianFinalDecay *
          (2 * (j : ℝ) - (ms.sum : ℝ)) ^ 2 / (ms.sum : ℝ)) := by
  obtain ⟨hAmpPos, hDecayPos, hprofile⟩ :=
    squaredBinomialConvolution_even_profile_localGaussian ms N hN hn
  have hnR : 0 < (ms.sum : ℝ) := by exact_mod_cast hn
  have hAmpLe : squaredBinomialGaussianAmplitude ≤ squaredBinomialGaussianFinalAmplitude := by
    have hE : 1 ≤ Real.exp (squaredBinomialGaussianDecay / 8) :=
      Real.one_le_exp_iff.mpr (by positivity)
    calc
      squaredBinomialGaussianAmplitude = squaredBinomialGaussianAmplitude * 1 := by ring
      _ ≤ squaredBinomialGaussianAmplitude * Real.exp (squaredBinomialGaussianDecay / 8) :=
        mul_le_mul_of_nonneg_left hE (le_of_lt hAmpPos)
      _ = squaredBinomialGaussianFinalAmplitude := rfl
  have hcoeff : squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) ≤
      squaredBinomialGaussianFinalAmplitude / Real.sqrt (ms.sum : ℝ) :=
    div_le_div_of_nonneg_right hAmpLe (Real.sqrt_nonneg _)
  by_cases hjmem : j ∈ Finset.Icc (0 : ℤ) ms.sum
  · have hj0 := (Finset.mem_Icc.mp hjmem).1
    have hjmax : j ≤ ((2 * N : ℕ) : ℤ) := by simpa [hN] using (Finset.mem_Icc.mp hjmem).2
    have hjcast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
    have hjNatInt : (j.toNat : ℤ) ≤ (2 * N : ℤ) := by simpa [hjcast] using hjmax
    have hjNat : j.toNat ≤ 2 * N := by exact_mod_cast hjNatInt
    by_cases hjleft : j ≤ (N : ℤ)
    · have hjNatNInt : (j.toNat : ℤ) ≤ (N : ℤ) := by simpa [hjcast] using hjleft
      have hjNatN : j.toNat ≤ N := by exact_mod_cast hjNatNInt
      let k : ℕ := N - j.toNat
      have hkN : k ≤ N := Nat.sub_le _ _
      have hidx : ((N + k : ℕ) : ℤ) = ((2 * N : ℕ) : ℤ) - j := by
        have hnat : N + k = 2 * N - j.toNat := by dsimp [k]; omega
        have hsub : ((2 * N - j.toNat : ℕ) : ℤ) =
            ((2 * N : ℕ) : ℤ) - (j.toNat : ℤ) := by
          rw [Nat.cast_sub (by omega : j.toNat ≤ 2 * N)]
        rw [← hjcast, ← hsub]
        exact_mod_cast hnat
      have hsymm := squaredBinomialConvolution_symm ms j
      rw [hN, ← hidx] at hsymm
      have hval : squaredBinomialConvolution ms j =
          squaredBinomialConvolution ms ((N + k : ℕ) : ℤ) := hsymm.symm
      have hcoord : 2 * (j : ℝ) - (ms.sum : ℝ) = -2 * (k : ℝ) := by
        rw [hN]
        have hjR : (j : ℝ) = (j.toNat : ℝ) := by exact_mod_cast hjcast.symm
        have hkR : (k : ℝ) = (N : ℝ) - (j.toNat : ℝ) := by
          dsimp [k]
          rw [Nat.cast_sub hjNatN]
        rw [hjR, hkR]
        push_cast
        ring
      have harg : -squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ) ≤
          -squaredBinomialGaussianFinalDecay *
            (2 * (j : ℝ) - (ms.sum : ℝ)) ^ 2 / (ms.sum : ℝ) := by
        rw [hcoord]
        apply (div_le_div_iff₀ hnR hnR).2
        have hprod : 0 ≤ squaredBinomialGaussianDecay * (k : ℝ) ^ 2 :=
          mul_nonneg (le_of_lt hDecayPos) (sq_nonneg _)
        dsimp [squaredBinomialGaussianFinalDecay]
        nlinarith [hprod]
      calc
        squaredBinomialConvolution ms j =
            squaredBinomialConvolution ms ((N + k : ℕ) : ℤ) := hval
        _ ≤ squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) *
              Real.exp (-squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ)) :=
                hprofile k hkN
        _ ≤ squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) *
              Real.exp (-squaredBinomialGaussianFinalDecay *
                (2 * (j : ℝ) - (ms.sum : ℝ)) ^ 2 / (ms.sum : ℝ)) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
        _ ≤ squaredBinomialGaussianFinalAmplitude / Real.sqrt (ms.sum : ℝ) *
              Real.exp (-squaredBinomialGaussianFinalDecay *
                (2 * (j : ℝ) - (ms.sum : ℝ)) ^ 2 / (ms.sum : ℝ)) :=
                mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
    · have hjNle : (N : ℤ) ≤ j := by omega
      have hjNatNInt : (N : ℤ) ≤ (j.toNat : ℤ) := by simpa [hjcast] using hjNle
      have hjNatN : N ≤ j.toNat := by exact_mod_cast hjNatNInt
      let k : ℕ := j.toNat - N
      have hkN : k ≤ N := by dsimp [k]; omega
      have hidx : ((N + k : ℕ) : ℤ) = j := by
        have hnat : N + k = j.toNat := by dsimp [k]; omega
        rw [← hjcast]
        exact_mod_cast hnat
      have hval : squaredBinomialConvolution ms j =
          squaredBinomialConvolution ms ((N + k : ℕ) : ℤ) := by rw [hidx]
      have hcoord : 2 * (j : ℝ) - (ms.sum : ℝ) = 2 * (k : ℝ) := by
        rw [hN]
        have hjR : (j : ℝ) = (j.toNat : ℝ) := by exact_mod_cast hjcast.symm
        have hkR : (k : ℝ) = (j.toNat : ℝ) - (N : ℝ) := by
          dsimp [k]
          rw [Nat.cast_sub hjNatN]
        rw [hjR, hkR]
        push_cast
        ring
      have harg : -squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ) ≤
          -squaredBinomialGaussianFinalDecay *
            (2 * (j : ℝ) - (ms.sum : ℝ)) ^ 2 / (ms.sum : ℝ) := by
        rw [hcoord]
        apply (div_le_div_iff₀ hnR hnR).2
        have hprod : 0 ≤ squaredBinomialGaussianDecay * (k : ℝ) ^ 2 :=
          mul_nonneg (le_of_lt hDecayPos) (sq_nonneg _)
        dsimp [squaredBinomialGaussianFinalDecay]
        nlinarith [hprod]
      calc
        squaredBinomialConvolution ms j =
            squaredBinomialConvolution ms ((N + k : ℕ) : ℤ) := hval
        _ ≤ squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) *
              Real.exp (-squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ)) :=
                hprofile k hkN
        _ ≤ squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) *
              Real.exp (-squaredBinomialGaussianFinalDecay *
                (2 * (j : ℝ) - (ms.sum : ℝ)) ^ 2 / (ms.sum : ℝ)) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by positivity)
        _ ≤ squaredBinomialGaussianFinalAmplitude / Real.sqrt (ms.sum : ℝ) *
              Real.exp (-squaredBinomialGaussianFinalDecay *
                (2 * (j : ℝ) - (ms.sum : ℝ)) ^ 2 / (ms.sum : ℝ)) :=
                mul_le_mul_of_nonneg_right hcoeff (Real.exp_nonneg _)
  · rw [squaredBinomialConvolution_eq_zero_of_notMem hjmem]
    have hfinalPos : 0 < squaredBinomialGaussianFinalAmplitude := by
      dsimp [squaredBinomialGaussianFinalAmplitude]
      positivity
    have hsqrt : 0 < Real.sqrt (ms.sum : ℝ) := Real.sqrt_pos.mpr hnR
    positivity

private theorem squaredBinomialConvolution_odd_pointwise_localGaussian
    (ms : List ℕ) (N : ℕ) (hN : ms.sum = 2 * N + 1) (hn : 0 < ms.sum) (j : ℤ) :
    squaredBinomialConvolution ms j ≤
      squaredBinomialGaussianFinalAmplitude / Real.sqrt (ms.sum : ℝ) *
        Real.exp (-squaredBinomialGaussianFinalDecay *
          (2 * (j : ℝ) - (ms.sum : ℝ)) ^ 2 / (ms.sum : ℝ)) := by
  obtain ⟨hAmpPos, hDecayPos, hprofile⟩ :=
    squaredBinomialConvolution_odd_profile_localGaussian ms N hN hn
  have hnR : 0 < (ms.sum : ℝ) := by exact_mod_cast hn
  have hnOne : 1 ≤ (ms.sum : ℝ) := by exact_mod_cast Nat.one_le_of_lt hn
  have hE : 1 ≤ Real.exp (squaredBinomialGaussianDecay / 8) :=
    Real.one_le_exp_iff.mpr (by positivity)
  have hAmpLe : squaredBinomialGaussianAmplitude ≤ squaredBinomialGaussianFinalAmplitude := by
    calc
      squaredBinomialGaussianAmplitude = squaredBinomialGaussianAmplitude * 1 := by ring
      _ ≤ squaredBinomialGaussianAmplitude * Real.exp (squaredBinomialGaussianDecay / 8) :=
        mul_le_mul_of_nonneg_left hE (le_of_lt hAmpPos)
      _ = squaredBinomialGaussianFinalAmplitude := rfl
  have hcoeff : squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) ≤
      squaredBinomialGaussianFinalAmplitude / Real.sqrt (ms.sum : ℝ) :=
    div_le_div_of_nonneg_right hAmpLe (Real.sqrt_nonneg _)
  by_cases hjmem : j ∈ Finset.Icc (0 : ℤ) ms.sum
  · have hj0 := (Finset.mem_Icc.mp hjmem).1
    have hjmax : j ≤ ((2 * N + 1 : ℕ) : ℤ) := by simpa [hN] using (Finset.mem_Icc.mp hjmem).2
    have hjcast : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg hj0
    have hjNatInt : (j.toNat : ℤ) ≤ ((2 * N + 1 : ℕ) : ℤ) := by simpa [hjcast] using hjmax
    have hjNat : j.toNat ≤ 2 * N + 1 := by exact_mod_cast hjNatInt
    by_cases hjleft : j ≤ (N : ℤ)
    · have hjNatNInt : (j.toNat : ℤ) ≤ (N : ℤ) := by simpa [hjcast] using hjleft
      have hjNatN : j.toNat ≤ N := by exact_mod_cast hjNatNInt
      let k : ℕ := N - j.toNat
      have hkN : k ≤ N := Nat.sub_le _ _
      have hidx : ((N + k + 1 : ℕ) : ℤ) = ((2 * N + 1 : ℕ) : ℤ) - j := by
        have hnat : N + k + 1 = 2 * N + 1 - j.toNat := by dsimp [k]; omega
        have hsub : ((2 * N + 1 - j.toNat : ℕ) : ℤ) =
            ((2 * N + 1 : ℕ) : ℤ) - (j.toNat : ℤ) := by
          rw [Nat.cast_sub (by omega : j.toNat ≤ 2 * N + 1)]
        rw [← hjcast, ← hsub]
        exact_mod_cast hnat
      have hsymm := squaredBinomialConvolution_symm ms j
      rw [hN, ← hidx] at hsymm
      have hval : squaredBinomialConvolution ms j =
          squaredBinomialConvolution ms ((N + k + 1 : ℕ) : ℤ) := hsymm.symm
      have hcoord : 2 * (j : ℝ) - (ms.sum : ℝ) = -(2 * (k : ℝ) + 1) := by
        rw [hN]
        have hjR : (j : ℝ) = (j.toNat : ℝ) := by exact_mod_cast hjcast.symm
        have hkR : (k : ℝ) = (N : ℝ) - (j.toNat : ℝ) := by
          dsimp [k]
          rw [Nat.cast_sub hjNatN]
        rw [hjR, hkR]
        push_cast
        ring
      have hpoly : squaredBinomialGaussianFinalDecay * (2 * (k : ℝ) + 1) ^ 2 -
          squaredBinomialGaussianDecay * (k : ℝ) ^ 2 ≤ squaredBinomialGaussianDecay / 8 := by
        simpa [squaredBinomialGaussianFinalDecay] using
          shiftedSquareExponent_le k squaredBinomialGaussianDecay (le_of_lt hDecayPos)
      have hpolyScale : squaredBinomialGaussianFinalDecay * (2 * (k : ℝ) + 1) ^ 2 -
          squaredBinomialGaussianDecay * (k : ℝ) ^ 2 ≤
            squaredBinomialGaussianDecay / 8 * (ms.sum : ℝ) := by
        have hscale := mul_le_mul_of_nonneg_left hnOne (by positivity :
          0 ≤ squaredBinomialGaussianDecay / 8)
        nlinarith [hpoly, hscale]
      have harg : -squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ) ≤
          squaredBinomialGaussianDecay / 8 - squaredBinomialGaussianFinalDecay *
            (2 * (k : ℝ) + 1) ^ 2 / (ms.sum : ℝ) := by
        calc
          _ ≤ (squaredBinomialGaussianDecay / 8 * (ms.sum : ℝ) -
              squaredBinomialGaussianFinalDecay * (2 * (k : ℝ) + 1) ^ 2) /
                (ms.sum : ℝ) := by
                  apply (div_le_div_iff₀ hnR hnR).2
                  nlinarith [hpolyScale]
          _ = _ := by field_simp [ne_of_gt hnR]
      have hexp :
          Real.exp (-squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ)) ≤
            Real.exp (squaredBinomialGaussianDecay / 8) *
              Real.exp (-squaredBinomialGaussianFinalDecay *
                (2 * (k : ℝ) + 1) ^ 2 / (ms.sum : ℝ)) := by
        calc
          _ ≤ Real.exp (squaredBinomialGaussianDecay / 8 -
              squaredBinomialGaussianFinalDecay * (2 * (k : ℝ) + 1) ^ 2 /
                (ms.sum : ℝ)) := Real.exp_le_exp.mpr harg
          _ = _ := by rw [← Real.exp_add]; congr 1; ring
      calc
        squaredBinomialConvolution ms j =
            squaredBinomialConvolution ms ((N + k + 1 : ℕ) : ℤ) := hval
        _ ≤ squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) *
              Real.exp (-squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ)) :=
                hprofile k hkN
        _ ≤ squaredBinomialGaussianFinalAmplitude / Real.sqrt (ms.sum : ℝ) *
              Real.exp (-squaredBinomialGaussianFinalDecay *
                (2 * (j : ℝ) - (ms.sum : ℝ)) ^ 2 / (ms.sum : ℝ)) := by
                rw [hcoord]
                dsimp [squaredBinomialGaussianFinalAmplitude]
                calc
                  _ ≤ squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) *
                      (Real.exp (squaredBinomialGaussianDecay / 8) *
                        Real.exp (-squaredBinomialGaussianFinalDecay *
                          (2 * (k : ℝ) + 1) ^ 2 / (ms.sum : ℝ))) :=
                            mul_le_mul_of_nonneg_left hexp (by positivity)
                  _ = _ := by ring_nf
    · have hjNle : (N : ℤ) ≤ j := by omega
      have hjNatNInt : (N : ℤ) ≤ (j.toNat : ℤ) := by simpa [hjcast] using hjNle
      have hjNatN : N ≤ j.toNat := by exact_mod_cast hjNatNInt
      let k : ℕ := j.toNat - (N + 1)
      have hkN : k ≤ N := by dsimp [k]; omega
      have hidx : ((N + k + 1 : ℕ) : ℤ) = j := by
        have hnat : N + k + 1 = j.toNat := by dsimp [k]; omega
        rw [← hjcast]
        exact_mod_cast hnat
      have hval : squaredBinomialConvolution ms j =
          squaredBinomialConvolution ms ((N + k + 1 : ℕ) : ℤ) := by rw [hidx]
      have hcoord : 2 * (j : ℝ) - (ms.sum : ℝ) = 2 * (k : ℝ) + 1 := by
        rw [hN]
        have hjR : (j : ℝ) = (j.toNat : ℝ) := by exact_mod_cast hjcast.symm
        have hkR : (k : ℝ) = (j.toNat : ℝ) - ((N : ℝ) + 1) := by
          dsimp [k]
          rw [Nat.cast_sub (by omega : N + 1 ≤ j.toNat)]
          push_cast
          ring
        rw [hjR, hkR]
        push_cast
        ring
      have hpoly : squaredBinomialGaussianFinalDecay * (2 * (k : ℝ) + 1) ^ 2 -
          squaredBinomialGaussianDecay * (k : ℝ) ^ 2 ≤ squaredBinomialGaussianDecay / 8 := by
        simpa [squaredBinomialGaussianFinalDecay] using
          shiftedSquareExponent_le k squaredBinomialGaussianDecay (le_of_lt hDecayPos)
      have hpolyScale : squaredBinomialGaussianFinalDecay * (2 * (k : ℝ) + 1) ^ 2 -
          squaredBinomialGaussianDecay * (k : ℝ) ^ 2 ≤
            squaredBinomialGaussianDecay / 8 * (ms.sum : ℝ) := by
        have hscale := mul_le_mul_of_nonneg_left hnOne (by positivity :
          0 ≤ squaredBinomialGaussianDecay / 8)
        nlinarith [hpoly, hscale]
      have harg : -squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ) ≤
          squaredBinomialGaussianDecay / 8 - squaredBinomialGaussianFinalDecay *
            (2 * (k : ℝ) + 1) ^ 2 / (ms.sum : ℝ) := by
        calc
          _ ≤ (squaredBinomialGaussianDecay / 8 * (ms.sum : ℝ) -
              squaredBinomialGaussianFinalDecay * (2 * (k : ℝ) + 1) ^ 2) /
                (ms.sum : ℝ) := by
                  apply (div_le_div_iff₀ hnR hnR).2
                  nlinarith [hpolyScale]
          _ = _ := by field_simp [ne_of_gt hnR]
      have hexp :
          Real.exp (-squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ)) ≤
            Real.exp (squaredBinomialGaussianDecay / 8) *
              Real.exp (-squaredBinomialGaussianFinalDecay *
                (2 * (k : ℝ) + 1) ^ 2 / (ms.sum : ℝ)) := by
        calc
          _ ≤ Real.exp (squaredBinomialGaussianDecay / 8 -
              squaredBinomialGaussianFinalDecay * (2 * (k : ℝ) + 1) ^ 2 /
                (ms.sum : ℝ)) := Real.exp_le_exp.mpr harg
          _ = _ := by rw [← Real.exp_add]; congr 1; ring
      calc
        squaredBinomialConvolution ms j =
            squaredBinomialConvolution ms ((N + k + 1 : ℕ) : ℤ) := hval
        _ ≤ squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) *
              Real.exp (-squaredBinomialGaussianDecay * (k : ℝ) ^ 2 / (ms.sum : ℝ)) :=
                hprofile k hkN
        _ ≤ squaredBinomialGaussianFinalAmplitude / Real.sqrt (ms.sum : ℝ) *
              Real.exp (-squaredBinomialGaussianFinalDecay *
                (2 * (j : ℝ) - (ms.sum : ℝ)) ^ 2 / (ms.sum : ℝ)) := by
                rw [hcoord]
                dsimp [squaredBinomialGaussianFinalAmplitude]
                calc
                  _ ≤ squaredBinomialGaussianAmplitude / Real.sqrt (ms.sum : ℝ) *
                      (Real.exp (squaredBinomialGaussianDecay / 8) *
                        Real.exp (-squaredBinomialGaussianFinalDecay *
                          (2 * (k : ℝ) + 1) ^ 2 / (ms.sum : ℝ))) :=
                            mul_le_mul_of_nonneg_left hexp (by positivity)
                  _ = _ := by ring
  · rw [squaredBinomialConvolution_eq_zero_of_notMem hjmem]
    have hfinalPos : 0 < squaredBinomialGaussianFinalAmplitude := by
      dsimp [squaredBinomialGaussianFinalAmplitude]
      positivity
    have hsqrt : 0 < Real.sqrt (ms.sum : ℝ) := Real.sqrt_pos.mpr hnR
    positivity

/-- Uniform local Gaussian bound for squared-binomial compositions: constants are independent of
the composition and of its length. -/
theorem squaredBinomialConvolution_le_localGaussian :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ ks : List ℕ, 0 < ks.sum → ∀ j : ℤ,
      squaredBinomialConvolution ks j ≤
        C / Real.sqrt ks.sum *
          Real.exp (-c * (2 * (j : ℝ) - ks.sum) ^ 2 / ks.sum) := by
  refine ⟨squaredBinomialGaussianFinalAmplitude, squaredBinomialGaussianFinalDecay,
    ?_, ?_, ?_⟩
  · dsimp [squaredBinomialGaussianFinalAmplitude, squaredBinomialGaussianAmplitude,
      squaredBinomialGaussianDecay]
    positivity
  · dsimp [squaredBinomialGaussianFinalDecay, squaredBinomialGaussianDecay]
    positivity
  · intro ks hks j
    rcases Nat.even_or_odd ks.sum with ⟨N, hN⟩ | ⟨N, hN⟩
    · have hsum : ks.sum = 2 * N := by omega
      exact squaredBinomialConvolution_even_pointwise_localGaussian ks N hsum hks j
    · have hsum : ks.sum = 2 * N + 1 := by omega
      exact squaredBinomialConvolution_odd_pointwise_localGaussian ks N hsum hks j


end Critical2DKPZ.Collision

end
