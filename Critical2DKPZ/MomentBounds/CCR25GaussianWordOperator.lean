/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25PartitionMoments
public import Critical2DKPZ.MomentBounds.CCR25WordCounting
import Mathlib.Tactic

/-! # Gaussian full-support weights in finite CCR25 operator words -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The finite-volume CCR25 operator-word estimate with the exact Gaussian
full-support gain. The operator norms remain explicit inputs; this result
combines their factorization with Proposition 4.13's partition-moment power
and the elementary finite partition count. -/
theorem ccr25_finite_gaussian_partition_word_operator_bound {h n : ℕ}
    (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (W : LatticeConfiguration h → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ)
    (cU cQ left right : ℝ)
    (hCU : 0 ≤ cU) (hCQ : 0 ≤ cQ) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hleft_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s p (fun x => u I x / W x) ≤ left)
    (hright_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s q (fun x => W x * v I x) ≤ right)
    (hU_bound : ∀ I, I ≠ ⊥ → ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q
        (finiteKernelApply s
          (weightedKernel W (ccr25LabelKernel L lam β (.interacting I))) f) ≤
        cU * finiteLpNorm s q f)
    (hQ_bound : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
      ∀ f : LatticeConfiguration h → ℝ,
      finiteLpNorm s q
        (finiteKernelApply s
          (weightedKernel W (ccr25LabelKernel L lam β (.free I J))) f) ≤
        cQ * finiteLpNorm s q f)
    (hσ : Critical2DKPZ.Polymer.sigmaSq β ≤ 1) :
    (∑ I ∈ ccr25AdmissibleWords h n,
      (∏ j : Fin (n + 1),
        |replicaPartitionDisorderMoment β (I j)|) *
        ccr25FiniteWordPairing s L lam β I u v) ≤
      left * right *
        (cU * ((max 1 (ccr25GaussianMomentUniformConstant h)) ^ h) *
          (2 ^ (h * h) : ℝ)) ^ (n + 1) * cQ ^ n *
        Real.sqrt (Critical2DKPZ.Polymer.sigmaSq β) ^ Nat.max (2 * (n + 1)) h := by
  classical
  let words := ccr25AdmissibleWords h n
  let C := max 1 (ccr25GaussianMomentUniformConstant h)
  let M := C ^ h
  let σ := Real.sqrt (Critical2DKPZ.Polymer.sigmaSq β)
  have hC0 : 0 ≤ C := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)
  have hM0 : 0 ≤ M := pow_nonneg hC0 _
  have hσ0 : 0 ≤ σ := by dsimp [σ]; positivity
  have hweights :
      (∑ I ∈ words, ∏ j : Fin (n + 1),
        |replicaPartitionDisorderMoment β (I j)|) ≤
      (M * (2 ^ (h * h) : ℝ)) ^ (n + 1) *
        σ ^ Nat.max (2 * (n + 1)) h := by
    have hcardNat : words.card ≤ 2 ^ ((h * h) * (n + 1)) := by
      simpa [words] using ccr25_admissibleWords_card_le_explicit (h := h) (n := n)
    have hcard : (words.card : ℝ) ≤ (2 ^ (h * h) : ℝ) ^ (n + 1) := by
      calc
        (words.card : ℝ) ≤ (2 ^ ((h * h) * (n + 1)) : ℝ) := by
          exact_mod_cast hcardNat
        _ = (2 ^ (h * h) : ℝ) ^ (n + 1) := by
          exact_mod_cast (show 2 ^ ((h * h) * (n + 1)) =
            (2 ^ (h * h)) ^ (n + 1) by rw [pow_mul])
    have hword : ∀ I ∈ words,
        ∏ j : Fin (n + 1), |replicaPartitionDisorderMoment β (I j)| ≤
          M ^ (n + 1) * σ ^ Nat.max (2 * (n + 1)) h := by
      intro I hI
      have hI' : I ∈ Finset.univ.filter ccr25AdmissibleWord := by
        simpa [words, ccr25AdmissibleWords] using hI
      have hIadm : ccr25AdmissibleWord I := (Finset.mem_filter.mp hI').2
      have hpart : ∀ j, I j ≠ ⊥ := hIadm.1
      have hfull : ccr25WordFullSupport I := hIadm.2.2
      have hmoment := ccr25_gaussian_partitionWord_moment_bound β I hpart hfull hσ
      have habs :
          ∏ j : Fin (n + 1), |replicaPartitionDisorderMoment β (I j)| =
            |∏ j : Fin (n + 1), replicaPartitionDisorderMoment β (I j)| := by
        rw [← Finset.abs_prod]
      calc
        ∏ j : Fin (n + 1), |replicaPartitionDisorderMoment β (I j)| =
            |∏ j : Fin (n + 1), replicaPartitionDisorderMoment β (I j)| := habs
        _ ≤ C ^ (h * (n + 1)) * σ ^ Nat.max (2 * (n + 1)) h := by
          simpa only [C, σ] using hmoment
        _ = M ^ (n + 1) * σ ^ Nat.max (2 * (n + 1)) h := by
          dsimp [M]
          rw [pow_mul]
    calc
      (∑ I ∈ words, ∏ j : Fin (n + 1),
          |replicaPartitionDisorderMoment β (I j)|) ≤
          ∑ I ∈ words, M ^ (n + 1) * σ ^ Nat.max (2 * (n + 1)) h := by
        apply Finset.sum_le_sum
        intro I hI
        exact hword I hI
      _ = (words.card : ℝ) *
          (M ^ (n + 1) * σ ^ Nat.max (2 * (n + 1)) h) := by simp
      _ ≤ (2 ^ (h * h) : ℝ) ^ (n + 1) *
          (M ^ (n + 1) * σ ^ Nat.max (2 * (n + 1)) h) :=
        mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (pow_nonneg hM0 _) (pow_nonneg hσ0 _))
      _ = (M * (2 ^ (h * h) : ℝ)) ^ (n + 1) *
          σ ^ Nat.max (2 * (n + 1)) h := by
        calc
          _ = ((2 ^ (h * h) : ℝ) ^ (n + 1) * M ^ (n + 1)) *
              σ ^ Nat.max (2 * (n + 1)) h := by ring
          _ = ((2 ^ (h * h) : ℝ) * M) ^ (n + 1) *
              σ ^ Nat.max (2 * (n + 1)) h := by rw [← mul_pow]
          _ = (M * (2 ^ (h * h) : ℝ)) ^ (n + 1) *
              σ ^ Nat.max (2 * (n + 1)) h := by
                rw [mul_comm (2 ^ (h * h) : ℝ) M]
  have hop := ccr25_finite_word_bound (h := h) (n := n)
    s L lam β W hW hpq u v
    (fun I => replicaPartitionDisorderMoment β I) cU cQ left right
    hCU hCQ hleft hleft_bound hright_bound hU_bound hQ_bound
  have hcoef : 0 ≤ left * right * cU ^ (n + 1) * cQ ^ n := by positivity
  calc
    (∑ I ∈ ccr25AdmissibleWords h n,
        (∏ j : Fin (n + 1),
          |replicaPartitionDisorderMoment β (I j)|) *
          ccr25FiniteWordPairing s L lam β I u v) ≤
        left * right * cU ^ (n + 1) * cQ ^ n *
          ∑ I ∈ words, ∏ j : Fin (n + 1),
            |replicaPartitionDisorderMoment β (I j)| := by
      simpa [words] using hop
    _ ≤ left * right * cU ^ (n + 1) * cQ ^ n *
          ((M * (2 ^ (h * h) : ℝ)) ^ (n + 1) *
            σ ^ Nat.max (2 * (n + 1)) h) :=
      mul_le_mul_of_nonneg_left hweights hcoef
    _ = left * right * (cU * M * (2 ^ (h * h) : ℝ)) ^ (n + 1) *
          cQ ^ n * σ ^ Nat.max (2 * (n + 1)) h := by
      calc
        _ = left * right *
              (cU ^ (n + 1) * (M * (2 ^ (h * h) : ℝ)) ^ (n + 1)) *
              cQ ^ n * σ ^ Nat.max (2 * (n + 1)) h := by ring
        _ = left * right *
              (cU * (M * (2 ^ (h * h) : ℝ))) ^ (n + 1) *
              cQ ^ n * σ ^ Nat.max (2 * (n + 1)) h := by rw [← mul_pow]
        _ = left * right * (cU * M * (2 ^ (h * h) : ℝ)) ^ (n + 1) *
              cQ ^ n * σ ^ Nat.max (2 * (n + 1)) h := by ring

end

end Critical2DKPZ.MomentBounds
