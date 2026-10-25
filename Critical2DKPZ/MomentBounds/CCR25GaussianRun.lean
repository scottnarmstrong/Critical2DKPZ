/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Critical2DKPZ.MomentBounds.CCR25GaussianWordOperator
public import Critical2DKPZ.MomentBounds.CCR25GeometricSeries
import Mathlib.Tactic

/-! # Finite Gaussian CCR25 moment runs -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The nonnegative finite partition-word contribution with `n + 1`
interacting runs, using the Gaussian disorder moment at each collision and the
absolute interacting kernels. -/
def ccr25GaussianFiniteWordRun {h : ℕ}
    (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ)
    (n : ℕ) : ℝ := by
  classical
  exact ∑ I ∈ ccr25AdmissibleWords h n,
    (∏ j : Fin (n + 1),
      |replicaPartitionDisorderMoment β (I j)|) *
      ccr25FiniteWordPairing s L lam β I u v

/-- Nonnegative endpoint vectors make every finite Gaussian CCR25 word run
nonnegative. -/
theorem ccr25GaussianFiniteWordRun_nonneg {h : ℕ}
    (s : Finset (LatticeConfiguration h)) (L : ℕ) (lam β : ℝ)
    (u v : ReplicaPartition h → LatticeConfiguration h → ℝ)
    (hu : ∀ I x, 0 ≤ u I x) (hv : ∀ I x, 0 ≤ v I x) (n : ℕ) :
    0 ≤ ccr25GaussianFiniteWordRun s L lam β u v n := by
  classical
  unfold ccr25GaussianFiniteWordRun
  apply Finset.sum_nonneg
  intro I hI
  apply mul_nonneg
  · exact Finset.prod_nonneg fun j _ => abs_nonneg _
  · exact ccr25FiniteWordPairing_nonneg s L lam β I u v hu hv

/-- Full-support Gaussian bound for each finite operator run, with every
operator norm and boundary norm stated as an explicit input. -/
theorem ccr25GaussianFiniteWordRun_le {h n : ℕ}
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
    ccr25GaussianFiniteWordRun s L lam β u v n ≤
      left * right *
        (cU * ((max 1 (ccr25GaussianMomentUniformConstant h)) ^ h) *
          (2 ^ (h * h) : ℝ)) ^ (n + 1) * cQ ^ n *
        Real.sqrt (Critical2DKPZ.Polymer.sigmaSq β) ^ Nat.max (2 * (n + 1)) h := by
  simpa only [ccr25GaussianFiniteWordRun] using
    ccr25_finite_gaussian_partition_word_operator_bound
      s L lam β W hW hpq u v cU cQ left right hCU hCQ hleft hright
      hleft_bound hright_bound hU_bound hQ_bound hσ


end

end Critical2DKPZ.MomentBounds
