/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25GaussianFourthSeries
import Mathlib.Tactic

/-! # The higher-run remainder in the sharp CCR fourth moment estimate -/

@[expose] public noncomputable section

open Critical2DKPZ.MomentBounds
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- Removing the first two runs exposes an additional small geometric factor.
This is the operator-series estimate for the at-least-three-run remainder. -/
theorem summable_fourth_word_run_tail
    (s : Finset (LatticeConfiguration 4)) (L : ℕ) (lam β : ℝ)
    (W : LatticeConfiguration 4 → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : ReplicaPartition 4 → LatticeConfiguration 4 → ℝ)
    (cU cQ left right : ℝ)
    (hCU : 0 ≤ cU) (hCQ : 0 ≤ cQ) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hleft_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s p (fun x => u I x / W x) ≤ left)
    (hright_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s q (fun x => W x * v I x) ≤ right)
    (hU_bound : ∀ I, I ≠ ⊥ → ∀ f : LatticeConfiguration 4 → ℝ,
      finiteLpNorm s q
        (finiteKernelApply s
          (weightedKernel W (ccr25LabelKernel L lam β (.interacting I))) f) ≤
        cU * finiteLpNorm s q f)
    (hQ_bound : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
      ∀ f : LatticeConfiguration 4 → ℝ,
      finiteLpNorm s q
        (finiteKernelApply s
          (weightedKernel W (ccr25LabelKernel L lam β (.free I J))) f) ≤
        cQ * finiteLpNorm s q f)
    (hu : ∀ I x, 0 ≤ u I x) (hv : ∀ I x, 0 ≤ v I x)
    (hσ : Polymer.sigmaSq β ≤ 1)
    (hsmall :
      (ccr25GaussianFiniteWordOperatorScale 4 cU * Polymer.sigmaSq β) * cQ < 1) :
    Summable (fun n => ccr25GaussianFiniteWordRun s L lam β u v (n + 2)) ∧
      (∑' n, ccr25GaussianFiniteWordRun s L lam β u v (n + 2)) ≤
        left * right * (ccr25GaussianFiniteWordOperatorScale 4 cU) ^ 3 * cQ ^ 2 *
          Polymer.sigmaSq β ^ 3 /
            (1 - (ccr25GaussianFiniteWordOperatorScale 4 cU * Polymer.sigmaSq β) * cQ) := by
  let A := ccr25GaussianFiniteWordOperatorScale 4 cU
  let sig := Polymer.sigmaSq β
  let B := left * right
  let F : ℕ → ℝ := fun n => ccr25GaussianFiniteWordRun s L lam β u v (n + 2)
  have hsig : 0 ≤ sig := sigmaSq_nonneg β
  have hsqrt : Real.sqrt sig ^ 2 = sig := Real.sq_sqrt hsig
  have hA : 0 ≤ A := by dsimp [A, ccr25GaussianFiniteWordOperatorScale]; positivity
  have hbase (n : ℕ) :
      F n ≤ (B * (A * sig) ^ 2 * cQ ^ 2) * (A * sig) ^ (n + 1) * cQ ^ n := by
    have hrun := ccr25GaussianFiniteWordRun_le
      (h := 4) (n := n + 2) s L lam β W hW hpq u v cU cQ left right
      hCU hCQ hleft hright hleft_bound hright_bound hU_bound hQ_bound hσ
    have hmax : Nat.max (2 * ((n + 2) + 1)) 4 = 2 * ((n + 2) + 1) :=
      Nat.max_eq_left (by omega)
    rw [hmax] at hrun
    have hpow : Real.sqrt sig ^ (2 * ((n + 2) + 1)) = sig ^ ((n + 2) + 1) := by
      rw [pow_mul, hsqrt]
    change F n ≤ B * A ^ ((n + 2) + 1) * cQ ^ (n + 2) *
      Real.sqrt sig ^ (2 * ((n + 2) + 1)) at hrun
    rw [hpow] at hrun
    calc
      F n ≤ B * A ^ ((n + 2) + 1) * cQ ^ (n + 2) * sig ^ ((n + 2) + 1) := hrun
      _ = _ := by simp only [pow_succ, mul_pow]; ring
  have htail := ccr25_tsum_le_geometric_run_sum (F := F) (A * sig) cQ
    (B * (A * sig) ^ 2 * cQ ^ 2) (mul_nonneg hA hsig) hCQ hsmall
    (fun n => ccr25GaussianFiniteWordRun_nonneg s L lam β u v hu hv (n + 2)) hbase
  refine ⟨htail.1, htail.2.trans_eq ?_⟩
  dsimp only [A, sig, B]
  ring

end Critical2DKPZ.Extensions.GffTangent
