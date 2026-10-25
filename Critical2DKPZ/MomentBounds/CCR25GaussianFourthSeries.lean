/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25GaussianRun
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # The fourth-moment Gaussian CCR25 run series -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- The operator coefficient of one Gaussian partition-word run, before its
factor of `sigmaSq` and the free-operator cost. -/
def ccr25GaussianFiniteWordOperatorScale (h : ℕ) (cU : ℝ) : ℝ :=
  cU * ((max 1 (ccr25GaussianMomentUniformConstant h)) ^ h) *
    (2 ^ (h * h) : ℝ)

/-- At order four, the run series is summable with the fourth Gaussian power supplied by its first run. -/
theorem ccr25GaussianFiniteWordRun_fourth_tsum_bound
    {h : ℕ} (hh : h = 4)
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
    (hu : ∀ I x, 0 ≤ u I x) (hv : ∀ I x, 0 ≤ v I x)
    (hσ : Polymer.sigmaSq β ≤ 1)
    (hsmall :
      (ccr25GaussianFiniteWordOperatorScale 4 cU * Polymer.sigmaSq β) * cQ < 1) :
    Summable (fun n => ccr25GaussianFiniteWordRun s L lam β u v n) ∧
      (∑' n, ccr25GaussianFiniteWordRun s L lam β u v n) ≤
        left * right * ccr25GaussianFiniteWordOperatorScale 4 cU *
            Polymer.sigmaSq β ^ 2 +
          left * right * (ccr25GaussianFiniteWordOperatorScale 4 cU) ^ 2 * cQ *
            Polymer.sigmaSq β ^ 2 /
              (1 - (ccr25GaussianFiniteWordOperatorScale 4 cU *
                Polymer.sigmaSq β) * cQ) := by
  subst h
  let A₀ := ccr25GaussianFiniteWordOperatorScale 4 cU
  let sig := Polymer.sigmaSq β
  let B := left * right
  let F : ℕ → ℝ := fun n => ccr25GaussianFiniteWordRun s L lam β u v n
  have hσnonneg : 0 ≤ sig := by
    dsimp [sig]
    exact sigmaSq_nonneg β
  have hsqrt : Real.sqrt sig ^ 2 = sig := Real.sq_sqrt hσnonneg
  have hA₀ : 0 ≤ A₀ := by
    dsimp [A₀, ccr25GaussianFiniteWordOperatorScale]
    positivity
  have hA : 0 ≤ A₀ * sig := mul_nonneg hA₀ hσnonneg
  have hsmall' : (A₀ * sig) * cQ < 1 := by simpa [A₀, sig] using hsmall
  have hbase :
      ∀ n, F (n + 1) ≤
        (B * (A₀ * sig) * cQ) * (A₀ * sig) ^ (n + 1) * cQ ^ n := by
    intro n
    have hrun := ccr25GaussianFiniteWordRun_le
      (h := 4) (n := n + 1) s L lam β W hW hpq u v cU cQ left right
      hCU hCQ hleft hright hleft_bound hright_bound hU_bound hQ_bound hσ
    have hmax : Nat.max (2 * ((n + 1) + 1)) 4 = 2 * ((n + 1) + 1) :=
      Nat.max_eq_left (by omega)
    rw [hmax] at hrun
    have hpow (m : ℕ) : Real.sqrt sig ^ (2 * m) = sig ^ m := by
      rw [pow_mul, hsqrt]
    rw [hpow (n + 2)] at hrun
    have hscale : A₀ =
        cU * ((max 1 (ccr25GaussianMomentUniformConstant 4)) ^ 4) *
          (2 ^ 16 : ℝ) := by
      dsimp [A₀, ccr25GaussianFiniteWordOperatorScale]
    have hrun' : F (n + 1) ≤ B * A₀ ^ (n + 2) * cQ ^ (n + 1) * sig ^ (n + 2) := by
      simpa [F, B, sig, hscale] using hrun
    have hfactor : B * A₀ ^ (n + 2) * cQ ^ (n + 1) * sig ^ (n + 2) =
        (B * (A₀ * sig) * cQ) * (A₀ * sig) ^ (n + 1) * cQ ^ n := by
      simp only [pow_succ, mul_pow]
      ring
    calc
      F (n + 1) ≤ B * A₀ ^ (n + 2) * cQ ^ (n + 1) * sig ^ (n + 2) := hrun'
      _ = _ := hfactor
  have hFnonneg : ∀ n, 0 ≤ F n := by
    intro n
    exact ccr25GaussianFiniteWordRun_nonneg s L lam β u v hu hv n
  have htail := ccr25_tsum_le_geometric_run_sum
    (F := fun n => F (n + 1)) (A₀ * sig) cQ (B * (A₀ * sig) * cQ)
    hA hCQ hsmall'
    (fun n => hFnonneg (n + 1)) hbase
  have hFsum : Summable F := (summable_nat_add_iff 1).mp htail.1
  have hfirst : F 0 ≤ B * A₀ * sig ^ 2 := by
    have hrun := ccr25GaussianFiniteWordRun_le
      (h := 4) (n := 0) s L lam β W hW hpq u v cU cQ left right
      hCU hCQ hleft hright hleft_bound hright_bound hU_bound hQ_bound hσ
    have hmax : Nat.max (2 * (0 + 1)) 4 = 4 := by norm_num
    rw [hmax] at hrun
    have hpow : Real.sqrt sig ^ 4 = sig ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hsqrt]
    simpa [F, B, A₀, sig, ccr25GaussianFiniteWordOperatorScale, hpow] using hrun
  have hsplit := hFsum.sum_add_tsum_nat_add 1
  have htailBound :
      (∑' n, F (n + 1)) ≤
        (B * (A₀ * sig) * cQ) * (A₀ * sig) /
          (1 - (A₀ * sig) * cQ) := by
    simpa [A₀, sig, B, div_eq_mul_inv] using htail.2
  refine ⟨hFsum, ?_⟩
  calc
    (∑' n, F n) = F 0 + ∑' n, F (n + 1) := by
      simpa only [Finset.sum_range_one] using hsplit.symm
    _ ≤ B * A₀ * sig ^ 2 +
          (B * (A₀ * sig) * cQ) * (A₀ * sig) /
            (1 - (A₀ * sig) * cQ) :=
      add_le_add hfirst htailBound
    _ = _ := by
      dsimp [A₀, sig, B, ccr25GaussianFiniteWordOperatorScale]
      ring

end

end Critical2DKPZ.MomentBounds

end
