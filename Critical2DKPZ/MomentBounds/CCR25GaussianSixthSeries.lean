/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25GaussianRun
public import Critical2DKPZ.MomentBounds.CCR25GaussianFourthSeries
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # The sixth-moment Gaussian CCR25 run series -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- At order six, the first two run counts carry the full sixth Gaussian
power; from the third run onward the run count supplies the stronger
geometric variance power. -/
theorem ccr25GaussianFiniteWordRun_sixth_tsum_bound
    (s : Finset (LatticeConfiguration 6)) (L : ℕ) (lam β : ℝ)
    (W : LatticeConfiguration 6 → ℝ) (hW : ∀ x ∈ s, 0 < W x)
    {p q : ℝ} (hpq : p.HolderConjugate q)
    (u v : ReplicaPartition 6 → LatticeConfiguration 6 → ℝ)
    (cU cQ left right : ℝ)
    (hCU : 0 ≤ cU) (hCQ : 0 ≤ cQ) (hleft : 0 ≤ left) (hright : 0 ≤ right)
    (hleft_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s p (fun x => u I x / W x) ≤ left)
    (hright_bound : ∀ I, I ≠ ⊥ →
      finiteLpNorm s q (fun x => W x * v I x) ≤ right)
    (hU_bound : ∀ I, I ≠ ⊥ → ∀ f : LatticeConfiguration 6 → ℝ,
      finiteLpNorm s q
        (finiteKernelApply s
          (weightedKernel W (ccr25LabelKernel L lam β (.interacting I))) f) ≤
        cU * finiteLpNorm s q f)
    (hQ_bound : ∀ I J, I ≠ ⊥ → J ≠ ⊥ → I ≠ J →
      ∀ f : LatticeConfiguration 6 → ℝ,
      finiteLpNorm s q
        (finiteKernelApply s
          (weightedKernel W (ccr25LabelKernel L lam β (.free I J))) f) ≤
        cQ * finiteLpNorm s q f)
    (hu : ∀ I x, 0 ≤ u I x) (hv : ∀ I x, 0 ≤ v I x)
    (hσ : Polymer.sigmaSq β ≤ 1)
    (hsmall : (ccr25GaussianFiniteWordOperatorScale 6 cU * Polymer.sigmaSq β) * cQ < 1) :
    Summable (fun n => ccr25GaussianFiniteWordRun s L lam β u v n) ∧
      (∑' n, ccr25GaussianFiniteWordRun s L lam β u v n) ≤
        left * right *
          (ccr25GaussianFiniteWordOperatorScale 6 cU * Polymer.sigmaSq β ^ 3 +
            ccr25GaussianFiniteWordOperatorScale 6 cU ^ 2 * cQ * Polymer.sigmaSq β ^ 3 +
            ccr25GaussianFiniteWordOperatorScale 6 cU ^ 3 * cQ ^ 2 *
              Polymer.sigmaSq β ^ 3 /
                (1 - (ccr25GaussianFiniteWordOperatorScale 6 cU *
                  Polymer.sigmaSq β) * cQ)) := by
  let A₀ := ccr25GaussianFiniteWordOperatorScale 6 cU
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
  have hbase (n : ℕ) :
      F (n + 2) ≤
        (B * (A₀ * sig) ^ 2 * cQ ^ 2) * (A₀ * sig) ^ (n + 1) * cQ ^ n := by
    have hrun := ccr25GaussianFiniteWordRun_le
      (h := 6) (n := n + 2) s L lam β W hW hpq u v cU cQ left right
      hCU hCQ hleft hright hleft_bound hright_bound hU_bound hQ_bound hσ
    have hmax : Nat.max (2 * ((n + 2) + 1)) 6 = 2 * ((n + 2) + 1) := by
      apply Nat.max_eq_left
      omega
    rw [hmax] at hrun
    have hpow (m : ℕ) : Real.sqrt sig ^ (2 * m) = sig ^ m := by
      rw [pow_mul, hsqrt]
    rw [hpow (n + 3)] at hrun
    have hscale : A₀ =
        cU * ((max 1 (ccr25GaussianMomentUniformConstant 6)) ^ 6) *
          (2 ^ 36 : ℝ) := by
      dsimp [A₀, ccr25GaussianFiniteWordOperatorScale]
    have hrun' :
        F (n + 2) ≤ B * A₀ ^ (n + 3) * cQ ^ (n + 2) * sig ^ (n + 3) := by
      simpa [F, B, sig, hscale] using hrun
    have hfactor :
        B * A₀ ^ (n + 3) * cQ ^ (n + 2) * sig ^ (n + 3) =
          (B * (A₀ * sig) ^ 2 * cQ ^ 2) * (A₀ * sig) ^ (n + 1) * cQ ^ n := by
      rw [pow_add, pow_add, pow_add]
      ring
    calc
      F (n + 2) ≤ B * A₀ ^ (n + 3) * cQ ^ (n + 2) * sig ^ (n + 3) := hrun'
      _ = _ := hfactor
  have hFnonneg : ∀ n, 0 ≤ F n := by
    intro n
    exact ccr25GaussianFiniteWordRun_nonneg s L lam β u v hu hv n
  have htail := ccr25_tsum_le_geometric_run_sum
    (F := fun n => F (n + 2)) (A₀ * sig) cQ
    (B * (A₀ * sig) ^ 2 * cQ ^ 2) hA hCQ hsmall'
    (fun n => hFnonneg (n + 2)) (fun n => hbase n)
  have hFsum : Summable F := (summable_nat_add_iff 2).mp htail.1
  have hsplit := hFsum.sum_add_tsum_nat_add 2
  have hfirst : F 0 ≤ B * A₀ * sig ^ 3 := by
    have hrun := ccr25GaussianFiniteWordRun_le
      (h := 6) (n := 0) s L lam β W hW hpq u v cU cQ left right
      hCU hCQ hleft hright hleft_bound hright_bound hU_bound hQ_bound hσ
    have hmax : Nat.max (2 * (0 + 1)) 6 = 6 := by norm_num
    rw [hmax] at hrun
    have hpow : Real.sqrt sig ^ 6 = sig ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hsqrt]
    simpa [F, B, A₀, sig, ccr25GaussianFiniteWordOperatorScale, hpow] using hrun
  have hsecond : F 1 ≤ B * A₀ ^ 2 * cQ * sig ^ 3 := by
    have hrun := ccr25GaussianFiniteWordRun_le
      (h := 6) (n := 1) s L lam β W hW hpq u v cU cQ left right
      hCU hCQ hleft hright hleft_bound hright_bound hU_bound hQ_bound hσ
    have hmax : Nat.max (2 * (1 + 1)) 6 = 6 := by norm_num
    rw [hmax] at hrun
    have hpow : Real.sqrt sig ^ 6 = sig ^ 3 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, hsqrt]
    simpa [F, B, A₀, sig, ccr25GaussianFiniteWordOperatorScale, hpow] using hrun
  have htailBound :
      (∑' n, F (n + 2)) ≤
        B * (A₀ * sig) ^ 3 * cQ ^ 2 / (1 - (A₀ * sig) * cQ) := by
    have h := htail.2
    calc
      _ ≤ (B * (A₀ * sig) ^ 2 * cQ ^ 2) * (A₀ * sig) /
          (1 - (A₀ * sig) * cQ) := h
      _ = _ := by ring
  refine ⟨hFsum, ?_⟩
  have hsplit' :
      (∑' n, F n) = F 0 + F 1 + ∑' n, F (n + 2) := by
    rw [← hsplit]
    simp only [Finset.sum_range_succ]
    ring
  have htailBound' :
      (∑' n, F (n + 2)) ≤
        B * A₀ ^ 3 * cQ ^ 2 * sig ^ 3 /
          (1 - (A₀ * sig) * cQ) := by
    calc
      _ ≤ B * (A₀ * sig) ^ 3 * cQ ^ 2 /
          (1 - (A₀ * sig) * cQ) := htailBound
      _ = _ := by ring
  rw [hsplit']
  calc
    F 0 + F 1 + ∑' n, F (n + 2) ≤
        B * A₀ * sig ^ 3 + B * A₀ ^ 2 * cQ * sig ^ 3 +
          B * A₀ ^ 3 * cQ ^ 2 * sig ^ 3 /
            (1 - (A₀ * sig) * cQ) := add_le_add (add_le_add hfirst hsecond) htailBound'
    _ = _ := by
      dsimp [A₀, sig, B, ccr25GaussianFiniteWordOperatorScale]
      ring

end

end Critical2DKPZ.MomentBounds

end
