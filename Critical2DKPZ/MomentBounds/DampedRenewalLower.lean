/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.TruncatedRenewalLower

/-! # The damped renewal lower bound underlying CSZ25 Lemma 5.5 -/

@[expose] public noncomputable section

open Critical2DKPZ.Renewal

namespace Critical2DKPZ.MomentBounds

/-- A reciprocal step bound controls the first-moment loss at half the cutoff. The
parameter `σ` denotes the disorder variance, rather than its square root. -/
theorem half_geometric_le_damped_renewal (q : ℕ → ℝ) (hq : ∀ r, 0 ≤ q r)
    {A σ damping : ℝ} (hA : 0 < A) (hσ : 0 ≤ σ) (hdamping : 0 ≤ damping)
    (hupper : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * q r ≤ A) (L : ℕ) :
    let D := ∑ r ∈ Finset.Icc 1 L, Real.exp (-damping * r / L) * q r
    σ * (D + 4 * A) ≤ 1 →
      1 / (2 * (1 - σ * D)) ≤ renewalFunction (fun r => σ * q r) (L / 2) := by
  intro D hc
  let w : ℕ → ℝ := fun r => σ * (Real.exp (-damping * r / L) * q r)
  have hw : ∀ r, 0 ≤ w r := fun r => mul_nonneg hσ
    (mul_nonneg (Real.exp_pos _).le (hq r))
  have hexp : ∀ r : ℕ, Real.exp (-damping * r / L) ≤ 1 := by
    intro r
    apply Real.exp_le_one_iff.2
    exact div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hdamping) (Nat.cast_nonneg r))
      (Nat.cast_nonneg L)
  have hD : 0 ≤ D := Finset.sum_nonneg fun r _ =>
    mul_nonneg (Real.exp_pos _).le (hq r)
  have hmass : cutoffMass w L = σ * D := by
    dsimp [cutoffMass, w, D]
    rw [Finset.mul_sum]
  have hsub : cutoffMass w L < 1 := by
    rw [hmass]
    by_cases hs0 : σ = 0
    · simp only [hs0, zero_mul, zero_lt_one]
    · have hspos : 0 < σ := lt_of_le_of_ne hσ (Ne.symm hs0)
      nlinarith only [hc, mul_pos hspos hA]
  have hfirst : cutoffFirstMoment w L ≤ σ * A * L := by
    calc
      _ ≤ ∑ _r ∈ Finset.Icc 1 L, σ * A := by
        apply Finset.sum_le_sum
        intro r hr
        have hu := hupper r (Finset.mem_Icc.1 hr).1
        dsimp [w]
        calc
          (r : ℝ) * (σ * (Real.exp (-damping * r / L) * q r)) =
              σ * (Real.exp (-damping * r / L) * ((r : ℝ) * q r)) := by ring
          _ ≤ σ * ((r : ℝ) * q r) := mul_le_mul_of_nonneg_left
            (mul_le_of_le_one_left (mul_nonneg (Nat.cast_nonneg r) (hq r)) (hexp r)) hσ
          _ ≤ σ * A := mul_le_mul_of_nonneg_left hu hσ
      _ = _ := by simp [mul_comm]
  have hhalf : (L : ℝ) ≤ 2 * ((L / 2 : ℕ) + 1 : ℝ) := by
    exact_mod_cast (show L ≤ 2 * (L / 2 + 1) by omega)
  have hsmall : 2 * cutoffFirstMoment w L ≤
      (↑(L / 2) + 1 : ℝ) * (1 - cutoffMass w L) := by
    rw [hmass]
    have hgap : 4 * (σ * A) ≤ 1 - σ * D := by nlinarith only [hc]
    have hf := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hσ hA.le)
    have hg := mul_le_mul_of_nonneg_left hgap (by positivity : (0 : ℝ) ≤ (L / 2 : ℕ) + 1)
    nlinarith only [hfirst, hf, hg]
  have hlower := half_geometric_le_renewalFunction hw (Nat.div_le_self L 2) hsub hsmall
  rw [hmass] at hlower
  apply hlower.trans
  apply renewalFunction_mono hw
  intro r
  exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (hq r) (hexp r)) hσ

end Critical2DKPZ.MomentBounds
