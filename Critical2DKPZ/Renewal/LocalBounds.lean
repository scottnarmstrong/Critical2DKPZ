/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.MarkedIdentity
public import Critical2DKPZ.Renewal.CriticalWindow
import Critical2DKPZ.RandomWalk.ReplicaOverlap

/-!
# Local bounds from marked cumulative renewal functions

The differentiated renewal identity controls a local mass by the marked cumulative
mass. The period-2 local CLT supplies the uniform first-moment bound on step weights.
-/

@[expose] public noncomputable section

namespace Critical2DKPZ.Renewal

/-- The marked cumulative renewal function increases with time. -/
theorem markedRenewalFunction_mono_time {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) :
    Monotone (markedRenewalFunction w) := by
  intro m n hmn
  rw [← sum_markedRenewalMass_range, ← sum_markedRenewalMass_range]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right hmn 1))
    (fun r _ _ => markedRenewalMass_nonneg hw r)

/-- A uniform bound on time times the step kernel controls time times renewal mass by the marked cumulative function. -/
theorem mul_renewalMass_le_markedRenewalFunction {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    {C : ℝ} (hC : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * w r ≤ C) (n : ℕ) :
    ((n : ℝ) + 1) * renewalMass w (n + 1) ≤ C * markedRenewalFunction w n := by
  rw [mul_renewalMass_eq]
  simp_rw [renewalSquare_eq_markedRenewalMass]
  calc
    _ ≤ ∑ r ∈ Finset.range (n + 1), C * markedRenewalMass w (n - r) := by
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_right _ (markedRenewalMass_nonneg hw _)
      simpa only [Nat.cast_add, Nat.cast_one] using hC (r + 1) (by omega)
    _ = C * markedRenewalFunction w n := by
      rw [← Finset.mul_sum, ← sum_markedRenewalMass_range]
      congr 1
      simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect (markedRenewalMass w) (n + 1)

/-- Time times the return weight is uniformly bounded over positive integer times. -/
theorem exists_returnWeight_moment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 1 ≤ r → (r : ℝ) * returnWeight r ≤ C := by
  obtain ⟨K, hK, he⟩ := srwKernel_two_mul_zero_localCLT
  refine ⟨1 / Real.pi + K, add_pos (one_div_pos.mpr Real.pi_pos) hK, ?_⟩
  intro r hr
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans_le hrR
  have he' := (abs_le.mp (he r hr)).2
  have hk : K / (r : ℝ) ^ 2 ≤ K / r := by
    apply div_le_div_of_nonneg_left hK.le hr0
    nlinarith only [hrR]
  have hret : srwKernel (2 * r) 0 ≤ (1 / Real.pi) * (r : ℝ)⁻¹ + K / r := by
    linarith only [he', hk]
  have h := mul_le_mul_of_nonneg_left hret hr0.le
  change (r : ℝ) * returnWeight r ≤ _
  dsimp only [returnWeight]
  have hc : (r : ℝ) * ((1 / Real.pi) * (r : ℝ)⁻¹ + K / r) = 1 / Real.pi + K := by
    field_simp
  exact h.trans_eq hc

end Critical2DKPZ.Renewal

end
