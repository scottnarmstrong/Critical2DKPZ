/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.AiiKCollisionWeight
import Mathlib.Tactic

/-! # The weighted terminal collision profile at exponent two -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- For weight parameter `0 < t ≤ 1`, the exponentially weighted `ℓ²` norm of a nontrivial collision indicator is bounded by `(C/t)^(h-1)`, uniformly over finite supports. -/
theorem finiteLpNorm_weight_collisionIndicator_two_le :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h : ℕ, 1 ≤ h → ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∀ (s : Finset (LatticeConfiguration h)) (I : ReplicaPartition h), I ≠ ⊥ →
      finiteLpNorm s 2 (fun x => replicaExponentialWeight t x * collisionIndicator I x) ≤
        (C / t) ^ (h - 1) := by
  obtain ⟨C, hC, hbound⟩ := finiteLpNorm_weight_mul_collisionIndicator_le
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  refine ⟨Real.sqrt C, ?_, ?_⟩
  · simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hC
  · intro h hh t ht ht1 s I hI
    have hb := hbound h t ht ht1 2 (by norm_num) s I hI
    have hexp : ((h : ℝ) - 1) / 2 = (1 / 2 : ℝ) * ((h - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hh]
      push_cast
      ring
    rw [hexp, Real.rpow_mul_natCast (div_nonneg hC0 (sq_nonneg t)),
      ← Real.sqrt_eq_rpow, Real.sqrt_div hC0,
      Real.sqrt_sq_eq_abs, abs_of_pos ht] at hb
    exact hb

end Critical2DKPZ.SHF.Moments

end
