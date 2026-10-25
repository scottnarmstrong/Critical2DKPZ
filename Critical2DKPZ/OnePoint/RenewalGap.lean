/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Chaos
public import Critical2DKPZ.RandomWalk.ReplicaOverlap
import Mathlib.Tactic

/-!
# Renewal gap and the logarithmic replica-overlap estimate

The gap follows the paper's convention `π/σ² − π R_s`; the overlap estimate
retains the period-two walk normalization.
-/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.OnePoint

/-- `ϑ_N(s) = π / σ² − π R_s`, with `σ² = e^{β²} − 1`. -/
def renewalGap (β : ℝ) (s : ℕ) : ℝ :=
  Real.pi / Polymer.sigmaSq β - Real.pi * replicaOverlap s

/-- The period-two replica overlap differs from the logarithmic scale by a bounded amount. -/
theorem replicaOverlap_sub_log_bounded :
    ∃ C : ℝ, ∀ s t : ℕ, s ≤ t →
      |Real.pi * (replicaOverlap t - replicaOverlap s) -
        Real.log (((max t 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ))| ≤ C := by
  obtain ⟨C, hC⟩ := Critical2DKPZ.replicaOverlap_log_bound
  have hCnonneg : 0 ≤ C := by
    have h := hC 1 (by omega)
    exact le_trans (abs_nonneg _) h
  have hpiC : 0 ≤ Real.pi * C := mul_nonneg Real.pi_pos.le hCnonneg
  have happrox (n : ℕ) :
      |Real.pi * replicaOverlap n - Real.log ((max n 1 : ℕ) : ℝ)| ≤ Real.pi * C := by
    by_cases hn : n = 0
    · subst n
      simpa [replicaOverlap] using hpiC
    · have hn1 : 1 ≤ n := by omega
      have hnmax : max n 1 = n := max_eq_left (by omega)
      rw [hnmax]
      have h := hC n hn1
      have heq : Real.pi * replicaOverlap n - Real.log (n : ℝ) =
          Real.pi * (replicaOverlap n - (1 / Real.pi) * Real.log n) := by
        rw [mul_sub]
        field_simp
      rw [heq, abs_mul, abs_of_pos Real.pi_pos]
      exact mul_le_mul_of_nonneg_left h Real.pi_pos.le
  refine ⟨2 * (Real.pi * C), fun s t hst => ?_⟩
  have hmpos (n : ℕ) : 0 < ((max n 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < max n 1 by omega)
  have hlog :
      Real.log (((max t 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) =
        Real.log ((max t 1 : ℕ) : ℝ) - Real.log ((max s 1 : ℕ) : ℝ) :=
    Real.log_div (ne_of_gt (hmpos t)) (ne_of_gt (hmpos s))
  have hsplit :
      Real.pi * (replicaOverlap t - replicaOverlap s) -
        Real.log (((max t 1 : ℕ) : ℝ) / ((max s 1 : ℕ) : ℝ)) =
      (Real.pi * replicaOverlap t - Real.log ((max t 1 : ℕ) : ℝ)) -
        (Real.pi * replicaOverlap s - Real.log ((max s 1 : ℕ) : ℝ)) := by
    rw [hlog]
    ring
  rw [hsplit]
  have habs := abs_add_le
    (Real.pi * replicaOverlap t - Real.log ((max t 1 : ℕ) : ℝ))
    (-(Real.pi * replicaOverlap s - Real.log ((max s 1 : ℕ) : ℝ)))
  rw [abs_neg] at habs
  calc
    |(Real.pi * replicaOverlap t - Real.log ((max t 1 : ℕ) : ℝ)) -
        (Real.pi * replicaOverlap s - Real.log ((max s 1 : ℕ) : ℝ))|
      ≤ |Real.pi * replicaOverlap t - Real.log ((max t 1 : ℕ) : ℝ)| +
        |Real.pi * replicaOverlap s - Real.log ((max s 1 : ℕ) : ℝ)| := habs
    _ ≤ Real.pi * C + Real.pi * C := add_le_add (happrox t) (happrox s)
    _ = 2 * (Real.pi * C) := by ring

end Critical2DKPZ.OnePoint
