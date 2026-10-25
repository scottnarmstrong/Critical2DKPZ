/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitGapPotential
public import Critical2DKPZ.SHF.Moments.WordLimitUniformSingleMass

/-! # The one-letter base of gap-potential domination -/

@[expose] public noncomputable section

open Filter
open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- One-letter terminal mass is dominated by the time-weighted gap potential,
with a constant uniform over every starting configuration. -/
theorem eventually_single_mass_le_gapPotential (ϑ T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * N →
      ∀ {h : ℕ} (α : CollisionPair h) (x : Fin h → Site),
      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) [α] n x (fun _ => 1) ≤
        B * Real.sqrt ((n : ℝ) + 1) * wordGapPotential n (x α.1.2 - x α.1.1) := by
  obtain ⟨B, hB, hrun⟩ := eventually_critical_run_mass_le ϑ T hT
  refine ⟨B, hB, hrun.mono fun N hrunN n hn h α x => ?_⟩
  have hslice (s : ℕ) (hs : s ∈ Finset.Icc 1 n) :
      srwKernel (2 * s) (x α.1.2 - x α.1.1) ≤
        Real.sqrt ((n : ℝ) + 1) *
          (srwKernel (2 * s) (x α.1.2 - x α.1.1) / Real.sqrt ((s : ℝ) + 1)) := by
    have hpos : 0 < Real.sqrt ((s : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have hsq : Real.sqrt ((s : ℝ) + 1) ≤ Real.sqrt ((n : ℝ) + 1) :=
      Real.sqrt_le_sqrt (add_le_add (Nat.cast_le.mpr (Finset.mem_Icc.mp hs).2) le_rfl)
    have hm := mul_le_mul_of_nonneg_left hsq
      (srwKernel_nonneg (2 * s) (x α.1.2 - x α.1.1))
    apply (le_div_iff₀ hpos).mpr at hm
    simpa only [mul_div_assoc, mul_comm] using hm
  rw [wordTerminalTest_single_one_eq]
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 n, B * srwKernel (2 * s) (x α.1.2 - x α.1.1) := by
      apply Finset.sum_le_sum
      intro s hs
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left
        (hrunN (n - s) ((Nat.cast_le.mpr (Nat.sub_le n s)).trans hn))
        (srwKernel_nonneg (2 * s) (x α.1.2 - x α.1.1))
    _ ≤ ∑ s ∈ Finset.Icc 1 n, B * (Real.sqrt ((n : ℝ) + 1) *
        (srwKernel (2 * s) (x α.1.2 - x α.1.1) / Real.sqrt ((s : ℝ) + 1))) :=
      Finset.sum_le_sum (fun s hs => mul_le_mul_of_nonneg_left (hslice s hs) hB.le)
    _ = _ := by simp only [wordGapPotential, Finset.mul_sum, mul_assoc]

/-- The one-letter base with the common diffusive normalization used by the
word induction, uniformly over all starting configurations. -/
theorem eventually_single_mass_le_scaled_gapPotential (ϑ T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * N →
      ∀ {h : ℕ} (α : CollisionPair h) (x : Fin h → Site),
      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) [α] n x (fun _ => 1) ≤
        C * Real.sqrt (N : ℝ) * wordGapPotential n (x α.1.2 - x α.1.1) := by
  obtain ⟨B, hB, hbound⟩ := eventually_single_mass_le_gapPotential ϑ T hT
  refine ⟨B * Real.sqrt (T + 1), mul_pos hB (Real.sqrt_pos.mpr (by linarith only [hT])), ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1] with N hboundN hN
  intro n hn h α x
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hclock : (n : ℝ) + 1 ≤ (T + 1) * N := by
    calc
      _ ≤ T * N + N := add_le_add hn hNr
      _ = _ := by ring
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (T + 1) * Real.sqrt (N : ℝ) := by
    calc
      _ ≤ Real.sqrt ((T + 1) * N) := Real.sqrt_le_sqrt hclock
      _ = _ := Real.sqrt_mul (by linarith only [hT]) _
  calc
    _ ≤ B * Real.sqrt ((n : ℝ) + 1) * wordGapPotential n (x α.1.2 - x α.1.1) :=
      hboundN n hn α x
    _ ≤ B * (Real.sqrt (T + 1) * Real.sqrt (N : ℝ)) *
        wordGapPotential n (x α.1.2 - x α.1.1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsqrt hB.le)
        (wordGapPotential_nonneg _ _)
    _ = _ := by ring

end Critical2DKPZ.SHF.Moments
