/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSeparated
public import Critical2DKPZ.SHF.Moments.EntranceScaling
import Mathlib.Tactic

/-! # Uniform diffusive potential bounds at separated starts -/

@[expose] public noncomputable section

open Filter
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- At a fixed positive macroscopic separation, the diffusive gap potential
is bounded uniformly in the volume and every shorter horizon. -/
theorem exists_scaled_wordGapPotential_separated_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (T δ : ℝ), 0 < T → 0 < δ →
      ∀ (N n : ℕ), 1 ≤ N → (n : ℝ) ≤ T * N → ∀ z : Site,
      δ ≤ ‖latticeRepresentative N z‖ →
      Real.sqrt (N : ℝ) * wordGapPotential n z ≤
        4 * C * T * Real.sqrt (T + 1) / δ ^ 4 := by
  obtain ⟨C, hC, hbound⟩ := exists_wordGapPotential_inverse_fourth_bound
  refine ⟨C, hC, fun T δ hT hδ N n hN hn z hz => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hzp : 0 < ‖latticeRepresentative N z‖ := hδ.trans_le hz
  have hraw : ‖siteToPlane z‖ ^ 2 =
      ((N : ℝ) / 2) * ‖latticeRepresentative N z‖ ^ 2 := by
    rw [norm_latticeRepresentative_sq]
    field_simp
  have hrawp : 0 < ‖siteToPlane z‖ := by
    have hp : 0 < ‖siteToPlane z‖ ^ 2 := by rw [hraw]; positivity
    nlinarith only [hp, norm_nonneg (siteToPlane z)]
  have hraw4 : ‖siteToPlane z‖ ^ 4 =
      (N : ℝ) ^ 2 * ‖latticeRepresentative N z‖ ^ 4 / 4 := by
    calc
      _ = (‖siteToPlane z‖ ^ 2) ^ 2 := by ring
      _ = _ := by rw [hraw]; ring
  have hclock : (n : ℝ) + 1 ≤ (T + 1) * N := by
    nlinarith only [hn, hN1]
  have hsqrt : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt (T + 1) * Real.sqrt (N : ℝ) := by
    exact (Real.sqrt_le_sqrt hclock).trans_eq (Real.sqrt_mul (by positivity) _)
  have hnum : Real.sqrt (N : ℝ) * (C * n * Real.sqrt ((n : ℝ) + 1)) ≤
      C * T * Real.sqrt (T + 1) * (N : ℝ) ^ 2 := by
    calc
      _ ≤ Real.sqrt (N : ℝ) * (C * (T * N) *
          (Real.sqrt (T + 1) * Real.sqrt (N : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        exact mul_le_mul (mul_le_mul_of_nonneg_left hn hC.le) hsqrt
          (Real.sqrt_nonneg _) (by positivity)
      _ = C * T * Real.sqrt (T + 1) * N * Real.sqrt (N : ℝ) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hNp.le]; ring
  calc
    _ ≤ Real.sqrt (N : ℝ) * (C * n * Real.sqrt ((n : ℝ) + 1) / ‖siteToPlane z‖ ^ 4) :=
      mul_le_mul_of_nonneg_left (hbound n z hrawp) (Real.sqrt_nonneg _)
    _ = (Real.sqrt (N : ℝ) * (C * n * Real.sqrt ((n : ℝ) + 1))) /
        ((N : ℝ) ^ 2 * ‖latticeRepresentative N z‖ ^ 4 / 4) := by
      rw [hraw4]
      ring
    _ ≤ (C * T * Real.sqrt (T + 1) * (N : ℝ) ^ 2) /
        ((N : ℝ) ^ 2 * ‖latticeRepresentative N z‖ ^ 4 / 4) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 4 * C * T * Real.sqrt (T + 1) / ‖latticeRepresentative N z‖ ^ 4 := by
      field_simp [hNp.ne', hzp.ne']
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (pow_pos hδ 4)
      (pow_le_pow_left₀ hδ.le hz 4)

/-- Potential domination gives a mass bound uniform over every separated
starting configuration, rather than only along a chosen moving sequence. -/
theorem eventually_wordTerminalTest_mass_le_uniform_of_potentialDomination
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (T δ : ℝ) (hT : 0 < T) (hδ : 0 < δ)
    (α : CollisionPair h) (w : List (CollisionPair h))
    (hw : (α :: w).IsChain (· ≠ ·)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      (n : ℝ) ≤ T * N → ∀ x : Fin h → Site,
      δ ≤ ‖latticeRepresentative N (x α.1.2 - x α.1.1)‖ →
      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) n x (fun _ => 1) ≤ C := by
  obtain ⟨C0, hC0, hmass⟩ := hD hT α w hw
  obtain ⟨C1, hC1, hpotential⟩ := exists_scaled_wordGapPotential_separated_bound
  refine ⟨C0 * (4 * C1 * T * Real.sqrt (T + 1) / δ ^ 4), by positivity, ?_⟩
  filter_upwards [hmass, eventually_ge_atTop 1] with N hmassN hN
  intro n hn x hx
  calc
    _ ≤ C0 * Real.sqrt (N : ℝ) * wordGapPotential n (x α.1.2 - x α.1.1) := hmassN n hn x
    _ = C0 * (Real.sqrt (N : ℝ) * wordGapPotential n (x α.1.2 - x α.1.1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hpotential T δ hT hδ N n hN hn _ hx) hC0.le

end Critical2DKPZ.SHF.Moments
