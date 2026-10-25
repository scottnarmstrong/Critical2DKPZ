/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.ProfileParity
public import Critical2DKPZ.MomentBounds.ProfileBoxes
import Critical2DKPZ.MomentBounds.DiffusiveWalkLower

/-! # Lower even-time energies for profiles concentrated in a finite box -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- Local CLT plus the parity split gives a lower energy bound for any profile with
half its mass in a box of diffusive radius. Constants precede all profile and time variables. -/
theorem exists_evenTimeEnergy_lower_of_box_mass (K : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      ∀ (φ : Site → ℝ), (∀ z, 0 ≤ φ z) → HasSum φ 1 → ∀ (x : Plane) (R : ℝ), 0 ≤ R →
        16 * (R + 3) ^ 2 ≤ K * n → (1 / 2 : ℝ) ≤ ∑ z ∈ profileBox x R, φ z →
          c / n ≤ ∑' z, ∑' w, φ z * srwKernel (2 * n) (z - w) * φ w := by
  obtain ⟨c, hc, N₀, hN₀, hwalk⟩ := exists_srwKernel_two_mul_lower K
  refine ⟨c / 16, by positivity, N₀, hN₀, fun n hn φ hφ hmass x R hR hscale hmassBox => ?_⟩
  obtain ⟨B, hB, hpar, hmassB⟩ := exists_parity_subset (profileBox x R) φ
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from lt_of_lt_of_le Nat.zero_lt_one (hN₀.trans hn))
  have hlower : ∀ z ∈ B, ∀ w ∈ B, c / n ≤ srwKernel (2 * n) (z - w) := by
    intro z hz w hw
    apply hwalk n hn (z - w) (hpar z hz w hw)
    have hzR := norm_le_of_mem_profileBox hR (hB hz)
    have hwR := norm_le_of_mem_profileBox hR (hB hw)
    have hnorm : ‖siteToPlane (z - w)‖ ≤ 4 * (R + 3) := by
      have heq : siteToPlane (z - w) = (siteToPlane z - x) - (siteToPlane w - x) := by
        ext i
        simp [siteToPlane]
      rw [heq]
      exact (norm_sub_le _ _).trans (by linarith only [hzR, hwR])
    have hsquare := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith only [hsquare, hscale]
  have hp : (1 / 4 : ℝ) ≤ ∑ z ∈ B, φ z := by linarith only [hmassBox, hmassB]
  have hp2 : (1 / 16 : ℝ) ≤ (∑ z ∈ B, φ z) ^ 2 := by nlinarith only [hp]
  calc
    _ = (c / n) * (1 / 16 : ℝ) := by ring
    _ ≤ (c / n) * (∑ z ∈ B, φ z) ^ 2 := mul_le_mul_of_nonneg_left hp2 (div_nonneg hc.le hn0.le)
    _ ≤ _ := evenTimeEnergy_ge_of_finite_lower n φ hφ hmass.summable B hlower

end Critical2DKPZ.MomentBounds
