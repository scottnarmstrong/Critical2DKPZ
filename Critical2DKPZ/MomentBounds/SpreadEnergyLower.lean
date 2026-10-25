/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.BoxEnergyLower
public import Critical2DKPZ.MomentBounds.ProfileConcentration

/-! # Even-time energy lower bounds above the profile spread scale -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- Universal reciprocal-time energy bound once time dominates the profile spread. -/
theorem exists_evenTimeEnergy_lower_of_spread :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ n : ℕ, N₀ ≤ n →
      ∀ φ : Site → ℝ, (∀ z, 0 ≤ φ z) → HasSum φ 1 →
        Summable (fun z => ‖siteToPlane z - profileMean φ‖ ^ 2 * φ z) →
        profileSpread φ + 1 ≤ n →
          c / n ≤ ∑' z, ∑' w, φ z * srwKernel (2 * n) (z - w) * φ w := by
  obtain ⟨c, hc, N₀, hN₀, henergy⟩ := exists_evenTimeEnergy_lower_of_box_mass 400
  refine ⟨c, hc, N₀, hN₀, fun n hn φ hφ hmass hquad hspread => ?_⟩
  let D := profileSpread φ
  let R := 2 * Real.sqrt (D + 1)
  have hD : 0 ≤ D := profileSpread_nonneg φ hφ
  have hroot : 1 ≤ Real.sqrt (D + 1) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt (show 1 ≤ D + 1 by linarith only [hD])
  have hR : 0 < R := by dsimp [R]; positivity
  have hRsq : R ^ 2 = 4 * (D + 1) := by
    dsimp [R]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have hsmall : D / R ^ 2 ≤ 1 / 4 := by
    apply (div_le_iff₀ (sq_pos_of_pos hR)).2
    rw [hRsq]
    linarith
  have hbox := profileBox_mass_ge_quadratic φ hφ hmass (profileMean φ) hR hquad (le_refl D)
  apply henergy n hn φ hφ hmass (profileMean φ) R hR.le _ (by linarith only [hbox, hsmall])
  have hr : R + 3 ≤ 5 * Real.sqrt (D + 1) := by dsimp [R]; linarith only [hroot]
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ R + 3) hr 2
  rw [mul_pow, Real.sq_sqrt (by positivity)] at hs
  nlinarith only [hs, hspread]

end Critical2DKPZ.MomentBounds
