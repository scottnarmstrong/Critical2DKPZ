/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CSZ25Green

/-! # Quadratic moment summability under exponential localisation -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- Exponential localization supplies the summability needed for every centred quadratic moment. -/
theorem summable_quadratic_of_expLocalized (t c₁ : ℝ) (ht : 0 < t) (L : ℕ) (hL : 1 ≤ L)
    (φ : Site → ℝ) (hφ : ∀ z, 0 ≤ φ z) (hmass : HasSum φ 1)
    (hlocal : ExpLocalized t c₁ L φ) (x : Plane) :
    Summable (fun z => ‖siteToPlane z - x‖ ^ 2 * φ z) := by
  obtain ⟨x₀, hs, _⟩ := hlocal
  have h0 : Summable (fun z => ‖siteToPlane z - x₀‖ ^ 2 * φ z) := by
    apply Summable.of_nonneg_of_le (fun z => mul_nonneg (sq_nonneg _) (hφ z))
      (fun z => ?_) (hs.mul_left ((L : ℝ) / t ^ 2))
    have h := square_le_scaled_exp_of_sqrt t ht L (by omega)
      ‖siteToPlane z - x₀‖ (norm_nonneg _)
    calc
      _ ≤ (((L : ℝ) / t ^ 2) * Real.exp
          (2 * t * ‖siteToPlane z - x₀‖ / Real.sqrt L)) * φ z :=
        mul_le_mul_of_nonneg_right h (hφ z)
      _ = _ := by ring
  apply Summable.of_nonneg_of_le (fun z => mul_nonneg (sq_nonneg _) (hφ z))
    (fun z => ?_) ((h0.add (hmass.summable.mul_left (‖x₀ - x‖ ^ 2))).mul_left 2)
  have htri : ‖siteToPlane z - x‖ ≤ ‖siteToPlane z - x₀‖ + ‖x₀ - x‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hsq : ‖siteToPlane z - x‖ ^ 2 ≤ 2 * (‖siteToPlane z - x₀‖ ^ 2 + ‖x₀ - x‖ ^ 2) := by
    have h := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith only [h, sq_nonneg (‖siteToPlane z - x₀‖ - ‖x₀ - x‖)]
  calc
    _ ≤ (2 * (‖siteToPlane z - x₀‖ ^ 2 + ‖x₀ - x‖ ^ 2)) * φ z :=
      mul_le_mul_of_nonneg_right hsq (hφ z)
    _ = _ := by ring

end Critical2DKPZ.MomentBounds
