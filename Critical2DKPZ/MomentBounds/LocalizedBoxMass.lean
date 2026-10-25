/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.ProfileConcentration
public import Critical2DKPZ.MomentBounds.CSZ25Green

/-! # A uniform diffusive box containing half the localized profile mass -/

@[expose] public noncomputable section

namespace Critical2DKPZ.MomentBounds

/-- Exponential localization yields a finite profile box carrying a fixed amount of mass. -/
theorem exists_profileBox_mass_ge_of_expLocalized (t c₁ : ℝ) (ht : 0 < t) (hc₁ : 0 < c₁) :
    ∃ R : ℝ, 0 < R ∧ ∀ L : ℕ, 1 ≤ L → ∀ φ : Site → ℝ, (∀ z, 0 ≤ φ z) → HasSum φ 1 →
      ExpLocalized t c₁ L φ → ∃ x : Plane, (1 / 2 : ℝ) ≤
        ∑ z ∈ profileBox x (R * Real.sqrt L), φ z := by
  let R := (|Real.log (4 * c₁)| + 1) / (2 * t)
  have hR : 0 < R := div_pos (by positivity) (mul_pos (by norm_num) ht)
  refine ⟨R, hR, fun L hL φ hφ hmass hlocal => ?_⟩
  obtain ⟨x, hs, hC⟩ := hlocal
  have hL0 : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hroot : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 hL0
  let a := 2 * t / Real.sqrt (L : ℝ)
  have heq : (fun z => φ z * Real.exp (2 * t * ‖siteToPlane z - x‖ / Real.sqrt L)) =
      (fun z => φ z * Real.exp (a * ‖siteToPlane z - x‖)) := by
    funext z
    dsimp [a]
    congr 2
    ring
  rw [heq] at hs hC
  have hb := profileBox_mass_ge_exponential φ hφ hmass x
    (R := R * Real.sqrt L) (div_nonneg (by positivity) hroot.le) hs hC
  have hrate : a * (R * Real.sqrt L) = 2 * t * R := by dsimp [a]; field_simp
  have hlog : Real.log (4 * c₁) ≤ 2 * t * R := by
    have hr : 2 * t * R = |Real.log (4 * c₁)| + 1 := by dsimp [R]; field_simp
    rw [hr]
    exact (le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)
  have hsmall : Real.exp (-a * (R * Real.sqrt L)) * c₁ ≤ 1 / 4 := by
    rw [neg_mul, hrate]
    calc
      _ ≤ Real.exp (-Real.log (4 * c₁)) * c₁ :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (neg_le_neg hlog)) hc₁.le
      _ = _ := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  exact ⟨x, by linarith only [hb, hsmall]⟩

end Critical2DKPZ.MomentBounds
