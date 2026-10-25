/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceStrip
import Mathlib.Tactic

/-! # A macroscopic short-strip bound for separated entrance points -/

public section

namespace Critical2DKPZ.SHF.Moments

/-- The squared norm of a lattice representative is the squared lattice norm times the diffusive scale factor. -/
theorem norm_latticeRepresentative_sq (N : ℕ) (z : Site) :
    ‖latticeRepresentative N z‖ ^ 2 = (2 / (N : ℝ)) * ‖siteToPlane z‖ ^ 2 := by
  rw [latticeRepresentative, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
    Real.sq_sqrt (by positivity), inv_div]

/-- The off-diagonal entrance strip is O(epsilon + 1/N), with explicit separation dependence. -/
theorem collisionEntrance_scaled_short_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N K : ℕ, 0 < N → ∀ a b : Site,
      ∀ F : ℝ × Plane → ℝ, ∀ M d ε : ℝ,
      0 ≤ M → 0 < d → (∀ p, |F p| ≤ M) → (K : ℝ) ≤ ε * N →
      d ≤ ‖latticeRepresentative N (b - a)‖ →
      |collisionEntrance N 0 K a b F| ≤
        (2 * M * C / d ^ 2) * (ε + 1 / (N : ℝ)) := by
  obtain ⟨C, hC, h⟩ := collisionEntrance_short_strip_bound
  refine ⟨C, hC, fun N K hN a b F M d ε hM hd hF hK hsep => ?_⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hpn : 0 < ‖latticeRepresentative N (b - a)‖ := hd.trans_le hsep
  have hpn0 := ne_of_gt hpn
  have hraw : ‖siteToPlane (b - a)‖ ^ 2 =
      ((N : ℝ) / 2) * ‖latticeRepresentative N (b - a)‖ ^ 2 := by
    rw [norm_latticeRepresentative_sq]
    field_simp
  have hrawpos : 0 < ‖siteToPlane (b - a)‖ ^ 2 := by
    rw [hraw]
    positivity
  have hsep2 : d ^ 2 ≤ ‖latticeRepresentative N (b - a)‖ ^ 2 :=
    pow_le_pow_left₀ hd.le hsep 2
  have hratio : ((K : ℝ) + 1) / N ≤ ε + 1 / (N : ℝ) := by
    rw [div_le_iff₀ hNr]
    calc
      _ ≤ ε * N + 1 := add_le_add hK le_rfl
      _ = _ := by field_simp
  calc
    _ ≤ M * ((K : ℝ) + 1) * C / ‖siteToPlane (b - a)‖ ^ 2 := h N K a b F M hM hF hrawpos
    _ = (2 * M * C / ‖latticeRepresentative N (b - a)‖ ^ 2) *
        (((K : ℝ) + 1) / N) := by
      rw [hraw]
      field_simp [hpn0]
    _ ≤ (2 * M * C / d ^ 2) * (((K : ℝ) + 1) / N) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsep2
    _ ≤ _ := mul_le_mul_of_nonneg_left hratio (by positivity)

end Critical2DKPZ.SHF.Moments
