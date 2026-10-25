/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceSpatialTail
public import Critical2DKPZ.SHF.Moments.EntranceOrder
import Mathlib.Tactic

/-! # Spatial tail bounds for arbitrary collision clock windows -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments

/-- The canonical spatial entrance-tail bound applies to every subwindow,
with constants independent of the clocks and spatial tests. -/
theorem collisionEntrance_spatialTail_window_le :
    ∃ Creturn Cmoment : ℝ, 0 < Creturn ∧ 0 < Cmoment ∧
      ∀ N lo hi : ℕ, 0 < N → ∀ a b : Site, ∀ R M : ℝ, 0 < R → 0 ≤ M →
      ‖latticeRepresentative N a‖ ≤ R / 2 → ‖latticeRepresentative N b‖ ≤ R / 2 →
      ∀ F : ℝ × Plane → ℝ, (∀ u x, |F (u, x)| ≤ M) →
      (∀ u x, ‖x‖ ≤ R → F (u, x) = 0) →
      |collisionEntrance N lo hi a b F| ≤
        (2 * M / R) * (Creturn * (((hi : ℝ) + 1) / N) +
          2 * Cmoment * (Real.sqrt ((N : ℝ) / 2))⁻¹ * Real.sqrt ((hi : ℝ) + 1)) := by
  obtain ⟨Cr, Cm, hCr, hCm, hb⟩ := collisionEntrance_spatialTail_le
  refine ⟨Cr, Cm, hCr, hCm, ?_⟩
  intro N lo hi hN a b R M hR hM ha hbstart F hF hzero
  have htail := hb N hi hN a b R M hR hM ha hbstart (fun p => |F p|)
    (fun u x => by simpa only [abs_abs] using hF u x)
    (fun u x hx => by rw [hzero u x hx, abs_zero])
  calc
    |collisionEntrance N lo hi a b F| ≤ collisionEntrance N lo hi a b (fun p => |F p|) :=
      collisionEntrance_abs_le_absTest N lo hi a b F
    _ ≤ collisionEntrance N 0 hi a b (fun p => |F p|) :=
      collisionEntrance_mono_window N lo hi 0 hi a b _ (fun p => abs_nonneg _) (Nat.zero_le _) le_rfl
    _ ≤ |collisionEntrance N 0 hi a b (fun p => |F p|)| := le_abs_self _
    _ ≤ _ := htail

end Critical2DKPZ.SHF.Moments
