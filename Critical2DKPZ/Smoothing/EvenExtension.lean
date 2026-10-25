/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.Endpoints
import Mathlib.Tactic

/-! # Even-lattice terminal weights -/

@[expose] public section

namespace Critical2DKPZ.Smoothing

/-- Extend a terminal weight by one off the even lattice, where lattice cells are empty. -/
def evenExtension (f : Site → ℝ) (z : Site) : ℝ :=
  if Even (z 0 + z 1) then f z else 1

/-- A walk of even length from an even site ends on the even lattice. -/
theorem reachable_even_of_even {w z : Site} {n : ℕ}
    (hw : Even (w 0 + w 1)) (hn : Even n)
    (hz : z ∈ Polymer.endpoints w n) : Even (z 0 + z 1) := by
  obtain ⟨s, hs⟩ := (Polymer.mem_endpoints_iff w z n).mp hz
  rw [← hs]
  have hnZ : Even (n : ℤ) := by exact_mod_cast hn
  have hsum : Even (w 0 + w 1 + (n : ℤ)) := by
    simp [Int.even_add, hw, hnZ]
  have hsumMod : Int.ModEq 2 (w 0 + w 1 + (n : ℤ)) 0 := by
    change (w 0 + w 1 + (n : ℤ)) % 2 = 0
    exact Int.even_iff.mp hsum
  have hmod := (Polymer.walkPosition_parity w s).trans hsumMod
  have hmodEq : (walkPosition w s n 0 + walkPosition w s n 1) % 2 = 0 := hmod
  exact Int.even_iff.mpr hmodEq

end Critical2DKPZ.Smoothing

end
