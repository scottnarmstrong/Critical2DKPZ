/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTerminalGeneral
public import Critical2DKPZ.SHF.Moments.CollisionProduct
import Mathlib.Tactic

/-! # Preservation of the terminal parity phase in the first-letter recursion -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Accessible intermediate configurations retain the even terminal phase
for the remaining duration, including odd entrance and run durations. -/
theorem word_recursion_terminal_phase {h : ℕ} (n s r : ℕ) (hsr : s + r ≤ n)
    (x u v : LatticeConfiguration h)
    (hx : ∀ i, Even (x i 0 + x i 1 + (n : ℤ)))
    (hu : u ∈ collisionWordConfigurationEndpointSet s x)
    (hv : v ∈ collisionWordConfigurationEndpointSet r u) :
    ∀ i, Even (v i 0 + v i 1 + ((n - s - r : ℕ) : ℤ)) := by
  intro i
  have hp := hx i
  have hs := endpoints_accessible_phase s (x i) (u i) (Fintype.mem_piFinset.mp hu i)
  have hr := endpoints_accessible_phase r (u i) (v i) (Fintype.mem_piFinset.mp hv i)
  rw [Int.even_iff] at hp hs hr ⊢
  simp only [Pi.sub_apply] at hs hr
  omega


end Critical2DKPZ.SHF.Moments
