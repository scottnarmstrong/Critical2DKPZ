/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordTimeProfile
import Mathlib.Tactic

/-! # Interior time integration of the two-particle future profile -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- Clamping a real number stays in its closed interval. -/
theorem clamp_interval_mem {lo hi : ℝ} (hle : lo ≤ hi) (u : ℝ) :
    max lo (min hi u) ∈ Set.Icc lo hi :=
  ⟨le_max_left _ _, max_le hle (min_le_left _ _)⟩

/-- Clamping fixes every point of the closed interval. -/
theorem clamp_interval_eq {lo hi u : ℝ} (hu : u ∈ Set.Icc lo hi) :
    max lo (min hi u) = u := by
  rw [min_eq_right hu.2, max_eq_right hu.1]



end Critical2DKPZ.SHF.Moments

end
