/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceWindows
import Mathlib.Tactic

/-! # Exact two-particle representations uniform in moving time endpoints -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter DeltaBose
open scoped CompactlySupported Topology

/-- The tuning threshold in the exact entrance representation is independent
of both time endpoints. -/
theorem eventually_testedBlockWord_pairTwo_eq_entranceWindow_all_times
    (ϑ : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ,
      testedBlockWord ϑ N s t φ [pairTwo] =
        pairTwoTestedEntranceWindow ϑ N (evenCeil (N * t) - evenCeil (N * s))
          1 (evenCeil (N * t) - evenCeil (N * s)) φ (fun _ => 1) := by
  filter_upwards [eventually_testedBlockWord_pairTwo_eq_sampledEntrance_all_times ϑ φ] with N hN
  intro s t
  simpa only [pairTwoTestedEntranceWindow, one_mul] using hN s t


end Critical2DKPZ.SHF.Moments
