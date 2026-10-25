/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitPotentialTimeBound
import all Critical2DKPZ.SHF.Moments.EntranceWalkMoments

/-! # The uniform numerical smoothing envelope -/

@[expose] public noncomputable section

namespace Critical2DKPZ.SHF.Moments

/-- The free-spectator time envelope is bounded by `4 / √(m + 1)`. -/
theorem wordGapTimeEnvelope_le (m : ℕ) :
    wordGapTimeEnvelope m ≤ 4 / Real.sqrt ((m : ℝ) + 1) :=
  wordGapTimeEnvelope_le_of_initial_sum m (sum_inv_sqrt_add_one_le m)

end Critical2DKPZ.SHF.Moments
