/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordPotentialDomination
public import Critical2DKPZ.SHF.Moments.WordLimitDominationMass

/-! # Uniform gap-potential domination of collision-word masses -/

@[expose] public section

namespace Critical2DKPZ.SHF.Moments

/-- Terminal masses of collision words with at most four replicas satisfy uniform gap-potential domination. -/
theorem wordPotentialDomination (ϑ : ℝ) {h : ℕ} (hh : h ≤ 4) : WordPotentialDomination ϑ h := by
  intro T hT α w hchain
  exact eventually_word_mass_le_scaled_gapPotential ϑ hh hT α w hchain

end Critical2DKPZ.SHF.Moments
