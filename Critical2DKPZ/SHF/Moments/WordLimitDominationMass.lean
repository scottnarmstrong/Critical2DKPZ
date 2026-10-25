/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitDominationInduction
public import Critical2DKPZ.SHF.Moments.WordLimitDominationTimeEnvelope
import Mathlib.Tactic.NormNum

/-! # Gap-potential domination of lattice word masses -/

@[expose] public section

open Filter Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- With at most four replicas, every fixed collision word with distinct consecutive letters has a uniform scaled-potential mass bound on each fixed diffusive horizon. -/
theorem eventually_word_mass_le_scaled_gapPotential (ϑ : ℝ) {h : ℕ} (hh : h ≤ 4)
    {T : ℝ} (hT : 0 < T) (α : CollisionPair h) (w : List (CollisionPair h))
    (hchain : (α :: w).IsChain (· ≠ ·)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * N →
      ∀ x : Fin h → Site,
      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) n x (fun _ => 1) ≤
        C * Real.sqrt (N : ℝ) * wordGapPotential n (x α.1.2 - x α.1.1) :=
  word_mass_domination_of_time_envelope ϑ hh 4 (by norm_num) wordGapTimeEnvelope_le hT α w hchain

end Critical2DKPZ.SHF.Moments
