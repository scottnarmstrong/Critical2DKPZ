/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitTerminal
public import Critical2DKPZ.SHF.Moments.WordLimitGapPotential

/-! # Uniform gap-potential bounds for collision-word terminal masses -/

@[expose] public section

open Filter
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- For collision words with distinct consecutive letters, the lattice terminal mass is bounded by √N times the initial-pair gap potential uniformly over starts and horizons n ≤ TN for sufficiently large N. -/
def WordPotentialDomination (ϑ : ℝ) (h : ℕ) : Prop :=
  ∀ {T : ℝ}, 0 < T → ∀ (α : CollisionPair h) (w : List (CollisionPair h)),
    (α :: w).IsChain (· ≠ ·) →
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * N → ∀ x : Fin h → Site,
      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) n x (fun _ => 1) ≤
        C * Real.sqrt (N : ℝ) * wordGapPotential n (x α.1.2 - x α.1.1)

end Critical2DKPZ.SHF.Moments
