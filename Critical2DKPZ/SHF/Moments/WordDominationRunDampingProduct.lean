/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationPairRunCCR
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Damping cost for a finite sequence of pair runs -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds Polymer

/-- The undamped contribution of one distinguished collision and its pair renewal run. -/
def collisionWordUndampedPairRunFactor {h : ℕ} (β : ℝ) (α : CollisionPair h)
    (r : ℕ) (z x : LatticeConfiguration h) : ℝ :=
  (if z α.1.1 = z α.1.2 ∧ x α.1.1 = x α.1.2 then (1 : ℝ) else 0) *
    sigmaSq β * Collision.spatialRenewal (sigmaSq β) r
      (x α.1.1 - z α.1.1) *
    (∏ i : Fin h, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
      Critical2DKPZ.srwKernel r (x i - z i))


end Critical2DKPZ.SHF.Moments

end
