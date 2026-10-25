/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSamplePotential
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitBounds
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitDiagonal
import Mathlib.Tactic

/-! # A fixed spatial majorant for the sampled shorter-word test -/

@[expose] public noncomputable section

open Filter MeasureTheory
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- Collision sampling is the canonical scalar phase sample on every
embedded coordinate. -/
theorem wordCollisionPhaseSample_apply {h : ℕ} (N k : ℕ) (α : CollisionPair h)
    (v : FusedConfiguration α) (i : Fin h) :
    wordCollisionPhaseSample N k α v i =
      pairTwoFutureSampleSite N k (collisionEmbedding α v i) := by
  unfold wordCollisionPhaseSample collisionEmbedding
  split_ifs <;> rfl



end Critical2DKPZ.SHF.Moments
