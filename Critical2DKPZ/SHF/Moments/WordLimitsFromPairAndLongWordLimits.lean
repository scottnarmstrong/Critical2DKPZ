/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SingleCollisionWordLimit
public import Critical2DKPZ.SHF.Moments.LowReplicaLongWordLimits

/-! # Empty, one-letter and longer collision-word limits -/

@[expose] public section

open Filter
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- The two-particle limit and the long-word limits imply tested continuum limits for every collision word. -/
theorem wordLimits_of (ϑ : ℝ) (hP : PairTwoWordLimit ϑ) {h : ℕ}
    (hL : LongWordLimits ϑ h) : WordLimits ϑ h := by
  intro s t hs hst sN tN hsN htN hsN0 φ m w
  cases m with
  | zero =>
      simpa only [List.ofFn_zero] using
        testedBlockWord_tendsto_nil ϑ hs hst sN tN hsN htN hsN0 φ
  | succ m =>
      cases m with
      | zero =>
          simpa only [List.ofFn_succ, List.ofFn_zero] using
            testedBlockWord_tendsto_single_of ϑ hP (w.1 0) hs hst sN tN hsN htN hsN0 φ
      | succ m =>
          exact hL hs hst sN tN hsN htN hsN0 φ m w

end Critical2DKPZ.SHF.Moments
