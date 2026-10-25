/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordLimitFromEntranceIntegrals
public import Critical2DKPZ.SHF.Moments.SinglePairWordTestedDiagramIdentity
public import Critical2DKPZ.SHF.Moments.SinglePairWordDiscreteCutoffExhaustion
public import Critical2DKPZ.SHF.Moments.SinglePairWordFullCutoffLimit

/-! # Moving two-particle word limits -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments

/-- A single resummed pair block converges to its delta-Bose diagram along moving time endpoints with a positive finite limiting gap. -/
theorem pairTwoWordLimit (ϑ : ℝ) : PairTwoWordLimit ϑ :=
  pairTwoWordLimit_of_entrance_identification_and_cutoff_limits ϑ
    tested_pairTwo_diagram_eq_continuum_entrance
    pairTwo_entrance_cutoff_exhaustion_error
    tendsto_pairTwoTestedEntranceWindow_full_cutoff

end Critical2DKPZ.SHF.Moments
