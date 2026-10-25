/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordBoundary
import Mathlib.Tactic

/-! # Continuity of the complete tested two-particle future profile -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- The complete continuum future, including both renewal-time endpoints. -/
def pairTwoContinuumFuture (θ H : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (a : Fin 2 → Plane) (z : Plane) : ℝ :=
  ∫ u in (0 : ℝ)..H, pairTwoTestedSpatialProfile θ u (H - u) φ a z


end Critical2DKPZ.SHF.Moments
