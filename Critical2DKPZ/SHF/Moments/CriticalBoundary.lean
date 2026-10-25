/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.BoundaryConvention
public import Critical2DKPZ.Renewal.CriticalWindow
import Mathlib.Tactic

/-! # Vanishing endpoint error at critical coupling -/

public section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- The critical inverse temperature tends to zero as the lattice scale diverges. -/
theorem tendsto_criticalBeta_zero (ϑ : ℝ) :
    Tendsto (criticalBeta ϑ) atTop (𝓝 0) := by
  change Tendsto (fun N => Real.sqrt (Real.log (1 + criticalSigmaSq ϑ N))) atTop (𝓝 0)
  have h := (tendsto_const_nhds (x := (1 : ℝ))).add (Renewal.tendsto_sigma_zero ϑ)
  have hl := h.log (by norm_num : (1 : ℝ) + 0 ≠ 0)
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hl
  simpa only [add_zero, Real.log_one, Real.sqrt_zero, Function.comp_def] using hs


end Critical2DKPZ.SHF.Moments
