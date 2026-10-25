/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainMeasurability
public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.RandomMeasure.GeneralRandom

/-! # The common measurable approximation map for interval blocks

The approximation is defined on a finite tuple of measures, independently of
the probability space. On locally finite tuples it is the literal heat-smoothed
chain pairing, and it is zero elsewhere. Canonical locally finite modifications
prove measurability without changing the function on its defining event.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The heat-kernel mollifier `u_ℓ = g_{1/(ℓ+1)}` of dense-time uniqueness. -/
def heatMollifier (ℓ : ℕ) : Plane → ℝ := heatKernel (1 / ((ℓ : ℝ) + 1))



end Critical2DKPZ.SHF.Tsai

end
