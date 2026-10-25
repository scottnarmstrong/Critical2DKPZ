/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs
import Mathlib.Topology.Algebra.Support

/-! # The intermediate-variable cutoff in approximate flow -/

@[expose] public noncomputable section

open Filter Set
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- The cutoff takes values in the unit interval for every real radius. -/
theorem ballCutoff_mem_Icc (R : ℝ) (x : Plane) : ballCutoff R x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- The radial ball cutoff is continuous. -/
theorem continuous_ballCutoff (R : ℝ) : Continuous (ballCutoff R) := by
  unfold ballCutoff
  fun_prop

/-- The ball cutoff equals one inside its inner radius. -/
theorem ballCutoff_eq_one_of_norm_le {R : ℝ} {x : Plane} (hx : ‖x‖ ≤ R) :
    ballCutoff R x = 1 := by
  apply min_eq_left
  exact le_max_of_le_right (by linarith)

/-- The ball cutoff vanishes outside its outer radius. -/
theorem ballCutoff_eq_zero_of_le_norm {R : ℝ} {x : Plane} (hx : R + 1 ≤ ‖x‖) :
    ballCutoff R x = 0 := by
  simp only [ballCutoff, max_eq_left (by linarith : R + 1 - ‖x‖ ≤ 0), min_eq_right zero_le_one]

/-- Every radial ball cutoff has compact support. -/
theorem hasCompactSupport_ballCutoff (R : ℝ) : HasCompactSupport (ballCutoff R) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Plane) (R + 1))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  exact hx (ballCutoff_eq_zero_of_le_norm (lt_of_not_ge hn).le)

/-- At each fixed point the expanding ball cutoff eventually equals one. -/
theorem eventually_ballCutoff_eq_one (x : Plane) :
    ∀ᶠ R : ℝ in atTop, ballCutoff R x = 1 := by
  filter_upwards [eventually_ge_atTop ‖x‖] with R hR
  exact ballCutoff_eq_one_of_norm_le hR

/-- At each fixed point the expanding ball cutoff tends to one. -/
theorem tendsto_ballCutoff (x : Plane) :
    Tendsto (fun R : ℝ => ballCutoff R x) atTop (𝓝 1) :=
  (tendsto_congr' (eventually_ballCutoff_eq_one x)).2 tendsto_const_nhds

end Critical2DKPZ.SHF.Tsai

end
