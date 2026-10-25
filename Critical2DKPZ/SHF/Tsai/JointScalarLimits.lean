/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Filter.AtTopBot.Prod
import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-! # Identifying scalar limits through fixed-index limits

A joint limit controls a tail rectangle. Passing its distance bound through
each fiber limit identifies the outer limit with the same scalar.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- A joint scalar limit and all fixed-second-index fiber limits identify the outer scalar limit. -/
theorem tendsto_of_joint_of_scalar_fiber_limits (F : ℕ × ℕ → ℝ) (Y : ℕ → ℝ) (L : ℝ)
    (hJoint : Tendsto F atTop (𝓝 L))
    (hInner : ∀ n, Tendsto (fun k => F (k, n)) atTop (𝓝 (Y n))) :
    Tendsto Y atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨q, hq⟩ := (Metric.tendsto_atTop.1 hJoint) (ε / 2) (by positivity)
  refine ⟨q.2, fun n hn => ?_⟩
  have hdist : Tendsto (fun k => dist (F (k, n)) L) atTop (𝓝 (dist (Y n) L)) :=
    (hInner n).dist tendsto_const_nhds
  have hbound : ∀ᶠ k : ℕ in atTop, dist (F (k, n)) L ≤ ε / 2 := by
    filter_upwards [eventually_ge_atTop q.1] with k hk
    exact (hq (k, n) ⟨hk, hn⟩).le
  exact (le_of_tendsto hdist hbound).trans_lt (half_lt_self hε)

end Critical2DKPZ.SHF.Tsai

end
