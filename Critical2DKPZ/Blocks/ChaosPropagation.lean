/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Core
public import Critical2DKPZ.Polymer.Chaos
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Deterministic propagation through unoccupied blocks -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Blocks

/-- The empty-chaos coefficient of a discrepancy kernel. -/
def discrepancyHeatKernel (a b : ℕ) (x y : Site) : ℝ :=
  srwKernel (b - a) (y - x) - srwKernel b y


/-- The deterministic discrepancy kernel vanishes outside the union of the two walk endpoint sets. -/
theorem discrepancyHeatKernel_eq_zero_of_not_mem_support (a b : ℕ) (x y : Site)
    (hy : y ∉ Polymer.endpoints x (b - a) ∪ Polymer.endpoints 0 b) :
    discrepancyHeatKernel a b x y = 0 := by
  have hy1 : y ∉ Polymer.endpoints x (b - a) := fun h => hy (Finset.mem_union_left _ h)
  have hy2 : y ∉ Polymer.endpoints 0 b := fun h => hy (Finset.mem_union_right _ h)
  have hz := Polymer.srwKernel_eq_zero_of_not_mem b 0 y hy2
  simp only [sub_zero] at hz
  simp only [discrepancyHeatKernel,
    Polymer.srwKernel_eq_zero_of_not_mem (b - a) x y hy1, hz, sub_self]





end Critical2DKPZ.Blocks
