/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-! # Slowly diverging selectors preserving eventual estimates -/

@[expose] public noncomputable section

open Filter

namespace Critical2DKPZ.Extensions.GffTangent

/-- Given eventual estimates for every fixed index, choose an index tending
to infinity slowly enough that the corresponding estimate remains valid at
every sufficiently large original scale. The lattice scale is not reindexed. -/
theorem exists_slow_diagonal (P : ℕ → ℕ → Prop)
    (hP : ∀ k, ∀ᶠ N : ℕ in atTop, P k N) :
    ∃ k : ℕ → ℕ, Tendsto k atTop atTop ∧ (∀ N, k N ≤ N) ∧
      ∀ᶠ N : ℕ in atTop, P (k N) N := by
  classical
  have hthreshold : ∀ k, ∃ b : ℕ, ∀ N ≥ b, P k N :=
    fun k => eventually_atTop.mp (hP k)
  choose b hb using hthreshold
  let k : ℕ → ℕ := fun N => Nat.findGreatest (fun j => b j ≤ N) N
  refine ⟨k, ?_, fun N => Nat.findGreatest_le N, ?_⟩
  · apply tendsto_atTop.2
    intro j
    filter_upwards [eventually_ge_atTop (max j (b j))] with N hN
    exact Nat.le_findGreatest ((le_max_left _ _).trans hN) ((le_max_right _ _).trans hN)
  · filter_upwards [eventually_ge_atTop (b 0)] with N hN
    exact hb (k N) N (Nat.findGreatest_spec (P := fun j => b j ≤ N) (Nat.zero_le N) hN)

end Critical2DKPZ.Extensions.GffTangent
