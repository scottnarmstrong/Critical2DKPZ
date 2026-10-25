/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.LatticePowerSum
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic

/-! # Uniform one-coordinate sums with arbitrary lattice anchors -/

public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

/-- A shifted lattice sum of inverse powers satisfies the stated uniform bound. -/
theorem shifted_lattice_rpow_sum_bound {L r : ℝ} (hL : 1 ≤ L) (hr : 2 ≤ r) (w : Site) :
    Summable (fun z : Site => (L + ‖siteToPlane (z - w)‖ ^ 2) ^ (-r)) ∧
      (∑' z : Site, (L + ‖siteToPlane (z - w)‖ ^ 2) ^ (-r)) ≤ 9 * L ^ (1 - r) := by
  obtain ⟨hs, hb⟩ := lattice_rpow_sum_bound hL hr
  have he : (∑' z : Site, (L + ‖siteToPlane (z - w)‖ ^ 2) ^ (-r)) =
      ∑' z : Site, (L + ‖siteToPlane z‖ ^ 2) ^ (-r) :=
    (Equiv.subRight w).tsum_eq (fun z => (L + ‖siteToPlane z‖ ^ 2) ^ (-r))
  exact ⟨(Equiv.subRight w).summable_iff.mpr hs, he.trans_le hb⟩

/-- Arbitrary finite spatial cutoffs obey the same translation-uniform bound. -/
theorem sum_shifted_lattice_rpow_le {L r : ℝ} (hL : 1 ≤ L) (hr : 2 ≤ r)
    (w : Site) (s : Finset Site) :
    (∑ z ∈ s, (L + ‖siteToPlane (z - w)‖ ^ 2) ^ (-r)) ≤ 9 * L ^ (1 - r) := by
  obtain ⟨hs, hb⟩ := shifted_lattice_rpow_sum_bound hL hr w
  exact (hs.sum_le_tsum s (fun _ _ => Real.rpow_nonneg (by positivity) _)).trans hb

end Critical2DKPZ.MomentBounds
