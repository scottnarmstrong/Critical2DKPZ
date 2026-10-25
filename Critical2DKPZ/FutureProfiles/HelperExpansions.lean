/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.Expansion
public import Critical2DKPZ.FutureProfiles.Basic
import Mathlib.Tactic

/-! # Future-profile identities from block expansions -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

open Critical2DKPZ.Blocks

/-- The smoothed endpoint profile error after subtracting the common correction. -/
theorem smoothedEndpointDist_sub_commonCorrection_eq (β : ℝ) {t : ℕ → ℕ}
    (ht : Monotone t) {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s)
    (ω : Disorder) (y : Site) :
    smoothedEndpointDist β (t (r - 1)) (t s) 0 ω y - srwKernel (t s) y -
        commonCorrection β t r s ω y =
      (blockRatio β t r s ω)⁻¹ * ∑ u ∈ Finset.Icc r s,
          (blockRatio β t r (u - 1) ω - 1) * openCorrector β t u s ω y +
        (1 - blockRatio β t r s ω) / blockRatio β t r s ω *
          commonCorrection β t r s ω y := by
  have hR : 0 < blockRatio β t r s ω := by
    unfold blockRatio
    exact div_pos (Polymer.smoothedP2Plane_pos β (t (r - 1)) (t s) 0 ω)
      (Finset.prod_pos fun i _ => blockMass_pos β t i ω)
  have hsum :
      (∑ u ∈ Finset.Icc r s,
          (blockRatio β t r (u - 1) ω - 1) * openCorrector β t u s ω y) =
        (∑ u ∈ Finset.Icc r s,
          blockRatio β t r (u - 1) ω * openCorrector β t u s ω y) -
          commonCorrection β t r s ω y := by
    calc
      _ = ∑ u ∈ Finset.Icc r s,
          (blockRatio β t r (u - 1) ω * openCorrector β t u s ω y -
            openCorrector β t u s ω y) := by
          apply Finset.sum_congr rfl
          intro u hu
          ring
      _ = (∑ u ∈ Finset.Icc r s,
            blockRatio β t r (u - 1) ω * openCorrector β t u s ω y) -
          ∑ u ∈ Finset.Icc r s, openCorrector β t u s ω y := by
          rw [Finset.sum_sub_distrib]
      _ = _ - commonCorrection β t r s ω y := by rfl
  rw [smoothedEndpointDist_block_expansion β t ht r s hr hrs ω y]
  simp only [commonCorrection]
  rw [hsum]
  simp only [commonCorrection]
  field_simp [ne_of_gt hR]
  ring_nf

end Critical2DKPZ.FutureProfiles

end
