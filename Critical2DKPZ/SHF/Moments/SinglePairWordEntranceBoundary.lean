/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordEntranceWindowsHorizon
import Mathlib.Tactic

/-! # Clock and cutoff errors in the exact tested two-particle entrance formula -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- Splitting the first-entrance clock preserves the exact tested formula. -/
theorem pairTwoTestedEntranceWindow_split
    (ϑ : ℝ) (N L lo K hi : ℕ) (hlo : lo ≤ K) (hKhi : K < hi)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : ℝ × Plane → ℝ) :
    pairTwoTestedEntranceWindow ϑ N L lo hi φ η =
      pairTwoTestedEntranceWindow ϑ N L lo K φ η +
        pairTwoTestedEntranceWindow ϑ N L (K + 1) hi φ η := by
  have hs (x : Fin 2 → Site) := collisionEntrance_window_split N lo K hi (x 0) (x 1)
    (fun q => η q * pairTwoFutureSampleProfile ϑ N L φ x q) hlo hKhi
  simp only [pairTwoTestedEntranceWindow]
  simp_rw [hs]
  rw [Finset.sum_add_distrib, mul_add]

/-- Collision-cutoff errors are represented by the cutoff difference itself. -/
theorem pairTwoTestedEntranceWindow_sub_cutoff
    (ϑ : ℝ) (N L lo hi : ℕ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (η ξ : ℝ × Plane → ℝ) :
    pairTwoTestedEntranceWindow ϑ N L lo hi φ (fun q => η q - ξ q) =
      pairTwoTestedEntranceWindow ϑ N L lo hi φ η -
        pairTwoTestedEntranceWindow ϑ N L lo hi φ ξ := by
  have hs (x : Fin 2 → Site) :
      collisionEntrance N lo hi (x 0) (x 1)
        (fun q => (η q - ξ q) * pairTwoFutureSampleProfile ϑ N L φ x q) =
      collisionEntrance N lo hi (x 0) (x 1)
        (fun q => η q * pairTwoFutureSampleProfile ϑ N L φ x q) -
      collisionEntrance N lo hi (x 0) (x 1)
        (fun q => ξ q * pairTwoFutureSampleProfile ϑ N L φ x q) := by
    rw [← collisionEntrance_sub_test]
    congr 1
    funext q
    ring
  simp only [pairTwoTestedEntranceWindow]
  simp_rw [hs]
  rw [Finset.sum_sub_distrib, mul_sub]


end Critical2DKPZ.SHF.Moments
