/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.SiteToPlane
import Critical2DKPZ.RandomWalk.GaussianBridge
import Mathlib.Tactic

/-! # Geometry of two free replica coordinates -/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

/-- The integer sum and difference coordinates centered at a common reference site. -/
def pairSumDifference (u : Site) (p : Site × Site) : Site × Site :=
  (p.1 - p.2, p.1 + p.2 - u - u)

/-- The sum/difference map is injective on the integer lattice. -/
theorem pairSumDifference_injective (u : Site) :
    Function.Injective (pairSumDifference u) := by
  intro p q hpq
  rcases p with ⟨a, b⟩
  rcases q with ⟨c, d⟩
  apply Prod.ext
  · ext i
    have hd : a i - b i = c i - d i := by
      have hh := congrFun (congrArg Prod.fst hpq) i
      simpa [pairSumDifference] using hh
    have hs : a i + b i - u i - u i = c i + d i - u i - u i := by
      have hh := congrFun (congrArg Prod.snd hpq) i
      simpa [pairSumDifference] using hh
    have hsum : a i + b i = c i + d i := by omega
    linarith only [hd, hsum]
  · ext i
    have hd : a i - b i = c i - d i := by
      have hh := congrFun (congrArg Prod.fst hpq) i
      simpa [pairSumDifference] using hh
    have hs : a i + b i - u i - u i = c i + d i - u i - u i := by
      have hh := congrFun (congrArg Prod.snd hpq) i
      simpa [pairSumDifference] using hh
    have hsum : a i + b i = c i + d i := by omega
    linarith only [hd, hsum]

/-- The parallelogram identity for the two replica coordinates. -/
theorem pair_sum_difference_norm_identity (a b u : Site) :
    ‖siteToPlane (a - u)‖ ^ 2 + ‖siteToPlane (b - u)‖ ^ 2 =
      (‖siteToPlane (a - b)‖ ^ 2 + ‖siteToPlane (a + b - u - u)‖ ^ 2) / 2 := by
  rw [Critical2DKPZ.norm_siteToPlane_sq, Critical2DKPZ.norm_siteToPlane_sq,
    Critical2DKPZ.norm_siteToPlane_sq, Critical2DKPZ.norm_siteToPlane_sq]
  simp only [Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add]
  ring

/-- The squared separation of two anchors is controlled by distances to a common site. -/
theorem pair_anchor_distance_sq_le (a b u : Site) :
    ‖siteToPlane (a - b)‖ ^ 2 ≤
      2 * (‖siteToPlane (a - u)‖ ^ 2 + ‖siteToPlane (b - u)‖ ^ 2) := by
  rw [Critical2DKPZ.norm_siteToPlane_sq, Critical2DKPZ.norm_siteToPlane_sq,
    Critical2DKPZ.norm_siteToPlane_sq]
  simp only [Pi.sub_apply, Int.cast_sub]
  have h0 := sq_nonneg ((a 0 : ℝ) - u 0 + ((b 0 : ℝ) - u 0))
  have h1 := sq_nonneg ((a 1 : ℝ) - u 1 + ((b 1 : ℝ) - u 1))
  nlinarith only [h0, h1]

end Critical2DKPZ.MomentBounds
