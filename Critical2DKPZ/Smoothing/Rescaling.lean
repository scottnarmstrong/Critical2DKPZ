/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.Basic
public import Critical2DKPZ.Smoothing.SpatialRescaling
import Mathlib.Tactic.Ring

/-! # Exact spatial rescaling of the lattice smoothing error -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Smoothing

/-- The lattice smoothing error changes continuum scale by an exact dilation. -/
theorem latticeSmoothingError_rescale (β : ℝ) {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (L k j : ℕ)
    (h₀ : Plane →ᵇ ℝ) (φ : Plane → ℝ) (ω : Disorder) :
    latticeSmoothingError β N L k j h₀ φ ω =
      latticeSmoothingError β M L k j
        (h₀.compContinuous ⟨fun y => Real.sqrt ((M : ℝ) / N) • y, by fun_prop⟩)
        (fun y => (M / N : ℝ) * φ (Real.sqrt ((M : ℝ) / N) • y)) ω := by
  have ha : 0 < (M : ℝ) / N := by positivity
  have hC : cellAverage M (fun y => Real.exp
      ((h₀.compContinuous ⟨fun y => Real.sqrt ((M : ℝ) / N) • y, by fun_prop⟩) y)) =
      cellAverage N (fun y => Real.exp (h₀ y)) := by
    funext z
    exact (cellAverage_rescale hN hM (fun y => Real.exp (h₀ y)) z).symm
  unfold latticeSmoothingError
  rw [hC]
  conv_lhs => rw [integral_plane_sqrt_scale ha]
  simp_rw [latticePoint_rescale hN]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  ring

end Critical2DKPZ.Smoothing

end
