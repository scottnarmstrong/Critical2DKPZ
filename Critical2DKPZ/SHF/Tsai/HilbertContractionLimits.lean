/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Strong convergence from a contractive Hilbert-space pairing limit

The squared-distance identity bounds the error by twice the deficit of the
pairing with the proposed limit. This turns convergence of that one pairing
and a norm contraction into strong convergence.
-/

@[expose] public section

open Filter
open scoped Topology InnerProductSpace

namespace Critical2DKPZ.SHF.Tsai

/-- A norm contraction converges strongly when its pairing with the limit approaches
that limit's squared norm. -/
theorem tendsto_of_norm_le_of_inner_tendsto {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (f : ℕ → E) (g : E) (hbound : ∀ n, ‖f n‖ ≤ ‖g‖)
    (hinner : Tendsto (fun n => ⟪f n, g⟫_ℝ) atTop (𝓝 (‖g‖ ^ 2))) :
    Tendsto f atTop (𝓝 g) := by
  have hsq (n) : ‖f n - g‖ ^ 2 ≤ 2 * (‖g‖ ^ 2 - ⟪f n, g⟫_ℝ) := by
    rw [norm_sub_sq_real]
    have hn : ‖f n‖ ^ 2 ≤ ‖g‖ ^ 2 := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hbound n)
    calc
      _ ≤ ‖g‖ ^ 2 - 2 * ⟪f n, g⟫_ℝ + ‖g‖ ^ 2 :=
        add_le_add (sub_le_sub_right hn _) (le_refl _)
      _ = _ := by ring
  have hlim : Tendsto (fun n => ‖f n - g‖ ^ 2) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [sub_self, mul_zero] using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖g‖ ^ 2) atTop (𝓝 (‖g‖ ^ 2))).sub hinner).const_mul 2)
      (fun _ => sq_nonneg _) hsq
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hlim
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq, Real.sqrt_zero, norm_nonneg,
    abs_of_nonneg, dist_eq_norm] using hsqrt

end Critical2DKPZ.SHF.Tsai

end
