/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.Blocks
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # Normalizations on the geometric grid

An additive constant in a diverging logarithmic clock has no effect on its
square-root normalization.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Adding a fixed constant to a diverging positive clock does not change its
square-root normalization asymptotically. -/
theorem tendsto_sqrt_add_div_sqrt {κ : Type*} {l : Filter κ}
    (x : κ → ℝ) (hx : Tendsto x l atTop) (c : ℝ) :
    Tendsto (fun k => Real.sqrt (x k + c) / Real.sqrt (x k)) l (𝓝 1) := by
  have hsmall : Tendsto (fun k => c / x k) l (𝓝 0) := tendsto_const_nhds.div_atTop hx
  have hratio : Tendsto (fun k => (x k + c) / x k) l (𝓝 1) := by
    have hh : Tendsto (fun k => 1 + c / x k) l (𝓝 1) := by
      simpa only [add_zero] using tendsto_const_nhds.add hsmall
    apply hh.congr'
    filter_upwards [hx.eventually_gt_atTop 0] with k hk
    field_simp [hk.ne']
  have hroot : Tendsto (fun k => Real.sqrt ((x k + c) / x k)) l (𝓝 1) := by
    simpa only [Function.comp_def, Real.sqrt_one] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  apply hroot.congr'
  filter_upwards [hx.eventually_gt_atTop (max 0 (-c))] with k hk
  have hxpos : 0 < x k := lt_of_le_of_lt (le_max_left _ _) hk
  have hxc : 0 < x k + c := by linarith [le_max_right 0 (-c)]
  rw [Real.sqrt_div (by positivity)]

/-- The logarithm of the geometric time grid. -/
theorem log_tau (ρ : ℝ) (j : ℕ) :
    Real.log (tau ρ j) = -(j : ℝ) * Real.log ρ := by
  rw [tau, Real.log_pow, Real.log_inv]
  ring

/-- The geometric width has a logarithmic clock equal to `log j` plus a constant. -/
theorem loglog_inv_sqrt_tau {ρ : ℝ} (hρ : 1 < ρ) {j : ℕ} (hj : 0 < j) :
    Real.log (Real.log (Real.sqrt (tau ρ j))⁻¹) =
      Real.log (j : ℝ) + Real.log (Real.log ρ / 2) := by
  rw [Real.log_inv, Real.log_sqrt (tau_pos hρ j).le, log_tau]
  have heq : -(-(j : ℝ) * Real.log ρ / 2) = (j : ℝ) * (Real.log ρ / 2) := by ring
  rw [heq, Real.log_mul (by exact_mod_cast hj.ne')
    (div_ne_zero (Real.log_pos hρ).ne' (by norm_num))]

end Critical2DKPZ.Extensions.ScaleLimit
