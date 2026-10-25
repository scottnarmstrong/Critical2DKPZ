/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.CriticalWindow
public import Critical2DKPZ.Renewal.ParameterDerivative
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic.LinearCombination

/-!
# Differentiation in the critical parameter

The coupling is affine in `ϑ`. The marked renewal function is therefore exactly
`F_N + (log N + ϑ) ∂_ϑ F_N`, with no asymptotic replacement of the variance.
-/

@[expose] public noncomputable section

open Set Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- Derivative of the finite renewal polynomial with respect to the critical parameter. -/
def criticalRenewalParameterDerivative (ϑ : ℝ) (N n : ℕ) : ℝ :=
  renewalParameterDerivative returnWeight (criticalSigmaSq ϑ N) n *
    (1 / Real.log N / replicaOverlap N)

/-- Differentiating the critical renewal function gives its critical-parameter derivative. -/
theorem hasDerivAt_criticalRenewalFunction (ϑ : ℝ) (N n : ℕ) :
    HasDerivAt (fun v => criticalRenewalFunction v N n)
      (criticalRenewalParameterDerivative ϑ N n) ϑ := by
  have hs : HasDerivAt (fun v : ℝ => (1 + v / Real.log N) / replicaOverlap N)
      (1 / Real.log N / replicaOverlap N) ϑ := by
    simpa only [zero_add, Pi.add_apply, id_eq] using!
      ((hasDerivAt_const ϑ (1 : ℝ)).add ((hasDerivAt_id ϑ).div_const (Real.log N))).div_const
        (replicaOverlap N)
  have h := (hasDerivAt_renewalFunction_smul returnWeight (criticalSigmaSq ϑ N) n).comp ϑ hs
  exact h

/-- The critical disorder variance is monotone in the critical parameter. -/
theorem criticalSigmaSq_mono_parameter {N : ℕ} (hN : 2 ≤ N) :
    Monotone (fun ϑ => criticalSigmaSq ϑ N) := by
  intro x y hxy
  have hlog : 0 ≤ Real.log (N : ℝ) := (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).le
  exact div_le_div_of_nonneg_right
    (add_le_add le_rfl (div_le_div_of_nonneg_right hxy hlog)) (replicaOverlap_pos (by omega)).le

/-- The critical disorder variance preserves affine combinations of critical parameters. -/
theorem criticalSigmaSq_affine (N : ℕ) (x y a b : ℝ) (hab : a + b = 1) :
    criticalSigmaSq (a * x + b * y) N = a * criticalSigmaSq x N + b * criticalSigmaSq y N := by
  unfold criticalSigmaSq
  linear_combination -(replicaOverlap N)⁻¹ * hab

/-- The critical renewal function is convex in the parameter where the coupling is nonnegative. -/
theorem convexOn_criticalRenewalFunction {N : ℕ} (hN : 2 ≤ N) (l r : ℝ)
    (hl : 0 ≤ criticalSigmaSq l N) (n : ℕ) :
    ConvexOn ℝ (Icc l r) (fun ϑ => criticalRenewalFunction ϑ N n) := by
  refine ⟨convex_Icc _ _, fun x hx y hy a b ha hb hab => ?_⟩
  have hc := convexOn_renewalFunction_smul (fun r => srwKernel_nonneg (2 * r) 0) n
  change renewalFunction (fun j => criticalSigmaSq (a * x + b * y) N * returnWeight j) n ≤ _
  rw [criticalSigmaSq_affine N x y a b hab]
  exact hc.2 (hl.trans (criticalSigmaSq_mono_parameter hN hx.1))
    (hl.trans (criticalSigmaSq_mono_parameter hN hy.1)) ha hb hab

/-- The marked critical renewal function equals the renewal function plus its weighted parameter derivative. -/
theorem critical_markedRenewalFunction_eq (ϑ : ℝ) {N : ℕ} (hN : 2 ≤ N) (n : ℕ) :
    markedRenewalFunction (fun r => criticalSigmaSq ϑ N * returnWeight r) n =
      criticalRenewalFunction ϑ N n + (Real.log N + ϑ) * criticalRenewalParameterDerivative ϑ N n := by
  rw [markedRenewalFunction_eq]
  change criticalRenewalFunction ϑ N n + criticalSigmaSq ϑ N *
    renewalParameterDerivative returnWeight (criticalSigmaSq ϑ N) n = _
  congr 1
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  unfold criticalRenewalParameterDerivative criticalSigmaSq
  field_simp

end Critical2DKPZ.Renewal

end
