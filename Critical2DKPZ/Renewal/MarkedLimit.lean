/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.CumulativeLimit
public import Critical2DKPZ.Renewal.CriticalParameter
public import Critical2DKPZ.Renewal.PrimitiveDerivative
import Critical2DKPZ.Renewal.ConvexDerivativeLimit

/-!
# The marked critical renewal limit

Convexity of the finite coupling polynomial permits differentiating the cumulative
limit. The exact coupling converts that derivative into a marked renewal
function, whose limit is `t j_(ϑ-γ)(t)`.
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The critical-parameter derivative of the renewal function converges to its continuum counterpart. -/
theorem tendsto_criticalRenewalParameterDerivative (ϑ : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => criticalRenewalParameterDerivative ϑ N ⌊((N : ℝ) + 1) * t⌋₊ /
      Real.log N) atTop (nhds (t * DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) t)) := by
  apply tendsto_derivative_of_convex (l := ϑ - 1) (x := ϑ) (r := ϑ + 1)
    (F := fun N v => criticalRenewalFunction v N ⌊((N : ℝ) + 1) * t⌋₊ / Real.log N)
    (f := fun v => scalarRenewalPrimitive (v - Real.eulerMascheroniConstant) t)
    (by linarith) (by linarith)
  · filter_upwards [criticalSigmaSq_eventually_pos (ϑ - 1), eventually_ge_atTop 2] with N hσ hN
    have hlog : 0 < Real.log (N : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using!
      ConvexOn.smul (inv_nonneg.mpr hlog.le)
        (convexOn_criticalRenewalFunction hN (ϑ - 1) (ϑ + 1) hσ.le ⌊((N : ℝ) + 1) * t⌋₊)
  · exact Filter.Eventually.of_forall fun N =>
      (hasDerivAt_criticalRenewalFunction ϑ N ⌊((N : ℝ) + 1) * t⌋₊).div_const (Real.log N)
  · intro v hv
    exact tendsto_criticalRenewalFunction v ht
  · simpa only [mul_one] using!
      (hasDerivAt_scalarRenewalPrimitive_parameter (ϑ - Real.eulerMascheroniConstant) ht).comp ϑ
        ((hasDerivAt_id ϑ).sub_const Real.eulerMascheroniConstant)

/-- The cumulative squared resolvent divided by `log N` squared converges to time times the Euler-shifted scalar density. -/
theorem tendsto_markedCriticalRenewalFunction (ϑ : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => markedRenewalFunction
      (fun r => criticalSigmaSq ϑ N * returnWeight r) ⌊((N : ℝ) + 1) * t⌋₊ / (Real.log N) ^ 2)
      atTop (nhds (t * DeltaBose.scalarDensity (ϑ - Real.eulerMascheroniConstant) t)) := by
  have hinv : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := ((tendsto_criticalRenewalFunction ϑ ht).mul hinv).add
    ((tendsto_one_add_div_log ϑ).mul (tendsto_criticalRenewalParameterDerivative ϑ ht))
  simp only [mul_zero, one_mul, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  rw [critical_markedRenewalFunction_eq ϑ hN]
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  field_simp

end Critical2DKPZ.Renewal

end
