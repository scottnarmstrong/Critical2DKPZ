/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.WeakLimit
public import Critical2DKPZ.Renewal.HorizonIntegrals

/-! # Cumulative critical renewal convergence

The cumulative renewal mass divided by `log N` converges to the primitive of the
Euler-shifted scalar density. -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The cumulative renewal mass converges at each positive macroscopic time. -/
theorem tendsto_criticalRenewalFunction (ϑ : ℝ) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N : ℕ => criticalRenewalFunction ϑ N ⌊((N : ℝ) + 1) * t⌋₊ / Real.log N)
      atTop (nhds (scalarRenewalPrimitive (ϑ - Real.eulerMascheroniConstant) t)) := by
  let a : {a : ℝ // 0 < a} := ⟨Real.exp (ϑ - Real.eulerMascheroniConstant + 1), Real.exp_pos _⟩
  have ha : ϑ < Real.log a + Real.eulerMascheroniConstant := by
    rw [Real.log_exp]
    linarith
  let f := horizonUntilting a t
  let ν := compactScalarRenewalLaw (ϑ - Real.eulerMascheroniConstant) a (by linarith :
    ϑ - Real.eulerMascheroniConstant < Real.log a)
  let μ := compactCriticalLaw ϑ a ha
  let e : BoundedContinuousFunction (Set.Icc (0 : ℝ) 1) ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun x => Real.exp (f x), by fun_prop⟩
  have hμ : Tendsto μ atTop (nhds ν) := tendsto_compactCriticalLaw ϑ a ha
  have hm := tendsto_compactTilt_horizon_mass hμ f ht
  have he := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ e
  have hg := (tendsto_log_mul_critical_gap ϑ a).comp
    (tendsto_add_atTop_nat (renewalStart ϑ a ha))
  have h := (hm.mul he).div hg (sub_pos.mpr ha).ne'
  have hc : (compactTilt ν f : Measure _).real (horizonSet t) *
      (∫ x, e x ∂(ν : Measure _)) /
      (Real.log a + Real.eulerMascheroniConstant - ϑ) =
      scalarRenewalPrimitive (ϑ - Real.eulerMascheroniConstant) t := by
    change (compactTilt ν f : Measure _).real (horizonSet t) *
      (∫ x, Real.exp (f x) ∂(ν : Measure _)) / _ = _
    rw [compactTilt_real_mul_integral ν f (measurableSet_horizonSet t),
      integral_horizon_scalarRenewalLaw _ a _ (le_refl t)]
    have heq : Real.log a - (ϑ - Real.eulerMascheroniConstant) =
        Real.log a + Real.eulerMascheroniConstant - ϑ := by ring
    rw [heq]
    exact mul_div_cancel_left₀ _ (sub_pos.mpr ha).ne'
  rw [hc] at h
  apply (tendsto_add_atTop_iff_nat (renewalStart ϑ a ha)).mp
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hM : 1 < N + renewalStart ϑ a ha := by omega
  have hlog : Real.log ((N + renewalStart ϑ a ha : ℕ) : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hM)).ne'
  have hgap := (renewalStart_spec ϑ a ha N).2
  change ((compactTilt (μ N) f : Measure _).real (horizonSet t) *
    (∫ x, Real.exp (f x) ∂(μ N : Measure _))) /
    (Real.log ((N + renewalStart ϑ a ha : ℕ) : ℝ) * criticalGap ϑ a _) = _
  rw [compactTilt_real_mul_integral (μ N) f (measurableSet_horizonSet t)]
  have hi : (∫ x in horizonSet t, Real.exp (f x) ∂(μ N : Measure _)) =
      criticalGap ϑ a (N + renewalStart ϑ a ha) *
      criticalRenewalFunction ϑ (N + renewalStart ϑ a ha)
        ⌊(((N + renewalStart ϑ a ha : ℕ) : ℝ) + 1) * t⌋₊ := by
    simpa only [μ, compactCriticalLaw, f] using!
      integral_horizon_compactRenewalLaw ϑ a (N + renewalStart ϑ a ha)
        (renewalStart_spec ϑ a ha N).1.le hgap ht.le (le_refl t)
  rw [hi]
  field_simp [hgap.ne']

end Critical2DKPZ.Renewal

end
