/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.TiltedDensity
public import Critical2DKPZ.Renewal.CompactTilting
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Compactified finite time horizons

A clipped logarithm removes exponential damping continuously on a fixed horizon.
The scalar renewal law gives zero mass to each positive-time boundary.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The time coordinate clipped above at a fixed horizon. -/
def clippedTime (T : ℝ) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun x => -Real.log (max (x : ℝ) (Real.exp (-T))), by
    apply Continuous.neg
    apply Continuous.log
    · fun_prop
    · intro x
      exact (lt_of_lt_of_le (Real.exp_pos _) (le_max_right _ _)).ne'⟩

/-- Clipping a compactified finite time recovers its value up to the horizon. -/
theorem clippedTime_compactifyTime {T t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    clippedTime T (compactifyTime t) = t := by
  change -Real.log (max (compactifyTime t : ℝ) (Real.exp (-T))) = t
  rw [compactifyTime_coe ht, max_eq_left (Real.exp_le_exp.mpr (neg_le_neg htT)), Real.log_exp, neg_neg]

/-- Positive times at most `t`, in compactified coordinates. -/
def horizonSet (t : ℝ) : Set (Icc (0 : ℝ) 1) := {x | Real.exp (-t) ≤ (x : ℝ)}

/-- The compactified time horizon set is measurable. -/
theorem measurableSet_horizonSet (t : ℝ) : MeasurableSet (horizonSet t) :=
  measurableSet_le measurable_const measurable_subtype_coe

/-- Membership of a compactified time in the horizon set is characterized by the time bound. -/
theorem compactifyTime_mem_horizonSet {t u : ℝ} (hu : 0 ≤ u) :
    compactifyTime u ∈ horizonSet t ↔ u ≤ t := by
  change Real.exp (-t) ≤ (compactifyTime u : ℝ) ↔ _
  rw [compactifyTime_coe hu, Real.exp_le_exp, neg_le_neg_iff]

/-- A level set of time compactification has the stated singleton preimage. -/
theorem compactifyTime_preimage_level {t : ℝ} (ht : 0 < t) :
    compactifyTime ⁻¹' {x : Icc (0 : ℝ) 1 | (x : ℝ) = Real.exp (-t)} = {t} := by
  ext u
  change Real.exp (-max u 0) = Real.exp (-t) ↔ u = t
  rw [Real.exp_eq_exp, neg_inj]
  constructor
  · intro h
    by_cases hu : 0 ≤ u
    · simpa only [max_eq_left hu] using h
    · rw [max_eq_right (le_of_not_ge hu)] at h
      exact False.elim (ht.ne' h.symm)
  · rintro rfl
    exact max_eq_left ht.le

/-- The compact scalar renewal law gives zero mass to finite-time level sets. -/
theorem compactScalarRenewalLaw_null_level (θ : ℝ) (a : {a : ℝ // 0 < a})
    (hθ : θ < Real.log a) {t : ℝ} (ht : 0 < t) :
    (compactScalarRenewalLaw θ a hθ : Measure _) {x : Icc (0 : ℝ) 1 |
      (x : ℝ) = Real.exp (-t)} = 0 := by
  rw [compactScalarRenewalLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply continuous_compactifyTime.measurable
      (measurableSet_eq_fun measurable_subtype_coe measurable_const),
    compactifyTime_preimage_level ht, measure_singleton]

/-- The boundary of the horizon set is contained in its terminal level set. -/
theorem frontier_horizonSet_subset (t : ℝ) :
    frontier (horizonSet t) ⊆ {x : Icc (0 : ℝ) 1 | (x : ℝ) = Real.exp (-t)} := by
  simpa only [frontier_Ici] using!
    (continuous_subtype_val : Continuous (Subtype.val : Icc (0 : ℝ) 1 → ℝ)).frontier_preimage_subset
      (Ici (Real.exp (-t)))

/-- The tilted compact scalar renewal law gives zero mass to the horizon boundary. -/
theorem compactTilt_scalarRenewalLaw_null_frontier (θ : ℝ) (a : {a : ℝ // 0 < a})
    (hθ : θ < Real.log a) (f : C(Icc (0 : ℝ) 1, ℝ)) {t : ℝ} (ht : 0 < t) :
    (compactTilt (compactScalarRenewalLaw θ a hθ) f : Measure _) (frontier (horizonSet t)) = 0 := by
  have hnull := measure_mono_null (frontier_horizonSet_subset t)
    (compactScalarRenewalLaw_null_level θ a hθ ht)
  exact withDensity_absolutelyContinuous _ _ hnull

/-- The tilted mass of any positive finite horizon converges under weak convergence. -/
theorem tendsto_compactTilt_horizon_mass
    {μ : ℕ → ProbabilityMeasure (Icc (0 : ℝ) 1)} {θ : ℝ}
    {a : {a : ℝ // 0 < a}} {hθ : θ < Real.log a}
    (hμ : Tendsto μ atTop (nhds (compactScalarRenewalLaw θ a hθ)))
    (f : C(Icc (0 : ℝ) 1, ℝ)) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => (compactTilt (μ N) f : Measure _).real (horizonSet t)) atTop
      (nhds ((compactTilt (compactScalarRenewalLaw θ a hθ) f : Measure _).real (horizonSet t))) := by
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (tendsto_compactTilt hμ f) (compactTilt_scalarRenewalLaw_null_frontier θ a hθ f ht)
  exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp h

end Critical2DKPZ.Renewal

end
