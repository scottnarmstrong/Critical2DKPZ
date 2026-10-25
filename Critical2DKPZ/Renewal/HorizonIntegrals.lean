/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.Primitive
public import Critical2DKPZ.Renewal.RenewalLaw
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Exact finite-horizon integrals after removal of damping

The discrete weighted integral is the cumulative renewal mass, including its atom at
zero. The corresponding continuum integral is the primitive of the scalar density.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace Critical2DKPZ.Renewal

/-- The continuous logarithmic density change that removes damping up to time `T`. -/
def horizonUntilting (a T : ℝ) : C(Icc (0 : ℝ) 1, ℝ) :=
  ⟨fun x => a * clippedTime T x, continuous_const.mul (clippedTime T).continuous⟩

/-- The compactified horizon untilting factor equals the original exponential factor below the horizon. -/
theorem exp_horizonUntilting_compactifyTime (a : ℝ) {T u : ℝ} (hu : 0 ≤ u) (huT : u ≤ T) :
    Real.exp (horizonUntilting a T (compactifyTime u)) = Real.exp (a * u) := by
  change Real.exp (a * clippedTime T (compactifyTime u)) = _
  rw [clippedTime_compactifyTime hu huT]

/-- The continuum finite-horizon integral is the scalar renewal primitive. -/
theorem integral_horizon_scalarRenewalLaw (θ : ℝ) (a : {a : ℝ // 0 < a})
    (hθ : θ < Real.log a) {t T : ℝ} (htT : t ≤ T) :
    (∫ x in horizonSet t, Real.exp (horizonUntilting a T x)
      ∂(compactScalarRenewalLaw θ a hθ : Measure _)) =
      (Real.log a - θ) * scalarRenewalPrimitive θ t := by
  rw [← integral_indicator (measurableSet_horizonSet t), compactScalarRenewalLaw,
    ProbabilityMeasure.toMeasure_map,
    integral_map continuous_compactifyTime.measurable.aemeasurable
      ((by fun_prop : Measurable (fun x => Real.exp (horizonUntilting a T x))).indicator
        (measurableSet_horizonSet t)).aestronglyMeasurable,
    integral_scalarRenewalLaw]
  have heq : (fun u => tiltedScalarDensity θ a u *
      (horizonSet t).indicator (fun x => Real.exp (horizonUntilting a T x)) (compactifyTime u))
      =ᵐ[volume.restrict (Ioi 0)]
      (Iic t).indicator (fun u => (Real.log a - θ) * DeltaBose.scalarDensity θ u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    by_cases hut : u ≤ t
    · rw [indicator_of_mem ((compactifyTime_mem_horizonSet hu.le).mpr hut),
        indicator_of_mem (show u ∈ Iic t from hut),
        exp_horizonUntilting_compactifyTime a hu.le (hut.trans htT)]
      unfold tiltedScalarDensity
      have he : Real.exp (-(a * u)) * Real.exp (a * u) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      calc
        _ = (Real.log a - θ) * DeltaBose.scalarDensity θ u *
            (Real.exp (-(a * u)) * Real.exp (a * u)) := by ring
        _ = _ := by rw [he, mul_one]
    · rw [indicator_of_notMem (mt (compactifyTime_mem_horizonSet hu.le).mp hut),
        indicator_of_notMem (show u ∉ Iic t from hut), mul_zero]
  rw [integral_congr_ae heq, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic]
  have hs : Iic t ∩ Ioi (0 : ℝ) = Ioc 0 t := by
    ext u
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_Ioc]
    exact and_comm
  rw [hs, integral_const_mul]
  rfl

/-- A rescaled lattice time belongs to the horizon set exactly when it meets the time cutoff. -/
theorem nat_div_mem_horizonSet (N n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    compactifyTime ((n : ℝ) / (N + 1)) ∈ horizonSet t ↔
      n ∈ Finset.range (⌊((N : ℝ) + 1) * t⌋₊ + 1) := by
  rw [compactifyTime_mem_horizonSet (by positivity), div_le_iff₀ (by positivity : (0 : ℝ) < N + 1),
    Finset.mem_range, Nat.lt_add_one_iff, Nat.le_floor_iff (mul_nonneg (by positivity) ht)]
  rw [mul_comm]

/-- Exact accumulated lattice renewal mass under the continuous finite-horizon density change. -/
theorem integral_horizon_compactRenewalLaw (ϑ : ℝ) (a : {a : ℝ // 0 < a}) (N : ℕ)
    (hσ : 0 ≤ criticalSigmaSq ϑ N) (hgap : 0 < criticalGap ϑ a N)
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    (∫ x in horizonSet t, Real.exp (horizonUntilting a T x)
      ∂(compactRenewalLaw ϑ a N hσ hgap : Measure _)) =
      criticalGap ϑ a N * criticalRenewalFunction ϑ N ⌊((N : ℝ) + 1) * t⌋₊ := by
  let g : C(Icc (0 : ℝ) 1, ℝ) := ⟨fun x => Real.exp (horizonUntilting a T x), by fun_prop⟩
  have hi := (integrable_continuousMap_compact
    (compactRenewalLaw ϑ a N hσ hgap : Measure _) g).indicator (measurableSet_horizonSet t)
  rw [← integral_indicator (measurableSet_horizonSet t)]
  change (∫ x, (horizonSet t).indicator g x ∂(compactRenewalLaw ϑ a N hσ hgap : Measure _)) = _
  rw [integral_compactRenewalLaw ϑ a N hσ hgap _ hi]
  have heq (n : ℕ) : (criticalGap ϑ a N *
      (criticalRenewalMass ϑ N n * Real.exp (-a * n / (N + 1)))) *
      (horizonSet t).indicator g (compactifyTime ((n : ℝ) / (N + 1))) =
      if n ∈ Finset.range (⌊((N : ℝ) + 1) * t⌋₊ + 1) then
        criticalGap ϑ a N * criticalRenewalMass ϑ N n else 0 := by
    by_cases hn : n ∈ Finset.range (⌊((N : ℝ) + 1) * t⌋₊ + 1)
    · have hu : (n : ℝ) / (N + 1) ≤ t :=
        (compactifyTime_mem_horizonSet (by positivity)).mp ((nat_div_mem_horizonSet N n ht).mpr hn)
      rw [ite_eq_left hn, indicator_of_mem ((nat_div_mem_horizonSet N n ht).mpr hn)]
      change (criticalGap ϑ a N * (criticalRenewalMass ϑ N n * Real.exp (-a * n / (N + 1)))) *
        Real.exp (horizonUntilting a T (compactifyTime ((n : ℝ) / (N + 1)))) = _
      rw [exp_horizonUntilting_compactifyTime a (by positivity) (hu.trans htT)]
      have he : Real.exp (-a * n / (N + 1)) * Real.exp (a * ((n : ℝ) / (N + 1))) = 1 := by
        rw [← Real.exp_add]
        convert Real.exp_zero using 1
        congr 1
        ring
      calc
        _ = criticalGap ϑ a N * criticalRenewalMass ϑ N n *
            (Real.exp (-a * n / (N + 1)) * Real.exp (a * ((n : ℝ) / (N + 1)))) := by ring
        _ = _ := by rw [he, mul_one]
    · rw [ite_eq_right hn, indicator_of_notMem (mt (nat_div_mem_horizonSet N n ht).mp hn), mul_zero]
  simp_rw [heq]
  rw [tsum_eq_sum (s := Finset.range (⌊((N : ℝ) + 1) * t⌋₊ + 1))
    (fun n hn => ite_eq_right hn)]
  simp only [Finset.sum_ite_mem, Finset.inter_self, ← Finset.mul_sum,
    criticalRenewalMass, sum_renewalMass_range, criticalRenewalFunction]

end Critical2DKPZ.Renewal

end
