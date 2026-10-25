/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.Inputs
import Critical2DKPZ.Differentiation.Balls
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! # Lebesgue differentiation bound for small balls -/

@[expose] public section

open MeasureTheory Filter
open Critical2DKPZ
open scoped Topology ENNReal

namespace Critical2DKPZ.SmallScales

/-- For a locally finite measure on the plane, the mass of a small closed ball is `O(ε²)` at Lebesgue-almost every center. -/
theorem ae_exists_measure_closedBall_le_sq (μ : Measure Plane) [IsLocallyFiniteMeasure μ] :
    ∀ᵐ x ∂(volume : Measure Plane), ∃ C : ℝ, ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      (μ (Metric.closedBall x ε)).toReal ≤ C * ε ^ 2 := by
  filter_upwards [
    Critical2DKPZ.Differentiation.ae_closedBall_ratio_tendsto_rnDeriv μ,
    Measure.rnDeriv_lt_top μ (volume : Measure Plane)] with x hlim htop
  let a := μ.rnDeriv (volume : Measure Plane) x
  have hfinite : a ≠ ⊤ := by
    change μ.rnDeriv (volume : Measure Plane) x ≠ ⊤
    exact ne_of_lt htop
  have hsmall : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      μ (Metric.closedBall x ε) / (volume : Measure Plane) (Metric.closedBall x ε) < a + 1 := by
    have hmem : Set.Iio (a + 1) ∈ 𝓝 a :=
      Iio_mem_nhds (ENNReal.lt_add_right hfinite one_ne_zero)
    have hevent := hlim.eventually hmem
    simpa only [a, Set.mem_Iio] using hevent
  refine ⟨(a + 1).toReal * Real.pi, ?_⟩
  have hpositive : ∀ᶠ ε : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < ε :=
    eventually_mem_nhdsWithin
  filter_upwards [hsmall, hpositive] with ε hε hεpos
  have hv : (volume : Measure Plane) (Metric.closedBall x ε) =
      ENNReal.ofReal ε ^ 2 * ENNReal.ofReal Real.pi := by
    simpa only [Plane] using EuclideanSpace.volume_closedBall_fin_two x ε
  have hvpos : 0 < (volume : Measure Plane) (Metric.closedBall x ε) := by
    rw [hv]
    positivity
  have hvolTop : (volume : Measure Plane) (Metric.closedBall x ε) ≠ ⊤ := by
    rw [hv]
    finiteness
  have hratio : μ (Metric.closedBall x ε) ≤ (a + 1) *
      (volume : Measure Plane) (Metric.closedBall x ε) := by
    exact (ENNReal.div_lt_iff (Or.inl hvpos.ne') (Or.inl hvolTop)).mp hε |>.le
  have hupper : (a + 1) * (volume : Measure Plane) (Metric.closedBall x ε) ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · exact ENNReal.add_ne_top.2 ⟨hfinite, by simp⟩
    · exact hvolTop
  have htoReal := ENNReal.toReal_mono hupper hratio
  rw [hv] at htoReal
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (le_of_lt hεpos), ENNReal.toReal_ofReal Real.pi_nonneg] at htoReal
  convert htoReal using 1; ring

end Critical2DKPZ.SmallScales

end
