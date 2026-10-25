/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralData
import Critical2DKPZ.CovarianceKernel.RadialAsymptotic

/-! # Sharp spectral ball growth

The double logarithmic asymptotic controls all spectral balls of radius at least
two and, uniformly, the dyadic radii used in the band decomposition.
-/

public section

noncomputable section

open MeasureTheory Filter Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Spectral ball mass is monotone, including at negative radii. -/
theorem specMass_mono (ν : Measure Plane) [IsLocallyFiniteMeasure ν] :
    Monotone (specMass ν) :=
  CovarianceKernel.spectralBallMass_mono ν

/-- The unshifted envelope is strictly positive starting at radius two. -/
theorem one_add_log_log_two_pos : 0 < 1 + Real.log (Real.log 2) := by
  have hlow : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hu : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    linarith only [h]
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hlow
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv] at h
  linarith only [hu, h]

/-- A double logarithmic asymptotic gives a uniform double logarithmic envelope. -/
theorem specMass_loglog_bound (ν : Measure Plane) (hν : IsLocallyFiniteMeasure ν)
    (h : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R))
      atTop (𝓝 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R →
      specMass ν R ≤ C * (1 + Real.log (Real.log R)) := by
  let : IsLocallyFiniteMeasure ν := hν
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp
    (h.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2)))
  let R₀ := max S (Real.exp (Real.exp 1) + 1)
  let b := 1 + Real.log (Real.log 2)
  have hb : 0 < b := one_add_log_log_two_pos
  let C := max 2 (specMass ν R₀ / b)
  have hC : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  refine ⟨C, hC, fun R hR => ?_⟩
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log R := Real.log_le_log (by norm_num) hR
  have hbR : b ≤ 1 + Real.log (Real.log R) := by
    dsimp [b]
    exact add_le_add_right (Real.log_le_log hlog2 hlog) 1
  have henv : 0 ≤ 1 + Real.log (Real.log R) := hb.le.trans hbR
  by_cases hlarge : R₀ ≤ R
  · have hSR : S ≤ R := (le_max_left _ _).trans hlarge
    have hthreshold : Real.exp (Real.exp 1) < R :=
      lt_of_lt_of_le (lt_add_one _) ((le_max_right _ _).trans hlarge)
    have hlogR : Real.exp 1 < Real.log R := by
      have hh := Real.log_lt_log (Real.exp_pos _) hthreshold
      rwa [Real.log_exp] at hh
    have hll : 0 < Real.log (Real.log R) :=
      Real.log_pos ((Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 1)).trans hlogR)
    have hm : specMass ν R ≤ 2 * Real.log (Real.log R) :=
      ((div_lt_iff₀ hll).mp (hS R hSR)).le
    calc
      specMass ν R ≤ 2 * Real.log (Real.log R) := hm
      _ ≤ 2 * (1 + Real.log (Real.log R)) := by linarith only
      _ ≤ C * (1 + Real.log (Real.log R)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) henv
  · have hm := specMass_mono ν (le_of_not_ge hlarge)
    have hM : 0 ≤ specMass ν R₀ := ENNReal.toReal_nonneg
    have hquot : 0 ≤ specMass ν R₀ / b := div_nonneg hM hb.le
    calc
      specMass ν R ≤ specMass ν R₀ := hm
      _ = (specMass ν R₀ / b) * b := (div_mul_cancel₀ _ hb.ne').symm
      _ ≤ (specMass ν R₀ / b) * (1 + Real.log (Real.log R)) :=
        mul_le_mul_of_nonneg_left hbR hquot
      _ ≤ C * (1 + Real.log (Real.log R)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) henv




end Critical2DKPZ.Extensions.ScaleLimit

end
