/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SpectralShapeScale
public import Critical2DKPZ.Extensions.ScaleLimit.WidthClock
import Mathlib.Tactic

/-! # Spectral ball mass at the canonical double-exponential clock -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Any fixed frequency multiplier gives the same normalized spectral mass
at a positive scale time. -/
theorem specMass_scaleRadius_tendsto_pos (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hball : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R)) atTop (𝓝 1))
    {κ s : ℝ} (hκ : 0 < κ) (hs : 0 < s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ * specMass ν (κ / scaleRadius L s))
      atTop (𝓝 s) := by
  have hε : Tendsto (fun L : Set.Ioi (0 : ℝ) => scaleRadius L s) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨scaleRadius_tendsto_zero hs,
      Eventually.of_forall fun L => scaleRadius_pos L s⟩
  have hh := ((specMass_scaled_inv_tendsto ν hball hκ).comp hε).const_mul s
  have hh' : Tendsto (fun L : Set.Ioi (0 : ℝ) => s *
      (specMass ν (κ / scaleRadius L s) / Real.log (Real.log (scaleRadius L s)⁻¹)))
      atTop (𝓝 s) := by simpa only [Function.comp_apply, mul_one] using hh
  apply hh'.congr
  intro L
  rw [log_log_inv_scaleRadius]
  field_simp [hs.ne']

/-- The spectral mass clock also holds at time zero: its ball is fixed,
so division by the diverging scale parameter sends its finite mass to zero. -/
theorem specMass_scaleRadius_tendsto (ν : Measure Plane) [IsLocallyFiniteMeasure ν]
    (hball : Tendsto (fun R : ℝ => specMass ν R / Real.log (Real.log R)) atTop (𝓝 1))
    {κ s : ℝ} (hκ : 0 < κ) (hs : 0 ≤ s) :
    Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)⁻¹ * specMass ν (κ / scaleRadius L s))
      atTop (𝓝 s) := by
  rcases hs.eq_or_lt with h0 | hs
  · subst s
    have hL : Tendsto (fun L : Set.Ioi (0 : ℝ) => (L : ℝ)) atTop atTop :=
      tendsto_Ioi_atTop.mp tendsto_id
    have hh := (tendsto_inv_atTop_zero.comp hL).mul_const
      (specMass ν (κ / Real.exp (-1)))
    simpa only [Function.comp_apply, scaleRadius, mul_zero, Real.exp_zero, zero_mul] using hh
  · exact specMass_scaleRadius_tendsto_pos ν hball hκ hs

/-- Positive scale parameters strictly reverse the order of scale times. -/
theorem scaleRadius_strictAnti {L : ℝ} (hL : 0 < L) : StrictAnti (scaleRadius L) := by
  intro s t hst
  apply Real.exp_lt_exp.mpr
  apply neg_lt_neg
  apply Real.exp_lt_exp.mpr
  exact mul_lt_mul_of_pos_left hst hL

end Critical2DKPZ.Extensions.ScaleLimit
