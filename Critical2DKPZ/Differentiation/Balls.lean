/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.MeasureTheory.Measure.Prod
public import Critical2DKPZ.Definitions.Plane

/-! # Ball differentiation of planar measures

The Besicovitch differentiation theorem identifies the small-ball density of a locally finite
measure on the plane with its Radon–Nikodym derivative with respect to Lebesgue measure. In
particular, a locally finite measure is singular to Lebesgue measure exactly when its normalized
ball masses tend to zero at almost every point.
-/

@[expose] public section

open MeasureTheory Filter
open Critical2DKPZ
open scoped Topology ENNReal

namespace Critical2DKPZ.Differentiation

/-- The normalized mass of a closed ball for a planar measure. -/
noncomputable def closedBallDensity (ρ : Measure Plane)
    (x : Plane) (r : ℝ) : ℝ≥0∞ :=
  ρ (Metric.closedBall x r) /
    (volume : Measure Plane) (Metric.closedBall x r)

/-- A countable lower density representative built from closed balls with radii tending to zero.
It is useful when the measure itself depends on an additional measurable parameter. -/
noncomputable def lowerClosedBallDensity
    (ρ : Measure Plane) (x : Plane) : ℝ≥0∞ :=
  liminf (fun n : ℕ => closedBallDensity ρ x (1 / ((n : ℝ) + 1))) atTop

/-- For a fixed locally finite measure, the mass of a closed ball is measurable in its center. -/
theorem measurable_measure_closedBall (ρ : Measure Plane) [SFinite ρ]
    (r : ℝ) :
    Measurable (fun x : Plane => ρ (Metric.closedBall x r)) := by
  let E := Plane
  let s : Set (E × E) := {p | dist p.1 p.2 ≤ r}
  have hs : MeasurableSet s := measurableSet_le measurable_dist measurable_const
  let f : E × E → ℝ≥0∞ := s.indicator fun _ => 1
  have hf : Measurable f := measurable_const.indicator hs
  have hlin : Measurable (fun x : E => ∫⁻ y, f (x, y) ∂ρ) := hf.lintegral_prod_right'
  have hEq : (fun x : E => ∫⁻ y, f (x, y) ∂ρ) = fun x => ρ (Metric.closedBall x r) := by
    funext x
    rw [← lintegral_indicator_one (measurableSet_closedBall)]
    congr 1
    funext y
    change (if dist x y ≤ r then (1 : ℝ≥0∞) else 0) =
      (if dist y x ≤ r then 1 else 0)
    rw [dist_comm]
  rw [← hEq]
  exact hlin



/-- For a locally finite measure on `ℝ²`, its ratios of closed-ball masses converge almost
everywhere to its Radon–Nikodym derivative with respect to planar Lebesgue measure. -/
theorem ae_closedBall_ratio_tendsto_rnDeriv
    (ρ : Measure Plane) [IsLocallyFiniteMeasure ρ] :
    ∀ᵐ x ∂(volume : Measure Plane),
      Tendsto (fun r : ℝ => ρ (Metric.closedBall x r) /
        (volume : Measure Plane) (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 (ρ.rnDeriv (volume : Measure Plane) x)) := by
  exact Besicovitch.ae_tendsto_rnDeriv ρ (volume : Measure Plane)

/-- The measurable lower density representative agrees almost everywhere with the
Radon–Nikodym derivative. -/
theorem ae_lowerClosedBallDensity_eq_rnDeriv
    (ρ : Measure Plane) [IsLocallyFiniteMeasure ρ] :
    lowerClosedBallDensity ρ =ᵐ[(volume : Measure Plane)]
      ρ.rnDeriv (volume : Measure Plane) := by
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr
      ⟨tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ), ?_⟩
    filter_upwards with n
    change 0 < 1 / ((n : ℝ) + 1)
    positivity
  filter_upwards [ae_closedBall_ratio_tendsto_rnDeriv ρ] with x hx
  have hseq := hx.comp hr
  change liminf (fun n : ℕ => closedBallDensity ρ x (1 / ((n : ℝ) + 1))) atTop = _
  exact hseq.liminf_eq


/-- The measurable liminf density vanishes almost everywhere exactly for measures singular to
planar Lebesgue measure. -/
theorem ae_lowerClosedBallDensity_eq_zero_iff_singular
    (ρ : Measure Plane) [IsLocallyFiniteMeasure ρ] :
    lowerClosedBallDensity ρ =ᵐ[(volume : Measure Plane)] 0 ↔
      Measure.MutuallySingular ρ (volume : Measure Plane) := by
  constructor
  · intro h
    have hdensity : ρ.rnDeriv (volume : Measure Plane) =ᵐ[
        (volume : Measure Plane)] 0 := by
      filter_upwards [ae_lowerClosedBallDensity_eq_rnDeriv ρ, h] with x hρ hx
      rw [← hρ]
      exact hx
    exact (Measure.rnDeriv_eq_zero ρ (volume : Measure Plane)).mp
      hdensity
  · intro h
    filter_upwards [ae_lowerClosedBallDensity_eq_rnDeriv ρ, h.rnDeriv_ae_eq_zero]
      with x hρ hx
    rw [hρ]
    exact hx

end Critical2DKPZ.Differentiation

end
