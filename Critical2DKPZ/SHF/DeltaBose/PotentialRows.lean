/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PiCoordinateSplit
public import Critical2DKPZ.SHF.DeltaBose.HeatPotential
import Mathlib.Tactic

/-! # One and two coordinate heat-potential rows -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- The uniform half-time constant in the heat-potential convolution estimate. -/
noncomputable def heatPotentialRowBound (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹ * t ^ (-(1 / 2 : ℝ))) * halfTimeResolventConstant

/-- The heat-potential row bound is finite. -/
theorem heatPotentialRowBound_ne_top (t : ℝ) : heatPotentialRowBound t ≠ ⊤ := by
  unfold heatPotentialRowBound
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top halfTimeResolventConstant_ne_top

/-- Translation of the heat-potential convolution bound to an arbitrary center. -/
theorem lintegral_heatKernel_mul_heatPotential_shifted {t : ℝ} (ht : 0 < t)
    (x d : Plane) :
    (∫⁻ y : Plane, ENNReal.ofReal (heatKernel t (x - y)) *
      heatPotential (y - d)) ≤ heatPotentialRowBound t := by
  let F : Plane → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (heatKernel t (x - y)) * heatPotential (y - d)
  have hF : Measurable F := by
    dsimp [F]
    have hh : Measurable (fun y : Plane => heatKernel t (x - y)) := by
      unfold heatKernel
      fun_prop
    exact hh.ennreal_ofReal.mul (measurable_heatPotential.comp (measurable_id.sub_const d))
  have he := (measurePreserving_add_right volume d).lintegral_comp hF
  calc (∫⁻ y : Plane, ENNReal.ofReal (heatKernel t (x - y)) *
        heatPotential (y - d))
      = ∫⁻ u : Plane, F (u + d) := he.symm
    _ = ∫⁻ u : Plane,
        ENNReal.ofReal (heatKernel t ((x - d) - u)) * heatPotential u := by
          apply lintegral_congr
          intro u
          dsimp [F]
          rw [show x - (u + d) = (x - d) - u by
            calc
              x - (u + d) = x - (d + u) := by rw [add_comm]
              _ = (x - d) - u := by rw [← sub_sub]]
          rw [add_sub_cancel_right]
    _ ≤ heatPotentialRowBound t := by
          exact lintegral_heatKernel_mul_heatPotential_le ht (x - d)


/-- Time integration turns the half-time row bound into the same potential weight. -/
theorem lintegral_heatPotentialRowBound_mul_heatKernel_double (x : Plane) :
    (∫⁻ t in Ioi (0 : ℝ), heatPotentialRowBound t *
      ENNReal.ofReal (heatKernel (2 * t) x)) =
      (ENNReal.ofReal ((2 * Real.pi)⁻¹) * halfTimeResolventConstant) *
        (ENNReal.ofReal ((2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) * heatPotential x) := by
  let c : ℝ≥0∞ := ENNReal.ofReal ((2 * Real.pi)⁻¹) * halfTimeResolventConstant
  have hc : c ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    halfTimeResolventConstant_ne_top
  have he (t : ℝ) (ht : 0 < t) :
      heatPotentialRowBound t * ENNReal.ofReal (heatKernel (2 * t) x) =
        c * (ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (heatKernel (2 * t) x)) := by
    dsimp [c, heatPotentialRowBound]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (2 * Real.pi)⁻¹)]
    ac_rfl
  calc (∫⁻ t in Ioi (0 : ℝ), heatPotentialRowBound t *
        ENNReal.ofReal (heatKernel (2 * t) x))
      = ∫⁻ t in Ioi (0 : ℝ), c * (ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (heatKernel (2 * t) x)) := by
            apply lintegral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
            exact he t ht
    _ = c * (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-(1 / 2 : ℝ))) *
          ENNReal.ofReal (heatKernel (2 * t) x)) :=
          lintegral_const_mul' c _ hc
    _ = c * (ENNReal.ofReal ((2 * (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) *
          heatPotential x) := by rw [lintegral_halfTime_heatKernel_double]
    _ = _ := rfl

end Critical2DKPZ.DeltaBose
