/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BallIntegralLaw
public import Critical2DKPZ.Extensions.ScaleLimit.MaximalMeasurability
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Finite-family stationarity of ball averages -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A ball average agrees almost everywhere with the normalized real integral. -/
theorem ballAverage_ae_eq_integral {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hstat : ∀ y, IdentDistrib (g y) (g 0) P P) (hint : Integrable (g 0) P)
    (y : Plane) (r : ℝ) :
    (fun ω => ballAverage (fun z => g z ω) y r) =ᵐ[P]
      fun ω => (volume (ball y r))⁻¹ * ENNReal.ofReal (∫ z in ball y r, ‖g z ω‖) := by
  let μ := volume.restrict (ball y r)
  let : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hp := integrable_stationary_prod μ hg hstat hint
  filter_upwards [hp.prod_left_ae] with ω hω
  change Integrable (fun z => g z ω) μ at hω
  change (volume (ball y r))⁻¹ * (∫⁻ z, ‖g z ω‖ₑ ∂μ) = _
  rw [← ofReal_integral_norm_eq_lintegral_enorm hω]

/-- The joint law of every finite family of ball averages is independent of
the center. -/
theorem ballAverages_identDistrib {g : Plane → Ω → ℝ}
    (hg : Measurable (Function.uncurry g))
    (hstat : ∀ (n : ℕ) (x : Fin n → Plane) (z : Plane),
      IdentDistrib (fun ω i => g (x i + z) ω) (fun ω i => g (x i) ω) P P)
    (hcont : ∀ y₀, TendstoInMeasure P g (𝓝 y₀) (g y₀))
    (hint : Integrable (g 0) P) (n : ℕ) (r : Fin n → ℝ) (y : Plane) :
    IdentDistrib (fun ω i => ballAverage (fun z => g z ω) y (r i))
      (fun ω i => ballAverage (fun z => g z ω) 0 (r i)) P P := by
  let T : (Fin n → ℝ) → Fin n → ℝ≥0∞ :=
    fun v i => (volume (ball (0 : Plane) (r i)))⁻¹ * ENNReal.ofReal (v i)
  have hT : Measurable T := by
    apply Measurable.of_eval
    intro i
    exact measurable_const.mul ((measurable_pi_apply i).ennreal_ofReal)
  have hraw := (ballIntegrals_identDistrib hg hstat hcont hint n r y).comp hT
  have hf : (fun ω i => ballAverage (fun z => g z ω) y (r i)) =ᵐ[P]
      fun ω => T (fun i => ∫ z in ball y (r i), ‖g z ω‖) := by
    filter_upwards [ae_all_iff.mpr (fun i =>
      ballAverage_ae_eq_integral hg (identDistrib_eval_zero hstat) hint y (r i))] with ω hω
    ext i
    rw [hω i, volume.addHaar_ball_center y (r i)]
  have hf₀ : (fun ω i => ballAverage (fun z => g z ω) 0 (r i)) =ᵐ[P]
      fun ω => T (fun i => ∫ z in ball (0 : Plane) (r i), ‖g z ω‖) := by
    filter_upwards [ae_all_iff.mpr (fun i =>
      ballAverage_ae_eq_integral hg (identDistrib_eval_zero hstat) hint 0 (r i))] with ω hω
    exact funext hω
  have hm (z : Plane) : Measurable (fun ω i => ballAverage (fun w => g w ω) z (r i)) :=
    Measurable.of_eval fun i => measurable_ballAverage hg z (r i)
  exact (IdentDistrib.of_ae_eq (hm y).aemeasurable hf).trans
    (hraw.trans (IdentDistrib.of_ae_eq (hm 0).aemeasurable hf₀).symm)

end Critical2DKPZ.Extensions.ScaleLimit

end
