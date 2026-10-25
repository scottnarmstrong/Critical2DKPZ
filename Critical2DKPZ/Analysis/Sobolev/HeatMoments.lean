/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.HeatRepresentation
public import Critical2DKPZ.Analysis.Sobolev.ExpectedHeatEnergy
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Averaging the heat quadratic form

For a jointly measurable L¹ random field whose L¹ norm has finite second moment, the spatial
quadratic form can be averaged using Fubini. This is the moment condition used at a fixed cutoff.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ

/-- Finite second moment of the L¹ norm gives an integrable two-point product. -/
theorem integrable_field_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → Plane → ℝ} (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hX1 : ∀ ω, Integrable (X ω))
    (hX2 : MemLp (fun ω => ∫ x : Plane, ‖X ω x‖) 2 μ) :
    Integrable (fun p : Ω × (Plane × Plane) => X p.1 p.2.1 * X p.1 p.2.2)
      (μ.prod (volume.prod volume)) := by
  have hm : Measurable (fun p : Ω × (Plane × Plane) => X p.1 p.2.1 * X p.1 p.2.2) :=
    (hX.comp (measurable_fst.prodMk measurable_snd.fst)).mul
      (hX.comp (measurable_fst.prodMk measurable_snd.snd))
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun ω => (hX1 ω).mul_prod (hX1 ω)
  · have he (ω : Ω) : (∫ p : Plane × Plane, ‖X ω p.1 * X ω p.2‖ ∂volume.prod volume) =
        (∫ x : Plane, ‖X ω x‖) ^ 2 := by
      simp_rw [norm_mul]
      simpa only [pow_two] using! integral_prod_mul (μ := (volume : Measure Plane))
        (ν := (volume : Measure Plane)) (fun x => ‖X ω x‖) (fun x => ‖X ω x‖)
    simpa only [he] using hX2.integrable_sq

/-- The full fixed-time heat quadratic integrand is integrable before interchanging variables. -/
theorem integrable_field_heat_product {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → Plane → ℝ} (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hX1 : ∀ ω, Integrable (X ω))
    (hX2 : MemLp (fun ω => ∫ x : Plane, ‖X ω x‖) 2 μ)
    {u : ℝ} (hu : 0 < u) :
    Integrable (fun p : Ω × (Plane × Plane) =>
      heatKernel (2 * u) (p.2.1 - p.2.2) * (X p.1 p.2.1 * X p.1 p.2.2))
      (μ.prod (volume.prod volume)) := by
  apply (integrable_field_product μ hX hX1 hX2).bdd_mul (c := heatKernel (2 * u) 0)
    (((continuous_heatKernel (2 * u)).comp
      (continuous_fst.sub continuous_snd)).measurable.comp measurable_snd).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro p
  change ‖heatKernel (2 * u) (p.2.1 - p.2.2)‖ ≤ heatKernel (2 * u) 0
  rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg (by linarith only [hu]) _)]
  rw [heatKernel_at_zero]
  exact heatKernel_le_at_zero (u := 2 * u) (mul_nonneg (by norm_num) hu.le) _

/-- Expectation of the heat quadratic form is the heat pairing of the two-point moment. -/
theorem integral_field_heat_quadratic {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [SFinite μ] {X : Ω → Plane → ℝ}
    (hX : Measurable (fun p : Ω × Plane => X p.1 p.2))
    (hX1 : ∀ ω, Integrable (X ω))
    (hX2 : MemLp (fun ω => ∫ x : Plane, ‖X ω x‖) 2 μ)
    {u : ℝ} (hu : 0 < u) :
    (∫ ω, (∫ p : Plane × Plane,
      heatKernel (2 * u) (p.1 - p.2) * (X ω p.1 * X ω p.2) ∂volume.prod volume) ∂μ) =
      ∫ p : Plane × Plane, (heatKernel (2 * u) (p.1 - p.2) *
        ∫ ω, X ω p.1 * X ω p.2 ∂μ) ∂volume.prod volume := by
  rw [integral_integral_swap (integrable_field_heat_product μ hX hX1 hX2 hu)]
  apply integral_congr_ae
  filter_upwards [] with p
  exact integral_const_mul _ _

end Critical2DKPZ

end
