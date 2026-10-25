/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzField
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! # Stochastic Fubini for the selected Schwartz fields -/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A jointly integrable representative of an integrable L2 family integrates
to the representative of its Bochner integral. Finite-measure set integrals,
viewed as Hilbert continuous linear functionals, identify the two sides.
This generalizes the main library's weighted-convolution representation proof. -/
theorem integral_L2_ae_eq {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure α) [SFinite μ]
    (F : α → Lp ℝ 2 P) {f : α → Ω → ℝ}
    (hF : Integrable F μ) (hf : Integrable (Function.uncurry f) (μ.prod P))
    (hrep : ∀ y, (F y : Ω → ℝ) =ᵐ[P] f y) :
    ((∫ y, F y ∂μ : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] fun ω => ∫ y, f y ω ∂μ := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
    ((Lp.memLp _).integrable (by norm_num)) hf.integral_prod_right
  intro s hs _
  let I : Lp ℝ 2 P := indicatorConstLp 2 hs (measure_ne_top P s) 1
  let L : Lp ℝ 2 P →L[ℝ] ℝ := innerSL ℝ I
  have hL (X : Lp ℝ 2 P) : L X = ∫ ω in s, X ω ∂P := by
    simpa only [L, I, innerSL_apply_apply] using
      L2.inner_indicatorConstLp_one hs (measure_ne_top P s) X
  have hfs : Integrable (Function.uncurry f) (μ.prod (P.restrict s)) :=
    hf.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    _ = L (∫ y, F y ∂μ) := (hL _).symm
    _ = ∫ y, L (F y) ∂μ := (L.integral_comp_comm hF).symm
    _ = ∫ y, ∫ ω in s, f y ω ∂P ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => (hL _).trans
        (integral_congr_ae (ae_restrict_of_ae (hrep y)))
    _ = _ := integral_integral_swap hfs

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {D : Ω → Distr} {ν : Measure Plane}

/-- Smooth compact spatial averages of the measurable Schwartz field are jointly
integrable. The uniform square bound follows from one-point stationarity. -/
theorem schwartzField_average_integrable_prod (hD : StationarySpectralData P D ν)
    (ψ : SchwartzMap Plane ℝ) (φ : TestFn) (x : Plane) (r : ℝ) :
    Integrable (fun q : Plane × Ω => φ q.1 *
      schwartzField hD ψ (x + r • q.1) q.2) (volume.prod P) := by
  have hm : Measurable (fun q : Plane × Ω => schwartzField hD ψ (x + r • q.1) q.2) :=
    (schwartzField_measurable hD ψ).comp
      ((measurable_const.add (measurable_fst.const_smul r)).prodMk measurable_snd)
  have hw : Measurable (fun q : Plane × Ω => φ q.1 *
      schwartzField hD ψ (x + r • q.1) q.2) :=
    (φ.continuous.measurable.comp measurable_fst).mul hm
  apply (integrable_prod_iff hw.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun y =>
    ((schwartzField_memLp hD ψ (x + r • y)).integrable (by norm_num)).const_mul (φ y)), ?_⟩
  have heq : (fun y : Plane => ∫ ω, ‖φ y * schwartzField hD ψ (x + r • y) ω‖ ∂P) =
      fun y => ‖φ y‖ * ∫ ω, ‖schwartzField hD ψ 0 ω‖ ∂P := by
    funext y
    simp_rw [norm_mul]
    rw [integral_const_mul, (schwartzField_identDistrib hD ψ (x + r • y)).norm.integral_eq]
  rw [heq]
  exact (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).norm.mul_const _

/-- The spatially averaged field is the representative of the Bochner average
of the extended translated pairings. Both integrability obligations are proved
from the field and spectral specifications. -/
theorem schwartzField_average_ae_eq (hD : StationarySpectralData P D ν)
    (ψ : SchwartzMap Plane ℝ) (φ : TestFn) (x : Plane) (r : ℝ) :
    Integrable (fun z : Plane => φ z • schwartzExt hD
      (translateSchwartz (x + r • z) ψ)) ∧
      (fun ω => ∫ z, φ z * schwartzField hD ψ (x + r • z) ω) =ᵐ[P]
        fun ω => (∫ z : Plane, φ z • schwartzExt hD (translateSchwartz (x + r • z) ψ)) ω := by
  let : ν.HasTemperateGrowth := temperateGrowth_of_spectralData P D ν hD
  have hc : Continuous (fun z : Plane => schwartzExt hD (translateSchwartz (x + r • z) ψ)) :=
    (continuous_schwartzPairing_translate P ν (schwartzExt hD)
      (schwartzExt_covariance hD) ψ).comp (continuous_const.add (continuous_const_smul r))
  have hi : Integrable (fun z : Plane => φ z • schwartzExt hD
      (translateSchwartz (x + r • z) ψ)) :=
    hc.locallyIntegrable.integrable_smul_left_of_hasCompactSupport φ.continuous φ.hasCompactSupport
  refine ⟨hi, ?_⟩
  apply (integral_L2_ae_eq P volume _
    (f := fun z ω => φ z * schwartzField hD ψ (x + r • z) ω) hi
    (schwartzField_average_integrable_prod hD ψ φ x r) ?_).symm
  intro z
  filter_upwards [Lp.coeFn_smul (φ z) (schwartzExt hD (translateSchwartz (x + r • z) ψ)),
    schwartzField_ae_eq hD ψ (x + r • z)] with ω hsmul hrep
  change _ = φ z * schwartzExt hD (translateSchwartz (x + r • z) ψ) ω at hsmul
  rw [hsmul, ← hrep]

end Critical2DKPZ.Extensions.ScaleLimit
