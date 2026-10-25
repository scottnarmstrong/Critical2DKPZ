/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! # Subprobability measures representing endpoint pairings -/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal CompactlySupported

namespace Critical2DKPZ.NonGaussian

/-- Heat-weight the initial coordinate, project to the terminal coordinate,
and normalize by the real heat mass. Zero or infinite heat mass gives the zero measure. -/
def endpointTerminalMeasure (μ : Measure (Plane × Plane)) (r : ℝ) (x : Plane) : Measure Plane :=
  ENNReal.ofReal ((∫ p, heatKernel r (p.1 - x) ∂μ)⁻¹) •
    (μ.withDensity (fun p => ENNReal.ofReal (heatKernel r (p.1 - x)))).map Prod.snd

/-- Normalization gives a subprobability measure, including when the real heat mass vanishes. -/
theorem endpointTerminalMeasure_mass_le_one (μ : Measure (Plane × Plane))
    {r : ℝ} (hr : 0 < r) (x : Plane) :
    endpointTerminalMeasure μ r x Set.univ ≤ 1 := by
  let k : Plane × Plane → ℝ := fun p => heatKernel r (p.1 - x)
  let d : ℝ := ∫ p, k p ∂μ
  have hk : ∀ p, 0 ≤ k p := fun p => heatKernel_nonneg hr.le _
  change (ENNReal.ofReal d⁻¹ • (μ.withDensity (fun p => ENNReal.ofReal (k p))).map
    Prod.snd) Set.univ ≤ 1
  by_cases hd : d = 0
  · simp [hd]
  have hi : Integrable k μ := by
    by_contra h
    exact hd (integral_undef h)
  have hmass : μ.withDensity (fun p => ENNReal.ofReal (k p)) Set.univ =
      ENNReal.ofReal d := by
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    exact (ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hk)).symm
  have hd0 : 0 ≤ d := integral_nonneg hk
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply measurable_snd MeasurableSet.univ,
    Set.preimage_univ, hmass, ← ENNReal.ofReal_mul (inv_nonneg.mpr hd0),
    inv_mul_cancel₀ hd, ENNReal.ofReal_one]


/-- A terminal test integrated against the normalized measure is precisely
the quotient defining an endpoint pairing. -/
theorem integral_endpointTerminalMeasure (μ : Measure (Plane × Plane))
    {r : ℝ} (hr : 0 < r) (x : Plane) (f : Plane → ℝ) (hf : StronglyMeasurable f) :
    (∫ y, f y ∂endpointTerminalMeasure μ r x) =
      (∫ p, heatKernel r (p.1 - x) * f p.2 ∂μ) /
        (∫ p, heatKernel r (p.1 - x) ∂μ) := by
  have hn : 0 ≤ (∫ p, heatKernel r (p.1 - x) ∂μ)⁻¹ :=
    inv_nonneg.mpr (integral_nonneg fun p => heatKernel_nonneg hr.le _)
  have hm : Measurable (fun p : Plane × Plane => ENNReal.ofReal (heatKernel r (p.1 - x))) :=
    ((measurable_heatKernel r).comp (measurable_fst.sub_const x)).ennreal_ofReal
  rw [endpointTerminalMeasure, integral_smul_measure, ENNReal.toReal_ofReal hn,
    integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hm
      (Filter.Eventually.of_forall fun p => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (heatKernel_nonneg hr.le _), smul_eq_mul]
  rw [div_eq_mul_inv, mul_comm]

/-- The endpoint quotient is represented by the normalized terminal measure. -/
theorem endpointPairing_eq_integral_endpointTerminalMeasure {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) {r : ℝ} (hr : 0 < r)
    (t : ℝ) (x : Plane) (f : Plane → ℝ) (hf : StronglyMeasurable f) (ω : Ω) :
    endpointPairing Z r t x f ω = ∫ y, f y ∂endpointTerminalMeasure (Z r t ω) r x := by
  rw [integral_endpointTerminalMeasure _ hr x f hf]
  simp only [endpointPairing, shfPairing, mul_one]

end Critical2DKPZ.NonGaussian
