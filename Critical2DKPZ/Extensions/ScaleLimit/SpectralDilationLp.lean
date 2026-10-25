/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.ShapeDilation
public import Critical2DKPZ.Extensions.ScaleLimit.RadialSchwartzDerivative
public import Critical2DKPZ.Extensions.ScaleLimit.L2DominatedLimit
public import Critical2DKPZ.Extensions.ScaleLimit.SchwartzDecayEnvelope
import Mathlib.Tactic

/-! # Spectral L2 realizations of dilated Schwartz shapes with bounded multipliers -/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Ordinary frequency dilation of a complex Schwartz shape. -/
def frequencyScaleSchwartz (m : SchwartzMap Plane ℂ) (r : ℝ) (hr : r ≠ 0) :
    SchwartzMap Plane ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (inverseScaleEquiv r⁻¹ (inv_ne_zero hr)) m

/-- Frequency dilation has the literal value `m(r ξ)`. -/
theorem frequencyScaleSchwartz_apply (m : SchwartzMap Plane ℂ) (r : ℝ) (hr : r ≠ 0) (ξ : Plane) :
    frequencyScaleSchwartz m r hr ξ = m (r • ξ) := by
  simp only [frequencyScaleSchwartz, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
    Function.comp_apply, inverseScaleEquiv_apply, inv_inv]

/-- A bounded measurable multiplier preserves square integrability of a
rescaled Schwartz shape for any tempered spectral measure. -/
theorem memLp_spectralMultipliedDilate (ν : Measure Plane) [ν.HasTemperateGrowth]
    (A : Plane → ℂ) (hAm : Measurable A) (hAn : ∀ ξ, ‖A ξ‖ ≤ 1)
    (m : SchwartzMap Plane ℂ) {r : ℝ} (hr : r ≠ 0) :
    MemLp (fun ξ => A ξ * m (r • ξ)) 2 ν := by
  have hs : MemLp (fun ξ : Plane => m (r • ξ)) 2 ν := by
    have hh := (frequencyScaleSchwartz m r hr).memLp 2 ν
    exact (memLp_congr_ae (Eventually.of_forall
      (frequencyScaleSchwartz_apply m r hr))).mp hh
  apply hs.of_le (hAm.aestronglyMeasurable.mul
    (m.continuous.comp (continuous_const_smul r)).aestronglyMeasurable)
  filter_upwards [] with ξ
  change ‖A ξ * m (r • ξ)‖ ≤ ‖m (r • ξ)‖
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right (hAn ξ) (norm_nonneg _)).trans_eq (one_mul _)

/-- The L2 class of a bounded multiplier times a rescaled Schwartz shape.
The value at zero is harmless and is never used by the radius calculus. -/
def spectralMultipliedDilate (ν : Measure Plane) [ν.HasTemperateGrowth]
    (A : Plane → ℂ) (hAm : Measurable A) (hAn : ∀ ξ, ‖A ξ‖ ≤ 1)
    (m : SchwartzMap Plane ℂ) (r : ℝ) : Lp ℂ 2 ν :=
  if hr : r = 0 then 0 else
    (memLp_spectralMultipliedDilate ν A hAm hAn m hr).toLp (fun ξ => A ξ * m (r • ξ))

/-- The spectral class has its explicit representative at each nonzero radius. -/
theorem spectralMultipliedDilate_ae_eq (ν : Measure Plane) [ν.HasTemperateGrowth]
    (A : Plane → ℂ) (hAm : Measurable A) (hAn : ∀ ξ, ‖A ξ‖ ≤ 1)
    (m : SchwartzMap Plane ℂ) {r : ℝ} (hr : r ≠ 0) :
    (spectralMultipliedDilate ν A hAm hAn m r : Plane → ℂ) =ᵐ[ν]
      fun ξ => A ξ * m (r • ξ) := by
  rw [spectralMultipliedDilate, dite_eq_right hr]
  exact MemLp.coeFn_toLp _

end Critical2DKPZ.Extensions.ScaleLimit
