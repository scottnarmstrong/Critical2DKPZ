/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.PolymerSixthMoment
public import Critical2DKPZ.SHF.Limit.LocalFinite
public import Critical2DKPZ.SHF.Limit.Marginal
public import Critical2DKPZ.SHF.Limit.FirstMoment
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Compact pair tests controlled by the flat marginal -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

local instance polymerMeasureIsLocallyFinite (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (ω : Disorder) :
    IsLocallyFiniteMeasure (SHF.Limit.polymerMeasure ϑ N s t ω) :=
  SHF.Limit.isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω

local instance polymerMarginalIsLocallyFinite (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (ω : Disorder) :
    IsLocallyFiniteMeasure ((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst) :=
  SHF.Limit.isLocallyFiniteMeasure_polymerMarginal ϑ N s t ω

/-- A compact pair test bounded by a first-coordinate weight is controlled by
its flat marginal pairing. -/
theorem abs_integral_pairTest_rescaledP2P_le_marginal
    (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder)
    (φ : C_c(Plane × Plane, ℝ))
    (χ : C_c(Plane, ℝ)) (M : ℝ)
    (hbound : ∀ p, |φ p| ≤ M * χ p.1) :
    |∫ p, φ p * rescaledP2P ϑ N s t p ω ∂volume| ≤
      M * ∫ x, χ x ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst) := by
  let μ : Measure (Plane × Plane) := SHF.Limit.polymerMeasure ϑ N s t ω
  let ν : Measure Plane := μ.map Prod.fst
  have hφμ : Integrable (fun p : Plane × Plane => φ p) μ := by
    exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hχν : Integrable (fun x : Plane => χ x) ν := by
    exact χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport
  have hχμ : Integrable (fun p : Plane × Plane => χ p.1) μ := by
    exact (integrable_map_measure hχν.aestronglyMeasurable
      measurable_fst.aemeasurable).1 hχν
  have hmap : ∫ x, χ x ∂ν = ∫ p, χ p.1 ∂μ :=
    integral_map measurable_fst.aemeasurable hχν.aestronglyMeasurable
  have hmajorInt : Integrable (fun p : Plane × Plane => M * χ p.1) μ :=
    hχμ.const_mul M
  have hmajor : ∫ p : Plane × Plane, M * χ p.1 ∂μ = M * ∫ x, χ x ∂ν := by
    rw [integral_const_mul, ← hmap]
  have hpMeasure :
      ∫ p : Plane × Plane, φ p ∂μ =
        ∫ p, φ p * rescaledP2P ϑ N s t p ω ∂volume := by
    simpa [μ] using SHF.Limit.integral_polymerMeasure ϑ N s t ω φ
  calc
    |∫ p, φ p * rescaledP2P ϑ N s t p ω ∂volume| =
        |∫ p : Plane × Plane, φ p ∂μ| := by rw [← hpMeasure]
    _ ≤ ∫ p : Plane × Plane, |φ p| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ p, M * χ p.1 ∂μ := integral_mono hφμ.norm hmajorInt hbound
    _ = M * ∫ x, χ x ∂ν := hmajor

end Critical2DKPZ.SHF.Moments

end
