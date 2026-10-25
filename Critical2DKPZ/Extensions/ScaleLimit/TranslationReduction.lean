/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Extensions.ScaleLimit.MollifierReductions
import Critical2DKPZ.Extensions.ScaleLimit.FiniteFamilyLaw
import Critical2DKPZ.Extensions.ScaleLimit.TranslationInvariance
import Critical2DKPZ.Extensions.ScaleLimit.Centring

/-! # Translation of finite families of mollified flat KPZ values -/

@[expose] public section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Every finite width family can be moved to the spatial origin in law. -/
theorem translation_dilate_law (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) {I : Type*} [Fintype I]
    (φ : TestFn) (x : Plane) (ε : I → ℝ) :
    P.map (fun ω i => H t 0 ω (φ.dilate (ε i) x)) =
      P.map (fun ω i => H t 0 ω (φ.dilate (ε i) 0)) := by
  have hXm : AEMeasurable (fun ω i => H t 0 ω (φ.dilate (ε i) x)) P :=
    aemeasurable_pi_iff.mpr fun i => (memLp_kpz_two ϑ P Z hZ H hH t ht _).aemeasurable
  have hYm : AEMeasurable (fun ω i => H t 0 ω (φ.dilate (ε i) 0)) P :=
    aemeasurable_pi_iff.mpr fun i => (memLp_kpz_two ϑ P Z hZ H hH t ht _).aemeasurable
  apply map_fintype_eq_of_fin_laws P P _ _ hXm hYm
  intro k f
  have h := (identDistrib_kpz_translate ϑ P Z hZ H hH ht k
    (fun i => φ.dilate (ε (f i)) 0) x).map_eq
  simpa only [dilate_dilate_zero, mul_one] using h

end Critical2DKPZ.Extensions.ScaleLimit
