/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.RandomMeasureLimitFactors
public import Critical2DKPZ.SHF.Tsai.TwoBlockReadouts

/-! # A coarse increment as a function of adjacent increments

Approximate composition gives a measurable, almost surely locally finite function of two
adjacent increments that agrees almost surely with their combined flow increment.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology CompactlySupported

namespace Critical2DKPZ.SHF.Tsai

/-- The composition axiom determines a coarse increment measurably from the two adjacent increments. -/
theorem IsDenseSHF.exists_measurable_composition_factor {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsDenseSHF θ D P Z)
    {a b c : ℝ} (ha : a ∈ D) (hb : b ∈ D) (hc : c ∈ D) (hab : a < b) (hbc : b < c) :
    ∃ φ : (Measure (Plane × Plane)) × (Measure (Plane × Plane)) → Measure (Plane × Plane),
      Measurable φ ∧ (∀ q, IsLocallyFiniteMeasure (φ q)) ∧
      Z a c =ᵐ[P] fun ω => φ (Z a b ω, Z b c ω) := by
  classical
  obtain ⟨w, hw, _hwell, hconv⟩ := hZ.2.1 a ha b hb c hc hab hbc
  let E := CompactExhaustion.choice (Plane × Plane)
  let v (f : C_c(Plane × Plane, ℝ)) (n : ℕ) := modifiedTwoBlockReadout E (w n) f
  have hvm (f : C_c(Plane × Plane, ℝ)) (n : ℕ) : Measurable (v f n) :=
    measurable_modifiedTwoBlockReadout E (w n) (hw.2.1 n).measurable f f.continuous.measurable
  have hvAE (f : C_c(Plane × Plane, ℝ)) (n : ℕ) :
      (fun ω => v f n (Z a b ω, Z b c ω)) =ᵐ[P]
        fun ω => smoothedProductPairing (Z a b ω) (w n) (Z b c ω) f := by
    filter_upwards [(hZ.1 a ha b hb hab).2, (hZ.1 b hb c hc hbc).2] with ω hLF hLF'
    let : IsLocallyFiniteMeasure (Z a b ω) := hLF
    let : IsLocallyFiniteMeasure (Z b c ω) := hLF'
    dsimp only [v]
    rw [modifiedTwoBlockReadout_eq_of_locallyFinite E]
    exact integral_smoothedProductMeasure_eq _ _ _ (hw.1 n) (hw.2.1 n).measurable _ f.continuous.measurable
  have hvconv (f : C_c(Plane × Plane, ℝ)) :
      TendstoInMeasure P (fun n ω => v f n (Z a b ω, Z b c ω)) atTop
        (fun ω => ∫ p, f p ∂Z a c ω) := by
    have hraw : TendstoInMeasure P
        (fun n ω => smoothedProductPairing (Z a b ω) (w n) (Z b c ω) f) atTop
          (fun ω => ∫ p, f p ∂Z a c ω) := by
      simpa only [tendstoInMeasure_iff_norm, Pi.zero_apply, sub_zero] using hconv f
    exact hraw.congr_left (fun n => (hvAE f n).symm)
  exact exists_measure_factor_of_pairing_limits P (fun ω => (Z a b ω, Z b c ω)) (Z a c)
    (hZ.1 a ha c hc (hab.trans hbc)).2 v hvm hvconv

end Critical2DKPZ.SHF.Tsai

end
