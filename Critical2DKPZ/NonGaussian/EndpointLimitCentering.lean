/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Centering spatial averages of integrable random fields -/

@[expose] public noncomputable section

open MeasureTheory Filter

namespace Critical2DKPZ.NonGaussian

/-- Equality in almost every environment for each spatial point gives
equality on the product space for integrable fields. -/
theorem ae_eq_prod_of_integrable_sections
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (mX : Measure X) [SFinite mX] (P : Measure Ω) [SFinite P]
    {F G : X × Ω → ℝ} (hF : Integrable F (mX.prod P))
    (hG : Integrable G (mX.prod P)) (hsec : ∀ x, (fun ω => F (x, ω)) =ᵐ[P] fun ω => G (x, ω)) :
    F =ᵐ[mX.prod P] G := by
  have hi : Integrable (fun q => ‖F q - G q‖) (mX.prod P) := (hF.sub hG).norm
  have hz : (∫ q, ‖F q - G q‖ ∂mX.prod P) = 0 := by
    rw [integral_prod _ hi]
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun x => integral_eq_zero_of_ae
      ((hsec x).mono fun ω hω => by
        change F (x, ω) = G (x, ω) at hω
        change ‖F (x, ω) - G (x, ω)‖ = 0
        rw [hω, sub_self, norm_zero])
  have hae := (integral_eq_zero_iff_of_nonneg (fun q => norm_nonneg (F q - G q)) hi).mp hz
  filter_upwards [hae] with q hq
  exact sub_eq_zero.mp (norm_eq_zero.mp hq)

/-- Integrating a field centered separately at every spatial point agrees
almost surely with centering the spatial integral itself. -/
theorem integral_centered_field_eq_centered_integral
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (mX : Measure X) [SFinite mX] (P : Measure Ω) [SFinite P]
    {F : X × Ω → ℝ} (hF : Integrable F (mX.prod P)) :
    (fun ω => ∫ x, (F (x, ω) - ∫ ω', F (x, ω') ∂P) ∂mX) =ᵐ[P]
      fun ω => (∫ x, F (x, ω) ∂mX) - ∫ ω', (∫ x, F (x, ω') ∂mX) ∂P := by
  have hsec : ∀ᵐ ω ∂P, Integrable (fun x => F (x, ω)) mX :=
    ((integrable_prod_iff' hF.aestronglyMeasurable).mp hF).1
  filter_upwards [hsec] with ω hω
  rw [integral_sub hω hF.integral_prod_left]
  exact congrArg (fun a : ℝ => (∫ x, F (x, ω) ∂mX) - a)
    (integral_integral_swap (f := fun x ω => F (x, ω)) hF)

/-- Product almost-everywhere equality is preserved by spatial integration
for almost every environment. -/
theorem integral_spatial_congr_ae {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (mX : Measure X) [SFinite mX] (P : Measure Ω) [SFinite P]
    {F G : X × Ω → ℝ} (hFG : F =ᵐ[mX.prod P] G) :
    (fun ω => ∫ x, F (x, ω) ∂mX) =ᵐ[P] fun ω => ∫ x, G (x, ω) ∂mX := by
  have hswap := (Measure.measurePreserving_swap (μ := P) (ν := mX)).quasiMeasurePreserving.ae_eq_comp hFG
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
  apply integral_congr_ae
  exact hω

end Critical2DKPZ.NonGaussian
