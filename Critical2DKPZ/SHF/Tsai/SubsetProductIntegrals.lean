/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.FinsetCoordinateSplit
import Critical2DKPZ.Collision.RenewalStringCells

/-! # Positive integrals separated by a coordinate subset

Measure-preserving subset regrouping factors a joint test of selected
coordinates from independent one-coordinate tests on the complement.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Increasing subset enumeration preserves the finite product of coordinate factors. -/
theorem prod_orderEmbOfFin {n : ℕ} {M : Type*} [CommMonoid M]
    (S : Finset (Fin n)) (f : Fin n → M) :
    (∏ i : Fin S.card, f (S.orderEmbOfFin rfl i)) = ∏ i ∈ S, f i := by
  conv_rhs => rw [← S.map_orderEmbOfFin_univ rfl, Finset.prod_map]
  rfl

/-- A full coordinate product separates into the subset and complement products. -/
theorem prod_subset_mul_compl {n : ℕ} {M : Type*} [CommMonoid M]
    (S : Finset (Fin n)) (f : Fin n → M) :
    (∏ i, f i) = (∏ i : Fin S.card, f (S.orderEmbOfFin rfl i)) *
      ∏ i : Fin Sᶜ.card, f (Sᶜ.orderEmbOfFin rfl i) := by
  rw [prod_orderEmbOfFin, prod_orderEmbOfFin, Finset.prod_mul_prod_compl]

/-- Positive functions of the two disjoint groups factor under product measure. -/
theorem lintegral_splitFinsetCoordinates_mul {n : ℕ} (S : Finset (Fin n))
    {X : Type*} [MeasurableSpace X] (μ : Fin n → Measure X) [∀ i, SigmaFinite (μ i)]
    (F : (Fin S.card → X) → ℝ≥0∞) (G : (Fin Sᶜ.card → X) → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ x, F (fun i => x (S.orderEmbOfFin rfl i)) *
      G (fun i => x (Sᶜ.orderEmbOfFin rfl i)) ∂Measure.pi μ) =
      (∫⁻ x, F x ∂Measure.pi (fun i => μ (S.orderEmbOfFin rfl i))) *
        ∫⁻ x, G x ∂Measure.pi (fun i => μ (Sᶜ.orderEmbOfFin rfl i)) := by
  have h := (measurePreserving_splitFinsetCoordinates S μ).lintegral_comp
    ((hF.comp measurable_fst).mul (hG.comp measurable_snd))
  change (∫⁻ x, F (fun i => x (S.orderEmbOfFin rfl i)) *
    G (fun i => x (Sᶜ.orderEmbOfFin rfl i)) ∂Measure.pi μ) = _ at h
  exact h.trans (lintegral_prod_mul hF.aemeasurable hG.aemeasurable)

/-- A joint subset test factors from the scalar integrals on its complement. -/
theorem lintegral_subsetCoordinates_mul_prod {n : ℕ} (S : Finset (Fin n))
    {X : Type*} [MeasurableSpace X] (μ : Fin n → Measure X) [∀ i, SigmaFinite (μ i)]
    (F : (Fin S.card → X) → ℝ≥0∞) (hF : Measurable F)
    (g : Fin n → X → ℝ≥0∞) (hg : ∀ i, Measurable (g i)) :
    (∫⁻ x, F (fun i => x (S.orderEmbOfFin rfl i)) * ∏ i ∈ Sᶜ, g i (x i) ∂Measure.pi μ) =
      (∫⁻ x, F x ∂Measure.pi (fun i => μ (S.orderEmbOfFin rfl i))) *
        ∏ i ∈ Sᶜ, ∫⁻ x, g i x ∂μ i := by
  let G (x : Fin Sᶜ.card → X) := ∏ i, g (Sᶜ.orderEmbOfFin rfl i) (x i)
  have hG : Measurable G := Finset.measurable_prod _ fun i _ =>
    (hg _).comp (measurable_pi_apply i)
  have h := lintegral_splitFinsetCoordinates_mul S μ F G hF hG
  have hGeq (x : Fin n → X) : G (fun i => x (Sᶜ.orderEmbOfFin rfl i)) =
      ∏ i ∈ Sᶜ, g i (x i) := prod_orderEmbOfFin Sᶜ (fun i => g i (x i))
  simp_rw [hGeq] at h
  have hGI := Collision.lintegral_fin_nat_prod_eq_prod_collision
    (fun i : Fin Sᶜ.card => μ (Sᶜ.orderEmbOfFin rfl i))
    (fun i => g (Sᶜ.orderEmbOfFin rfl i)) (fun i => hg _)
  have hGI' : (∫⁻ x, G x ∂Measure.pi (fun i => μ (Sᶜ.orderEmbOfFin rfl i))) =
      ∏ i ∈ Sᶜ, ∫⁻ x, g i x ∂μ i :=
    hGI.trans (prod_orderEmbOfFin Sᶜ (fun i => ∫⁻ x, g i x ∂μ i))
  rw [hGI'] at h
  exact h

end Critical2DKPZ.SHF.Tsai

end
