/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.TensorMoments
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Positive block moment formulas

The finite real moment formula first gives the positive identity for
nonnegative `L²` tests. Almost-everywhere finiteness of the literal diagram
series is essential when undoing its real conversion.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Conversion of a nonnegative tensor form to its literal positive moment-kernel integral. -/
theorem lintegral_momentKernel_tensor_ofReal {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (g g' : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2)
    (hg0 : ∀ i x, 0 ≤ g i x) (hg0' : ∀ i x, 0 ≤ g' i x) :
    (∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
      (∏ i, ENNReal.ofReal (g i (x i))) * momentKernel n θ τ x y *
        ∏ i, ENNReal.ofReal (g' i (y i))) =
      ENNReal.ofReal (∫ x : Configuration n, ∫ y : Configuration n,
        (∏ i, g i (x i)) * (momentKernel n θ τ x y).toReal * ∏ i, g' i (y i)) := by
  let F : Configuration n → ℝ := fun x => ∏ i, g i (x i)
  let G : Configuration n → ℝ := fun y => ∏ i, g' i (y i)
  have hF := memLp_configuration_tensor g hg
  have hG := memLp_configuration_tensor g' hg'
  have hI := ((momentKernel_L2_form_bounded n hn θ hτ).choose_spec F G hF hG).1
  have hF0 (x) : 0 ≤ F x := Finset.prod_nonneg fun i _ => hg0 i _
  have hG0 (y) : 0 ≤ G y := Finset.prod_nonneg fun i _ => hg0' i _
  have heq : (fun x : Configuration n => ∏ i, ENNReal.ofReal (g i (x i))) =
      fun x => ENNReal.ofReal (F x) := by
    funext x
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => hg0 i _)).symm
  have heq' : (fun y : Configuration n => ∏ i, ENNReal.ofReal (g' i (y i))) =
      fun y => ENNReal.ofReal (G y) := by
    funext y
    exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => hg0' i _)).symm
  simp_rw [show ∀ x : Configuration n, (∏ i, ENNReal.ofReal (g i (x i))) = ENNReal.ofReal (F x)
      from congrFun heq,
    show ∀ y : Configuration n, (∏ i, ENNReal.ofReal (g' i (y i))) = ENNReal.ofReal (G y)
      from congrFun heq']
  rw [← integral_prod _ hI, ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun xy => mul_nonneg
      (mul_nonneg (hF0 _) ENNReal.toReal_nonneg) (hG0 _))]
  have hK : Measurable (fun xy : Configuration n × Configuration n =>
      momentKernel n θ τ xy.1 xy.2) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun xy : Configuration n × Configuration n => ((θ, τ), xy))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  have hPos : AEMeasurable (fun xy : Configuration n × Configuration n =>
      ENNReal.ofReal (F xy.1) * momentKernel n θ τ xy.1 xy.2 * ENNReal.ofReal (G xy.2))
      (volume.prod volume) :=
    (hF.aestronglyMeasurable.aemeasurable.ennreal_ofReal.comp_fst.mul hK.aemeasurable).mul
      hG.aestronglyMeasurable.aemeasurable.ennreal_ofReal.comp_snd
  rw [← lintegral_prod _ hPos]
  apply lintegral_congr_ae
  filter_upwards [momentKernel_ne_top n hn θ hτ] with xy hxy
  rw [ENNReal.ofReal_mul (mul_nonneg (hF0 _) ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul (hF0 _), ENNReal.ofReal_toReal hxy]

/-- The positive moment formula for nonnegative real `L²` tests. -/
theorem HasDeltaBoseMoments.lintegral_prod_ofReal_eq {θ τ : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {B : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4) (g g' : Fin n → Plane → ℝ)
    (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2)
    (hg0 : ∀ i x, 0 ≤ g i x) (hg0' : ∀ i x, 0 ≤ g' i x) :
    (∫⁻ ω, ∏ i, (∫⁻ p, ENNReal.ofReal (g i p.1) * ENNReal.ofReal (g' i p.2) ∂B ω) ∂P) =
      ∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
        (∏ i, ENNReal.ofReal (g i (x i))) * momentKernel n θ τ x y *
          ∏ i, ENNReal.ofReal (g' i (y i)) := by
  obtain ⟨hI, hprod, hmoment⟩ := hB.2.2 n hn1 hn g g' hg hg'
  rw [lintegral_momentKernel_tensor_ofReal hn θ hτ g g' hg hg' hg0 hg0', ← hmoment,
    ofReal_integral_eq_lintegral_ofReal hprod
      (Filter.Eventually.of_forall fun ω => Finset.prod_nonneg fun i _ =>
        integral_nonneg fun p => mul_nonneg (hg0 i _) (hg0' i _))]
  apply lintegral_congr_ae
  filter_upwards [hI] with ω hω
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ =>
    integral_nonneg fun p => mul_nonneg (hg0 i _) (hg0' i _))]
  apply Finset.prod_congr rfl
  intro i _
  rw [ofReal_integral_eq_lintegral_ofReal (hω i)
    (Filter.Eventually.of_forall fun p => mul_nonneg (hg0 i _) (hg0' i _))]
  apply lintegral_congr
  intro p
  exact (ENNReal.ofReal_mul (hg0 i _)).symm

end Critical2DKPZ.SHF.Tsai

end
