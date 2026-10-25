/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.PositiveSubsetMoments
public import Critical2DKPZ.SHF.Tsai.MixedBlockFormBounds
public import Critical2DKPZ.SHF.Tsai.SubsetProductIntegrals

/-! # Positive tensor moments with a heat replacement in selected factors

Subset splitting separates the lower-particle random moment from the
independent heat factors on the complementary labels. All formulas are
positive integral identities, so they apply before imposing integrability.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Grouping planar endpoint pairs gives the positive tensor form of a measurable kernel. -/
theorem lintegral_tensorForm_eq_endpointPi {n : ℕ}
    (K : Configuration n → Configuration n → ℝ≥0∞) (hK : Measurable (Function.uncurry K))
    (f f' : Fin n → Plane → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hf' : ∀ i, Measurable (f' i)) :
    (∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
      (∏ i, f i (x i)) * K x y * ∏ i, f' i (y i)) =
      ∫⁻ p : Fin n → Plane × Plane, (∏ i, f i (p i).1) *
        K (fun i => (p i).1) (fun i => (p i).2) * ∏ i, f' i (p i).2 := by
  let H (q : Configuration n × Configuration n) :=
    (∏ i, f i (q.1 i)) * K q.1 q.2 * ∏ i, f' i (q.2 i)
  have hH : Measurable H := by
    apply Measurable.mul
    · exact (Finset.measurable_prod _ (fun i _ =>
        (hf i).comp ((measurable_pi_apply i).comp measurable_fst))).mul hK
    · exact Finset.measurable_prod _ (fun i _ =>
        (hf' i).comp ((measurable_pi_apply i).comp measurable_snd))
  have hgroup := (volume_measurePreserving_arrowProdEquivProdArrow Plane Plane (Fin n)).lintegral_comp hH
  have hprod := lintegral_prod (μ := (volume : Measure (Configuration n)))
    (ν := (volume : Measure (Configuration n))) H hH.aemeasurable
  exact hprod.symm.trans hgroup.symm

/-- The mixed block tensor form is the subset moment multiplied by complementary heat pairings. -/
theorem lintegral_mixedBlockKernel_tensor {n : ℕ} (S : Finset (Fin n)) (θ τ : ℝ)
    (f f' : Fin n → Plane → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (hf' : ∀ i, Measurable (f' i)) :
    (∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
      (∏ i, f i (x i)) * mixedBlockKernel n θ τ S x y * ∏ i, f' i (y i)) =
      (∫⁻ x : Configuration S.card, ∫⁻ y : Configuration S.card,
        (∏ i, f (S.orderEmbOfFin rfl i) (x i)) * momentKernel S.card θ τ x y *
          ∏ i, f' (S.orderEmbOfFin rfl i) (y i)) *
        ∏ i ∈ Sᶜ, ∫⁻ p, f i p.1 * f' i p.2 ∂heatBlock τ := by
  classical
  let A (p : Fin S.card → Plane × Plane) :=
    (∏ i, f (S.orderEmbOfFin rfl i) (p i).1) *
      momentKernel S.card θ τ (fun i => (p i).1) (fun i => (p i).2) *
        ∏ i, f' (S.orderEmbOfFin rfl i) (p i).2
  let g (i : Fin n) (p : Plane × Plane) :=
    f i p.1 * ENNReal.ofReal (heatKernel τ (p.2 - p.1)) * f' i p.2
  have hK : Measurable (Function.uncurry (momentKernel S.card θ τ)) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration S.card × Configuration S.card =>
        momentKernel S.card p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration S.card × Configuration S.card => ((θ, τ), q))
      (measurable_momentKernel S.card) (measurable_const.prodMk measurable_id)
  have hfst : Measurable (fun p : Fin S.card → Plane × Plane => fun i => (p i).1) :=
    Measurable.of_eval fun i => (measurable_pi_apply i).fst
  have hsnd : Measurable (fun p : Fin S.card → Plane × Plane => fun i => (p i).2) :=
    Measurable.of_eval fun i => (measurable_pi_apply i).snd
  have hKa : Measurable (fun p : Fin S.card → Plane × Plane =>
      momentKernel S.card θ τ (fun i => (p i).1) (fun i => (p i).2)) :=
    Measurable.comp (g := Function.uncurry (momentKernel S.card θ τ))
      (f := fun p : Fin S.card → Plane × Plane =>
        ((fun i => (p i).1), (fun i => (p i).2))) hK (hfst.prodMk hsnd)
  have hleft : Measurable (fun p : Fin S.card → Plane × Plane =>
      ∏ i, f (S.orderEmbOfFin rfl i) (p i).1) :=
    Finset.measurable_prod _ (fun i _ =>
      (hf _).comp (measurable_pi_apply i).fst)
  have hright : Measurable (fun p : Fin S.card → Plane × Plane =>
      ∏ i, f' (S.orderEmbOfFin rfl i) (p i).2) :=
    Finset.measurable_prod _ (fun i _ =>
      (hf' _).comp (measurable_pi_apply i).snd)
  have hA : Measurable A := (hleft.mul hKa).mul hright
  have hg (i) : Measurable (g i) :=
    (((hf i).comp measurable_fst).mul
      ((measurable_heatKernel τ).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal).mul
        ((hf' i).comp measurable_snd)
  have hpoint (p : Fin n → Plane × Plane) :
      (∏ i, f i (p i).1) * mixedBlockKernel n θ τ S (fun i => (p i).1) (fun i => (p i).2) *
          (∏ i, f' i (p i).2) =
        A (fun i => p (S.orderEmbOfFin rfl i)) * ∏ i ∈ Sᶜ, g i (p i) := by
    rw [prod_subset_mul_compl S (fun i => f i (p i).1),
      prod_subset_mul_compl S (fun i => f' i (p i).2)]
    simp only [mixedBlockKernel, A, g, Finset.prod_mul_distrib]
    rw [prod_orderEmbOfFin Sᶜ (fun i => f i (p i).1),
      prod_orderEmbOfFin Sᶜ (fun i => f' i (p i).2)]
    ring
  have hheat (i : Fin n) : (∫⁻ p : Plane × Plane, g i p) =
      ∫⁻ p, f i p.1 * f' i p.2 ∂heatBlock τ := by
    have hd : Measurable (fun p : Plane × Plane =>
        ENNReal.ofReal (heatKernel τ (p.2 - p.1))) :=
      ((measurable_heatKernel τ).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
    have ht : Measurable (fun p : Plane × Plane => f i p.1 * f' i p.2) :=
      ((hf i).comp measurable_fst).mul ((hf' i).comp measurable_snd)
    rw [heatBlock, lintegral_withDensity_eq_lintegral_mul volume hd ht]
    apply lintegral_congr
    intro p
    change f i p.1 * ENNReal.ofReal (heatKernel τ (p.2 - p.1)) * f' i p.2 =
      ENNReal.ofReal (heatKernel τ (p.2 - p.1)) * (f i p.1 * f' i p.2)
    ring
  rw [lintegral_tensorForm_eq_endpointPi _ (measurable_mixedBlockKernel n θ τ S) f f' hf hf']
  simp_rw [hpoint]
  have hsplit := lintegral_subsetCoordinates_mul_prod S (fun _ => (volume : Measure (Plane × Plane)))
    A hA g hg
  simp only [← volume_pi] at hsplit
  rw [hsplit]
  simp_rw [hheat]
  congr 1
  exact (lintegral_tensorForm_eq_endpointPi _ hK _ _ (fun i => hf _) (fun i => hf' _)).symm

/-- The selected random tensor factors and complementary heat factors have the mixed block moment. -/
theorem HasDeltaBoseMoments.lintegral_prod_ite_heat_eq {θ τ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    {n : ℕ} (hn : n ≤ 4) (S : Finset (Fin n)) (f f' : Fin n → Plane → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) (hf' : ∀ i, Measurable (f' i)) :
    (∫⁻ ω, ∏ i, (∫⁻ p, f i p.1 * f' i p.2 ∂(if i ∈ S then B ω else heatBlock τ)) ∂P) =
      ∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
        (∏ i, f i (x i)) * mixedBlockKernel n θ τ S x y * ∏ i, f' i (y i) := by
  classical
  have heq (ω) : (∏ i, ∫⁻ p, f i p.1 * f' i p.2 ∂(if i ∈ S then B ω else heatBlock τ)) =
      (∏ i ∈ S, ∫⁻ p, f i p.1 * f' i p.2 ∂B ω) *
        ∏ i ∈ Sᶜ, ∫⁻ p, f i p.1 * f' i p.2 ∂heatBlock τ := by
    rw [← Finset.prod_mul_prod_compl S]
    congr 1 <;> apply Finset.prod_congr rfl <;> intro i hi
    · rw [ite_eq_left hi]
    · rw [ite_eq_right (Finset.mem_compl.mp hi)]
  have hm : Measurable (fun ω => ∏ i ∈ S, ∫⁻ p, f i p.1 * f' i p.2 ∂B ω) :=
    Finset.measurable_prod _ fun i _ => (Measure.measurable_lintegral
      (((hf i).comp measurable_fst).mul ((hf' i).comp measurable_snd))).comp hB.1
  simp_rw [heq]
  rw [lintegral_mul_const _ hm, hB.lintegral_prod_finset_eq hτ hn S f f' hf hf',
    lintegral_mixedBlockKernel_tensor S θ τ f f' hf hf']

end Critical2DKPZ.SHF.Tsai

end
