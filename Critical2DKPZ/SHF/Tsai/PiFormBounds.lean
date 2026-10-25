/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ProductFormBounds
public import Critical2DKPZ.Definitions.Plane
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! # Configuration-space form bounds

Transport form bounds through the canonical measure-preserving coordinate
splittings, then iterate the two-factor product bound for configuration kernels.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Form bounds are preserved by measure-preserving changes of endpoint coordinates. -/
theorem formBound_pullback {X Y X' Y' : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace X'] [MeasurableSpace Y']
    {μ : Measure X} {ν : Measure Y} {μ' : Measure X'} {ν' : Measure Y'}
    (eX : X ≃ᵐ X') (eY : Y ≃ᵐ Y') (heX : MeasurePreserving eX μ μ') (heY : MeasurePreserving eY ν ν')
    {K : X' → Y' → ℝ≥0∞} {c : ℝ≥0∞} (hK : FormBound μ' ν' K c) :
    FormBound μ ν (fun x y => K (eX x) (eY y)) c := by
  intro f g hf hg
  have h := hK (fun y => f (eY.symm y)) (fun x => g (eX.symm x))
    (hf.comp eY.symm.measurable) (hg.comp eX.symm.measurable)
  have hinner (x' : X') :
      (∫⁻ y', K x' y' * f (eY.symm y') ∂ν') = ∫⁻ y, K x' (eY y) * f y ∂ν := by
    simpa only [eY.symm_apply_apply] using
      (heY.lintegral_comp_emb eY.measurableEmbedding (fun y' => K x' y' * f (eY.symm y'))).symm
  have hleft :
      (∫⁻ x, g x * (∫⁻ y, K (eX x) (eY y) * f y ∂ν) ∂μ) =
        ∫⁻ x', g (eX.symm x') * (∫⁻ y', K x' y' * f (eY.symm y') ∂ν') ∂μ' := by
    have ht := heX.lintegral_comp_emb eX.measurableEmbedding
      (fun x' => g (eX.symm x') * ∫⁻ y', K x' y' * f (eY.symm y') ∂ν')
    simpa only [eX.symm_apply_apply, hinner] using ht
  have hfnorm : (∫⁻ y', f (eY.symm y') ^ (2 : ℝ) ∂ν') = ∫⁻ y, f y ^ (2 : ℝ) ∂ν := by
    simpa only [eY.symm_apply_apply] using
      (heY.lintegral_comp_emb eY.measurableEmbedding (fun y' => f (eY.symm y') ^ (2 : ℝ))).symm
  have hgnorm : (∫⁻ x', g (eX.symm x') ^ (2 : ℝ) ∂μ') = ∫⁻ x, g x ^ (2 : ℝ) ∂μ := by
    simpa only [eX.symm_apply_apply] using
      (heX.lintegral_comp_emb eX.measurableEmbedding (fun x' => g (eX.symm x') ^ (2 : ℝ))).symm
  rw [← hleft, hfnorm, hgnorm] at h
  exact h

/-- One positive form bound per planar coordinate gives their product on configurations. -/
theorem formBound_configuration_prod (n : ℕ) :
    ∀ (K : Fin n → Plane → Plane → ℝ≥0∞)
      (_ : ∀ i, Measurable (Function.uncurry (K i))) (c : Fin n → ℝ≥0∞)
      (_ : ∀ i, FormBound volume volume (K i) (c i)),
      FormBound volume volume (fun x y : Configuration n => ∏ i, K i (x i) (y i)) (∏ i, c i) := by
  induction n with
  | zero =>
    intro K hKm c hK f g hf hg
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_mul, lintegral_unique,
      volume_pi, Measure.pi_empty_univ, mul_one]
    norm_num [← ENNReal.rpow_natCast_mul, mul_comm]
  | succ n ih =>
    intro K hKm c hK
    let L (x y : Configuration n) := ∏ i, K i.succ (x i) (y i)
    have hLm : Measurable (Function.uncurry L) := by
      apply Finset.measurable_prod
      intro i _
      exact Measurable.comp (g := Function.uncurry (K i.succ))
        (f := fun q : Configuration n × Configuration n => (q.1 i, q.2 i)) (hKm i.succ)
        (((measurable_pi_apply i).comp measurable_fst).prodMk
          ((measurable_pi_apply i).comp measurable_snd))
    have hLF : FormBound volume volume L (∏ i : Fin n, c i.succ) :=
      ih (fun i => K i.succ) (fun i => hKm i.succ) (fun i => c i.succ) (fun i => hK i.succ)
    have hp := formBound_prod (volume : Measure Plane) (volume : Measure (Configuration n))
      (volume : Measure Plane) (volume : Measure (Configuration n)) (hKm 0) hLm (hK 0) hLF
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => Plane) 0
    have he : MeasurePreserving e (volume : Measure (Configuration (n + 1)))
        ((volume : Measure Plane).prod (volume : Measure (Configuration n))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure Plane)) 0
    have h := formBound_pullback e e he he hp
    simpa [e, L, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail, Fin.prod_univ_succ] using h

end Critical2DKPZ.SHF.Tsai

end
