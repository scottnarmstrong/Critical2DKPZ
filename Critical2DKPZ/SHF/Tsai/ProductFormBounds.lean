/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.FormBounds

/-! # Form bounds for products of positive kernels

The product of two positive kernels has an `L²` form bound whose constant is the product
of the two coordinate form constants.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Products of two positive kernels multiply their `L²` form constants. -/
theorem formBound_prod {X₁ X₂ Y₁ Y₂ : Type*}
    [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y₁] [MeasurableSpace Y₂]
    (μ₁ : Measure X₁) (μ₂ : Measure X₂) (ν₁ : Measure Y₁) (ν₂ : Measure Y₂)
    [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν₁] [SigmaFinite ν₂]
    {K : X₁ → Y₁ → ℝ≥0∞} {L : X₂ → Y₂ → ℝ≥0∞} {c d : ℝ≥0∞}
    (hK : Measurable (Function.uncurry K)) (hL : Measurable (Function.uncurry L))
    (hKF : FormBound μ₁ ν₁ K c) (hLF : FormBound μ₂ ν₂ L d) :
    FormBound (μ₁.prod μ₂) (ν₁.prod ν₂)
      (fun x y => K x.1 y.1 * L x.2 y.2) (c * d) := by
  let T (x : X₁ × X₂) (y : Y₁ × Y₂) := K x.1 y.1 * L x.2 y.2
  have hT : Measurable (Function.uncurry T) :=
    (hK.comp (measurable_fst.fst.prodMk measurable_snd.fst)).mul
      (hL.comp (measurable_fst.snd.prodMk measurable_snd.snd))
  apply (formBound_iff_l2_sq_le (μ₁.prod μ₂) (ν₁.prod ν₂) hT (c * d)).2
  intro f hf
  let H (x₂ : X₂) (y₁ : Y₁) := ∫⁻ y₂, L x₂ y₂ * f (y₁, y₂) ∂ν₂
  have hHm : Measurable (Function.uncurry H) := by
    have h : Measurable (fun q : (X₂ × Y₁) × Y₂ => L q.1.1 q.2 * f (q.1.2, q.2)) :=
      (hL.comp (measurable_fst.fst.prodMk measurable_snd)).mul
        (hf.comp (measurable_fst.snd.prodMk measurable_snd))
    exact h.lintegral_prod_right'
  let E (x : X₁ × X₂) := ∫⁻ y₁, K x.1 y₁ * H x.2 y₁ ∂ν₁
  have hEm : Measurable E := by
    have h : Measurable (fun q : (X₁ × X₂) × Y₁ => K q.1.1 q.2 * H q.1.2 q.2) :=
      (hK.comp (measurable_fst.fst.prodMk measurable_snd)).mul
        (hHm.comp (measurable_fst.snd.prodMk measurable_snd))
    exact h.lintegral_prod_right'
  have hact (x : X₁ × X₂) : (∫⁻ y, T x y * f y ∂(ν₁.prod ν₂)) = E x := by
    have hm : Measurable (fun y : Y₁ × Y₂ => T x y * f y) :=
      ((hT.comp (measurable_const.prodMk measurable_id)).mul hf)
    rw [lintegral_prod _ hm.aemeasurable]
    apply lintegral_congr
    intro y₁
    have hrow : Measurable (fun y₂ => L x.2 y₂ * f (y₁, y₂)) :=
      ((hL.comp (measurable_const.prodMk measurable_id)).mul
        (hf.comp (measurable_const.prodMk measurable_id)))
    simp only [T, mul_assoc]
    exact lintegral_const_mul _ hrow
  have hKsq := (formBound_iff_l2_sq_le μ₁ ν₁ hK c).1 hKF
  have hLsq := (formBound_iff_l2_sq_le μ₂ ν₂ hL d).1 hLF
  have hHrow (x₂) : Measurable (H x₂) :=
    Measurable.comp (g := Function.uncurry H) (f := fun y₁ => (x₂, y₁)) hHm
      (measurable_const.prodMk measurable_id)
  have hHsq (x₂) : Measurable (fun y₁ => H x₂ y₁ ^ (2 : ℝ)) := (hHrow x₂).pow_const _
  have hHintegral : Measurable (fun x₂ => ∫⁻ y₁, H x₂ y₁ ^ (2 : ℝ) ∂ν₁) :=
    (hHm.pow_const (2 : ℝ)).lintegral_prod_right'
  have hfsq : Measurable (fun y₁ => ∫⁻ y₂, f (y₁, y₂) ^ (2 : ℝ) ∂ν₂) :=
    (hf.pow_const (2 : ℝ)).lintegral_prod_right'
  simp_rw [hact]
  rw [lintegral_prod _ (hEm.pow_const (2 : ℝ)).aemeasurable,
    lintegral_lintegral_swap (hEm.pow_const (2 : ℝ)).aemeasurable]
  calc
    _ ≤ ∫⁻ x₂, c ^ 2 * (∫⁻ y₁, H x₂ y₁ ^ (2 : ℝ) ∂ν₁) ∂μ₂ := by
      apply lintegral_mono
      intro x₂
      exact hKsq (H x₂) (hHrow x₂)
    _ = c ^ 2 * ∫⁻ x₂, ∫⁻ y₁, H x₂ y₁ ^ (2 : ℝ) ∂ν₁ ∂μ₂ :=
      lintegral_const_mul _ hHintegral
    _ = c ^ 2 * ∫⁻ y₁, ∫⁻ x₂, H x₂ y₁ ^ (2 : ℝ) ∂μ₂ ∂ν₁ := by
      rw [lintegral_lintegral_swap (hHm.pow_const (2 : ℝ)).aemeasurable]
    _ ≤ c ^ 2 * ∫⁻ y₁, d ^ 2 * (∫⁻ y₂, f (y₁, y₂) ^ (2 : ℝ) ∂ν₂) ∂ν₁ := by
      apply mul_le_mul' le_rfl
      apply lintegral_mono
      intro y₁
      exact hLsq (fun y₂ => f (y₁, y₂)) (hf.comp (measurable_const.prodMk measurable_id))
    _ = (c * d) ^ 2 * ∫⁻ y, f y ^ (2 : ℝ) ∂(ν₁.prod ν₂) := by
      rw [lintegral_const_mul _ hfsq, lintegral_prod _ (hf.pow_const (2 : ℝ)).aemeasurable]
      ring

end Critical2DKPZ.SHF.Tsai

end
