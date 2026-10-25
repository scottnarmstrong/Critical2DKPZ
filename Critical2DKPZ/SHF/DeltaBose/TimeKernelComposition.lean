/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Tactic

/-!
# Composition of positive time-dependent kernels

Time is integrated over the real line; causal kernels can be extended by zero
to this convention. Associativity and transposition require only
measurability, since all kernels are nonnegative and Tonelli applies.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- A time-dependent nonnegative kernel with specified input and output spaces. -/
abbrev TimeKernel (X Y : Type*) := ℝ × X × Y → ℝ≥0∞

/-- Integrate over the middle space and over the first elapsed time. -/
noncomputable def timeKernelComp {X Y Z : Type*} [MeasurableSpace Y]
    (ν : Measure Y) (K : TimeKernel X Y) (L : TimeKernel Y Z) : TimeKernel X Z := fun p =>
  ∫⁻ q : ℝ × Y, K (q.1, p.2.1, q.2) * L (p.1 - q.1, q.2, p.2.2) ∂volume.prod ν

/-- Transposition exchanges the spatial endpoints and leaves elapsed time fixed. -/
def timeKernelTranspose {X Y : Type*} (K : TimeKernel X Y) : TimeKernel Y X :=
  fun p => K (p.1, p.2.2, p.2.1)

/-- Composing measurable time kernels over an s-finite spatial measure gives a measurable kernel. -/
theorem measurable_timeKernelComp {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) [SFinite ν] {K : TimeKernel X Y} {L : TimeKernel Y Z}
    (hK : Measurable K) (hL : Measurable L) : Measurable (timeKernelComp ν K L) := by
  have h1 : Measurable (fun p : (ℝ × X × Z) × (ℝ × Y) => K (p.2.1, p.1.2.1, p.2.2)) :=
    hK.comp (by fun_prop)
  have h2 : Measurable (fun p : (ℝ × X × Z) × (ℝ × Y) => L (p.1.1 - p.2.1, p.2.2, p.1.2.2)) :=
    hL.comp (by fun_prop)
  exact (h1.mul h2).lintegral_prod_right'


/-- Associativity, with each intermediate space carrying its specified measure. -/
theorem timeKernelComp_assoc {X Y Z W : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] [MeasurableSpace W]
    (ν : Measure Y) (η : Measure Z) [SFinite ν] [SFinite η]
    {K : TimeKernel X Y} {L : TimeKernel Y Z} {M : TimeKernel Z W}
    (hK : Measurable K) (hL : Measurable L) (hM : Measurable M) :
    timeKernelComp η (timeKernelComp ν K L) M = timeKernelComp ν K (timeKernelComp η L M) := by
  funext ⟨t, x, w⟩
  let F : (ℝ × Z) → (ℝ × Y) → ℝ≥0∞ := fun p q =>
    K (q.1, x, q.2) * L (p.1 - q.1, q.2, p.2) * M (t - p.1, p.2, w)
  have hF : Measurable (Function.uncurry F) := by
    have h1 : Measurable (fun a : (ℝ × Z) × (ℝ × Y) => K (a.2.1, x, a.2.2)) := hK.comp (by fun_prop)
    have h2 : Measurable (fun a : (ℝ × Z) × (ℝ × Y) => L (a.1.1 - a.2.1, a.2.2, a.1.2)) := hL.comp (by fun_prop)
    have h3 : Measurable (fun a : (ℝ × Z) × (ℝ × Y) => M (t - a.1.1, a.1.2, w)) := hM.comp (by fun_prop)
    exact (h1.mul h2).mul h3
  calc
    timeKernelComp η (timeKernelComp ν K L) M (t, x, w)
        = ∫⁻ p : ℝ × Z, ∫⁻ q : ℝ × Y, F p q ∂volume.prod ν ∂volume.prod η := by
          apply lintegral_congr
          intro p
          have hm : Measurable (fun q : ℝ × Y => K (q.1, x, q.2) * L (p.1 - q.1, q.2, p.2)) :=
            (hK.comp (by fun_prop)).mul (hL.comp (by fun_prop))
          exact (lintegral_mul_const _ hm).symm
    _ = ∫⁻ q : ℝ × Y, ∫⁻ p : ℝ × Z, F p q ∂volume.prod η ∂volume.prod ν :=
      lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ q : ℝ × Y, ∫⁻ p : ℝ × Z, F (p.1 + q.1, p.2) q ∂volume.prod η ∂volume.prod ν := by
      apply lintegral_congr
      intro q
      have hs : MeasurePreserving (fun p : ℝ × Z => (p.1 + q.1, p.2))
          (volume.prod η) (volume.prod η) :=
        (measurePreserving_add_right volume q.1).prod (MeasurePreserving.id η)
      have hm : Measurable (fun p : ℝ × Z => F p q) :=
        hF.comp (measurable_id.prodMk measurable_const)
      exact (hs.lintegral_comp hm).symm
    _ = timeKernelComp ν K (timeKernelComp η L M) (t, x, w) := by
      apply lintegral_congr
      intro q
      have hm : Measurable (fun p : ℝ × Z => L (p.1, q.2, p.2) * M ((t - q.1) - p.1, p.2, w)) :=
        (hL.comp (by fun_prop)).mul (hM.comp (by fun_prop))
      change (∫⁻ p : ℝ × Z, F (p.1 + q.1, p.2) q ∂volume.prod η) =
        K (q.1, x, q.2) * ∫⁻ p : ℝ × Z,
          L (p.1, q.2, p.2) * M ((t - q.1) - p.1, p.2, w) ∂volume.prod η
      rw [← lintegral_const_mul _ hm]
      apply lintegral_congr
      intro p
      dsimp only [F]
      rw [add_sub_cancel_right, show t - (p.1 + q.1) = t - q.1 - p.1 by ring, mul_assoc]

/-- Transposing a composition reverses its factors. -/
theorem timeKernelComp_transpose {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (ν : Measure Y) [SFinite ν] {K : TimeKernel X Y} {L : TimeKernel Y Z}
    (hK : Measurable K) (hL : Measurable L) :
    timeKernelTranspose (timeKernelComp ν K L) =
      timeKernelComp ν (timeKernelTranspose L) (timeKernelTranspose K) := by
  funext ⟨t, z, x⟩
  have hm : Measurable (fun q : ℝ × Y => K (q.1, x, q.2) * L (t - q.1, q.2, z)) :=
    (hK.comp (by fun_prop)).mul (hL.comp (by fun_prop))
  have hs : MeasurePreserving (fun q : ℝ × Y => (t - q.1, q.2))
      (volume.prod ν) (volume.prod ν) :=
    (volume.measurePreserving_sub_left t).prod (MeasurePreserving.id ν)
  change (∫⁻ q : ℝ × Y, K (q.1, x, q.2) * L (t - q.1, q.2, z) ∂volume.prod ν) = _
  rw [← hs.lintegral_comp hm]
  apply lintegral_congr
  intro q
  dsimp only [Function.comp_def, timeKernelTranspose, timeKernelComp]
  rw [sub_sub_cancel, mul_comm]

end Critical2DKPZ.DeltaBose
