/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.MomentKernelL2Interfaces
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Bounded moment operators on configuration `L²`

The delta-Bose moment kernel defines a bounded bilinear form on configuration `L²` and hence
a bounded operator whose inner products are the kernel pairings.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal InnerProductSpace
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The real moment form on configuration `L²` classes. -/
def momentForm (n : ℕ) (θ t : ℝ)
    (F G : Lp ℝ 2 (volume : Measure (Configuration n))) : ℝ :=
  ∫ xy : Configuration n × Configuration n,
    F xy.1 * (momentKernel n θ t xy.1 xy.2).toReal * G xy.2 ∂(volume.prod volume)

/-- The form integrand is absolutely integrable, before representing the form as an operator. -/
theorem integrable_momentForm {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (F G : Lp ℝ 2 (volume : Measure (Configuration n))) :
    Integrable (fun xy : Configuration n × Configuration n =>
      F xy.1 * (momentKernel n θ t xy.1 xy.2).toReal * G xy.2) (volume.prod volume) := by
  obtain ⟨C, hC⟩ := momentKernel_L2_form_bounded n hn θ ht
  exact (hC F G (Lp.memLp F) (Lp.memLp G)).1

/-- The moment form is additive in its left argument. -/
theorem momentForm_add_left {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (F F' G : Lp ℝ 2 (volume : Measure (Configuration n))) :
    momentForm n θ t (F + F') G = momentForm n θ t F G + momentForm n θ t F' G := by
  unfold momentForm
  rw [← integral_add (integrable_momentForm hn θ ht F G) (integrable_momentForm hn θ ht F' G)]
  apply integral_congr_ae
  have h := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Configuration n))) (ν := (volume : Measure (Configuration n)))).ae_eq_comp (Lp.coeFn_add F F')
  filter_upwards [h] with xy hxy
  change (F + F') xy.1 * _ * _ = _
  rw [show (F + F') xy.1 = F xy.1 + F' xy.1 from hxy]
  ring

/-- The moment form is homogeneous in its left argument. -/
theorem momentForm_smul_left (n : ℕ) (θ t c : ℝ)
    (F G : Lp ℝ 2 (volume : Measure (Configuration n))) :
    momentForm n θ t (c • F) G = c • momentForm n θ t F G := by
  unfold momentForm
  rw [smul_eq_mul, ← integral_const_mul]
  apply integral_congr_ae
  have h := (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Configuration n))) (ν := (volume : Measure (Configuration n)))).ae_eq_comp (Lp.coeFn_smul c F)
  filter_upwards [h] with xy hxy
  change (c • F) xy.1 * _ * _ = _
  rw [show (c • F) xy.1 = c * F xy.1 from hxy]
  ring

/-- The moment form is additive in its right argument. -/
theorem momentForm_add_right {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (F G G' : Lp ℝ 2 (volume : Measure (Configuration n))) :
    momentForm n θ t F (G + G') = momentForm n θ t F G + momentForm n θ t F G' := by
  unfold momentForm
  rw [← integral_add (integrable_momentForm hn θ ht F G) (integrable_momentForm hn θ ht F G')]
  apply integral_congr_ae
  have h := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Configuration n))) (ν := (volume : Measure (Configuration n)))).ae_eq_comp (Lp.coeFn_add G G')
  filter_upwards [h] with xy hxy
  change _ * _ * (G + G') xy.2 = _
  rw [show (G + G') xy.2 = G xy.2 + G' xy.2 from hxy]
  ring

/-- The moment form is homogeneous in its right argument. -/
theorem momentForm_smul_right (n : ℕ) (θ t c : ℝ)
    (F G : Lp ℝ 2 (volume : Measure (Configuration n))) :
    momentForm n θ t F (c • G) = c • momentForm n θ t F G := by
  unfold momentForm
  rw [smul_eq_mul, ← integral_const_mul]
  apply integral_congr_ae
  have h := (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Configuration n))) (ν := (volume : Measure (Configuration n)))).ae_eq_comp (Lp.coeFn_smul c G)
  filter_upwards [h] with xy hxy
  change _ * _ * (c • G) xy.2 = _
  rw [show (c • G) xy.2 = c * G xy.2 from hxy]
  ring

/-- The moment form as a bilinear map on configuration `L²`. -/
def momentBilinearMap {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    Lp ℝ 2 (volume : Measure (Configuration n)) →ₗ[ℝ]
      Lp ℝ 2 (volume : Measure (Configuration n)) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (momentForm n θ t) (momentForm_add_left hn θ ht)
    (momentForm_smul_left n θ t) (momentForm_add_right hn θ ht) (momentForm_smul_right n θ t)

/-- One finite constant bounds the entire bilinear map. -/
theorem exists_momentBilinearMap_bound {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ C : ℝ, ∀ F G : Lp ℝ 2 (volume : Measure (Configuration n)),
      ‖momentBilinearMap hn θ ht F G‖ ≤ C * ‖F‖ * ‖G‖ := by
  obtain ⟨C, hC⟩ := momentKernel_L2_form_bounded n hn θ ht
  refine ⟨C, fun F G => ?_⟩
  simpa only [momentBilinearMap, LinearMap.mk₂_apply, momentForm, Real.norm_eq_abs,
    Lp.norm_def] using (hC F G (Lp.memLp F) (Lp.memLp G)).2

/-- The bounded bilinear moment form. -/
def momentBilinearOperator {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    Lp ℝ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Configuration n)) →L[ℝ] ℝ :=
  (momentBilinearMap hn θ ht).mkContinuousOfExistsBound₂
    (exists_momentBilinearMap_bound hn θ ht)

/-- The bounded operator representing the moment form, with the left endpoint as input. -/
def momentOperator {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    Lp ℝ 2 (volume : Measure (Configuration n)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Configuration n)) :=
  InnerProductSpace.continuousLinearMapOfBilin (momentBilinearOperator hn θ ht)

/-- The representing operator has the same kernel pairing as the moment form, with integrability supplied by `integrable_momentForm`. -/
theorem inner_momentOperator {n : ℕ} (hn : n ≤ 4) (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (F G : Lp ℝ 2 (volume : Measure (Configuration n))) :
    ⟪momentOperator hn θ ht F, G⟫_ℝ =
      ∫ xy : Configuration n × Configuration n,
        F xy.1 * (momentKernel n θ t xy.1 xy.2).toReal * G xy.2 ∂(volume.prod volume) := by
  exact InnerProductSpace.continuousLinearMapOfBilin_apply _ F G


end Critical2DKPZ.SHF.Tsai

end
