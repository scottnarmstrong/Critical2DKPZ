/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.CovarianceClock
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integration against the difference density

Shearing preserves planar product volume even when the relative width is zero.
This gives the difference density and its pairing with locally integrable kernels.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The shear that changes a difference variable back to the first endpoint. -/
def differenceShear (ρ : ℝ) : Plane × Plane ≃ᵐ Plane × Plane where
  toEquiv := {
    toFun := fun p => (p.1 + ρ • p.2, p.2)
    invFun := fun p => (p.1 - ρ • p.2, p.2)
    left_inv := by intro p; ext <;> simp only [add_sub_cancel_right]
    right_inv := by intro p; ext <;> simp only [sub_add_cancel] }
  measurable_toFun := by
    change Measurable (fun p : Plane × Plane => (p.1 + ρ • p.2, p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : Plane × Plane => (p.1 - ρ • p.2, p.2))
    fun_prop

/-- The shear preserves volume for every real relative width. -/
theorem measurePreserving_differenceShear (ρ : ℝ) :
    MeasurePreserving (differenceShear ρ) (volume.prod volume) (volume.prod volume) := by
  have hskew : MeasurePreserving (fun p : Plane × Plane => (p.1, p.2 + ρ • p.1))
      (volume.prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure Plane)).skew_product
      (g := fun v w : Plane => w + ρ • v) (by fun_prop) ?_
    exact Eventually.of_forall fun v => (measurePreserving_add_right volume (ρ • v)).map_eq
  have hs := Measure.measurePreserving_swap (μ := (volume : Measure Plane))
    (ν := (volume : Measure Plane))
  exact hs.comp (hskew.comp hs)

/-- The transformed independent test weights are integrable on the product. -/
theorem integrable_subDensity_product (φ ψ : TestFn) (ρ : ℝ) :
    Integrable (fun p : Plane × Plane => φ (p.1 + ρ • p.2) * ψ p.2)
      (volume.prod volume) := by
  have hφ : Integrable φ (volume : Measure Plane) :=
    φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
  have hψ : Integrable ψ (volume : Measure Plane) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hint := hφ.mul_prod hψ
  exact ((measurePreserving_differenceShear ρ).integrable_comp_emb
    (differenceShear ρ).measurableEmbedding).mpr hint

/-- The difference density has total mass equal to the product of the test masses. -/
theorem integral_subDensity (φ ψ : TestFn) (ρ : ℝ) :
    (∫ w, subDensity φ ψ ρ w) = (∫ u, φ u) * (∫ v, ψ v) := by
  change (∫ w, ∫ v, φ (w + ρ • v) * ψ v) = _
  rw [integral_integral_swap (integrable_subDensity_product φ ψ ρ)]
  simp_rw [integral_mul_const, integral_add_right_eq_self]
  exact integral_const_mul _ _

/-- A common ball contains the difference of both compact test supports. -/
theorem exists_difference_support_radius (φ ψ : TestFn) :
    ∃ K : ℝ, 0 < K ∧ ∀ ρ ∈ Set.Icc (0 : ℝ) 1, ∀ w v : Plane,
      φ (w + ρ • v) * ψ v ≠ 0 → ‖w‖ < K := by
  obtain ⟨R, hR, hφ⟩ := φ.hasCompactSupport.isCompact.isBounded.exists_pos_norm_lt
  obtain ⟨S, hS, hψ⟩ := ψ.hasCompactSupport.isCompact.isBounded.exists_pos_norm_lt
  refine ⟨R + S, add_pos hR hS, ?_⟩
  intro ρ hρ w v hfg
  obtain ⟨hf, hg⟩ := mul_ne_zero_iff.mp hfg
  have hr : ‖w + ρ • v‖ < R := hφ _ (subset_tsupport φ hf)
  have hs : ‖v‖ < S := hψ _ (subset_tsupport ψ hg)
  have hn : ‖ρ • v‖ ≤ ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hρ.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hρ.2
  have ht : ‖w‖ ≤ ‖w + ρ • v‖ + ‖ρ • v‖ := by
    simpa only [add_sub_cancel_right] using norm_sub_le (w + ρ • v) (ρ • v)
  exact ht.trans_lt (add_lt_add hr (hn.trans_lt hs))

/-- Locally integrable kernels can be multiplied by the transformed test weights. -/
theorem integrable_subDensity_kernel_product (φ ψ : TestFn) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (F : Plane → ℝ)
    (hF : ∀ R : ℝ, 0 < R → IntegrableOn F (Metric.ball 0 R) volume) :
    Integrable (fun p : Plane × Plane => φ (p.1 + ρ • p.2) * ψ p.2 * F p.1)
      (volume.prod volume) := by
  obtain ⟨K, hK, hs⟩ := exists_difference_support_radius φ ψ
  have hcut : Integrable ((Metric.ball (0 : Plane) K).indicator F) :=
    (hF K hK).integrable_indicator measurableSet_ball
  have hψint : Integrable ψ (volume : Measure Plane) :=
    ψ.continuous.integrable_of_hasCompactSupport ψ.hasCompactSupport
  have hg := hcut.mul_prod hψint
  have hφmeas : AEStronglyMeasurable
      (fun p : Plane × Plane => φ (p.1 + ρ • p.2)) (volume.prod volume) := by
    apply Continuous.aestronglyMeasurable
    exact φ.continuous.comp (continuous_fst.add
      ((continuous_const : Continuous (fun _ : Plane × Plane => ρ)).smul continuous_snd))
  have hint := hg.bdd_mul hφmeas (Eventually.of_forall fun p =>
    BoundedContinuousFunction.norm_coe_le_norm (φ : Plane →ᵇ ℝ) (p.1 + ρ • p.2))
  apply hint.congr
  filter_upwards [] with p
  by_cases hfg : φ (p.1 + ρ • p.2) * ψ p.2 = 0
  · change φ (p.1 + ρ • p.2) * (_ * ψ p.2) = _
    rw [mul_comm _ (ψ p.2), ← mul_assoc, hfg, zero_mul, zero_mul]
  · have hp : p.1 ∈ Metric.ball (0 : Plane) K := by
      simpa only [Metric.mem_ball, dist_zero_right] using hs ρ hρ p.1 p.2 hfg
    rw [Set.indicator_of_mem hp]
    ring

/-- Compact test weights make every locally integrable difference kernel integrable. -/
theorem integrable_difference_kernel_product (φ ψ : TestFn) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (F : Plane → ℝ)
    (hF : ∀ R : ℝ, 0 < R → IntegrableOn F (Metric.ball 0 R) volume) :
    Integrable (fun p : Plane × Plane => φ p.1 * ψ p.2 * F (p.1 - ρ • p.2))
      (volume.prod volume) := by
  have hint := integrable_subDensity_kernel_product φ ψ hρ F hF
  apply ((measurePreserving_differenceShear ρ).integrable_comp_emb
    (differenceShear ρ).measurableEmbedding).mp
  convert hint using 1
  funext p
  simp only [Function.comp_apply, differenceShear, MeasurableEquiv.coe_mk,
    Equiv.coe_fn_mk, add_sub_cancel_right]

/-- The difference density represents integration of a locally integrable kernel. -/
theorem integral_subDensity_mul (φ ψ : TestFn) {ρ : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (F : Plane → ℝ)
    (hF : ∀ R : ℝ, 0 < R → IntegrableOn F (Metric.ball 0 R) volume) :
    (∫ w, subDensity φ ψ ρ w * F w) =
      ∫ u, ∫ v, φ u * ψ v * F (u - ρ • v) := by
  have hint := integrable_subDensity_kernel_product φ ψ hρ F hF
  have heq : (fun p : Plane × Plane => φ (p.1 + ρ • p.2) * ψ p.2 * F p.1) =
      (fun p : Plane × Plane => φ p.1 * ψ p.2 * F (p.1 - ρ • p.2)) ∘
        differenceShear ρ := by
    funext p
    simp only [Function.comp_apply, differenceShear, MeasurableEquiv.coe_mk,
      Equiv.coe_fn_mk, add_sub_cancel_right]
  have hin : Integrable (fun p : Plane × Plane => φ p.1 * ψ p.2 * F (p.1 - ρ • p.2))
      (volume.prod volume) := by
    apply ((measurePreserving_differenceShear ρ).integrable_comp_emb
      (differenceShear ρ).measurableEmbedding).mp
    exact heq ▸ hint
  calc
    _ = ∫ w, ∫ v, φ (w + ρ • v) * ψ v * F w := by
      simp only [subDensity, integral_mul_const]
    _ = ∫ p : Plane × Plane, φ (p.1 + ρ • p.2) * ψ p.2 * F p.1 ∂volume.prod volume :=
      integral_integral hint
    _ = ∫ p : Plane × Plane, φ p.1 * ψ p.2 * F (p.1 - ρ • p.2) ∂volume.prod volume := by
      rw [heq]
      exact (measurePreserving_differenceShear ρ).integral_comp
        (differenceShear ρ).measurableEmbedding
        (fun p : Plane × Plane => φ p.1 * ψ p.2 * F (p.1 - ρ • p.2))
    _ = _ := integral_prod _ hin

/-- Only the values of a kernel on the common difference support matter. -/
theorem difference_kernel_integral_of_support (φ ψ : TestFn) {ρ R : ℝ}
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hs : ∀ w v : Plane, φ (w + ρ • v) * ψ v ≠ 0 → w ∈ Metric.ball 0 R)
    (F : Plane → ℝ) (hF : IntegrableOn F (Metric.ball 0 R) volume) :
    Integrable (fun p : Plane × Plane => φ p.1 * ψ p.2 * F (p.1 - ρ • p.2))
        (volume.prod volume) ∧
      Integrable (fun w => subDensity φ ψ ρ w * F w) ∧
      (∫ w, subDensity φ ψ ρ w * F w) =
        ∫ u, ∫ v, φ u * ψ v * F (u - ρ • v) := by
  let G := (Metric.ball (0 : Plane) R).indicator F
  have hG : Integrable G := hF.integrable_indicator measurableSet_ball
  have hGloc : ∀ r : ℝ, 0 < r → IntegrableOn G (Metric.ball 0 r) volume :=
    fun _ _ => hG.integrableOn
  have hprod := integrable_difference_kernel_product φ ψ hρ G hGloc
  have htrans := integrable_subDensity_kernel_product φ ψ hρ G hGloc
  have hD : Integrable (fun w => subDensity φ ψ ρ w * G w) := by
    simpa only [subDensity, integral_mul_const] using htrans.integral_prod_left
  have hpair (u v : Plane) : φ u * ψ v * G (u - ρ • v) =
      φ u * ψ v * F (u - ρ • v) := by
    by_cases hfg : φ u * ψ v = 0
    · rw [hfg, zero_mul, zero_mul]
    · have hm : u - ρ • v ∈ Metric.ball (0 : Plane) R := by
        apply hs (u - ρ • v) v
        simpa only [sub_add_cancel] using hfg
      dsimp only [G]
      rw [Set.indicator_of_mem hm]
  have hdensity (w : Plane) : subDensity φ ψ ρ w * G w = subDensity φ ψ ρ w * F w := by
    by_cases hw : w ∈ Metric.ball (0 : Plane) R
    · dsimp only [G]
      rw [Set.indicator_of_mem hw]
    · have hz : subDensity φ ψ ρ w = 0 := by
        apply integral_eq_zero_of_ae
        filter_upwards [] with v
        by_contra hfg
        exact hw (hs w v hfg)
      rw [hz, zero_mul, zero_mul]
  refine ⟨hprod.congr (Eventually.of_forall fun p => hpair p.1 p.2),
    hD.congr (Eventually.of_forall hdensity), ?_⟩
  calc
    _ = ∫ w, subDensity φ ψ ρ w * G w :=
      integral_congr_ae (Eventually.of_forall fun w => (hdensity w).symm)
    _ = ∫ u, ∫ v, φ u * ψ v * G (u - ρ • v) := integral_subDensity_mul φ ψ hρ G hGloc
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with u
      exact integral_congr_ae (Eventually.of_forall fun v => hpair u v)

end Critical2DKPZ.Extensions.ScaleLimit
