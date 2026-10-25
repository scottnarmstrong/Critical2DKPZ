/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.UFunction
public import Critical2DKPZ.Extensions.GffTangent.HeatFourier
public import Critical2DKPZ.Extensions.GffTangent.LogKernelIdentities
import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Critical2DKPZ.Definitions.ShfPairing
import Critical2DKPZ.Extensions.GffTangent.ConvergenceTools
public import Critical2DKPZ.SHF.DeltaBose.ScalarDensity
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.SHF.Tsai.BlockMoments
import Critical2DKPZ.Assembly.Final
import Critical2DKPZ.SHF.Tsai.BlockMarginals
import Critical2DKPZ.Renewal.Primitive
import Critical2DKPZ.SHF.DeltaBose.Measurability
import Critical2DKPZ.SHF.DeltaBose.KernelCompositionL2
import Critical2DKPZ.SHF.Flow.TwoParticleGapCut
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Integrating the scalar collision density

Fubini and the Gamma recurrence identify the primitive of the exact moment
kernel's collision density with the function in the four-results note.
-/

public section

open MeasureTheory Set ProbabilityTheory Filter
open scoped ENNReal Topology ComplexConjugate RealInnerProductSpace

namespace Critical2DKPZ.Extensions.GffTangent

open Spectral Analysis.Sobolev

/-- Absolute integrability in the Gamma variable at every positive time. -/
theorem integrableOn_scalarIntegrand (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (DeltaBose.scalarIntegrand θ t) (Ioi 0) := by
  have he : DeltaBose.scalarIntegrand θ t =
      fun z => t⁻¹ * DeltaBose.gammaLaplaceIntegrand (θ + Real.log t) z :=
    funext (fun z => DeltaBose.scalarIntegrand_eq ht θ z)
  rw [he]
  exact (DeltaBose.integrableOn_gammaLaplaceIntegrand _).const_mul _

/-- Absolute integrability on the time-Gamma product domain. -/
theorem integrable_scalarIntegrand_prod (θ v : ℝ) :
    Integrable (fun p : ℝ × ℝ => DeltaBose.scalarIntegrand θ p.1 p.2)
      ((volume.restrict (Ioo 0 v)).prod (volume.restrict (Ioi 0))) := by
  have hm : Measurable (fun p : ℝ × ℝ => DeltaBose.scalarIntegrand θ p.1 p.2) :=
    DeltaBose.measurable_scalarIntegrand.comp
      (show Measurable (fun p : ℝ × ℝ => ((θ, p.1), p.2)) by fun_prop)
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact integrableOn_scalarIntegrand θ ht.1
  · apply ((Renewal.integrableOn_scalarDensity_Ioc θ v).mono_set Ioo_subset_Ioc_self).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    unfold DeltaBose.scalarDensity
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    rw [Real.norm_eq_abs, abs_of_pos]
    exact div_pos (mul_pos (Real.rpow_pos_of_pos ht.1 _) (Real.exp_pos _))
      (Real.Gamma_pos_of_pos hz)

/-- Elementary integration in time, followed by the Gamma recurrence. -/
theorem integral_scalarIntegrand_time (l : ℝ) {v z : ℝ} (hv : 0 < v) (hz : 0 < z) :
    (∫ t in Ioo 0 v, DeltaBose.scalarIntegrand (-l - Real.eulerMascheroniConstant) t z) =
      Real.exp (-(l - Real.log v) * z - Real.eulerMascheroniConstant * z) /
        Real.Gamma (1 + z) := by
  unfold DeltaBose.scalarIntegrand
  rw [integral_div, integral_mul_const, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hv.le,
    integral_rpow (Or.inl (by linarith : -1 < z - 1))]
  rw [sub_add_cancel, Real.zero_rpow hz.ne', sub_zero, Real.rpow_def_of_pos hv,
    add_comm 1 z, Real.Gamma_add_one hz.ne']
  rw [div_mul_eq_mul_div, div_div, ← Real.exp_add]
  have he : Real.log v * z + (-l - Real.eulerMascheroniConstant) * z =
      -(l - Real.log v) * z - Real.eulerMascheroniConstant * z := by ring
  rw [he]

/-- The primitive of the library's collision density is exactly `uFun`.
The companion product-integrability lemma justifies Fubini at time zero. -/
theorem integral_scalarDensity_eq_uFun (l : ℝ) {v : ℝ} (hv : 0 < v) :
    (∫ t in Ioo 0 v, DeltaBose.scalarDensity (-l - Real.eulerMascheroniConstant) t) =
      uFun l v := by
  unfold DeltaBose.scalarDensity uFun
  rw [integral_integral_swap (integrable_scalarIntegrand_prod _ v)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro z hz
  exact integral_scalarIntegrand_time l hv hz

/-- Each positive-duration block has the literal delta-Bose moment formulas. -/
theorem shf_hasDeltaBoseMoments (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T) :
    SHF.Tsai.HasDeltaBoseMoments (ϑ - Real.eulerMascheroniConstant) (T - a) P (Z a T) := by
  have hD := Assembly.denseSHFAt ϑ P Z hZ ({a, T} : Set ℝ)
    (Set.Finite.countable ((Set.finite_singleton T).insert a))
    (by
      intro s hs
      rcases (show s = a ∨ s = T from hs) with rfl | rfl
      · exact ha
      · exact ha.trans haT.le)
  exact hD.hasDeltaBoseMoments (by simp only [mem_insert_iff, mem_singleton_iff, true_or])
    (by simp only [mem_insert_iff, mem_singleton_iff, or_true]) haT

/-- The positive moment identity with terminal weight one, without an `L²`
assumption on that weight. The library's positive extension performs the
bounded finite-volume exhaustion and monotone-convergence step. -/
theorem lintegral_shf_mass_prod (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T) {n : ℕ} (hn : 1 ≤ n) (hn4 : n ≤ 4)
    (f : Fin n → Plane → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ ω, ∏ i, (∫⁻ p, f i p.1 ∂(Z a T ω)) ∂P) =
      ∫⁻ x : DeltaBose.Configuration n, ∫⁻ y : DeltaBose.Configuration n,
        (∏ i, f i (x i)) *
          DeltaBose.momentKernel n (ϑ - Real.eulerMascheroniConstant) (T - a) x y := by
  simpa only [mul_one, Finset.prod_const_one] using
    (shf_hasDeltaBoseMoments ϑ P Z hZ ha haT).lintegral_prod_eq (sub_pos.mpr haT)
      hn hn4 f (fun _ _ => 1) hf (fun _ => measurable_const)

/-- The annealed first marginal is Lebesgue measure, with terminal weight one. -/
theorem lintegral_shf_mass (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    (f : Plane → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ p, f p.1 ∂(Z a T ω) ∂P) = ∫⁻ x, f x :=
  (shf_hasDeltaBoseMoments ϑ P Z hZ ha haT).lintegral_initial_marginal
    (sub_pos.mpr haT) f hf


/-- Tonelli across the two time variables of the collision triangle. -/
theorem lintegral_lintegral_Ioo_triangle_swap {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [SFinite μ] (h : ℝ) (F : Y → ℝ → ℝ → ℝ≥0∞)
    (hF : Measurable (fun p : (Y × ℝ) × ℝ => F p.1.1 p.1.2 p.2)) :
    (∫⁻ y, (∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, F y r u) ∂μ) =
      ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, ∫⁻ y, F y r u ∂μ := by
  have hm : Measurable (fun p : Y × ℝ => ∫⁻ u in Ioo p.2 h, F p.1 p.2 u) :=
    DeltaBose.measurable_lintegral_Ioo measurable_snd measurable_const hF
  rw [lintegral_lintegral_swap hm.aemeasurable]
  apply lintegral_congr
  intro r
  exact lintegral_lintegral_swap (hF.comp
    (show Measurable (fun p : Y × ℝ => ((p.1, r), p.2)) by fun_prop)).aemeasurable

/-- Integrating both spatial collision coordinates and the terminal endpoints
leaves the separation heat kernel and the scalar collision density. -/
theorem lintegral_single_collision_space {n : ℕ} (α : DeltaBose.CollisionPair n)
    (θ : ℝ) {r d q : ℝ} (hr : 0 < r) (hd : 0 < d) (hq : 0 < q)
    (x : DeltaBose.Configuration n) :
    (∫⁻ y : DeltaBose.Configuration n,
      ∫⁻ z : DeltaBose.FusedConfiguration α, ∫⁻ w : DeltaBose.FusedConfiguration α,
        ENNReal.ofReal (DeltaBose.incomingKernel α r z x) *
          ENNReal.ofReal (DeltaBose.collisionKernel α θ d z w) *
          ENNReal.ofReal (DeltaBose.freeKernel n q (DeltaBose.collisionEmbedding α w) y)) =
      ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
        ENNReal.ofReal (4 * Real.pi * DeltaBose.scalarDensity θ d) := by
  let A (z : DeltaBose.FusedConfiguration α) :=
    ENNReal.ofReal (DeltaBose.incomingKernel α r z x)
  let B (z w : DeltaBose.FusedConfiguration α) :=
    ENNReal.ofReal (DeltaBose.collisionKernel α θ d z w)
  let C (w : DeltaBose.FusedConfiguration α) (y : DeltaBose.Configuration n) :=
    ENNReal.ofReal (DeltaBose.freeKernel n q (DeltaBose.collisionEmbedding α w) y)
  have hA : Measurable A := ((DeltaBose.measurable_incomingKernel α).comp
    (show Measurable (fun z : DeltaBose.FusedConfiguration α => (r, z, x)) by fun_prop)).ennreal_ofReal
  have hB : Measurable (Function.uncurry B) := ((DeltaBose.measurable_collisionKernel α).comp
    (show Measurable (fun p : DeltaBose.FusedConfiguration α × DeltaBose.FusedConfiguration α =>
      ((θ, d), p)) by fun_prop)).ennreal_ofReal
  have hC : Measurable (Function.uncurry C) := ((DeltaBose.measurable_freeKernel n).comp
    (measurable_const.prodMk (((DeltaBose.measurable_collisionEmbedding α).comp
      measurable_fst).prodMk measurable_snd))).ennreal_ofReal
  have hBC := DeltaBose.measurable_spatialKernelComp volume hB hC
  have houter := DeltaBose.spatialKernelComp_action_eq volume volume
    (K := fun _ : Unit => A) (L := DeltaBose.spatialKernelComp volume B C)
    (hA.comp measurable_snd) hBC (f := fun _ => 1) measurable_const ()
  have hinner (z : DeltaBose.FusedConfiguration α) :=
    DeltaBose.spatialKernelComp_action_eq volume volume hB hC
      (f := fun _ => 1) measurable_const z
  simp only [mul_one] at houter hinner
  have hCrow (w : DeltaBose.FusedConfiguration α) : (∫⁻ y, C w y) = 1 :=
    DeltaBose.lintegral_freeKernel_right n hq _
  have hBrow (z : DeltaBose.FusedConfiguration α) :
      (∫⁻ y, DeltaBose.spatialKernelComp volume B C z y) =
        ENNReal.ofReal (4 * Real.pi * DeltaBose.scalarDensity θ d) := by
    rw [hinner]
    simp only [hCrow, mul_one]
    exact DeltaBose.lintegral_collisionKernel_right α θ hd z
  change (∫⁻ y, ∫⁻ z, ∫⁻ w, A z * B z w * C w y) = _
  simp_rw [mul_assoc, lintegral_const_mul' (A _) _ ENNReal.ofReal_ne_top]
  change (∫⁻ y, DeltaBose.spatialKernelComp volume (fun _ : Unit => A)
    (DeltaBose.spatialKernelComp volume B C) () y) = _
  rw [houter]
  simp_rw [hBrow]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  rw [show (∫⁻ z, A z) = ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) from
    DeltaBose.lintegral_incomingKernel_fused α hr x]
  simp only [mul_assoc]


/-- The exact mass of a single resummed collision diagram. -/
theorem lintegral_diagram_singleton {n : ℕ} (α : DeltaBose.CollisionPair n)
    (θ : ℝ) {h : ℝ} (_hh : 0 < h) (x : DeltaBose.Configuration n) :
    (∫⁻ y : DeltaBose.Configuration n, DeltaBose.diagramKernel θ [α] h x y) =
      ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h,
        ENNReal.ofReal (heatKernel (2 * r) (x α.1.2 - x α.1.1)) *
          ENNReal.ofReal (4 * Real.pi * DeltaBose.scalarDensity θ (u - r)) := by
  let F (y : DeltaBose.Configuration n) (r u : ℝ) :=
    ∫⁻ z : DeltaBose.FusedConfiguration α, ∫⁻ w : DeltaBose.FusedConfiguration α,
      ENNReal.ofReal (DeltaBose.incomingKernel α r z x) *
        ENNReal.ofReal (DeltaBose.collisionKernel α θ (u - r) z w) *
        ENNReal.ofReal (DeltaBose.freeKernel n (h - u) (DeltaBose.collisionEmbedding α w) y)
  have hF : Measurable (fun p : (DeltaBose.Configuration n × ℝ) × ℝ => F p.1.1 p.1.2 p.2) := by
    apply Measurable.lintegral_prod_right
    apply Measurable.lintegral_prod_right
    let R := (((DeltaBose.Configuration n × ℝ) × ℝ) × DeltaBose.FusedConfiguration α) ×
      DeltaBose.FusedConfiguration α
    have hy : Measurable (fun p : R => p.1.1.1.1) := by fun_prop
    have hr : Measurable (fun p : R => p.1.1.1.2) := by fun_prop
    have hu : Measurable (fun p : R => p.1.1.2) := by fun_prop
    have hz : Measurable (fun p : R => p.1.2) := by fun_prop
    have hw : Measurable (fun p : R => p.2) := measurable_snd
    have hi := ((DeltaBose.measurable_incomingKernel α).comp
      (hr.prodMk (hz.prodMk (measurable_const (a := x))))).ennreal_ofReal
    have hc := ((DeltaBose.measurable_collisionKernel α).comp
      (((measurable_const (a := θ)).prodMk (hu.sub hr)).prodMk (hz.prodMk hw))).ennreal_ofReal
    have hf := ((DeltaBose.measurable_freeKernel n).comp
      (((measurable_const (a := h)).sub hu).prodMk
        (((DeltaBose.measurable_collisionEmbedding α).comp hw).prodMk hy))).ennreal_ofReal
    exact (hi.mul hc).mul hf
  change (∫⁻ y, ∫⁻ r in Ioo 0 h, ∫⁻ u in Ioo r h, F y r u) = _
  rw [lintegral_lintegral_Ioo_triangle_swap volume h F hF]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact lintegral_single_collision_space α θ hr.1 (sub_pos.mpr hu.1) (sub_pos.mpr hu.2) x

/-- The time-integrated collision coefficient on a translated interval. -/
theorem lintegral_scalarDensity_sub_eq_uFun (l : ℝ) {r h : ℝ} (hrh : r < h) :
    (∫⁻ u in Ioo r h, ENNReal.ofReal
      (DeltaBose.scalarDensity (-l - Real.eulerMascheroniConstant) (u - r))) =
        ENNReal.ofReal (uFun l (h - r)) := by
  have ht := SHF.Flow.lintegral_Ioo_translate r 0 (h - r)
    (fun u => ENNReal.ofReal (DeltaBose.scalarDensity (-l - Real.eulerMascheroniConstant) (u - r)))
  simp only [add_zero, add_sub_cancel_left, add_sub_cancel] at ht
  rw [ht]
  rw [← ofReal_integral_eq_lintegral_ofReal
    ((Renewal.integrableOn_scalarDensity_Ioc _ (h - r)).mono_set Ioo_subset_Ioc_self)]
  · rw [integral_scalarDensity_eq_uFun l (sub_pos.mpr hrh)]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
    exact (DeltaBose.scalarDensity_pos _ hu.1).le

/-- Integrating out all terminal coordinates gives the exact collision
coefficient in the linear covariance formula, before testing the entrance. -/
theorem lintegral_twoParticleCorrection (l : ℝ) {h : ℝ} (hh : 0 < h)
    (x : DeltaBose.Configuration 2) :
    (∫⁻ y : DeltaBose.Configuration 2,
      DeltaBose.twoParticleCorrection (-l - Real.eulerMascheroniConstant) h x y) =
        ∫⁻ r in Ioo 0 h,
          ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) *
            ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (uFun l (h - r)) := by
  change (∫⁻ y, DeltaBose.diagramKernel (-l - Real.eulerMascheroniConstant)
    [DeltaBose.pairTwo] h x y) = _
  rw [lintegral_diagram_singleton _ _ hh]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  change (∫⁻ u in Ioo r h, ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) *
    ENNReal.ofReal (4 * Real.pi * DeltaBose.scalarDensity
      (-l - Real.eulerMascheroniConstant) (u - r))) = _
  simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi), ← mul_assoc]
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top),
    lintegral_scalarDensity_sub_eq_uFun l hr.2]


/-- Joint measurability of the integrated collision density, including the
total real logarithm convention used in its definition. -/
theorem measurable_uFun : Measurable (fun p : ℝ × ℝ => uFun p.1 p.2) := by
  unfold uFun
  simp only [div_eq_mul_inv]
  have he : Measurable (fun p : (ℝ × ℝ) × ℝ =>
      Real.exp (-(p.1.1 - Real.log p.1.2) * p.2 - Real.eulerMascheroniConstant * p.2)) := by
    fun_prop
  have hg : Measurable (fun p : (ℝ × ℝ) × ℝ => (Real.Gamma (1 + p.2))⁻¹) :=
    DeltaBose.continuous_inv_gamma.measurable.comp (by fun_prop)
  exact (he.mul hg).stronglyMeasurable.integral_prod_right'.measurable

/-- The complete two-particle kernel with terminal weight one. -/
theorem lintegral_momentKernel_two (l : ℝ) {h : ℝ} (hh : 0 < h)
    (x : DeltaBose.Configuration 2) :
    (∫⁻ y : DeltaBose.Configuration 2,
      DeltaBose.momentKernel 2 (-l - Real.eulerMascheroniConstant) h x y) =
      1 + ∫⁻ r in Ioo 0 h,
        ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) *
          ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (uFun l (h - r)) := by
  have hm : Measurable (fun y : DeltaBose.Configuration 2 =>
      ENNReal.ofReal (DeltaBose.freeKernel 2 h x y)) :=
    ((DeltaBose.measurable_freeKernel 2).comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))).ennreal_ofReal
  have he (y : DeltaBose.Configuration 2) :
      DeltaBose.momentKernel 2 (-l - Real.eulerMascheroniConstant) h x y =
        ENNReal.ofReal (DeltaBose.freeKernel 2 h x y) +
          DeltaBose.twoParticleCorrection (-l - Real.eulerMascheroniConstant) h x y := by
    simpa only [DeltaBose.freeKernel, Fin.prod_univ_two] using
      DeltaBose.momentKernel_two (-l - Real.eulerMascheroniConstant) h x y
  simp_rw [he]
  rw [lintegral_add_left hm, DeltaBose.lintegral_freeKernel_right 2 hh,
    lintegral_twoParticleCorrection l hh]

/-- Pulling a constant entrance weight through the terminal integral. -/
theorem lintegral_const_mul_momentKernel_two (l : ℝ) {h : ℝ} (hh : 0 < h)
    (x : DeltaBose.Configuration 2) (c : ℝ≥0∞) :
    (∫⁻ y : DeltaBose.Configuration 2,
      c * DeltaBose.momentKernel 2 (-l - Real.eulerMascheroniConstant) h x y) =
      c * (1 + ∫⁻ r in Ioo 0 h,
        ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) *
          ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (uFun l (h - r))) := by
  have hp : Measurable (fun y : DeltaBose.Configuration 2 =>
      ((-l - Real.eulerMascheroniConstant, h), x, y)) := by fun_prop
  have hm := (DeltaBose.measurable_momentKernel 2).comp hp
  change Measurable (fun y : DeltaBose.Configuration 2 =>
    DeltaBose.momentKernel 2 (-l - Real.eulerMascheroniConstant) h x y) at hm
  rw [lintegral_const_mul c hm, lintegral_momentKernel_two l hh]

/-- Nonnegative entrance tests of the exact second moment, after the flat
terminal weight has been integrated out. -/
theorem lintegral_shf_mass_mul (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, (∫⁻ p, f p.1 ∂(Z a T ω)) * (∫⁻ p, g p.1 ∂(Z a T ω)) ∂P) =
      ∫⁻ x : DeltaBose.Configuration 2, f (x 0) * g (x 1) *
        (1 + ∫⁻ r in Ioo 0 (T - a),
          ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) *
            ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (uFun l (T - a - r))) := by
  have hi := lintegral_shf_mass_prod (-l) P Z hZ ha haT (by norm_num : 1 ≤ 2)
    (by norm_num : 2 ≤ 4)
    ![f, g] (by intro i; fin_cases i; exact hf; exact hg)
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one] at hi
  rw [hi]
  apply lintegral_congr
  intro x
  exact lintegral_const_mul_momentKernel_two l (sub_pos.mpr haT) x (f (x 0) * g (x 1))


/-- An integrable entrance test has finite annealed absolute mass. -/
theorem lintegral_shf_abs_mass_lt_top (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T) {f : Plane → ℝ}
    (hf : Measurable f) (hf1 : Integrable f) :
    (∫⁻ ω, ∫⁻ p, ENNReal.ofReal |f p.1| ∂(Z a T ω) ∂P) < ⊤ := by
  have hAbs : Measurable (fun x => |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  rw [lintegral_shf_mass ϑ P Z hZ ha haT (fun x => ENNReal.ofReal |f x|)
    hAbs.ennreal_ofReal]
  simpa only [Real.enorm_eq_ofReal_abs] using
    (hasFiniteIntegral_iff_enorm.mp hf1.hasFiniteIntegral)

/-- Signed integrable entrance tests give samplewise and annealed integrable
flat-terminal pairings. No boundedness premise is needed for this first moment. -/
theorem integrable_shfPairing_one (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T) {f : Plane → ℝ}
    (hf : Measurable f) (hf1 : Integrable f) :
    (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => f p.1) (Z a T ω)) ∧
      Integrable (shfPairing Z a T f (fun _ => 1)) P := by
  have hi := integrable_randomMeasure_integral (hZ.1 a T ha haT)
    (show Measurable (fun p : Plane × Plane => f p.1) from hf.comp measurable_fst)
    (lintegral_shf_abs_mass_lt_top ϑ P Z hZ ha haT hf hf1)
  refine ⟨hi.1, ?_⟩
  change Integrable (fun ω => ∫ p : Plane × Plane, f p.1 * 1 ∂(Z a T ω)) P
  simpa only [mul_one] using hi.2

/-- The annealed mean of the signed flat-terminal mass is the test's integral. -/
theorem integral_shfPairing_one (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T) {f : Plane → ℝ}
    (hf : Measurable f) (hf1 : Integrable f) :
    (∫ ω, shfPairing Z a T f (fun _ => 1) ω ∂P) = ∫ x, f x := by
  simp only [shfPairing, mul_one]
  rw [integral_randomMeasure_integral (hZ.1 a T ha haT)
    (show Measurable (fun p : Plane × Plane => f p.1) from hf.comp measurable_fst)
    (lintegral_shf_abs_mass_lt_top ϑ P Z hZ ha haT hf hf1),
    lintegral_shf_mass ϑ P Z hZ ha haT (fun x => ENNReal.ofReal (f x)) hf.ennreal_ofReal,
    lintegral_shf_mass ϑ P Z hZ ha haT (fun x => ENNReal.ofReal (-f x)) hf.neg.ennreal_ofReal]
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf1).symm


/-- The integrated collision density is increasing in its positive horizon. -/
theorem uFun_mono {l u v : ℝ} (hu : 0 < u) (huv : u ≤ v) : uFun l u ≤ uFun l v := by
  rw [← integral_scalarDensity_eq_uFun l hu,
    ← integral_scalarDensity_eq_uFun l (hu.trans_le huv)]
  apply setIntegral_mono_set
    ((Renewal.integrableOn_scalarDensity_Ioc _ v).mono_set Ioo_subset_Ioc_self)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (DeltaBose.scalarDensity_pos _ ht.1).le
  · exact Filter.Eventually.of_forall fun t ht => ⟨ht.1, ht.2.trans_le huv⟩

/-- Products of two one-particle positive entrance tests factor under
configuration Lebesgue measure. -/
theorem lintegral_configuration_two_mul (f g : Plane → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x : DeltaBose.Configuration 2, f (x 0) * g (x 1)) =
      (∫⁻ x, f x) * ∫⁻ y, g y := by
  have hm : Measurable (fun p : Plane × Plane => f p.1 * g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  calc
    _ = ∫⁻ p : Plane × Plane, f p.1 * g p.2 :=
      (volume_preserving_finTwoArrow Plane).lintegral_comp hm
    _ = _ := lintegral_prod_mul hf.aemeasurable hg.aemeasurable

/-- A bounded entrance factor and an integrable entrance factor control the
heat pairing uniformly over all positive heat times. -/
theorem lintegral_configuration_heat_le {f g : Plane → ℝ≥0∞} (hg : Measurable g)
    {c : ℝ≥0∞} (hf : ∀ x, f x ≤ c) {s : ℝ} (hs : 0 < s) :
    (∫⁻ x : DeltaBose.Configuration 2,
      f (x 0) * g (x 1) * ENNReal.ofReal (heatKernel s (x 1 - x 0))) ≤
        c * ∫⁻ y, g y := by
  let F (p : Plane × Plane) := c * g p.2 * ENNReal.ofReal (heatKernel s (p.2 - p.1))
  have hm : Measurable F := by
    apply Measurable.mul
    · exact measurable_const.mul (hg.comp measurable_snd)
    · exact ((measurable_heatKernel s).comp (measurable_snd.sub measurable_fst)).ennreal_ofReal
  have hrow (y : Plane) :
      (∫⁻ x : Plane, F (x, y)) = c * g y := by
    have hk : Measurable (fun x : Plane => ENNReal.ofReal (heatKernel s (y - x))) :=
      ((measurable_heatKernel s).comp (measurable_const.sub measurable_id)).ennreal_ofReal
    change (∫⁻ x : Plane, (c * g y) * ENNReal.ofReal (heatKernel s (y - x))) = _
    rw [lintegral_const_mul _ hk]
    have he (x : Plane) : heatKernel s (y - x) = heatKernel s (x - y) := by
      rw [← DeltaBose.heatKernel_neg s (x - y), neg_sub]
    simp_rw [he]
    rw [DeltaBose.lintegral_heatKernel_sub hs y, mul_one]
  calc
    _ ≤ ∫⁻ x : DeltaBose.Configuration 2,
        c * g (x 1) * ENNReal.ofReal (heatKernel s (x 1 - x 0)) := by
      apply lintegral_mono
      intro x
      exact mul_le_mul' (mul_le_mul' (hf (x 0)) le_rfl) le_rfl
    _ = ∫⁻ p : Plane × Plane, F p :=
      (volume_preserving_finTwoArrow Plane).lintegral_comp hm
    _ = ∫⁻ y : Plane, ∫⁻ x : Plane, F (x, y) := by
      rw [Measure.volume_eq_prod, lintegral_prod _ hm.aemeasurable]
      exact lintegral_lintegral_swap hm.aemeasurable
    _ = c * ∫⁻ y, g y := by
      simp_rw [hrow]
      exact lintegral_const_mul c hg


/-- Fubini places the positive second-moment correction into its covariance
time-integral form, without assuming finiteness in advance. -/
theorem lintegral_shf_mass_mul_eq (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    (f g : Plane → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, (∫⁻ p, f p.1 ∂(Z a T ω)) * (∫⁻ p, g p.1 ∂(Z a T ω)) ∂P) =
      (∫⁻ x, f x) * (∫⁻ y, g y) +
        ∫⁻ r in Ioo 0 (T - a),
          (ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (uFun l (T - a - r))) *
            ∫⁻ x : DeltaBose.Configuration 2,
              f (x 0) * g (x 1) * ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) := by
  let K (x : DeltaBose.Configuration 2) (r : ℝ) :=
    ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) *
      ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (uFun l (T - a - r))
  have hx : Measurable (fun x : DeltaBose.Configuration 2 => f (x 0) * g (x 1)) :=
    (hf.comp (measurable_pi_apply 0)).mul (hg.comp (measurable_pi_apply 1))
  have hk : Measurable (Function.uncurry K) := by
    have hh : Measurable (fun p : DeltaBose.Configuration 2 × ℝ =>
        heatKernel (2 * p.2) (p.1 1 - p.1 0)) := by
      unfold heatKernel
      fun_prop
    have hp : Measurable (fun p : DeltaBose.Configuration 2 × ℝ =>
        (l, T - a - p.2)) := by fun_prop
    have hu := measurable_uFun.comp hp
    change Measurable (fun p : DeltaBose.Configuration 2 × ℝ => uFun l (T - a - p.2)) at hu
    exact (hh.ennreal_ofReal.mul measurable_const).mul hu.ennreal_ofReal
  have hF : Measurable (fun p : DeltaBose.Configuration 2 × ℝ =>
      f (p.1 0) * g (p.1 1) * K p.1 p.2) := (hx.comp measurable_fst).mul hk
  calc
    _ = (∫⁻ x : DeltaBose.Configuration 2, f (x 0) * g (x 1)) +
        ∫⁻ x : DeltaBose.Configuration 2,
          f (x 0) * g (x 1) * ∫⁻ r in Ioo 0 (T - a), K x r := by
      rw [lintegral_shf_mass_mul l P Z hZ ha haT f g hf hg]
      simp_rw [mul_add, mul_one]
      exact lintegral_add_left hx _
    _ = _ := by
      rw [lintegral_configuration_two_mul f g hf hg]
      apply congrArg ((∫⁻ x, f x) * (∫⁻ y, g y) + ·)
      calc
        _ = ∫⁻ x : DeltaBose.Configuration 2, ∫⁻ r in Ioo 0 (T - a),
            f (x 0) * g (x 1) * K x r := by
          apply lintegral_congr
          intro x
          have hr := hk.comp (show Measurable (fun r : ℝ => (x, r)) by fun_prop)
          change Measurable (K x) at hr
          exact (lintegral_const_mul (f (x 0) * g (x 1)) hr).symm
        _ = ∫⁻ r in Ioo 0 (T - a), ∫⁻ x : DeltaBose.Configuration 2,
            f (x 0) * g (x 1) * K x r := lintegral_lintegral_swap hF.aemeasurable
        _ = _ := by
          apply lintegral_congr
          intro r
          have he (x : DeltaBose.Configuration 2) : f (x 0) * g (x 1) * K x r =
              (ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (uFun l (T - a - r))) *
                (f (x 0) * g (x 1) * ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0))) := by
            dsimp only [K]
            ac_rfl
          simp_rw [he]
          exact lintegral_const_mul' _ _
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)


/-- Bounded integrable positive entrance tests have a finite second moment at
every finite positive horizon. Monotonicity of `uFun` supplies the uniform
time coefficient, even beyond the range of its elementary logarithmic bound. -/
theorem lintegral_shf_mass_sq_lt_top (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    (f : Plane → ℝ≥0∞) (hf : Measurable f) {c : ℝ≥0∞} (hc : c < ⊤)
    (hbound : ∀ x, f x ≤ c) (hint : (∫⁻ x, f x) < ⊤) :
    (∫⁻ ω, (∫⁻ p, f p.1 ∂(Z a T ω)) * (∫⁻ p, f p.1 ∂(Z a T ω)) ∂P) < ⊤ := by
  rw [lintegral_shf_mass_mul_eq l P Z hZ ha haT f f hf hf]
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact ENNReal.mul_lt_top hint hint
  · let D : ℝ≥0∞ := (ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (uFun l (T - a))) *
      (c * ∫⁻ x, f x)
    have hD : D < ⊤ := ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
      (ENNReal.mul_lt_top hc hint)
    have hv : (volume (Ioo (0 : ℝ) (T - a))) < ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    apply lt_of_le_of_lt _ (ENNReal.mul_lt_top hD hv)
    calc
      _ ≤ ∫⁻ _r in Ioo 0 (T - a), D := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
        apply mul_le_mul'
        · exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
            (uFun_mono (sub_pos.mpr hr.2) (sub_le_self _ hr.1.le)))
        · exact lintegral_configuration_heat_le hf hbound (mul_pos two_pos hr.1)
      _ = D * volume (Ioo 0 (T - a)) := by
        rw [lintegral_const, Measure.restrict_apply_univ]

/-- The flat-terminal signed mass of a bounded integrable entrance test is
square integrable. Its integrability follows from the positive second moment
of the absolute entrance test; it is not assumed as a covariance premise. -/
theorem memLp_two_shfPairing_one (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T) {f : Plane → ℝ}
    (hf : Measurable f) (hf1 : Integrable f) {C : ℝ} (hbound : ∀ x, |f x| ≤ C) :
    MemLp (shfPairing Z a T f (fun _ => 1)) 2 P := by
  let A (ω : Ω) := ∫⁻ p, ENNReal.ofReal |f p.1| ∂(Z a T ω)
  have hAbs : Measurable (fun x => |f x|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have hA := (Measure.measurable_lintegral
    (hAbs.ennreal_ofReal.comp measurable_fst)).comp (hZ.1 a T ha haT)
  change Measurable A at hA
  have hfin := lintegral_shf_mass_sq_lt_top l P Z hZ ha haT
    (fun x => ENNReal.ofReal |f x|) hAbs.ennreal_ofReal
    (c := ENNReal.ofReal C) ENNReal.ofReal_lt_top
    (fun x => ENNReal.ofReal_le_ofReal (hbound x))
    (by simpa only [Real.enorm_eq_ofReal_abs] using
      (hasFiniteIntegral_iff_enorm.mp hf1.hasFiniteIntegral))
  have hAA : Integrable (fun ω => (A ω ^ 2).toReal) P := by
    exact integrable_toReal_of_lintegral_ne_top (hA.pow_const 2).aemeasurable
      (by simpa only [pow_two, A] using hfin.ne)
  have hsq : Integrable (fun ω => (A ω).toReal ^ 2) P := by
    simpa only [ENNReal.toReal_pow] using hAA
  have hX := (integrable_shfPairing_one (-l) P Z hZ ha haT hf hf1).2
  apply (memLp_two_iff_integrable_sq hX.aestronglyMeasurable).mpr
  apply hsq.mono' (hX.aestronglyMeasurable.pow 2)
  filter_upwards with ω
  have hle : |shfPairing Z a T f (fun _ => 1) ω| ≤ (A ω).toReal := by
    simp only [shfPairing, mul_one]
    rw [show (A ω).toReal = ∫ p : Plane × Plane, |f p.1| ∂(Z a T ω) from
      (integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun p : Plane × Plane => abs_nonneg (f p.1))
        (hAbs.comp measurable_fst).aestronglyMeasurable).symm]
    simpa only [Real.norm_eq_abs] using
      norm_integral_le_integral_norm (μ := Z a T ω) (fun p : Plane × Plane => f p.1)
  change ‖shfPairing Z a T f (fun _ => 1) ω ^ 2‖ ≤ (A ω).toReal ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) ENNReal.toReal_nonneg).mpr hle


/-- Nonnegativity of the integrated collision coefficient. -/
theorem uFun_nonneg (l u : ℝ) : 0 ≤ uFun l u := by
  unfold uFun
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  exact div_nonneg (Real.exp_nonneg _) (Real.Gamma_pos_of_pos (add_pos zero_lt_one hz)).le

/-- A positive two-particle heat form is the nonnegative lift of its real
heat pairing. Product integrability is established before applying Fubini. -/
theorem lintegral_configuration_heat_eq_ofReal
    {f g : Plane → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : Integrable f) (hg1 : Integrable g) {r : ℝ} (hr : 0 < r) :
    (∫⁻ x : DeltaBose.Configuration 2,
      ENNReal.ofReal (f (x 0)) * ENNReal.ofReal (g (x 1)) *
        ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0))) =
      ENNReal.ofReal (∫ x, f x * heatSmooth (2 * r) g x) := by
  have hr2 : 0 < 2 * r := mul_pos two_pos hr
  let F : Plane × Plane → ℝ := fun p =>
    f p.1 * g p.2 * heatKernel (2 * r) (p.2 - p.1)
  have hF : Integrable F (volume.prod volume) := by
    apply (hf1.mul_prod hg1).mul_bdd
      (((continuous_heatKernel (2 * r)).comp
        (continuous_snd.sub continuous_fst)).aestronglyMeasurable)
    filter_upwards [] with p
    change ‖heatKernel (2 * r) (p.2 - p.1)‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hr2.le _)]
    exact heatKernel_le_at_zero hr2.le _
  have hF0 (p : Plane × Plane) : 0 ≤ F p :=
    mul_nonneg (mul_nonneg (hf0 p.1) (hg0 p.2)) (heatKernel_nonneg hr2.le _)
  have hm : Measurable (fun p : Plane × Plane => ENNReal.ofReal (F p)) :=
    (((hf.comp measurable_fst).mul (hg.comp measurable_snd)).mul
      ((measurable_heatKernel (2 * r)).comp
        (measurable_snd.sub measurable_fst))).ennreal_ofReal
  calc
    _ = ∫⁻ x : DeltaBose.Configuration 2,
        ENNReal.ofReal (F (MeasurableEquiv.finTwoArrow x)) := by
      apply lintegral_congr
      intro x
      symm
      change ENNReal.ofReal ((f (x 0) * g (x 1)) *
        heatKernel (2 * r) (x 1 - x 0)) = _
      rw [ENNReal.ofReal_mul (mul_nonneg (hf0 _) (hg0 _)), ENNReal.ofReal_mul (hf0 _)]
    _ = ∫⁻ p : Plane × Plane, ENNReal.ofReal (F p) :=
      (volume_preserving_finTwoArrow Plane).lintegral_comp hm
    _ = ENNReal.ofReal (∫ p : Plane × Plane, F p) :=
      (ofReal_integral_eq_lintegral_ofReal hF (Filter.Eventually.of_forall hF0)).symm
    _ = ENNReal.ofReal (∫ x, f x * heatSmooth (2 * r) g x) := by
      apply congrArg ENNReal.ofReal
      rw [Measure.volume_eq_prod, integral_prod _ hF]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp only [F, heatSmooth]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← DeltaBose.heatKernel_neg (2 * r) (x - y), neg_sub]
      ring

/-- Joint measurability gives the positive heat form as a measurable time
function, before any finiteness assertion. -/
theorem measurable_configuration_heat_pair (f g : Plane → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun r : ℝ => ∫⁻ x : DeltaBose.Configuration 2,
      f (x 0) * g (x 1) * ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0))) := by
  have hh : Measurable (fun p : ℝ × DeltaBose.Configuration 2 =>
      heatKernel (2 * p.1) (p.2 1 - p.2 0)) := by unfold heatKernel; fun_prop
  have hm : Measurable (fun p : ℝ × DeltaBose.Configuration 2 =>
      f (p.2 0) * g (p.2 1) * ENNReal.ofReal (heatKernel (2 * p.1) (p.2 1 - p.2 0))) :=
    ((hf.comp ((measurable_pi_apply 0).comp measurable_snd)).mul
      (hg.comp ((measurable_pi_apply 1).comp measurable_snd))).mul hh.ennreal_ofReal
  exact hm.lintegral_prod_right

/-- The positive second moment as an honest real integral. -/
theorem second_moment_shfPairing_nonneg (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {f g : Plane → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : Integrable f) (hg1 : Integrable g)
    {Cf Cg : ℝ} (hfbd : ∀ x, f x ≤ Cf) (hgbd : ∀ x, g x ≤ Cg) :
    IntegrableOn (fun r =>
      (∫ x, f x * heatSmooth (2 * r) g x) * uFun l (T - a - r))
        (Ioo 0 (T - a)) ∧
    (∫ ω, shfPairing Z a T f (fun _ => 1) ω *
        shfPairing Z a T g (fun _ => 1) ω ∂P) =
      (∫ x, f x) * (∫ y, g y) + 4 * Real.pi *
        ∫ r in Ioo 0 (T - a),
          (∫ x, f x * heatSmooth (2 * r) g x) * uFun l (T - a - r) := by
  let X : Ω → ℝ := shfPairing Z a T f (fun _ => 1)
  let Y : Ω → ℝ := shfPairing Z a T g (fun _ => 1)
  let q : ℝ → ℝ := fun r =>
    (∫ x, f x * heatSmooth (2 * r) g x) * uFun l (T - a - r)
  let Q : ℝ → ℝ≥0∞ := fun r =>
    (ENNReal.ofReal (4 * Real.pi) * ENNReal.ofReal (uFun l (T - a - r))) *
      ∫⁻ x : DeltaBose.Configuration 2,
        ENNReal.ofReal (f (x 0)) * ENNReal.ofReal (g (x 1)) *
          ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0))

  have hfAbs : ∀ x, |f x| ≤ max Cf 0 := by
    intro x
    rw [abs_of_nonneg (hf0 x)]
    exact (hfbd x).trans (le_max_left _ _)
  have hgAbs : ∀ x, |g x| ≤ max Cg 0 := by
    intro x
    rw [abs_of_nonneg (hg0 x)]
    exact (hgbd x).trans (le_max_left _ _)
  have hX2 := memLp_two_shfPairing_one l P Z hZ ha haT hf hf1 hfAbs
  have hY2 := memLp_two_shfPairing_one l P Z hZ ha haT hg hg1 hgAbs
  have hXY : Integrable (fun ω => X ω * Y ω) P := hX2.integrable_mul hY2
  have hX0 : ∀ ω, 0 ≤ X ω := by
    intro ω
    exact integral_nonneg fun p : Plane × Plane => mul_nonneg (hf0 p.1) zero_le_one
  have hY0 : ∀ ω, 0 ≤ Y ω := by
    intro ω
    exact integral_nonneg fun p : Plane × Plane => mul_nonneg (hg0 p.1) zero_le_one

  have hfSample := (integrable_shfPairing_one (-l) P Z hZ ha haT hf hf1).1
  have hgSample := (integrable_shfPairing_one (-l) P Z hZ ha haT hg hg1).1
  have hXlift : ∀ᵐ ω ∂P, ENNReal.ofReal (X ω) =
      ∫⁻ p, ENNReal.ofReal (f p.1) ∂(Z a T ω) := by
    filter_upwards [hfSample] with ω hω
    change ENNReal.ofReal (∫ p, f p.1 * 1 ∂(Z a T ω)) = _
    simp only [mul_one]
    exact ofReal_integral_eq_lintegral_ofReal hω
      (Filter.Eventually.of_forall fun p => hf0 p.1)
  have hYlift : ∀ᵐ ω ∂P, ENNReal.ofReal (Y ω) =
      ∫⁻ p, ENNReal.ofReal (g p.1) ∂(Z a T ω) := by
    filter_upwards [hgSample] with ω hω
    change ENNReal.ofReal (∫ p, g p.1 * 1 ∂(Z a T ω)) = _
    simp only [mul_one]
    exact ofReal_integral_eq_lintegral_ofReal hω
      (Filter.Eventually.of_forall fun p => hg0 p.1)

  have hLaw := lintegral_shf_mass_mul_eq l P Z hZ ha haT
    (fun x => ENNReal.ofReal (f x)) (fun x => ENNReal.ofReal (g x))
    hf.ennreal_ofReal hg.ennreal_ofReal
  have hMomentLift : ENNReal.ofReal (∫ ω, X ω * Y ω ∂P) =
      (∫⁻ x, ENNReal.ofReal (f x)) * (∫⁻ y, ENNReal.ofReal (g y)) +
        ∫⁻ r in Ioo 0 (T - a), Q r := by
    rw [ofReal_integral_eq_lintegral_ofReal hXY
      (Filter.Eventually.of_forall fun ω => mul_nonneg (hX0 ω) (hY0 ω))]
    calc
      (∫⁻ ω, ENNReal.ofReal (X ω * Y ω) ∂P) =
          ∫⁻ ω, (∫⁻ p, ENNReal.ofReal (f p.1) ∂(Z a T ω)) *
            (∫⁻ p, ENNReal.ofReal (g p.1) ∂(Z a T ω)) ∂P := by
        apply lintegral_congr_ae
        filter_upwards [hXlift, hYlift] with ω hxf hyg
        rw [ENNReal.ofReal_mul (hX0 ω), hxf, hyg]
      _ = _ := by simpa only [Q] using hLaw

  have hMomentTop : ENNReal.ofReal (∫ ω, X ω * Y ω ∂P) < ⊤ := ENNReal.ofReal_lt_top
  have hQtop : (∫⁻ r in Ioo 0 (T - a), Q r) < ⊤ := by
    apply lt_of_le_of_lt _ hMomentTop
    rw [hMomentLift]
    exact le_add_left le_rfl

  have hq0ae : 0 ≤ᵐ[volume.restrict (Ioo 0 (T - a))] q := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    dsimp only [q]
    exact mul_nonneg
      (integral_nonneg fun x => mul_nonneg (hf0 x)
        (integral_nonneg fun y => mul_nonneg
          (heatKernel_nonneg (mul_nonneg zero_le_two hr.1.le) _) (hg0 y)))
      (uFun_nonneg _ _)

  -- Use this only on the restricted time measure, where `0 < r`.
  have hQeq : ∀ᵐ r ∂volume.restrict (Ioo 0 (T - a)),
      Q r = ENNReal.ofReal (4 * Real.pi * q r) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    have hheat := lintegral_configuration_heat_eq_ofReal hf hg hf0 hg0 hf1 hg1 hr.1
    dsimp only [Q, q]
    rw [hheat]
    have hs0 : 0 ≤ ∫ x, f x * heatSmooth (2 * r) g x :=
      integral_nonneg fun x => mul_nonneg (hf0 x)
        (integral_nonneg fun y => mul_nonneg
          (heatKernel_nonneg (mul_nonneg zero_le_two hr.1.le) _) (hg0 y))
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi),
      ENNReal.ofReal_mul hs0]
    ac_rfl

  have hqMeas : AEStronglyMeasurable (fun r => 4 * Real.pi * q r)
      (volume.restrict (Ioo 0 (T - a))) := by
    -- `Q` is measurable from `measurable_configuration_heat_pair` and
    -- `measurable_uFun`; use `hQeq` and measurable `ENNReal.toReal`.
    have hQmeas : Measurable Q := by
      dsimp only [Q]
      exact (measurable_const.mul
        ((measurable_uFun.comp (show Measurable (fun r : ℝ => (l, T - a - r)) by
          fun_prop)).ennreal_ofReal)).mul
        (measurable_configuration_heat_pair
          (fun x => ENNReal.ofReal (f x)) (fun x => ENNReal.ofReal (g x))
          hf.ennreal_ofReal hg.ennreal_ofReal)
    apply (hQmeas.ennreal_toReal.aestronglyMeasurable.restrict).congr
    filter_upwards [hQeq, hq0ae] with r hrEq hrq
    rw [hrEq, ENNReal.toReal_ofReal]
    exact mul_nonneg (by positivity : 0 ≤ 4 * Real.pi) hrq

  have h4qInt : IntegrableOn (fun r => 4 * Real.pi * q r) (Ioo 0 (T - a)) :=
    (lintegral_ofReal_ne_top_iff_integrable hqMeas
      (hq0ae.mono fun r hrq => mul_nonneg (by positivity) hrq)).mp (by
        rw [← lintegral_congr_ae hQeq]
        exact hQtop.ne)
  have hqInt : IntegrableOn q (Ioo 0 (T - a)) := by
    have h := h4qInt.const_mul (4 * Real.pi)⁻¹
    apply h.congr
    filter_upwards [] with r
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : (4 * Real.pi : ℝ) ≠ 0), one_mul]


  refine ⟨hqInt, ?_⟩
  have hfMean := ofReal_integral_eq_lintegral_ofReal hf1
    (Filter.Eventually.of_forall hf0)
  have hgMean := ofReal_integral_eq_lintegral_ofReal hg1
    (Filter.Eventually.of_forall hg0)
  have htime := ofReal_integral_eq_lintegral_ofReal h4qInt
    (hq0ae.mono fun r hrq => mul_nonneg (by positivity) hrq)
  rw [← lintegral_congr_ae hQeq] at htime
  rw [← hfMean, ← hgMean, ← htime] at hMomentLift
  have ht0 : 0 ≤ ∫ r in Ioo 0 (T - a), 4 * Real.pi * q r :=
    integral_nonneg_of_ae (hq0ae.mono fun r hrq => mul_nonneg (by positivity) hrq)
  have hreal := congrArg ENNReal.toReal hMomentLift
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal ht0, integral_const_mul] at hreal
  have hnonneg : 0 ≤ ∫ ω, X ω * Y ω ∂P :=
    integral_nonneg fun ω => mul_nonneg (hX0 ω) (hY0 ω)
  simpa only [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (integral_nonneg hf0),
    ENNReal.toReal_ofReal (integral_nonneg hg0),
    X, Y] using hreal


/-- The flat-terminal SHF pairing is linear under subtraction of integrable entrance tests. -/
theorem shfPairing_sub_one_ae (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T) {f g : Plane → ℝ}
    (hf : Measurable f) (hg : Measurable g)
    (hf1 : Integrable f) (hg1 : Integrable g) :
    shfPairing Z a T (f - g) (fun _ => 1) =ᵐ[P]
      shfPairing Z a T f (fun _ => 1) - shfPairing Z a T g (fun _ => 1) := by
  have hfi := (integrable_shfPairing_one ϑ P Z hZ ha haT hf hf1).1
  have hgi := (integrable_shfPairing_one ϑ P Z hZ ha haT hg hg1).1
  filter_upwards [hfi, hgi] with ω hfω hgω
  simp only [shfPairing, mul_one, Pi.sub_apply]
  exact integral_sub hfω hgω


/-- Heat smoothing at positive time is linear under subtraction of integrable inputs. -/
theorem heatSmooth_sub {f g : Plane → ℝ} (hf : Integrable f) (hg : Integrable g)
    {s : ℝ} (hs : 0 < s) (x : Plane) :
    heatSmooth s (f - g) x = heatSmooth s f x - heatSmooth s g x := by
  unfold heatSmooth
  rw [← integral_sub (integrable_heatSmooth_integrand hf hs x)
    (integrable_heatSmooth_integrand hg hs x)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [Pi.sub_apply, mul_sub]


/-- The integrated heat pairing expands into four terms under two subtractions. -/
theorem integral_mul_heatSmooth_sub_sub
    {f₁ f₂ g₁ g₂ : Plane → ℝ}
    (hf₁ : Integrable f₁) (hf₂ : Integrable f₂)
    (hg₁ : Integrable g₁) (hg₂ : Integrable g₂)
    {s : ℝ} (hs : 0 < s) :
    (∫ x : Plane, (f₁ - f₂) x * heatSmooth (2 * s) (g₁ - g₂) x) =
      (∫ x : Plane, f₁ x * heatSmooth (2 * s) g₁ x) -
      (∫ x : Plane, f₁ x * heatSmooth (2 * s) g₂ x) -
      (∫ x : Plane, f₂ x * heatSmooth (2 * s) g₁ x) +
      (∫ x : Plane, f₂ x * heatSmooth (2 * s) g₂ x) := by
  have hs2 : 0 < 2 * s := mul_pos two_pos hs
  have h11 := integrable_inner_heatSemigroup hf₁ hg₁ hs
  have h12 := integrable_inner_heatSemigroup hf₁ hg₂ hs
  have h21 := integrable_inner_heatSemigroup hf₂ hg₁ hs
  have h22 := integrable_inner_heatSemigroup hf₂ hg₂ hs
  simp_rw [heatSmooth_sub hg₁ hg₂ hs2, Pi.sub_apply, sub_mul, mul_sub]
  have ha : Integrable (fun x => f₁ x * heatSmooth (2 * s) g₁ x -
      f₁ x * heatSmooth (2 * s) g₂ x) := h11.sub h12
  have hb : Integrable (fun x => f₂ x * heatSmooth (2 * s) g₁ x -
      f₂ x * heatSmooth (2 * s) g₂ x) := h21.sub h22
  rw [integral_sub ha hb, integral_sub h11 h12, integral_sub h21 h22]
  ring

/-- Integration of a four-term signed expansion, with all four terms integrable. -/
theorem integral_sub_sub_add {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {A B C D : α → ℝ} (hA : Integrable A μ) (hB : Integrable B μ)
    (hC : Integrable C μ) (hD : Integrable D μ) :
    (∫ x, A x - B x - C x + D x ∂μ) =
      (∫ x, A x ∂μ) - (∫ x, B x ∂μ) - (∫ x, C x ∂μ) + ∫ x, D x ∂μ := by
  have h₁ := integral_sub hA hB
  have h₂ := integral_sub (hA.sub hB) hC
  have h₃ := integral_add ((hA.sub hB).sub hC) hD
  simp only [Pi.sub_apply] at h₁ h₂ h₃
  rw [h₃, h₂, h₁]

/-- Signed bounded integrable entrance tests have the exact second moment, and the time
integrand in that formula is genuinely integrable. -/
theorem second_moment_shfPairing (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {f g : Plane → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf1 : Integrable f) (hg1 : Integrable g)
    {Cf Cg : ℝ} (hfbd : ∀ x, |f x| ≤ Cf) (hgbd : ∀ x, |g x| ≤ Cg) :
    IntegrableOn (fun r =>
      (∫ x, f x * heatSmooth (2 * r) g x) * uFun l (T - a - r))
        (Ioo 0 (T - a)) ∧
    (∫ ω, shfPairing Z a T f (fun _ => 1) ω *
        shfPairing Z a T g (fun _ => 1) ω ∂P) =
      (∫ x, f x) * (∫ y, g y) + 4 * Real.pi *
        ∫ r in Ioc 0 (T - a),
          (∫ x, f x * heatSmooth (2 * r) g x) * uFun l (T - a - r) := by
  rw [integral_Ioc_eq_integral_Ioo]
  let fp : Plane → ℝ := fun x => max (f x) 0
  let fn : Plane → ℝ := fun x => max (-f x) 0
  let gp : Plane → ℝ := fun x => max (g x) 0
  let gn : Plane → ℝ := fun x => max (-g x) 0
  have hfp : Integrable fp := hf1.pos_part
  have hfn : Integrable fn := hf1.neg_part
  have hgp : Integrable gp := hg1.pos_part
  have hgn : Integrable gn := hg1.neg_part
  have hfpm : Measurable fp := hf.max measurable_const
  have hfnm : Measurable fn := hf.neg.max measurable_const
  have hgpm : Measurable gp := hg.max measurable_const
  have hgnm : Measurable gn := hg.neg.max measurable_const
  have hfp0 : ∀ x, 0 ≤ fp x := fun x => le_max_right _ _
  have hfn0 : ∀ x, 0 ≤ fn x := fun x => le_max_right _ _
  have hgp0 : ∀ x, 0 ≤ gp x := fun x => le_max_right _ _
  have hgn0 : ∀ x, 0 ≤ gn x := fun x => le_max_right _ _
  have hfpbd : ∀ x, fp x ≤ max Cf 0 := by
    intro x; exact max_le_max (le_trans (le_abs_self _) (hfbd x)) le_rfl
  have hfnbd : ∀ x, fn x ≤ max Cf 0 := by
    intro x; exact max_le_max (le_trans (neg_le_abs _) (hfbd x)) le_rfl
  have hgpbd : ∀ x, gp x ≤ max Cg 0 := by
    intro x; exact max_le_max (le_trans (le_abs_self _) (hgbd x)) le_rfl
  have hgnbd : ∀ x, gn x ≤ max Cg 0 := by
    intro x; exact max_le_max (le_trans (neg_le_abs _) (hgbd x)) le_rfl
  have hf_eq : f = fp - fn := by
    funext x
    simp only [fp, fn, Pi.sub_apply, max_zero_sub_eq_self]
  have hg_eq : g = gp - gn := by
    funext x
    simp only [gp, gn, Pi.sub_apply, max_zero_sub_eq_self]

  have hpp := second_moment_shfPairing_nonneg l P Z hZ ha haT
    hfpm hgpm hfp0 hgp0 hfp hgp hfpbd hgpbd
  have hpn := second_moment_shfPairing_nonneg l P Z hZ ha haT
    hfpm hgnm hfp0 hgn0 hfp hgn hfpbd hgnbd
  have hnp := second_moment_shfPairing_nonneg l P Z hZ ha haT
    hfnm hgpm hfn0 hgp0 hfn hgp hfnbd hgpbd
  have hnn := second_moment_shfPairing_nonneg l P Z hZ ha haT
    hfnm hgnm hfn0 hgn0 hfn hgn hfnbd hgnbd

  let q : ℝ → ℝ := fun r =>
    (∫ x, f x * heatSmooth (2 * r) g x) * uFun l (T - a - r)
  let qpp : ℝ → ℝ := fun r =>
    (∫ x, fp x * heatSmooth (2 * r) gp x) * uFun l (T - a - r)
  let qpn : ℝ → ℝ := fun r =>
    (∫ x, fp x * heatSmooth (2 * r) gn x) * uFun l (T - a - r)
  let qnp : ℝ → ℝ := fun r =>
    (∫ x, fn x * heatSmooth (2 * r) gp x) * uFun l (T - a - r)
  let qnn : ℝ → ℝ := fun r =>
    (∫ x, fn x * heatSmooth (2 * r) gn x) * uFun l (T - a - r)
  have hqcomb : IntegrableOn (qpp - qpn - qnp + qnn) (Ioo 0 (T - a)) :=
    ((hpp.1.sub hpn.1).sub hnp.1).add hnn.1
  have hqae : q =ᵐ[volume.restrict (Ioo 0 (T - a))] qpp - qpn - qnp + qnn := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
    dsimp only [q, qpp, qpn, qnp, qnn, Pi.sub_apply, Pi.add_apply]
    rw [hf_eq, hg_eq,
      integral_mul_heatSmooth_sub_sub hfp hfn hgp hgn hr.1]
    ring
  have hqint : IntegrableOn q (Ioo 0 (T - a)) := hqcomb.congr hqae.symm

  let Xp : Ω → ℝ := shfPairing Z a T fp (fun _ => 1)
  let Xn : Ω → ℝ := shfPairing Z a T fn (fun _ => 1)
  let Yp : Ω → ℝ := shfPairing Z a T gp (fun _ => 1)
  let Yn : Ω → ℝ := shfPairing Z a T gn (fun _ => 1)
  let X : Ω → ℝ := shfPairing Z a T f (fun _ => 1)
  let Y : Ω → ℝ := shfPairing Z a T g (fun _ => 1)
  have hXsplit : X =ᵐ[P] Xp - Xn := by
    have h := shfPairing_sub_one_ae (-l) P Z hZ ha haT hfpm hfnm hfp hfn
    simpa only [X, Xp, Xn, hf_eq] using h
  have hYsplit : Y =ᵐ[P] Yp - Yn := by
    have h := shfPairing_sub_one_ae (-l) P Z hZ ha haT hgpm hgnm hgp hgn
    simpa only [Y, Yp, Yn, hg_eq] using h

  have hXp2 := memLp_two_shfPairing_one l P Z hZ ha haT hfpm hfp
    (fun x => by rw [abs_of_nonneg (hfp0 x)]; exact hfpbd x)
  have hXn2 := memLp_two_shfPairing_one l P Z hZ ha haT hfnm hfn
    (fun x => by rw [abs_of_nonneg (hfn0 x)]; exact hfnbd x)
  have hYp2 := memLp_two_shfPairing_one l P Z hZ ha haT hgpm hgp
    (fun x => by rw [abs_of_nonneg (hgp0 x)]; exact hgpbd x)
  have hYn2 := memLp_two_shfPairing_one l P Z hZ ha haT hgnm hgn
    (fun x => by rw [abs_of_nonneg (hgn0 x)]; exact hgnbd x)
  have hppI : Integrable (fun ω => Xp ω * Yp ω) P := hXp2.integrable_mul hYp2
  have hpnI : Integrable (fun ω => Xp ω * Yn ω) P := hXp2.integrable_mul hYn2
  have hnpI : Integrable (fun ω => Xn ω * Yp ω) P := hXn2.integrable_mul hYp2
  have hnnI : Integrable (fun ω => Xn ω * Yn ω) P := hXn2.integrable_mul hYn2
  have hprodAE : (fun ω => X ω * Y ω) =ᵐ[P]
      fun ω => Xp ω * Yp ω - Xp ω * Yn ω - Xn ω * Yp ω + Xn ω * Yn ω := by
    filter_upwards [hXsplit, hYsplit] with ω hx hy
    simp only [Pi.sub_apply] at hx hy
    rw [hx, hy]
    ring
  have hprod :
      (∫ ω, X ω * Y ω ∂P) =
        (∫ ω, Xp ω * Yp ω ∂P) - (∫ ω, Xp ω * Yn ω ∂P) -
        (∫ ω, Xn ω * Yp ω ∂P) + (∫ ω, Xn ω * Yn ω ∂P) := by
    rw [integral_congr_ae hprodAE]
    exact integral_sub_sub_add hppI hpnI hnpI hnnI

  have hfm : (∫ x, f x) = (∫ x, fp x) - ∫ x, fn x := by
    rw [hf_eq]
    exact integral_sub hfp hfn
  have hgm : (∫ x, g x) = (∫ x, gp x) - ∫ x, gn x := by
    rw [hg_eq]
    exact integral_sub hgp hgn
  have hqIntegral :
      (∫ r in Ioo 0 (T - a), q r) =
        (∫ r in Ioo 0 (T - a), qpp r) -
        (∫ r in Ioo 0 (T - a), qpn r) -
        (∫ r in Ioo 0 (T - a), qnp r) +
        (∫ r in Ioo 0 (T - a), qnn r) := by
    rw [integral_congr_ae hqae]
    exact integral_sub_sub_add hpp.1 hpn.1 hnp.1 hnn.1
  refine ⟨hqint, ?_⟩
  change (∫ ω, X ω * Y ω ∂P) =
    (∫ x, f x) * (∫ y, g y) + 4 * Real.pi * ∫ r in Ioo 0 (T - a), q r
  rw [hprod, hpp.2, hpn.2, hnp.2, hnn.2, hfm, hgm, hqIntegral]
  ring

/-- The signed flat-terminal covariance is the collision term. -/
theorem covariance_shfPairing_start (l : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF (-l) P Z)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {f g : Plane → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf1 : Integrable f) (hg1 : Integrable g)
    {Cf Cg : ℝ} (hfbd : ∀ x, |f x| ≤ Cf) (hgbd : ∀ x, |g x| ≤ Cg) :
    covariance (shfPairing Z a T f (fun _ => 1))
        (shfPairing Z a T g (fun _ => 1)) P =
      4 * Real.pi * ∫ r in Ioc 0 (T - a),
        (∫ x, f x * heatSmooth (2 * r) g x) * uFun l (T - a - r) := by
  have hf2 := memLp_two_shfPairing_one l P Z hZ ha haT hf hf1 hfbd
  have hg2 := memLp_two_shfPairing_one l P Z hZ ha haT hg hg1 hgbd
  have hsecond := (second_moment_shfPairing l P Z hZ ha haT
    hf hg hf1 hg1 hfbd hgbd).2
  rw [covariance_eq_sub hf2 hg2]
  simp only [Pi.mul_apply]
  rw [hsecond,
    integral_shfPairing_one (-l) P Z hZ ha haT hf hf1,
    integral_shfPairing_one (-l) P Z hZ ha haT hg hg1]
  ring

/-- The Fourier quotient of the heat-mollification error tends to zero.
This is the exact frequency-side quantity corresponding to the integrated
heat energy. -/
theorem tendsto_fourier_heatMultiplier_error (f : TestFn)
    (hfzero : (∫ x : Plane, f x) = 0) :
    Tendsto (fun δ : ℝ => ∫ ξ : Plane,
      ‖fourierKPZ f ξ‖ ^ 2 *
        (Real.exp (-δ * ‖ξ‖ ^ 2) - 1) ^ 2 / ‖ξ‖ ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
  have hf : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hf2 : MemLp (f : Plane → ℝ) 2 volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  have hfm := integrable_firstMoment_testFn f
  have hquotComplex := integrable_fourierKPZ_pairing_div_norm_sq
    hf hf hf2 hf2 hfzero hfzero hfm hfm
  have hself (ξ : Plane) :
      (fourierKPZ f ξ * conj (fourierKPZ f ξ)).re = ‖fourierKPZ f ξ‖ ^ 2 := by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hquot : Integrable (fun ξ : Plane => ‖fourierKPZ f ξ‖ ^ 2 / ‖ξ‖ ^ 2) := by
    apply hquotComplex.congr
    filter_upwards [] with ξ
    rw [hself]
  have hfourier : Continuous (fourierKPZ f) := by
    have he : fourierKPZ f = angularFourierIntegral f :=
      funext (fourierKPZ_eq_angularFourierIntegral_fun f)
    rw [he]
    exact continuous_angularFourierIntegral hf
  have hDCT : Tendsto (fun δ : ℝ => ∫ ξ : Plane,
      ‖fourierKPZ f ξ‖ ^ 2 *
        (Real.exp (-δ * ‖ξ‖ ^ 2) - 1) ^ 2 / ‖ξ‖ ^ 2)
      (𝓝[>] 0) (𝓝 (∫ _ : Plane, (0 : ℝ))) := by
    apply tendsto_integral_filter_of_dominated_convergence
      (bound := fun ξ => 4 * (‖fourierKPZ f ξ‖ ^ 2 / ‖ξ‖ ^ 2))
    · filter_upwards [] with δ
      have he : Continuous (fun ξ : Plane => (Real.exp (-δ * ‖ξ‖ ^ 2) - 1) ^ 2) := by
        fun_prop
      exact (((hfourier.norm.pow 2).measurable.mul he.measurable).div
        (continuous_norm.pow 2).measurable).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      filter_upwards [] with ξ
      have hexp : 0 < Real.exp (-δ * ‖ξ‖ ^ 2) := Real.exp_pos _
      have hexp_le : Real.exp (-δ * ‖ξ‖ ^ 2) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hδ.le) (sq_nonneg _))
      have hsq : (Real.exp (-δ * ‖ξ‖ ^ 2) - 1) ^ 2 ≤ 4 := by
        nlinarith [hexp.le]
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg
        (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _))]
      calc
        ‖fourierKPZ f ξ‖ ^ 2 * (Real.exp (-δ * ‖ξ‖ ^ 2) - 1) ^ 2 /
              ‖ξ‖ ^ 2
            ≤ ‖fourierKPZ f ξ‖ ^ 2 * 4 / ‖ξ‖ ^ 2 := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsq (sq_nonneg _)) (sq_nonneg _)
        _ = 4 * (‖fourierKPZ f ξ‖ ^ 2 / ‖ξ‖ ^ 2) := by ring
    · exact hquot.const_mul 4
    · filter_upwards [] with ξ
      have he : Tendsto (fun δ : ℝ => Real.exp (-δ * ‖ξ‖ ^ 2) - 1)
          (𝓝[>] 0) (𝓝 0) := by
        have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [zero_mul, neg_zero, Real.exp_zero, sub_self, neg_mul, Function.comp_def] using
          ((Real.continuous_exp.continuousAt.tendsto.comp
            (hδ.mul_const (‖ξ‖ ^ 2)).neg).sub_const 1)
      have hz := ((he.pow 2).const_mul (‖fourierKPZ f ξ‖ ^ 2)).div_const (‖ξ‖ ^ 2)
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div] using hz
  simpa only [integral_zero] using hDCT


/-- The angular Fourier transform of the planar heat kernel. -/
theorem fourierKPZ_heatKernel {δ : ℝ} (hδ : 0 < δ) (ξ : Plane) :
    (∫ x : Plane, Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) *
        (heatKernel δ x : ℂ)) =
      (Real.exp (-(δ / 2) * ‖ξ‖ ^ 2) : ℂ) := by
  have hb : 0 < ((((2 * δ)⁻¹ : ℝ) : ℂ)).re := by
    simpa only [Complex.ofReal_re] using inv_pos.mpr (mul_pos two_pos hδ)
  have hg := GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb (-Complex.I) ξ
  have hd : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  simp only [hd, Nat.cast_ofNat, div_self (by norm_num : (2 : ℂ) ≠ 0),
    Complex.cpow_one, neg_sq, Complex.I_sq] at hg
  have he : (fun x : Plane => Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) *
      (heatKernel δ x : ℂ)) = fun x => (((2 * Real.pi * δ)⁻¹ : ℝ) : ℂ) *
        Complex.exp (-((((2 * δ)⁻¹ : ℝ) : ℂ)) * (‖x‖ : ℂ) ^ 2 +
          (-Complex.I) * (inner ℝ ξ x : ℂ)) := by
    funext x
    rw [heatKernel_eq_exp, Complex.ofReal_mul, Complex.ofReal_exp]
    rw [mul_left_comm, ← Complex.exp_add, real_inner_comm x ξ]
    push_cast
    congr 2
    ring
  have hc : (((2 * Real.pi * δ)⁻¹ : ℝ) : ℂ) *
      (Real.pi / ((((2 * δ)⁻¹ : ℝ) : ℂ))) = 1 := by
    push_cast
    field_simp [hδ.ne', Real.pi_ne_zero]
  have hx : (-1 : ℂ) * (‖ξ‖ : ℂ) ^ 2 /
      (4 * ((((2 * δ)⁻¹ : ℝ) : ℂ))) = ((-(δ / 2) * ‖ξ‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    field_simp [hδ.ne']
    ring
  rw [he, integral_const_mul, hg, ← mul_assoc, hc, one_mul, hx, ← Complex.ofReal_exp]

/-- The spatial convolution integrand is integrable on the product plane. -/
theorem integrable_heatSmooth_prod {f : Plane → ℝ} (hf : Integrable f)
    {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - p.2) * f p.2)
      (volume.prod volume) := by
  have hbase := (integrable_heatKernel hδ).mul_prod hf
  have hm := (measurePreserving_sub_prod (volume : Measure Plane) volume).integrable_comp_of_integrable hbase
  simpa only [Function.comp_def] using hm

/-- Heat smoothing preserves integrability. -/
theorem integrable_heatSmooth {f : Plane → ℝ} (hf : Integrable f)
    {δ : ℝ} (hδ : 0 < δ) : Integrable (heatSmooth δ f) := by
  exact (integrable_heatSmooth_prod hf hδ).integral_prod_left

/-- Angular Fourier multiplication by the heat-semigroup symbol. -/
theorem fourierKPZ_heatSmooth {f : Plane → ℝ} (hf : Integrable f)
    {δ : ℝ} (hδ : 0 < δ) (ξ : Plane) :
    fourierKPZ (heatSmooth δ f) ξ =
      (Real.exp (-(δ / 2) * ‖ξ‖ ^ 2) : ℂ) * fourierKPZ f ξ := by
  let K : Plane × Plane → ℂ := fun p =>
    Complex.exp (-(Complex.I * (inner ℝ p.1 ξ : ℝ))) *
      ((heatKernel δ (p.1 - p.2) * f p.2 : ℝ) : ℂ)
  have hj := integrable_heatSmooth_prod hf hδ
  have hK : Integrable K (volume.prod volume) := by
    apply (hj.ofReal (𝕜 := ℂ)).bdd_mul (c := 1)
      ((by fun_prop : Continuous (fun p : Plane × Plane =>
        Complex.exp (-(Complex.I * (inner ℝ p.1 ξ : ℝ))))).aestronglyMeasurable)
    filter_upwards [] with p
    simp [Complex.norm_exp]
  calc
    fourierKPZ (heatSmooth δ f) ξ = ∫ x, ∫ y, K (x, y) := by
      unfold fourierKPZ heatSmooth
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← integral_complex_ofReal, ← integral_const_mul]
    _ = ∫ y, ∫ x, K (x, y) := integral_integral_swap hK
    _ = ∫ y, (Real.exp (-(δ / 2) * ‖ξ‖ ^ 2) : ℂ) *
        (Complex.exp (-(Complex.I * (inner ℝ y ξ : ℝ))) * (f y : ℂ)) := by
      apply integral_congr_ae
      filter_upwards [] with y
      have he (z : Plane) : K (z + y, y) =
          (Complex.exp (-(Complex.I * (inner ℝ z ξ : ℝ))) * (heatKernel δ z : ℂ)) *
            (Complex.exp (-(Complex.I * (inner ℝ y ξ : ℝ))) * (f y : ℂ)) := by
        dsimp only [K]
        rw [add_sub_cancel_right, inner_add_left, Complex.ofReal_add, mul_add,
          neg_add, Complex.exp_add, Complex.ofReal_mul]
        ring
      rw [← integral_add_right_eq_self (fun x : Plane => K (x, y)) y]
      simp_rw [he]
      rw [integral_mul_const]
      rw [fourierKPZ_heatKernel hδ ξ]
    _ = (Real.exp (-(δ / 2) * ‖ξ‖ ^ 2) : ℂ) * fourierKPZ f ξ := by
      unfold fourierKPZ
      exact integral_const_mul _ _

/-- Fourier multiplier for the heat-mollification error. -/
theorem fourierKPZ_heatSmooth_sub {f : Plane → ℝ} (hf : Integrable f)
    {δ : ℝ} (hδ : 0 < δ) (ξ : Plane) :
    fourierKPZ (fun x => heatSmooth δ f x - f x) ξ =
      ((Real.exp (-(δ / 2) * ‖ξ‖ ^ 2) : ℂ) - 1) * fourierKPZ f ξ := by
  have hheat := integrable_heatSmooth hf hδ
  have hA : Integrable (fun x => Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) *
      (heatSmooth δ f x : ℂ)) :=
    (hheat.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop)
      (by filter_upwards [] with x; simp [Complex.norm_exp])
  have hB : Integrable (fun x => Complex.exp (-(Complex.I * (inner ℝ x ξ : ℝ))) *
      (f x : ℂ)) :=
    (hf.ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (by fun_prop)
      (by filter_upwards [] with x; simp [Complex.norm_exp])
  have heq : fourierKPZ (fun x => heatSmooth δ f x - f x) ξ =
      fourierKPZ (heatSmooth δ f) ξ - fourierKPZ f ξ := by
    unfold fourierKPZ
    simp_rw [Complex.ofReal_sub, mul_sub]
    exact integral_sub hA hB
  rw [heq, fourierKPZ_heatSmooth hf hδ ξ]
  ring

/-- Heat smoothing of a test function is Borel measurable. -/
theorem measurable_heatSmooth_testFn (f : TestFn) (δ : ℝ) :
    Measurable (heatSmooth δ f) := by
  have hm : Measurable (fun p : Plane × Plane =>
      heatKernel δ (p.1 - p.2) * f p.2) := by
    exact ((measurable_heatKernel δ).comp (measurable_fst.sub measurable_snd)).mul
      (f.continuous.measurable.comp measurable_snd)
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- Heat smoothing preserves total mass. -/
theorem integral_heatSmooth_eq (f : TestFn) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : Plane, heatSmooth δ f x) = ∫ x : Plane, f x := by
  have hf : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hp := integrable_heatSmooth_prod hf hδ
  calc
    (∫ x : Plane, heatSmooth δ f x) =
        ∫ x : Plane, ∫ y : Plane, heatKernel δ (x - y) * f y := rfl
    _ = ∫ y : Plane, ∫ x : Plane, heatKernel δ (x - y) * f y :=
      integral_integral_swap hp
    _ = ∫ y : Plane, f y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_mul_const, integral_heatKernel_sub hδ y, one_mul]

/-- Convolution with the positive unit-mass heat kernel preserves an `L∞`
bound. -/
theorem abs_heatSmooth_le (f : TestFn) {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ x, |f x| ≤ C) (x : Plane) :
    |heatSmooth δ f x| ≤ C := by
  have hf : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hi := integrable_heatSmooth_integrand hf hδ x
  have hker : Integrable (fun y : Plane => heatKernel δ (x - y)) := by
    apply ((integrable_heatKernel hδ).comp_sub_right x).congr
    filter_upwards [] with y
    rw [show x - y = -(y - x) by abel, DeltaBose.heatKernel_neg]
  calc
    |heatSmooth δ f x| ≤
        ∫ y : Plane, |heatKernel δ (x - y) * f y| := by
      exact abs_integral_le_integral_abs
    _ = ∫ y : Plane, heatKernel δ (x - y) * |f y| := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hδ.le _)]
    _ ≤ ∫ y : Plane, heatKernel δ (x - y) * C := by
      have hia : Integrable (fun y => heatKernel δ (x - y) * |f y|) := by
        apply hi.abs.congr
        filter_upwards [] with y
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hδ.le _)]
      apply integral_mono hia
      · exact hker.mul_const C
      · intro y
        exact mul_le_mul_of_nonneg_left (hC y) (heatKernel_nonneg hδ.le _)
    _ = C := by
      rw [integral_mul_const]
      have hmass : (∫ y : Plane, heatKernel δ (x - y)) = 1 := by
        calc
          _ = ∫ y : Plane, heatKernel δ (y - x) := by
            apply integral_congr_ae
            filter_upwards [] with y
            rw [show x - y = -(y - x) by abel, DeltaBose.heatKernel_neg]
          _ = 1 := integral_heatKernel_sub hδ x
      rw [hmass, one_mul]

/-- The heat-mollification error is measurable. -/
theorem measurable_heatSmooth_sub_testFn (f : TestFn) (δ : ℝ) :
    Measurable (fun x => heatSmooth δ f x - f x) :=
  (measurable_heatSmooth_testFn f δ).sub f.continuous.measurable

/-- The heat-mollification error is integrable. -/
theorem integrable_heatSmooth_sub_testFn (f : TestFn) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => heatSmooth δ f x - f x) := by
  have hf : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  exact (integrable_heatSmooth hf hδ).sub hf

/-- A heat-mollification error has zero total mass. -/
theorem integral_heatSmooth_sub_eq_zero (f : TestFn) {δ : ℝ} (hδ : 0 < δ) :
    (∫ x : Plane, (heatSmooth δ f x - f x)) = 0 := by
  have hf : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  rw [integral_sub (integrable_heatSmooth hf hδ) hf, integral_heatSmooth_eq f hδ,
    sub_self]

/-- If `f` is bounded by `C`, its heat-mollification error is bounded by
`2*C`. -/
theorem abs_heatSmooth_sub_le (f : TestFn) {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ x, |f x| ≤ C) (x : Plane) :
    |heatSmooth δ f x - f x| ≤ 2 * C := by
  calc
    |heatSmooth δ f x - f x| ≤ |heatSmooth δ f x| + |f x| := abs_sub _ _
    _ ≤ C + C := add_le_add (abs_heatSmooth_le f hδ hC x) (hC x)
    _ = 2 * C := by ring

/-- The four elementary regularity facts used for the mollification error:
measurability, `L¹`, zero mass, and the uniform `2*C` bound. -/
theorem heatSmooth_sub_regular (f : TestFn) {δ C : ℝ} (hδ : 0 < δ)
    (hC : ∀ x, |f x| ≤ C) :
    Measurable (fun x => heatSmooth δ f x - f x) ∧
    Integrable (fun x => heatSmooth δ f x - f x) ∧
    (∫ x : Plane, (heatSmooth δ f x - f x)) = 0 ∧
    ∀ x, |heatSmooth δ f x - f x| ≤ 2 * C := by
  exact ⟨measurable_heatSmooth_sub_testFn f δ,
    integrable_heatSmooth_sub_testFn f hδ,
    integral_heatSmooth_sub_eq_zero f hδ,
    abs_heatSmooth_sub_le f hδ hC⟩

/-- Fourier energy identity assuming exactly the quotient integrability needed
for the time--frequency interchange. -/
theorem integral_inner_heatSemigroup_eq_fourier_of_quotient
    {f g : Plane → ℝ} (hf : Integrable f) (hg : Integrable g)
    (hq : Integrable (fun ξ : Plane =>
      (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re / ‖ξ‖ ^ 2)) :
    IntegrableOn (fun s : ℝ => ∫ x : Plane,
      f x * heatSmooth (2 * s) g x) (Set.Ioi 0) ∧
    (∫ s in Set.Ioi (0 : ℝ), ∫ x : Plane,
      f x * heatSmooth (2 * s) g x) =
      (2 * Real.pi)⁻¹ ^ 2 * ∫ ξ : Plane,
        (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re / ‖ξ‖ ^ 2 := by
  have hF : Continuous (fun ξ => fourierKPZ f ξ) := by
    simp_rw [fourierKPZ_eq_angularFourierIntegral_fun]
    exact continuous_angularFourierIntegral hf
  have hG : Continuous (fun ξ => fourierKPZ g ξ) := by
    simp_rw [fourierKPZ_eq_angularFourierIntegral_fun]
    exact continuous_angularFourierIntegral hg
  obtain ⟨hj, heq⟩ := integrable_fourier_time_kernel
    (fun ξ => (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re)
    (Complex.continuous_re.comp
      (hF.mul (Complex.continuous_conj.comp hG))).measurable hq
  constructor
  · apply (hj.swap.integral_prod_left.const_mul
      ((2 * Real.pi)⁻¹ ^ 2)).congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact (inner_heatSemigroup_eq_fourier hf hg hs).symm
  · calc
      _ = ∫ s in Set.Ioi (0 : ℝ), (2 * Real.pi)⁻¹ ^ 2 *
          ∫ ξ : Plane,
            (fourierKPZ f ξ * conj (fourierKPZ g ξ)).re *
              Real.exp (-s * ‖ξ‖ ^ 2) :=
        setIntegral_congr_fun measurableSet_Ioi fun s hs =>
          inner_heatSemigroup_eq_fourier hf hg hs
      _ = _ := by rw [MeasureTheory.integral_const_mul, heq]


/-- The heat-mollification error has the inverse-Laplacian Fourier energy. -/
theorem integral_heatSmooth_sub_energy_eq_fourier
    (f : TestFn) (hfzero : (∫ x : Plane, f x) = 0) {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun s : ℝ => ∫ x : Plane, (heatSmooth δ f x - f x) *
      heatSmooth (2 * s) (fun y => heatSmooth δ f y - f y) x) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), ∫ x : Plane, (heatSmooth δ f x - f x) *
      heatSmooth (2 * s) (fun y => heatSmooth δ f y - f y) x) =
      (2 * Real.pi)⁻¹ ^ 2 * ∫ ξ : Plane, ‖fourierKPZ f ξ‖ ^ 2 *
        (Real.exp (-(δ / 2) * ‖ξ‖ ^ 2) - 1) ^ 2 / ‖ξ‖ ^ 2 := by
  let e : Plane → ℝ := fun x => heatSmooth δ f x - f x
  let a : Plane → ℝ := fun ξ => Real.exp (-(δ / 2) * ‖ξ‖ ^ 2) - 1
  have hf : Integrable (f : Plane → ℝ) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have he : Integrable e := (integrable_heatSmooth hf hδ).sub hf
  have hF : Continuous (fourierKPZ e) := by
    have heq : fourierKPZ e = angularFourierIntegral e :=
      funext (fourierKPZ_eq_angularFourierIntegral_fun e)
    rw [heq]
    exact continuous_angularFourierIntegral he
  have hself (g : Plane → ℝ) (ξ : Plane) :
      (fourierKPZ g ξ * conj (fourierKPZ g ξ)).re = ‖fourierKPZ g ξ‖ ^ 2 := by
    rw [Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hbase : Integrable (fun ξ : Plane => ‖fourierKPZ f ξ‖ ^ 2 / ‖ξ‖ ^ 2) := by
    simpa only [hself] using integrable_fourierKPZ_pairing_div_norm_sq hf hf
      (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)
      (f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport)
      hfzero hfzero (integrable_firstMoment_testFn f) (integrable_firstMoment_testFn f)
  have hnorm (ξ : Plane) : ‖fourierKPZ e ξ‖ ^ 2 = a ξ ^ 2 * ‖fourierKPZ f ξ‖ ^ 2 := by
    have hm := fourierKPZ_heatSmooth_sub hf hδ ξ
    change fourierKPZ e ξ = _ at hm
    rw [hm, show ((Real.exp (-(δ / 2) * ‖ξ‖ ^ 2) : ℂ) - 1) = (a ξ : ℂ) by
      simp only [a, Complex.ofReal_sub, Complex.ofReal_one], norm_mul,
      Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
  have ha (ξ : Plane) : a ξ ^ 2 ≤ 4 := by
    have hp := (Real.exp_pos (-(δ / 2) * ‖ξ‖ ^ 2)).le
    have hu : Real.exp (-(δ / 2) * ‖ξ‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (div_nonneg hδ.le zero_le_two)) (sq_nonneg _))
    have habs : |a ξ| ≤ 2 := abs_le.mpr ⟨by dsimp only [a]; linarith only [hp],
      by dsimp only [a]; linarith only [hu]⟩
    simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using
      (sq_le_sq₀ (abs_nonneg (a ξ)) zero_le_two).mpr habs
  have hq : Integrable (fun ξ : Plane =>
      (fourierKPZ e ξ * conj (fourierKPZ e ξ)).re / ‖ξ‖ ^ 2) := by
    apply (hbase.const_mul 4).mono'
    · have hn : Measurable (fun ξ : Plane => ‖fourierKPZ e ξ‖ ^ 2) :=
        hF.measurable.norm.pow_const 2
      have hd : Measurable (fun ξ : Plane => ‖ξ‖ ^ 2) := measurable_norm.pow_const 2
      have hh : AEStronglyMeasurable (fun ξ : Plane =>
          ‖fourierKPZ e ξ‖ ^ 2 / ‖ξ‖ ^ 2) volume := (hn.div hd).aestronglyMeasurable
      simpa only [hself] using hh
    · filter_upwards [] with ξ
      rw [hself, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _)), hnorm]
      calc
        a ξ ^ 2 * ‖fourierKPZ f ξ‖ ^ 2 / ‖ξ‖ ^ 2 ≤
            4 * ‖fourierKPZ f ξ‖ ^ 2 / ‖ξ‖ ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (ha ξ) (sq_nonneg _)) (sq_nonneg _)
        _ = 4 * (‖fourierKPZ f ξ‖ ^ 2 / ‖ξ‖ ^ 2) := by ring
  have hid := integral_inner_heatSemigroup_eq_fourier_of_quotient he he hq
  refine ⟨hid.1, ?_⟩
  change (∫ s in Ioi (0 : ℝ), ∫ x : Plane, e x * heatSmooth (2 * s) e x) = _
  rw [hid.2]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ξ
  rw [hself, hnorm]
  dsimp only [a]
  ring

/-- The inverse-Laplacian energy of the heat-mollification error vanishes. -/
theorem tendsto_integral_heatSmooth_sub_energy
    (f : TestFn) (hfzero : (∫ x : Plane, f x) = 0) :
    Tendsto (fun δ : ℝ => ∫ s in Set.Ioi (0 : ℝ), ∫ x : Plane,
      (heatSmooth δ f x - f x) *
        heatSmooth (2 * s) (fun y => heatSmooth δ f y - f y) x)
      (𝓝[>] 0) (𝓝 0) := by
  have hhalf : Tendsto (fun δ : ℝ => δ / 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [id_eq, zero_div] using
        ((tendsto_id : Tendsto (fun δ : ℝ => δ) (𝓝 (0 : ℝ)) (𝓝 0)).mono_left
          nhdsWithin_le_nhds).div_const 2
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      exact div_pos hδ (by norm_num)
  have hfourier := (tendsto_fourier_heatMultiplier_error f hfzero).comp hhalf
  have hscaled := hfourier.const_mul ((2 * Real.pi)⁻¹ ^ 2)
  simp only [mul_zero, Function.comp_def] at hscaled
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact (integral_heatSmooth_sub_energy_eq_fourier f hfzero hδ).2.symm


end Critical2DKPZ.Extensions.GffTangent
