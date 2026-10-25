/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Symmetries.DenseTransportHelpers
public import Critical2DKPZ.SHF.DeltaBose.KernelScaling
public import Critical2DKPZ.Smoothing.SpatialRescaling
public import Critical2DKPZ.SHF.Tsai.MollifierOperators
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Parabolic scaling of the dense-time SHF axioms -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped Topology ENNReal CompactlySupported

namespace Critical2DKPZ.SHF.Symmetries

private def scalePlaneHomeomorph (a : ℝ) (ha : 0 < a) : Plane ≃ₜ Plane :=
  Homeomorph.smulOfNeZero (Real.sqrt a) (Real.sqrt_pos.mpr ha).ne'

private def scalePairHomeomorph (a : ℝ) (ha : 0 < a) :
    (Plane × Plane) ≃ₜ (Plane × Plane) :=
  (scalePlaneHomeomorph a ha).symm.prodCongr (scalePlaneHomeomorph a ha).symm

private def scalePairMeas (a : ℝ) (ha : 0 < a) :
    (Plane × Plane) ≃ᵐ (Plane × Plane) :=
  (scalePairHomeomorph a ha).toMeasurableEquiv

private def scaleQuadMeas (a : ℝ) (ha : 0 < a) :
    ((Plane × Plane) × (Plane × Plane)) ≃ᵐ ((Plane × Plane) × (Plane × Plane)) :=
  (scalePairMeas a ha).prodCongr (scalePairMeas a ha)

private def scaleMollifier (a : ℝ) (w : ℕ → Plane → ℝ) : ℕ → Plane → ℝ :=
  fun ℓ x => a * w ℓ (Real.sqrt a • x)

private def scalePairTest {a : ℝ} (ha : 0 < a) (f : C_c(Plane × Plane, ℝ)) :
    C_c(Plane × Plane, ℝ) := f.comp (scalePairHomeomorph a ha).toCocompactMap

private def scalePairMeasure {a : ℝ} (ha : 0 < a)
    (μ : Measure (Plane × Plane)) : Measure (Plane × Plane) :=
  (ENNReal.ofReal a)⁻¹ • μ.map (scalePairMeas a ha)

private theorem scalePairTest_apply {a : ℝ} (ha : 0 < a)
    (f : C_c(Plane × Plane, ℝ)) (p : Plane × Plane) :
    scalePairTest ha f p = f ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2) := by
  change f (scalePairHomeomorph a ha p) = _
  rfl

private theorem scalePairMeas_apply {a : ℝ} (ha : 0 < a) (p : Plane × Plane) :
    scalePairMeas a ha p =
      ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2) := by
  rfl

private theorem measure_prod_smul_right {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (c : ℝ≥0∞) :
    μ.prod (c • ν) = c • (μ.prod ν) := by
  rw [← Measure.prod_swap, Measure.prod_smul_left]
  rw [Measure.map_smul c measurable_swap.aemeasurable, Measure.prod_swap]

private theorem measure_prod_two_smul {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] (c : ℝ≥0∞) :
    (c • μ).prod (c • ν) = (c * c) • (μ.prod ν) := by
  rw [Measure.prod_smul_left, measure_prod_smul_right, smul_smul]

private theorem scalePairMeasure_prod {a : ℝ} (ha : 0 < a)
    (μ ν : Measure (Plane × Plane)) [SFinite μ] [SFinite ν] :
    (scalePairMeasure ha μ).prod (scalePairMeasure ha ν) =
      ((ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a)⁻¹) •
        Measure.map (scaleQuadMeas a ha) (μ.prod ν) := by
  rw [scalePairMeasure, scalePairMeasure, measure_prod_two_smul,
    Measure.map_prod_map _ _ (scalePairMeas a ha).measurable
      (scalePairMeas a ha).measurable]
  rfl

private theorem measurable_scalePairMeasure {Ω : Type*} [MeasurableSpace Ω] {a : ℝ}
    (ha : 0 < a) (F : Ω → Measure (Plane × Plane)) (hF : Measurable F) :
    Measurable (fun ω => scalePairMeasure ha (F ω)) := by
  have hmap : Measurable (fun ω => (F ω).map (scalePairMeas a ha)) := by
    simpa only [scalePairMeas, Homeomorph.toMeasurableEquiv_coe] using
      measurable_map_homeomorph (scalePairHomeomorph a ha) F hF
  have hsmul : Measurable (fun μ : Measure (Plane × Plane) =>
      (ENNReal.ofReal a)⁻¹ • μ) := by
    apply Measure.measurable_of_measurable_coe
    intro s hs
    change Measurable (fun μ : Measure (Plane × Plane) => (ENNReal.ofReal a)⁻¹ * μ s)
    exact measurable_const.mul (Measure.measurable_coe hs)
  exact hsmul.comp hmap

private theorem ae_locallyFinite_scalePairMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {a : ℝ} (ha : 0 < a)
    (F : Ω → Measure (Plane × Plane))
    (hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (F ω)) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (scalePairMeasure ha (F ω)) := by
  have hmap := ae_locallyFinite_map_homeomorph (scalePairHomeomorph a ha) P F hLF
  filter_upwards [hmap] with ω hω
  have hnn : NNReal.mk a ha.le ≠ 0 := by
    intro hz
    have hz' := congrArg (fun r : NNReal => (r : ℝ)) hz
    simp only [NNReal.coe_mk, NNReal.coe_zero] at hz'
    exact ha.ne' hz'
  let c : NNReal := (NNReal.mk a ha.le)⁻¹
  have hc : (ENNReal.ofReal a)⁻¹ = (c : ℝ≥0∞) := by
    change (ENNReal.ofReal a)⁻¹ = ↑((NNReal.mk a ha.le)⁻¹)
    rw [ENNReal.ofReal_eq_coe_nnreal ha.le, ENNReal.coe_inv hnn]
  have hmapLocal : IsLocallyFiniteMeasure ((F ω).map (scalePairMeas a ha)) := by
    simpa only [scalePairMeas, Homeomorph.toMeasurableEquiv_coe] using hω
  have hsmul : IsLocallyFiniteMeasure
      (c • (F ω).map (scalePairMeas a ha)) := by
    exact @MeasureTheory.isLocallyFiniteMeasureSMulNNReal (Plane × Plane) _ _
      ((F ω).map (scalePairMeas a ha)) hmapLocal c
  simpa only [scalePairMeasure, hc, ENNReal.smul_def,
    scalePairMeas, Homeomorph.toMeasurableEquiv_coe] using hsmul

private theorem locallyFinite_scalePairMeasure {a : ℝ} (ha : 0 < a)
    (μ : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (scalePairMeasure ha μ) := by
  have hmap : IsLocallyFiniteMeasure (μ.map (scalePairMeas a ha)) := by
    simpa only [scalePairMeas, Homeomorph.toMeasurableEquiv_coe] using
      locallyFinite_map_homeomorph (scalePairHomeomorph a ha) μ
  have hnn : NNReal.mk a ha.le ≠ 0 := by
    intro hz
    have hz' := congrArg (fun r : NNReal => (r : ℝ)) hz
    simp only [NNReal.coe_mk, NNReal.coe_zero] at hz'
    exact ha.ne' hz'
  let c : NNReal := (NNReal.mk a ha.le)⁻¹
  have hc : (ENNReal.ofReal a)⁻¹ = (c : ℝ≥0∞) := by
    change (ENNReal.ofReal a)⁻¹ = ↑((NNReal.mk a ha.le)⁻¹)
    rw [ENNReal.ofReal_eq_coe_nnreal ha.le, ENNReal.coe_inv hnn]
  have hsmul : IsLocallyFiniteMeasure (c • μ.map (scalePairMeas a ha)) := by
    exact @MeasureTheory.isLocallyFiniteMeasureSMulNNReal (Plane × Plane) _ _
      (μ.map (scalePairMeas a ha)) hmap c
  simpa only [scalePairMeasure, hc, ENNReal.smul_def] using hsmul

private theorem pairClause_scale {D : Set ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)} {a : ℝ} (ha : 0 < a)
    (hpair : ∀ s ∈ D, ∀ t ∈ D, s < t →
      Measurable (Z s t) ∧ ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (Z s t ω)) :
    ∀ s ∈ {s | a * s ∈ D}, ∀ t ∈ {t | a * t ∈ D}, s < t →
      Measurable (fun ω => scalePairMeasure ha (Z (a * s) (a * t) ω)) ∧
        ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (scalePairMeasure ha (Z (a * s) (a * t) ω)) := by
  intro s hs t ht hst
  change a * s ∈ D at hs
  change a * t ∈ D at ht
  have hst' : a * s < a * t := (mul_lt_mul_of_pos_left hst ha)
  exact ⟨measurable_scalePairMeasure ha _ (hpair (a * s) hs (a * t) ht hst').1,
    ae_locallyFinite_scalePairMeasure P ha _ (hpair (a * s) hs (a * t) ht hst').2⟩

private theorem independenceClause_scale {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)} {a : ℝ} (ha : 0 < a)
    (hindep : ∀ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t → (∀ i, t i ∈ D) →
      iIndepFun (fun i : Fin k => Z (t i.castSucc) (t i.succ)) P) :
    ∀ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t →
      (∀ i, t i ∈ {s | a * s ∈ D}) →
        iIndepFun (fun i : Fin k => fun ω =>
          scalePairMeasure ha (Z (a * t i.castSucc) (a * t i.succ) ω)) P := by
  intro k t htstrict ht
  have hscaleStrict : StrictMono (fun i => a * t i) := by
    intro i j hij
    exact mul_lt_mul_of_pos_left (htstrict hij) ha
  have hscaleMem : ∀ i, a * t i ∈ D := fun i => ht i
  have hsource := hindep k (fun i => a * t i) hscaleStrict hscaleMem
  have hscaleMeas : Measurable (fun μ : Measure (Plane × Plane) => scalePairMeasure ha μ) :=
    measurable_scalePairMeasure ha _ measurable_id
  have h := hsource.comp (fun _ μ => scalePairMeasure ha μ) (fun _ => hscaleMeas)
  simpa only [Function.comp_def] using h

private theorem scaleSmoothedProductIntegrand_comp {a : ℝ} (ha : 0 < a)
    (w : Plane → ℝ) (ℓ : ℕ) (f : C_c(Plane × Plane, ℝ)) :
    (fun q : (Plane × Plane) × (Plane × Plane) =>
      f (q.1.1, q.2.2) * scaleMollifier a (fun _ => w) ℓ (q.1.2 - q.2.1)) ∘
        scaleQuadMeas a ha =
      fun q => a * (scalePairTest ha f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)) := by
  funext q
  have hsqrt : Real.sqrt a * (Real.sqrt a)⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.sqrt_pos.mpr ha).ne'
  change f ((scalePairMeas a ha q.1).1, (scalePairMeas a ha q.2).2) *
    scaleMollifier a (fun _ => w) ℓ ((scalePairMeas a ha q.1).2 -
      (scalePairMeas a ha q.2).1) = _
  rw [scalePairMeas_apply ha q.1, scalePairMeas_apply ha q.2, scaleMollifier, smul_sub]
  have hleft : Real.sqrt a • ((Real.sqrt a)⁻¹ • q.1.2) = q.1.2 := by
    rw [smul_smul, hsqrt, one_smul]
  have hright : Real.sqrt a • ((Real.sqrt a)⁻¹ • q.2.1) = q.2.1 := by
    rw [smul_smul, hsqrt, one_smul]
  rw [hleft, hright, scalePairTest_apply]
  ring

private theorem smoothedProductWellDefined_scale {a : ℝ} (ha : 0 < a)
    (μ ν : Measure (Plane × Plane)) [SFinite μ] [SFinite ν]
    (w : Plane → ℝ) (ℓ : ℕ)
    (hdef : SmoothedProductWellDefined μ w ν) :
    SmoothedProductWellDefined (scalePairMeasure ha μ) (scaleMollifier a (fun _ => w) ℓ)
      (scalePairMeasure ha ν) := by
  intro f
  let e := scaleQuadMeas a ha
  let F : (Plane × Plane) × (Plane × Plane) → ℝ := fun q =>
    f (q.1.1, q.2.2) * scaleMollifier a (fun _ => w) ℓ (q.1.2 - q.2.1)
  have hcomp := scaleSmoothedProductIntegrand_comp ha w ℓ f
  have hsource : Integrable
      (fun q : (Plane × Plane) × (Plane × Plane) =>
        scalePairTest ha f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)) (μ.prod ν) := hdef _
  have hcompInt : Integrable (F ∘ e) (μ.prod ν) := by
    rw [hcomp]
    exact hsource.const_mul a
  have hmapInt : Integrable F (Measure.map e (μ.prod ν)) :=
    (integrable_map_equiv e F).2 hcompInt
  have hc : (ENNReal.ofReal a)⁻¹ ≠ ⊤ := by
    rw [← ENNReal.ofReal_inv_of_pos ha]
    exact ENNReal.ofReal_ne_top
  have hcc : (ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top hc hc
  have hscaled : Integrable F
      (((ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a)⁻¹) • Measure.map e (μ.prod ν)) :=
    hmapInt.smul_measure hcc
  rw [← scalePairMeasure_prod ha μ ν] at hscaled
  exact hscaled

private theorem smoothedProductPairing_scale {a : ℝ} (ha : 0 < a)
    (μ ν : Measure (Plane × Plane)) [SFinite μ] [SFinite ν]
    (w : Plane → ℝ) (ℓ : ℕ) (f : C_c(Plane × Plane, ℝ))
    (hdef : SmoothedProductWellDefined μ w ν) :
    smoothedProductPairing (scalePairMeasure ha μ) (scaleMollifier a (fun _ => w) ℓ)
      (scalePairMeasure ha ν) f =
        a⁻¹ * smoothedProductPairing μ w ν (scalePairTest ha f) := by
  let e := scaleQuadMeas a ha
  let F : (Plane × Plane) × (Plane × Plane) → ℝ := fun q =>
    f (q.1.1, q.2.2) * scaleMollifier a (fun _ => w) ℓ (q.1.2 - q.2.1)
  have hcomp := scaleSmoothedProductIntegrand_comp ha w ℓ f
  have hsource : Integrable
      (fun q : (Plane × Plane) × (Plane × Plane) =>
        scalePairTest ha f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)) (μ.prod ν) := hdef _
  have hcReal : ((ENNReal.ofReal a)⁻¹).toReal = a⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos ha]
    exact ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)
  have hccReal : ((ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a)⁻¹).toReal * a = a⁻¹ := by
    rw [ENNReal.toReal_mul, hcReal]
    field_simp [ha.ne']
  unfold smoothedProductPairing
  change ∫ q, F q ∂((scalePairMeasure ha μ).prod (scalePairMeasure ha ν)) =
    a⁻¹ * ∫ q : (Plane × Plane) × (Plane × Plane),
      scalePairTest ha f (q.1.1, q.2.2) * w (q.1.2 - q.2.1) ∂(μ.prod ν)
  calc
    ∫ q, F q ∂((scalePairMeasure ha μ).prod (scalePairMeasure ha ν)) =
        ((ENNReal.ofReal a)⁻¹ * (ENNReal.ofReal a)⁻¹).toReal *
          (a * ∫ q : (Plane × Plane) × (Plane × Plane),
            scalePairTest ha f (q.1.1, q.2.2) * w (q.1.2 - q.2.1) ∂(μ.prod ν)) := by
      rw [scalePairMeasure_prod ha μ ν, integral_smul_measure, integral_map_equiv e F]
      rw [smul_eq_mul]
      congr 1
      calc
        ∫ q, F (e q) ∂(μ.prod ν) = ∫ q, (F ∘ e) q ∂(μ.prod ν) := rfl
        _ = a * ∫ q, scalePairTest ha f (q.1.1, q.2.2) * w (q.1.2 - q.2.1)
            ∂(μ.prod ν) := by rw [hcomp, integral_const_mul]
    _ = a⁻¹ * ∫ q : (Plane × Plane) × (Plane × Plane),
          scalePairTest ha f (q.1.1, q.2.2) * w (q.1.2 - q.2.1) ∂(μ.prod ν) := by
      rw [← mul_assoc, hccReal]

private theorem integral_scalePairMeasure {a : ℝ} (ha : 0 < a)
    (μ : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ]
    (hμ : IsLocallyFiniteMeasure (scalePairMeasure ha μ))
    (f : C_c(Plane × Plane, ℝ)) :
    Integrable f (scalePairMeasure ha μ) ∧
      ∫ p, f p ∂(scalePairMeasure ha μ) = a⁻¹ * ∫ p, scalePairTest ha f p ∂μ := by
  let μ' : RandomMeasure.PositiveRadonMeasure (Plane × Plane) :=
    ⟨scalePairMeasure ha μ, hμ⟩
  have hI : Integrable f (scalePairMeasure ha μ) := RandomMeasure.integrable_vagueTest μ' f
  have hcReal : ((ENNReal.ofReal a)⁻¹).toReal = a⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos ha]
    exact ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)
  refine ⟨hI, ?_⟩
  calc
    ∫ p, f p ∂(scalePairMeasure ha μ) =
        ((ENNReal.ofReal a)⁻¹).toReal * ∫ p, f p ∂(μ.map (scalePairMeas a ha)) := by
      rw [scalePairMeasure, integral_smul_measure, smul_eq_mul]
    _ = a⁻¹ * ∫ p, f (scalePairMeas a ha p) ∂μ := by
      rw [hcReal, integral_map_equiv]
    _ = a⁻¹ * ∫ p, scalePairTest ha f p ∂μ := by
      congr 1

private theorem integrable_integral_scalePairMeasure {a : ℝ} (ha : 0 < a)
    (μ : Measure (Plane × Plane)) (f : Plane × Plane → ℝ)
    (hsource : Integrable (fun p => f (scalePairMeas a ha p)) μ) :
    Integrable f (scalePairMeasure ha μ) ∧
      ∫ p, f p ∂(scalePairMeasure ha μ) =
        a⁻¹ * ∫ p, f (scalePairMeas a ha p) ∂μ := by
  have hmapInt : Integrable f (μ.map (scalePairMeas a ha)) :=
    (integrable_map_equiv (scalePairMeas a ha) f).2 hsource
  have hc0 : (ENNReal.ofReal a)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hcTop : (ENNReal.ofReal a)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr ha))
  have hcReal : ((ENNReal.ofReal a)⁻¹).toReal = a⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos ha]
    exact ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)
  have hInt : Integrable f (scalePairMeasure ha μ) := by
    exact (integrable_smul_measure hc0 hcTop).2 hmapInt
  refine ⟨hInt, ?_⟩
  calc
    ∫ p, f p ∂(scalePairMeasure ha μ) =
        ((ENNReal.ofReal a)⁻¹).toReal * ∫ p, f p ∂(μ.map (scalePairMeas a ha)) := by
      rw [scalePairMeasure, integral_smul_measure, smul_eq_mul]
    _ = a⁻¹ * ∫ p, f (scalePairMeas a ha p) ∂μ := by
      rw [hcReal, integral_map_equiv]

private theorem tendstoInMeasure_const_mul_pos {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {f : ℕ → Ω → ℝ} {c : ℝ} (hc : 0 < c)
    (hlim : TendstoInMeasure P f atTop (fun _ => 0)) :
    TendstoInMeasure P (fun n ω => c * f n ω) atTop (fun _ => 0) := by
  rw [tendstoInMeasure_iff_dist] at hlim ⊢
  intro ε hε
  have hδ : 0 < ε / c := div_pos hε hc
  have hsubset (n : ℕ) :
      {ω | ε ≤ dist (c * f n ω) (0 : ℝ)} ⊆ {ω | ε / c ≤ dist (f n ω) (0 : ℝ)} := by
    intro ω hω
    simp only [dist_eq_norm, sub_zero, norm_mul, Real.norm_eq_abs, abs_of_pos hc] at hω ⊢
    change ε ≤ c * |f n ω| at hω
    exact (div_le_iff₀ hc).2 (by simpa only [mul_comm] using hω)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hlim (ε / c) hδ)
    (fun _ => zero_le) (fun n => measure_mono (hsubset n))

private theorem map_sqrt_smul_volume {a : ℝ} (ha : 0 < a) :
    Measure.map (fun x : Plane => Real.sqrt a • x) volume = ENNReal.ofReal a⁻¹ • volume := by
  have hr : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  rw [Measure.map_addHaar_smul volume hr]
  have hd : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  rw [hd, Real.sq_sqrt ha.le, abs_of_pos (inv_pos.mpr ha)]

private theorem map_invSqrt_smul_volume {a : ℝ} (ha : 0 < a) :
    Measure.map (fun x : Plane => (Real.sqrt a)⁻¹ • x) volume = ENNReal.ofReal a • volume := by
  have hr : (Real.sqrt a)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr ha).ne'
  rw [Measure.map_addHaar_smul volume hr]
  have hd : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  rw [hd, abs_of_pos (by positivity : 0 < (((Real.sqrt a)⁻¹ ^ 2)⁻¹)), inv_pow,
    inv_inv, Real.sq_sqrt ha.le]

private theorem map_sqrt_smul_configuration_volume {n : ℕ} {a : ℝ} (ha : 0 < a) :
    Measure.map (fun x : Critical2DKPZ.DeltaBose.Configuration n => Real.sqrt a • x) volume =
      ENNReal.ofReal ((a ^ n)⁻¹) • volume := by
  have hr : Real.sqrt a ≠ 0 := (Real.sqrt_pos.mpr ha).ne'
  rw [Measure.map_addHaar_smul volume hr]
  have hd : Module.finrank ℝ (Critical2DKPZ.DeltaBose.Configuration n) = 2 * n := by
    simp [Critical2DKPZ.DeltaBose.Configuration, Module.finrank_pi_fintype]
    omega
  rw [hd, abs_of_pos (inv_pos.mpr (pow_pos (Real.sqrt_pos.mpr ha) _))]
  have hp : Real.sqrt a ^ (2 * n) = a ^ n := by
    rw [pow_mul, Real.sq_sqrt ha.le]
  rw [hp]

private theorem integral_comp_sqrt_configuration {n : ℕ} {a : ℝ} (ha : 0 < a)
    (F : Critical2DKPZ.DeltaBose.Configuration n → ℝ) :
    ∫ x, F x ∂(volume : Measure (Critical2DKPZ.DeltaBose.Configuration n)) =
      a ^ n * ∫ x, F (Real.sqrt a • x) := by
  let e : Critical2DKPZ.DeltaBose.Configuration n ≃ᵐ _ :=
    (Homeomorph.smulOfNeZero (Real.sqrt a) (Real.sqrt_pos.mpr ha).ne').toMeasurableEquiv
  have hcReal : (ENNReal.ofReal ((a ^ n)⁻¹)).toReal = (a ^ n)⁻¹ :=
    ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos ha n).le)
  have hcomp :
      ∫ x, F (Real.sqrt a • x) ∂(volume : Measure (Critical2DKPZ.DeltaBose.Configuration n)) =
        (a ^ n)⁻¹ * ∫ x, F x := by
    calc
      ∫ x, F (Real.sqrt a • x) ∂(volume : Measure (Critical2DKPZ.DeltaBose.Configuration n)) =
          ∫ x, F x ∂Measure.map e volume := (integral_map_equiv e F).symm
      _ = ∫ x, F x ∂(ENNReal.ofReal ((a ^ n)⁻¹) • volume) := by
        change ∫ x, F x ∂Measure.map (fun x => Real.sqrt a • x) volume = _
        rw [← map_sqrt_smul_configuration_volume ha]
      _ = (a ^ n)⁻¹ * ∫ x, F x := by
        rw [integral_smul_measure, smul_eq_mul, hcReal]
  calc
    ∫ x, F x ∂(volume : Measure (Critical2DKPZ.DeltaBose.Configuration n)) =
        a ^ n * ((a ^ n)⁻¹ * ∫ x, F x) := by
          field_simp [pow_ne_zero n ha.ne']
    _ = a ^ n * ∫ x, F (Real.sqrt a • x) := by rw [← hcomp]

private theorem momentKernel_integral_scale {n : ℕ} (θ : ℝ) {a h : ℝ} (ha : 0 < a)
    (g g' : Fin n → Plane → ℝ) :
    (∫ x : Critical2DKPZ.DeltaBose.Configuration n, ∫ y,
      (∏ i, g i ((Real.sqrt a)⁻¹ • x i)) *
        (Critical2DKPZ.DeltaBose.momentKernel n θ (a * h) x y).toReal *
          ∏ i, g' i ((Real.sqrt a)⁻¹ • y i)) =
      a ^ n * ∫ x : Critical2DKPZ.DeltaBose.Configuration n, ∫ y,
        (∏ i, g i (x i)) *
          (Critical2DKPZ.DeltaBose.momentKernel n (θ + Real.log a) h x y).toReal *
            ∏ i, g' i (y i) := by
  let G : Critical2DKPZ.DeltaBose.Configuration n →
      Critical2DKPZ.DeltaBose.Configuration n → ℝ := fun x y =>
    (∏ i, g i ((Real.sqrt a)⁻¹ • x i)) *
      (Critical2DKPZ.DeltaBose.momentKernel n θ (a * h) x y).toReal *
        ∏ i, g' i ((Real.sqrt a)⁻¹ • y i)
  let H : Critical2DKPZ.DeltaBose.Configuration n →
      Critical2DKPZ.DeltaBose.Configuration n → ℝ := fun x y =>
    (∏ i, g i (x i)) *
      (Critical2DKPZ.DeltaBose.momentKernel n (θ + Real.log a) h x y).toReal *
        ∏ i, g' i (y i)
  have hsqrt : Real.sqrt a * (Real.sqrt a)⁻¹ = 1 :=
    mul_inv_cancel₀ (Real.sqrt_pos.mpr ha).ne'
  have hkernel (x y : Critical2DKPZ.DeltaBose.Configuration n) :
      (Critical2DKPZ.DeltaBose.momentKernel n θ (a * h)
        (fun i => Real.sqrt a • x i) (fun i => Real.sqrt a • y i)).toReal =
        (a ^ n)⁻¹ *
          (Critical2DKPZ.DeltaBose.momentKernel n (θ + Real.log a) h x y).toReal := by
    rw [Critical2DKPZ.DeltaBose.momentKernel_scale n θ ha x y,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (pow_pos ha n).le)]
  have hG (x y : Critical2DKPZ.DeltaBose.Configuration n) :
      G (Real.sqrt a • x) (Real.sqrt a • y) = (a ^ n)⁻¹ * H x y := by
    have hleft : (∏ i, g i ((Real.sqrt a)⁻¹ • (Real.sqrt a • x i))) = ∏ i, g i (x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr ha).ne', one_smul]
    have hright : (∏ i, g' i ((Real.sqrt a)⁻¹ • (Real.sqrt a • y i))) = ∏ i, g' i (y i) := by
      apply Finset.prod_congr rfl
      intro i hi
      congr 1
      rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr ha).ne', one_smul]
    dsimp [G, H]
    rw [hleft, hright]
    change (∏ i, g i (x i)) *
      (Critical2DKPZ.DeltaBose.momentKernel n θ (a * h)
        (fun i => Real.sqrt a • x i) (fun i => Real.sqrt a • y i)).toReal *
        ∏ i, g' i (y i) = _
    rw [hkernel x y]
    ring
  have hdouble :
      (∫ x : Critical2DKPZ.DeltaBose.Configuration n, ∫ y, G (Real.sqrt a • x) (Real.sqrt a • y)) =
        (a ^ n)⁻¹ * ∫ x : Critical2DKPZ.DeltaBose.Configuration n, ∫ y, H x y := by
    calc
      ∫ x, ∫ y, G (Real.sqrt a • x) (Real.sqrt a • y) =
          ∫ x, ∫ y, (a ^ n)⁻¹ * H x y := by
            apply integral_congr_ae
            filter_upwards [] with x
            apply integral_congr_ae
            filter_upwards [] with y
            exact hG x y
      _ = (a ^ n)⁻¹ * ∫ x, ∫ y, H x y := by
            calc
              ∫ x, ∫ y, (a ^ n)⁻¹ * H x y =
                  ∫ x, (a ^ n)⁻¹ * ∫ y, H x y := by
                apply integral_congr_ae
                filter_upwards [] with x
                exact integral_const_mul (a ^ n)⁻¹ (fun y => H x y)
              _ = (a ^ n)⁻¹ * ∫ x, ∫ y, H x y :=
                integral_const_mul (a ^ n)⁻¹ (fun x => ∫ y, H x y)
  have hinner (x : Critical2DKPZ.DeltaBose.Configuration n) :
      ∫ y, G x y = a ^ n * ∫ y, G x (Real.sqrt a • y) :=
    integral_comp_sqrt_configuration ha (G x)
  calc
    ∫ x, ∫ y, G x y = ∫ x, a ^ n * ∫ y, G x (Real.sqrt a • y) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hinner x
    _ = a ^ n * ∫ x, ∫ y, G x (Real.sqrt a • y) := by rw [integral_const_mul]
    _ = a ^ n * (a ^ n * ∫ x, ∫ y, G (Real.sqrt a • x) (Real.sqrt a • y)) := by
      congr 1
      exact integral_comp_sqrt_configuration ha (fun x => ∫ y, G x (Real.sqrt a • y))
    _ = a ^ n * ∫ x, ∫ y, H x y := by
      rw [hdouble]
      field_simp [pow_ne_zero n ha.ne']

private def scaleL2Factor (c : ℝ≥0∞) : ℝ≥0∞ := c ^ ((2 : ℝ≥0∞)⁻¹).toReal

private theorem memLp_sqrt_comp {a : ℝ} (ha : 0 < a) {f : Plane → ℝ}
    (hf : MemLp f 2) : MemLp (fun x => f (Real.sqrt a • x)) 2 := by
  have hmap := map_sqrt_smul_volume ha
  have hmem : MemLp f 2 (Measure.map (fun x : Plane => Real.sqrt a • x) volume) := by
    rw [hmap]
    exact hf.smul_measure (by simp)
  exact (memLp_map_measure_iff hmem.aestronglyMeasurable
    (measurable_const_smul (Real.sqrt a)).aemeasurable).mp hmem

private theorem memLp_invSqrt_comp {a : ℝ} (ha : 0 < a) {f : Plane → ℝ}
    (hf : MemLp f 2) : MemLp (fun x => f ((Real.sqrt a)⁻¹ • x)) 2 := by
  have hmap := map_invSqrt_smul_volume ha
  have hmem : MemLp f 2 (Measure.map (fun x : Plane => (Real.sqrt a)⁻¹ • x) volume) := by
    rw [hmap]
    exact hf.smul_measure (by simp)
  exact (memLp_map_measure_iff hmem.aestronglyMeasurable
    (measurable_const_smul (Real.sqrt a)⁻¹).aemeasurable).mp hmem

private theorem eLpNorm_sqrt_comp {a : ℝ} (ha : 0 < a) {f : Plane → ℝ}
    (hf : MemLp f 2) :
    eLpNorm (fun x => f (Real.sqrt a • x)) 2 volume =
      scaleL2Factor (ENNReal.ofReal a⁻¹) * eLpNorm f 2 volume := by
  have hmap := map_sqrt_smul_volume ha
  have hmem : MemLp f 2 (Measure.map (fun x : Plane => Real.sqrt a • x) volume) := by
    rw [hmap]
    exact hf.smul_measure (by simp)
  change eLpNorm (f ∘ fun x : Plane => Real.sqrt a • x) 2 volume = _
  rw [← eLpNorm_map_measure hmem.aestronglyMeasurable
    (measurable_const_smul (Real.sqrt a)).aemeasurable, hmap,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
  simp only [scaleL2Factor, smul_eq_mul, one_div]

private theorem eLpNorm_invSqrt_comp {a : ℝ} (ha : 0 < a) {f : Plane → ℝ}
    (hf : MemLp f 2) :
    eLpNorm (fun x => f ((Real.sqrt a)⁻¹ • x)) 2 volume =
      scaleL2Factor (ENNReal.ofReal a) * eLpNorm f 2 volume := by
  have hmap := map_invSqrt_smul_volume ha
  have hmem : MemLp f 2 (Measure.map (fun x : Plane => (Real.sqrt a)⁻¹ • x) volume) := by
    rw [hmap]
    exact hf.smul_measure (by simp)
  change eLpNorm (f ∘ fun x : Plane => (Real.sqrt a)⁻¹ • x) 2 volume = _
  rw [← eLpNorm_map_measure hmem.aestronglyMeasurable
    (measurable_const_smul (Real.sqrt a)⁻¹).aemeasurable, hmap,
    eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num) (by norm_num)]
  simp only [scaleL2Factor, smul_eq_mul, one_div]

private theorem scaleL2Factors_cancel {a : ℝ} (ha : 0 < a) :
    scaleL2Factor (ENNReal.ofReal a⁻¹) * scaleL2Factor (ENNReal.ofReal a) = 1 := by
  simp only [scaleL2Factor, ENNReal.inv_rpow, ENNReal.ofReal_inv_of_pos ha]
  exact ENNReal.inv_mul_cancel (by positivity) (by simp)

private theorem mollifierAction_scale {a : ℝ} (ha : 0 < a)
    (w φ : Plane → ℝ) (x : Plane) :
    mollifierAction (fun y => a * w (Real.sqrt a • y)) φ x =
      mollifierAction w (fun y => φ ((Real.sqrt a)⁻¹ • y)) (Real.sqrt a • x) := by
  let b : ℝ := a⁻¹
  have hb : 0 < b := inv_pos.mpr ha
  have hsqrt : Real.sqrt b = (Real.sqrt a)⁻¹ := by
    dsimp [b]
    rw [Real.sqrt_inv]
  have hchange := Critical2DKPZ.Smoothing.integral_plane_sqrt_scale hb
    (fun y : Plane => a * w (Real.sqrt a • (x - y)) * φ y)
  rw [show (Real.sqrt b) = (Real.sqrt a)⁻¹ from hsqrt] at hchange
  have hfac : a * b = 1 := by dsimp [b]; exact mul_inv_cancel₀ ha.ne'
  unfold mollifierAction
  change (∫ y, a * w (Real.sqrt a • (x - y)) * φ y) = _
  calc
    _ = b * ∫ y, a * w (Real.sqrt a • (x - (Real.sqrt a)⁻¹ • y)) *
          φ ((Real.sqrt a)⁻¹ • y) := hchange
    _ = b * (a * ∫ y, w (Real.sqrt a • x - y) * φ ((Real.sqrt a)⁻¹ • y)) := by
      apply congrArg (fun r : ℝ => b * r)
      have hsplit :
          (∫ y, a * w (Real.sqrt a • (x - (Real.sqrt a)⁻¹ • y)) *
            φ ((Real.sqrt a)⁻¹ • y)) =
          a * ∫ y, w (Real.sqrt a • x - y) * φ ((Real.sqrt a)⁻¹ • y) := by
        calc
          _ = ∫ y, a * (w (Real.sqrt a • (x - (Real.sqrt a)⁻¹ • y)) *
                φ ((Real.sqrt a)⁻¹ • y)) := by
            apply integral_congr_ae
            filter_upwards [] with y
            ring
          _ = a * ∫ y, w (Real.sqrt a • x - y) * φ ((Real.sqrt a)⁻¹ • y) := by
            rw [integral_const_mul]
            congr 1
            apply integral_congr_ae
            filter_upwards [] with y
            have hroot : Real.sqrt a * (Real.sqrt a)⁻¹ = 1 :=
              mul_inv_cancel₀ (Real.sqrt_pos.mpr ha).ne'
            rw [smul_sub, smul_smul, hroot, one_smul]
      exact hsplit
    _ = ∫ y, w (Real.sqrt a • x - y) * φ ((Real.sqrt a)⁻¹ • y) := by
      rw [← mul_assoc, mul_comm b a, hfac, one_mul]

private theorem scaleL2_operator_absorb {a : ℝ} (ha : 0 < a)
    (M q v : ℝ≥0∞)
    (hv : v = scaleL2Factor (ENNReal.ofReal a) * q) :
    scaleL2Factor (ENNReal.ofReal a⁻¹) * (M * v) = M * q := by
  rw [hv]
  calc
    scaleL2Factor (ENNReal.ofReal a⁻¹) *
        (M * (scaleL2Factor (ENNReal.ofReal a) * q)) =
      (scaleL2Factor (ENNReal.ofReal a⁻¹) *
        scaleL2Factor (ENNReal.ofReal a)) * (M * q) := by ac_rfl
    _ = M * q := by rw [scaleL2Factors_cancel ha, one_mul]

private theorem scaleL2_operator_bound {a : ℝ} (ha : 0 < a)
    {M q u v : ℝ≥0∞}
    (hv : v = scaleL2Factor (ENNReal.ofReal a) * q)
    (hu : u ≤ M * v) :
    scaleL2Factor (ENNReal.ofReal a⁻¹) * u ≤ M * q := by
  calc
    scaleL2Factor (ENNReal.ofReal a⁻¹) * u ≤
        scaleL2Factor (ENNReal.ofReal a⁻¹) * (M * v) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = M * q := scaleL2_operator_absorb ha M q v hv

private theorem scaledMollifier_operator {a : ℝ} (ha : 0 < a)
    {w : ℕ → Plane → ℝ}
    (hwop : ∀ ℓ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ φ : Plane → ℝ, MemLp φ 2 →
      MemLp (mollifierAction (w ℓ) φ) 2 ∧
        eLpNorm (mollifierAction (w ℓ) φ) 2 ≤ M * eLpNorm φ 2)
    (ℓ : ℕ) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ φ : Plane → ℝ, MemLp φ 2 →
      MemLp (mollifierAction (scaleMollifier a w ℓ) φ) 2 ∧
        eLpNorm (mollifierAction (scaleMollifier a w ℓ) φ) 2 ≤ M * eLpNorm φ 2 := by
  obtain ⟨M, hMtop, hM⟩ := hwop ℓ
  refine ⟨M, hMtop, fun φ hφ => ?_⟩
  let ψ : Plane → ℝ := fun x => φ ((Real.sqrt a)⁻¹ • x)
  have hψ : MemLp ψ 2 := memLp_invSqrt_comp ha hφ
  have hbound := hM ψ hψ
  have hact : mollifierAction (scaleMollifier a w ℓ) φ =
      fun x => mollifierAction (w ℓ) ψ (Real.sqrt a • x) := by
    funext x
    exact mollifierAction_scale ha (w ℓ) φ x
  have hmem : MemLp (fun x => mollifierAction (w ℓ) ψ (Real.sqrt a • x)) 2 :=
    memLp_sqrt_comp ha hbound.1
  have hscale : eLpNorm (fun x => mollifierAction (w ℓ) ψ (Real.sqrt a • x)) 2 =
      scaleL2Factor (ENNReal.ofReal a⁻¹) * eLpNorm (mollifierAction (w ℓ) ψ) 2 := by
    change eLpNorm (fun x => ∫ y, w ℓ (Real.sqrt a • x - y) * ψ y) 2 volume = _
    exact eLpNorm_sqrt_comp ha hbound.1
  have hψnorm : eLpNorm ψ 2 = scaleL2Factor (ENNReal.ofReal a) * eLpNorm φ 2 := by
    simpa only [ψ] using eLpNorm_invSqrt_comp ha hφ
  have hbound' : eLpNorm (mollifierAction (w ℓ) ψ) 2 ≤ M * eLpNorm ψ 2 := hbound.2
  constructor
  · rw [hact]
    exact hmem
  · change eLpNorm (fun x => mollifierAction (scaleMollifier a w ℓ) φ x) 2 ≤ _
    rw [hact, hscale]
    exact scaleL2_operator_bound ha hψnorm hbound'

private theorem scaledMollifier_strong {a : ℝ} (ha : 0 < a)
    {w : ℕ → Plane → ℝ}
    (hwop : ∀ ℓ, ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ φ : Plane → ℝ, MemLp φ 2 →
      MemLp (mollifierAction (w ℓ) φ) 2 ∧
        eLpNorm (mollifierAction (w ℓ) φ) 2 ≤ M * eLpNorm φ 2)
    (hwlim : ∀ φ : Plane → ℝ, MemLp φ 2 →
      Tendsto (fun ℓ => eLpNorm (mollifierAction (w ℓ) φ - φ) 2) atTop (𝓝 0))
    (φ : Plane → ℝ) (hφ : MemLp φ 2) :
    Tendsto (fun ℓ => eLpNorm (mollifierAction (scaleMollifier a w ℓ) φ - φ) 2)
      atTop (𝓝 0) := by
  let ψ : Plane → ℝ := fun x => φ ((Real.sqrt a)⁻¹ • x)
  have hψ : MemLp ψ 2 := memLp_invSqrt_comp ha hφ
  have hlim' := hwlim ψ hψ
  have hfun (ℓ : ℕ) :
      (fun x => mollifierAction (scaleMollifier a w ℓ) φ x - φ x) =
        fun x => (mollifierAction (w ℓ) ψ - ψ) (Real.sqrt a • x) := by
    funext x
    change mollifierAction (fun y => a * w ℓ (Real.sqrt a • y)) φ x - φ x = _
    rw [mollifierAction_scale ha]
    have hψx : ψ (Real.sqrt a • x) = φ x := by
      simp only [ψ, smul_smul]
      rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr ha).ne', one_smul]
    change mollifierAction (w ℓ) ψ (Real.sqrt a • x) - φ x = _
    rw [← hψx]
    rfl
  have hnorm (ℓ : ℕ) :
      eLpNorm (fun x => mollifierAction (scaleMollifier a w ℓ) φ x - φ x) 2 volume =
        scaleL2Factor (ENNReal.ofReal a⁻¹) *
          eLpNorm (mollifierAction (w ℓ) ψ - ψ) 2 volume := by
    obtain ⟨M, hMtop, hM⟩ := hwop ℓ
    have hbound := hM ψ hψ
    have hmem : MemLp (mollifierAction (w ℓ) ψ - ψ) 2 := hbound.1.sub hψ
    calc
      eLpNorm (fun x => mollifierAction (scaleMollifier a w ℓ) φ x - φ x) 2 volume =
          eLpNorm (fun x => (mollifierAction (w ℓ) ψ - ψ) (Real.sqrt a • x)) 2 volume :=
        congrArg (fun f : Plane → ℝ => eLpNorm f 2 volume) (hfun ℓ)
      _ = scaleL2Factor (ENNReal.ofReal a⁻¹) *
          eLpNorm (mollifierAction (w ℓ) ψ - ψ) 2 volume := by
        simpa only [mollifierAction] using eLpNorm_sqrt_comp ha hmem
  have hc : scaleL2Factor (ENNReal.ofReal a⁻¹) ≠ ⊤ := by simp [scaleL2Factor]
  have hcont := ENNReal.continuous_const_mul hc
  have hlimScaled : Tendsto (fun ℓ =>
      scaleL2Factor (ENNReal.ofReal a⁻¹) *
        eLpNorm (mollifierAction (w ℓ) ψ - ψ) 2)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, mollifierAction, mul_zero] using
      hcont.continuousAt.tendsto.comp hlim'
  have hnorm' (ℓ : ℕ) :
      eLpNorm (mollifierAction (scaleMollifier a w ℓ) φ - φ) 2 =
        scaleL2Factor (ENNReal.ofReal a⁻¹) *
          eLpNorm (mollifierAction (w ℓ) ψ - ψ) 2 := by
    change eLpNorm (fun x => mollifierAction (scaleMollifier a w ℓ) φ x - φ x)
      2 volume = _
    exact hnorm ℓ
  exact Tendsto.congr' (Filter.Eventually.of_forall fun ℓ => (hnorm' ℓ).symm) hlimScaled

private theorem isL2ApplicableMollifier_scale {a : ℝ} (ha : 0 < a)
    {w : ℕ → Plane → ℝ} (hw : IsL2ApplicableMollifier w) :
    IsL2ApplicableMollifier (scaleMollifier a w) := by
  rcases hw with ⟨hwpos, hwcont, hwmem, hwop, hwlim⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ x
    exact mul_nonneg (le_of_lt ha) (hwpos ℓ (Real.sqrt a • x))
  · intro ℓ
    have hscale : Continuous (fun x : Plane => Real.sqrt a • x) := by fun_prop
    exact (hwcont ℓ).const_mul a |>.comp hscale
  · intro ℓ
    exact (memLp_sqrt_comp ha (hwmem ℓ)).const_mul a
  · intro ℓ
    exact scaledMollifier_operator ha hwop ℓ
  · intro φ hφ
    exact scaledMollifier_strong ha hwop hwlim φ hφ

private theorem compositionClause_scale {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)} (hZ : IsDenseSHF θ D P Z)
    {a : ℝ} (ha : 0 < a) :
    ∀ t₀ ∈ {s | a * s ∈ D}, ∀ t₁ ∈ {s | a * s ∈ D},
      ∀ t₂ ∈ {s | a * s ∈ D}, t₀ < t₁ → t₁ < t₂ →
        ∃ w : ℕ → Plane → ℝ, IsL2ApplicableMollifier w ∧
          (∀ ℓ, ∀ᵐ ω ∂P, SmoothedProductWellDefined
            (scalePairMeasure ha (Z (a * t₀) (a * t₁) ω)) (w ℓ)
            (scalePairMeasure ha (Z (a * t₁) (a * t₂) ω))) ∧
          ∀ f : C_c(Plane × Plane, ℝ),
            TendstoInMeasure P (fun ℓ ω =>
              smoothedProductPairing (scalePairMeasure ha (Z (a * t₀) (a * t₁) ω)) (w ℓ)
                (scalePairMeasure ha (Z (a * t₁) (a * t₂) ω)) f -
              ∫ p, f p ∂(scalePairMeasure ha (Z (a * t₀) (a * t₂) ω))) atTop (fun _ => 0) := by
  intro t₀ ht₀ t₁ ht₁ t₂ ht₂ h01 h12
  change a * t₀ ∈ D at ht₀
  change a * t₁ ∈ D at ht₁
  change a * t₂ ∈ D at ht₂
  have h01' : a * t₀ < a * t₁ := mul_lt_mul_of_pos_left h01 ha
  have h12' : a * t₁ < a * t₂ := mul_lt_mul_of_pos_left h12 ha
  rcases hZ.2.1 (a * t₀) ht₀ (a * t₁) ht₁ (a * t₂) ht₂ h01' h12' with
    ⟨w, hw, hdef, hlim⟩
  let w' := scaleMollifier a w
  have hw' : IsL2ApplicableMollifier w' := isL2ApplicableMollifier_scale ha hw
  refine ⟨w', hw', ?_, ?_⟩
  · intro ℓ
    filter_upwards [hdef ℓ, (hZ.1 (a * t₀) ht₀ (a * t₁) ht₁ h01').2,
      (hZ.1 (a * t₁) ht₁ (a * t₂) ht₂ h12').2] with ω hω hLF₀₁ hLF₁₂
    let _ : IsLocallyFiniteMeasure (Z (a * t₀) (a * t₁) ω) := hLF₀₁
    let _ : IsLocallyFiniteMeasure (Z (a * t₁) (a * t₂) ω) := hLF₁₂
    convert smoothedProductWellDefined_scale ha (Z (a * t₀) (a * t₁) ω)
      (Z (a * t₁) (a * t₂) ω) (w ℓ) ℓ hω using 1; rfl
  · intro f
    have hleft (ℓ : ℕ) :
        (fun ω => smoothedProductPairing
            (scalePairMeasure ha (Z (a * t₀) (a * t₁) ω)) (w' ℓ)
            (scalePairMeasure ha (Z (a * t₁) (a * t₂) ω)) f -
          ∫ p, f p ∂(scalePairMeasure ha (Z (a * t₀) (a * t₂) ω))) =ᵐ[P]
        fun ω => a⁻¹ * (smoothedProductPairing (Z (a * t₀) (a * t₁) ω) (w ℓ)
            (Z (a * t₁) (a * t₂) ω) (scalePairTest ha f) -
          ∫ p, scalePairTest ha f p ∂(Z (a * t₀) (a * t₂) ω)) := by
      filter_upwards [hdef ℓ,
        (hZ.1 (a * t₀) ht₀ (a * t₁) ht₁ h01').2,
        (hZ.1 (a * t₁) ht₁ (a * t₂) ht₂ h12').2,
        (hZ.1 (a * t₀) ht₀ (a * t₂) ht₂ (lt_trans h01' h12')).2]
        with ω hω hLF₀₁ hLF₁₂ hLF₀₂
      let _ : IsLocallyFiniteMeasure (Z (a * t₀) (a * t₁) ω) := hLF₀₁
      let _ : IsLocallyFiniteMeasure (Z (a * t₁) (a * t₂) ω) := hLF₁₂
      let _ : IsLocallyFiniteMeasure (Z (a * t₀) (a * t₂) ω) := hLF₀₂
      have hpair := smoothedProductPairing_scale ha (Z (a * t₀) (a * t₁) ω)
        (Z (a * t₁) (a * t₂) ω) (w ℓ) ℓ f hω
      have hLFscaled := locallyFinite_scalePairMeasure ha (Z (a * t₀) (a * t₂) ω)
      have hint := integral_scalePairMeasure ha (Z (a * t₀) (a * t₂) ω) hLFscaled f
      have hpair' : smoothedProductPairing
          (scalePairMeasure ha (Z (a * t₀) (a * t₁) ω)) (scaleMollifier a w ℓ)
          (scalePairMeasure ha (Z (a * t₁) (a * t₂) ω)) f =
          a⁻¹ * smoothedProductPairing (Z (a * t₀) (a * t₁) ω) (w ℓ)
            (Z (a * t₁) (a * t₂) ω) (scalePairTest ha f) := by
        change smoothedProductPairing
            (scalePairMeasure ha (Z (a * t₀) (a * t₁) ω))
              (scaleMollifier a (fun _ => w ℓ) ℓ)
            (scalePairMeasure ha (Z (a * t₁) (a * t₂) ω)) f = _
        exact hpair
      rw [show w' ℓ = scaleMollifier a w ℓ from rfl, hpair', hint.2]
      ring
    have hscaled := tendstoInMeasure_const_mul_pos P (inv_pos.mpr ha)
      (hlim (scalePairTest ha f))
    exact TendstoInMeasure.congr (fun ℓ => (hleft ℓ).symm) EventuallyEq.rfl hscaled

private theorem momentClause_scale {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)} (hZ : IsDenseSHF θ D P Z)
    {a : ℝ} (ha : 0 < a) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ s ∈ {r | a * r ∈ D}, ∀ t ∈ {r | a * r ∈ D}, s < t →
      ∀ g g' : Fin n → Plane → ℝ, (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
        (∀ᵐ ω ∂P, ∀ i, Integrable
          (fun p : Plane × Plane => g i p.1 * g' i p.2)
          (scalePairMeasure ha (Z (a * s) (a * t) ω))) ∧
        Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂scalePairMeasure ha (Z (a * s) (a * t) ω)) P ∧
        ∫ ω, ∏ i, ∫ p, g i p.1 * g' i p.2 ∂scalePairMeasure ha (Z (a * s) (a * t) ω) ∂P =
          ∫ x : Critical2DKPZ.DeltaBose.Configuration n, ∫ y,
            (∏ i, g i (x i)) *
              (Critical2DKPZ.DeltaBose.momentKernel n (θ + Real.log a) (t - s) x y).toReal *
                ∏ i, g' i (y i) := by
  intro n hn hn4 s hs t ht hst g g' hg hg'
  change a * s ∈ D at hs
  change a * t ∈ D at ht
  have hst' : a * s < a * t := mul_lt_mul_of_pos_left hst ha
  let g0 : Fin n → Plane → ℝ := fun i x => g i ((Real.sqrt a)⁻¹ • x)
  let g0' : Fin n → Plane → ℝ := fun i x => g' i ((Real.sqrt a)⁻¹ • x)
  have hg0 : ∀ i, MemLp (g0 i) 2 := fun i => memLp_invSqrt_comp ha (hg i)
  have hg0' : ∀ i, MemLp (g0' i) 2 := fun i => memLp_invSqrt_comp ha (hg' i)
  obtain ⟨hInt, hMoment, hMean⟩ := hZ.2.2.2 n hn hn4 (a * s) hs (a * t) ht hst' g0 g0' hg0 hg0'
  let f0 : Fin n → Plane × Plane → ℝ := fun i p => g0 i p.1 * g0' i p.2
  let f : Fin n → Plane × Plane → ℝ := fun i p => g i p.1 * g' i p.2
  have hfcomp (i : Fin n) : (fun p => f i (scalePairMeas a ha p)) = f0 i := by
    funext p
    simp only [f, f0, g0, g0', scalePairMeas_apply]
  have hIntTarget : ∀ᵐ ω ∂P, ∀ i, Integrable (f i) (scalePairMeasure ha (Z (a * s) (a * t) ω)) := by
    apply ae_all_iff.2
    intro i
    filter_upwards [ae_all_iff.mp hInt i] with ω hω
    have hsource : Integrable (fun p => f i (scalePairMeas a ha p)) (Z (a * s) (a * t) ω) := by
      simpa only [hfcomp i] using hω
    exact (integrable_integral_scalePairMeasure ha (Z (a * s) (a * t) ω) (f i) hsource).1
  let cfac : ℝ := ∏ _i : Fin n, a⁻¹
  let X : Ω → ℝ := fun ω => ∏ i, ∫ p, f0 i p ∂Z (a * s) (a * t) ω
  let Y : Ω → ℝ := fun ω => ∏ i, ∫ p, f i p ∂scalePairMeasure ha (Z (a * s) (a * t) ω)
  have hYEq : Y =ᵐ[P] fun ω => cfac * X ω := by
    filter_upwards [hInt] with ω hω
    change (∏ i, ∫ p, f i p ∂scalePairMeasure ha (Z (a * s) (a * t) ω)) =
      cfac * ∏ i, ∫ p, f0 i p ∂Z (a * s) (a * t) ω
    calc
      (∏ i, ∫ p, f i p ∂scalePairMeasure ha (Z (a * s) (a * t) ω)) =
          ∏ i, (a⁻¹ * ∫ p, f0 i p ∂Z (a * s) (a * t) ω) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hsource : Integrable (fun p => f i (scalePairMeas a ha p))
            (Z (a * s) (a * t) ω) := by
          simpa only [hfcomp i] using hω i
        have hpair := (integrable_integral_scalePairMeasure ha
          (Z (a * s) (a * t) ω) (f i) hsource).2
        simpa only [hfcomp i] using hpair
      _ = cfac * ∏ i, ∫ p, f0 i p ∂Z (a * s) (a * t) ω := by
        simp only [cfac]
        rw [Finset.prod_mul_distrib]
  have hfac : cfac = (a ^ n)⁻¹ := by
    simp [cfac, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hMomentTarget : Integrable Y P := (hMoment.const_mul cfac).congr hYEq.symm
  have hgap : a * t - a * s = a * (t - s) := by ring
  have hKernelMean :
      (∫ x : Critical2DKPZ.DeltaBose.Configuration n, ∫ y,
        (∏ i, g0 i (x i)) *
          (Critical2DKPZ.DeltaBose.momentKernel n θ (a * t - a * s) x y).toReal *
            ∏ i, g0' i (y i)) =
        a ^ n * ∫ x : Critical2DKPZ.DeltaBose.Configuration n, ∫ y,
          (∏ i, g i (x i)) *
            (Critical2DKPZ.DeltaBose.momentKernel n (θ + Real.log a) (t - s) x y).toReal *
              ∏ i, g' i (y i) := by
    simpa only [g0, g0', hgap] using
      momentKernel_integral_scale (n := n) θ (a := a) (h := t - s) ha g g'
  have hMeanSource :
      ∫ ω, X ω ∂P =
        ∫ x : Critical2DKPZ.DeltaBose.Configuration n, ∫ y,
          (∏ i, g0 i (x i)) *
            (Critical2DKPZ.DeltaBose.momentKernel n θ (a * t - a * s) x y).toReal *
              ∏ i, g0' i (y i) := by
    simpa only [X, f0] using hMean
  refine ⟨?_, ?_, ?_⟩
  · simpa only [f] using hIntTarget
  · simpa only [Y, f] using hMomentTarget
  · calc
      ∫ ω, Y ω ∂P = ∫ ω, cfac * X ω ∂P := integral_congr_ae hYEq
      _ = cfac * ∫ ω, X ω ∂P := integral_const_mul cfac X
      _ = cfac * (a ^ n * ∫ x : Critical2DKPZ.DeltaBose.Configuration n, ∫ y,
            (∏ i, g i (x i)) *
              (Critical2DKPZ.DeltaBose.momentKernel n (θ + Real.log a) (t - s) x y).toReal *
                ∏ i, g' i (y i)) := by rw [hMeanSource, hKernelMean]
      _ = ∫ x : Critical2DKPZ.DeltaBose.Configuration n, ∫ y,
            (∏ i, g i (x i)) *
              (Critical2DKPZ.DeltaBose.momentKernel n (θ + Real.log a) (t - s) x y).toReal *
                ∏ i, g' i (y i) := by
          rw [hfac, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n ha.ne'), one_mul]

/-- Parabolic scaling transports all four dense-time SHF axioms and shifts the parameter by `log a`. -/
theorem isDenseSHF_scale {θ : ℝ} {D : Set ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)} (hZ : IsDenseSHF θ D P Z)
    {a : ℝ} (ha : 0 < a) :
    IsDenseSHF (θ + Real.log a) {s | a * s ∈ D} P fun s t ω =>
      ENNReal.ofReal a⁻¹ • (Z (a * s) (a * t) ω).map fun p =>
        ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2) := by
  have hmap : (fun p : Plane × Plane =>
      ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2)) = scalePairMeas a ha := by
    funext p
    exact (scalePairMeas_apply ha p).symm
  have hpair := pairClause_scale ha hZ.1
  have hcomp := compositionClause_scale hZ ha
  have hindep := independenceClause_scale ha hZ.2.2.1
  have hmom := momentClause_scale hZ ha
  change IsDenseSHF (θ + Real.log a) {s | a * s ∈ D} P fun s t ω =>
    ENNReal.ofReal a⁻¹ • (Z (a * s) (a * t) ω).map
      (fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2))
  simpa only [scalePairMeasure, ENNReal.ofReal_inv_of_pos ha, ← hmap] using
    (show IsDenseSHF (θ + Real.log a) {s | a * s ∈ D} P fun s t ω =>
      scalePairMeasure ha (Z (a * s) (a * t) ω) from ⟨hpair, hcomp, hindep, hmom⟩)

end Critical2DKPZ.SHF.Symmetries

end
