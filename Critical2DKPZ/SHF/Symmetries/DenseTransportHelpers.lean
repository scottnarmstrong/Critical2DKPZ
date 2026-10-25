/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.Defs
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.RandomMeasure.PlanePairInterface
public import Critical2DKPZ.SHF.Tsai.Products
public import Critical2DKPZ.SHF.Tsai.TensorMoments
public import Critical2DKPZ.SHF.DeltaBose.SpatialTransport
public import Critical2DKPZ.SHF.DeltaBose.EndpointSymmetry
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Dense-time SHF law transport and symmetry lemmas -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Tsai
open scoped Topology ENNReal CompactlySupported

namespace Critical2DKPZ.SHF.Symmetries

/-- The homeomorphism translating both endpoints by the same vector. -/
def pairTranslate (z : Plane) : (Plane × Plane) ≃ₜ (Plane × Plane) :=
  (Homeomorph.addRight z).prodCongr (Homeomorph.addRight z)

/-- The measurable equivalence translating both endpoints by the same vector. -/
def pairTranslateMeas (z : Plane) : (Plane × Plane) ≃ᵐ (Plane × Plane) :=
  (pairTranslate z).toMeasurableEquiv

/-- The compact test obtained by translating both endpoints. -/
def pairTranslateTest (z : Plane) (f : C_c(Plane × Plane, ℝ)) : C_c(Plane × Plane, ℝ) :=
  f.comp (pairTranslate z).toCocompactMap

/-- The homeomorphism applying a linear isometry to both endpoints. -/
def pairLinearIsometry (R : Plane ≃ₗᵢ[ℝ] Plane) :
    (Plane × Plane) ≃ₜ (Plane × Plane) :=
  R.toHomeomorph.prodCongr R.toHomeomorph

/-- The measurable equivalence applying a linear isometry to both endpoints. -/
def pairLinearIsometryMeas (R : Plane ≃ₗᵢ[ℝ] Plane) :
    (Plane × Plane) ≃ᵐ (Plane × Plane) :=
  (pairLinearIsometry R).toMeasurableEquiv

/-- The compact test obtained by applying a linear isometry to both endpoints. -/
def pairLinearIsometryTest (R : Plane ≃ₗᵢ[ℝ] Plane)
    (f : C_c(Plane × Plane, ℝ)) : C_c(Plane × Plane, ℝ) :=
  f.comp (pairLinearIsometry R).toCocompactMap

/-- The homeomorphism exchanging the two endpoints. -/
def pairSwap : (Plane × Plane) ≃ₜ (Plane × Plane) := Homeomorph.prodComm Plane Plane

/-- The measurable equivalence exchanging the two endpoints. -/
def pairSwapMeas : (Plane × Plane) ≃ᵐ (Plane × Plane) := pairSwap.toMeasurableEquiv

/-- The compact test obtained by exchanging the two endpoints. -/
def pairSwapTest (f : C_c(Plane × Plane, ℝ)) : C_c(Plane × Plane, ℝ) :=
  f.comp pairSwap.toCocompactMap

/-- The mollifier obtained by reflecting its argument. -/
def mollifierReverse (w : ℕ → Plane → ℝ) : ℕ → Plane → ℝ :=
  fun ℓ x => w ℓ (-x)

/-- Endpoint exchange acts coordinatewise as a measurable equivalence. -/
theorem pairSwapMeas_apply (p : Plane × Plane) : pairSwapMeas p = (p.2, p.1) := by
  change pairSwap p = _
  rfl

/-- Endpoint exchange acts on a test by composition with the endpoint map. -/
theorem pairSwapTest_apply (f : C_c(Plane × Plane, ℝ)) (p : Plane × Plane) :
    pairSwapTest f p = f (p.2, p.1) := by
  change f (pairSwap p) = _
  rfl

/-- The common endpoint isometry acts coordinatewise. -/
theorem pairLinearIsometry_apply (R : Plane ≃ₗᵢ[ℝ] Plane)
    (p : Plane × Plane) : pairLinearIsometry R p = (R p.1, R p.2) := by
  change (R.toHomeomorph p.1, R.toHomeomorph p.2) = _
  rfl

/-- The common endpoint isometry acts coordinatewise as a measurable equivalence. -/
theorem pairLinearIsometryMeas_apply (R : Plane ≃ₗᵢ[ℝ] Plane)
    (p : Plane × Plane) : pairLinearIsometryMeas R p = (R p.1, R p.2) := by
  change pairLinearIsometry R p = _
  rw [pairLinearIsometry_apply]

/-- The common endpoint isometry acts on a test by composition with the endpoint map. -/
theorem pairLinearIsometryTest_apply (R : Plane ≃ₗᵢ[ℝ] Plane)
    (f : C_c(Plane × Plane, ℝ)) (p : Plane × Plane) :
    pairLinearIsometryTest R f p = f (R p.1, R p.2) := by
  change f (pairLinearIsometry R p) = _
  rw [pairLinearIsometry_apply]

/-- A homeomorphism sends locally finite measures to locally finite measures. -/
theorem locallyFinite_map_homeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y] [BorelSpace Y]
    (e : X ≃ₜ Y) (μ : Measure X) [IsLocallyFiniteMeasure μ] :
    IsLocallyFiniteMeasure (μ.map e) := by
  refine ⟨fun y => ?_⟩
  rcases μ.exists_isOpen_measure_lt_top (e.symm y) with ⟨U, hmem, hUopen, hUfinite⟩
  refine ⟨e '' U, (e.isOpenMap U hUopen).mem_nhds ?_, ?_⟩
  · exact ⟨e.symm y, hmem, e.apply_symm_apply y⟩
  · rw [Measure.map_apply e.continuous.measurable (e.isOpenMap U hUopen).measurableSet]
    have hpre : e ⁻¹' (e '' U) = U := by
      ext x
      constructor
      · rintro ⟨x', hx', heq⟩
        exact e.injective heq ▸ hx'
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hpre]
    exact hUfinite

/-- The mollifier obtained by composing with the inverse linear isometry. -/
def mollifierLinearIsometry (R : Plane ≃ₗᵢ[ℝ] Plane)
    (w : ℕ → Plane → ℝ) : ℕ → Plane → ℝ :=
  fun ℓ x => w ℓ (R.symm x)

/-- The measurable equivalence associated with a linear isometry. -/
def linearIsometryMeas (R : Plane ≃ₗᵢ[ℝ] Plane) : Plane ≃ᵐ Plane :=
  R.toMeasurableEquiv

/-- A linear isometry preserves Lebesgue measure. -/
theorem measurePreserving_linearIsometryMeas (R : Plane ≃ₗᵢ[ℝ] Plane) :
    MeasurePreserving (linearIsometryMeas R) volume volume := by
  refine ⟨(linearIsometryMeas R).measurable, ?_⟩
  rcases exists_orthonormalBasis ℝ Plane with ⟨_, b, _⟩
  change Measure.map R volume = volume
  calc
    Measure.map R volume = Measure.map R b.toBasis.addHaar := by
      rw [OrthonormalBasis.addHaar_eq_volume b]
    _ = Measure.map R.toContinuousLinearEquiv b.toBasis.addHaar := by
      congr 1
    _ = (b.toBasis.map R.toContinuousLinearEquiv.toLinearEquiv).addHaar :=
      Module.Basis.map_addHaar b.toBasis R.toContinuousLinearEquiv
    _ = (b.map R).toBasis.addHaar := by
      rw [OrthonormalBasis.toBasis_map]
      congr 1
    _ = volume := OrthonormalBasis.addHaar_eq_volume (b.map R)

/-- The inverse of a linear isometry preserves Lebesgue measure. -/
theorem measurePreserving_linearIsometryMeas_symm
    (R : Plane ≃ₗᵢ[ℝ] Plane) :
    MeasurePreserving (linearIsometryMeas R).symm volume volume := by
  simpa only [linearIsometryMeas, LinearIsometryEquiv.toMeasurableEquiv_symm] using
    measurePreserving_linearIsometryMeas R.symm

/-- Composition with a linear isometry preserves admissibility of an L² mollifier. -/
theorem isL2ApplicableMollifier_linearIsometry {w : ℕ → Plane → ℝ}
    (hW : IsL2ApplicableMollifier w) (R : Plane ≃ₗᵢ[ℝ] Plane) :
    IsL2ApplicableMollifier (mollifierLinearIsometry R w) := by
  rcases hW with ⟨hpos, hcont, hmem, hop, hlim⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro ℓ x
    exact hpos ℓ (R.symm x)
  · intro ℓ
    exact (hcont ℓ).comp R.symm.continuous
  · intro ℓ
    exact (hmem ℓ).comp_measurePreserving R.symm.measurePreserving
  · intro ℓ
    rcases hop ℓ with ⟨M, hM, hbound⟩
    refine ⟨M, hM, ?_⟩
    intro φ hφ
    let ψ : Plane → ℝ := fun y => φ (R y)
    have hψ : MemLp ψ 2 := hφ.comp_measurePreserving R.measurePreserving
    rcases hbound ψ hψ with ⟨hconvW, hboundW⟩
    let convW : Plane → ℝ := fun x => ∫ y, w ℓ (x - y) * ψ y
    let convR : Plane → ℝ := fun x => ∫ y, mollifierLinearIsometry R w ℓ (x - y) * φ y
    have hconvAt (v : Plane) : convR (R v) = convW v := by
      let G : Plane → ℝ := fun y => mollifierLinearIsometry R w ℓ (R v - y) * φ y
      calc
        ∫ y, G y = ∫ y, G (R y) := by
          symm
          exact (measurePreserving_linearIsometryMeas R).integral_comp'
            G
        _ = ∫ y, w ℓ (v - y) * ψ y := by
          apply integral_congr_ae
          filter_upwards [] with y
          dsimp [G, mollifierLinearIsometry, ψ]
          congr 1
          congr 1
          rw [R.symm.map_sub]
          simp only [R.symm_apply_apply]
    have hconvEq : convR =ᵐ[volume] convW ∘ R.symm := by
      filter_upwards [] with x
      change convR x = convW (R.symm x)
      simpa only [R.apply_symm_apply] using hconvAt (R.symm x)
    have hconvEqMeas : convR =ᵐ[volume] convW ∘ (linearIsometryMeas R).symm := by
      filter_upwards [hconvEq] with x hx
      change convR x = convW ((R.toMeasurableEquiv).symm x)
      simpa only [Function.comp_apply,
        LinearIsometryEquiv.coe_symm_toMeasurableEquiv] using hx
    have hconvR : MemLp convR 2 := by
      have h := hconvW.comp_measurePreserving (measurePreserving_linearIsometryMeas_symm R)
      have hmeas := h.aestronglyMeasurable.congr hconvEqMeas.symm
      exact h.congr_enorm hmeas (hconvEqMeas.symm.mono fun _ hx => by rw [hx])
    have hnormψ : eLpNorm ψ 2 volume = eLpNorm φ 2 volume := by
      exact eLpNorm_comp_measurePreserving hφ.aestronglyMeasurable
        (measurePreserving_linearIsometryMeas R)
    have hnormConv : eLpNorm convR 2 volume = eLpNorm convW 2 volume := by
      calc
        eLpNorm convR 2 volume = eLpNorm (convW ∘ R.symm) 2 volume :=
          eLpNorm_congr_ae hconvEq
        _ = eLpNorm (convW ∘ (linearIsometryMeas R).symm) 2 volume := by
          congr 1
        _ = eLpNorm convW 2 volume := eLpNorm_comp_measurePreserving
          hconvW.aestronglyMeasurable (measurePreserving_linearIsometryMeas_symm R)
    refine ⟨hconvR, ?_⟩
    calc
      eLpNorm convR 2 volume = eLpNorm convW 2 volume := hnormConv
      _ ≤ M * eLpNorm ψ 2 volume := hboundW
      _ = M * eLpNorm φ 2 volume := by rw [hnormψ]
  · intro φ hφ
    let ψ : Plane → ℝ := fun y => φ (R y)
    have hψ : MemLp ψ 2 := hφ.comp_measurePreserving R.measurePreserving
    have hsequence (ℓ : ℕ) :
        eLpNorm (fun x => (∫ y, mollifierLinearIsometry R w ℓ (x - y) * φ y) - φ x)
          2 volume =
        eLpNorm (fun x => (∫ y, w ℓ (x - y) * ψ y) - ψ x) 2 volume := by
      rcases hop ℓ with ⟨_, _, hbound⟩
      rcases hbound ψ hψ with ⟨hconv, _⟩
      let conv : Plane → ℝ := fun x => ∫ y, w ℓ (x - y) * ψ y
      have hEq : (fun x => (∫ y, mollifierLinearIsometry R w ℓ (x - y) * φ y) - φ x) =ᵐ[volume]
          conv ∘ R.symm - ψ ∘ R.symm := by
        filter_upwards [] with x
        have hcv : (∫ y, mollifierLinearIsometry R w ℓ (x - y) * φ y) = conv (R.symm x) := by
          let G : Plane → ℝ := fun y => mollifierLinearIsometry R w ℓ (x - y) * φ y
          calc
            ∫ y, G y = ∫ y, G (R y) := by
              symm
              exact (measurePreserving_linearIsometryMeas R).integral_comp'
                G
            _ = conv (R.symm x) := by
              dsimp [G, conv, mollifierLinearIsometry, ψ]
              apply integral_congr_ae
              filter_upwards [] with y
              rw [R.symm.map_sub]
              simp only [R.symm_apply_apply]
        rw [hcv]
        change conv (R.symm x) - φ x =
          conv (R.symm x) - φ (R (R.symm x))
        rw [R.apply_symm_apply]
      have hdiff : MemLp (fun y => conv y - ψ y) 2 := hconv.sub hψ
      calc
        eLpNorm (fun x => (∫ y, mollifierLinearIsometry R w ℓ (x - y) * φ y) - φ x)
            2 volume = eLpNorm (fun x => conv (R.symm x) - ψ (R.symm x)) 2 volume :=
          eLpNorm_congr_ae hEq
        _ = eLpNorm (fun x => (fun y => conv y - ψ y) (R.symm x)) 2 volume := by
          rfl
        _ = eLpNorm (fun x => conv x - ψ x) 2 volume :=
          eLpNorm_comp_measurePreserving hdiff.aestronglyMeasurable
            (measurePreserving_linearIsometryMeas_symm R)
    have htend := hlim ψ hψ
    exact Tendsto.congr' (Filter.Eventually.of_forall fun ℓ => (hsequence ℓ).symm) htend

/-- Reflection preserves admissibility of an L² mollifier. -/
theorem isL2ApplicableMollifier_reverse {w : ℕ → Plane → ℝ}
    (hW : IsL2ApplicableMollifier w) : IsL2ApplicableMollifier (mollifierReverse w) := by
  have h := isL2ApplicableMollifier_linearIsometry hW (LinearIsometryEquiv.neg ℝ)
  change IsL2ApplicableMollifier
    (fun ℓ x => w ℓ ((LinearIsometryEquiv.neg ℝ : Plane ≃ₗᵢ[ℝ] Plane).symm x)) at h
  change IsL2ApplicableMollifier (fun ℓ x => w ℓ (-x))
  exact h

/-- An integrable pairing transforms under a linear isometry by composition of its tests. -/
theorem integrable_pairing_map_linearIsometry (R : Plane ≃ₗᵢ[ℝ] Plane)
    (μ : Measure (Plane × Plane)) (g g' : Plane → ℝ)
    (hI : Integrable (fun p : Plane × Plane => g (R p.1) * g' (R p.2)) μ) :
    Integrable (fun p : Plane × Plane => g p.1 * g' p.2)
      (μ.map (pairLinearIsometryMeas R)) ∧
    ∫ p, g p.1 * g' p.2 ∂(μ.map (pairLinearIsometryMeas R)) =
      ∫ p, g (R p.1) * g' (R p.2) ∂μ := by
  let e := pairLinearIsometryMeas R
  let F : Plane × Plane → ℝ := fun p => g p.1 * g' p.2
  have hsource : Integrable (fun p => F (e p)) μ := by
    simpa only [F, e, pairLinearIsometryMeas_apply] using hI
  have htarget : Integrable F (μ.map e) := (integrable_map_equiv e F).2 hsource
  refine ⟨htarget, ?_⟩
  calc
    ∫ p, F p ∂(μ.map e) = ∫ p, F (e p) ∂μ :=
      integral_map e.measurable.aemeasurable htarget.aestronglyMeasurable
    _ = ∫ p, g (R p.1) * g' (R p.2) ∂μ := by
      apply integral_congr_ae
      filter_upwards with p
      rfl

/-- A compact pairing against a pushed measure is integrable and equals the pulled-back pairing. -/
theorem integral_pairLinearIsometryTest_map (R : Plane ≃ₗᵢ[ℝ] Plane)
    (μ : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ]
    (f : C_c(Plane × Plane, ℝ)) :
    Integrable f (μ.map (pairLinearIsometryMeas R)) ∧
      ∫ p, f p ∂(μ.map (pairLinearIsometryMeas R)) =
        ∫ p, pairLinearIsometryTest R f p ∂μ := by
  have hLF : IsLocallyFiniteMeasure (μ.map (pairLinearIsometryMeas R)) := by
    simpa only [pairLinearIsometryMeas, Homeomorph.toMeasurableEquiv_coe] using
      locallyFinite_map_homeomorph (pairLinearIsometry R) μ
  let μ' : RandomMeasure.PositiveRadonMeasure (Plane × Plane) :=
    ⟨μ.map (pairLinearIsometryMeas R), hLF⟩
  have hI : Integrable f (μ.map (pairLinearIsometryMeas R)) :=
    RandomMeasure.integrable_vagueTest μ' f
  refine ⟨hI, ?_⟩
  calc
    ∫ p, f p ∂(μ.map (pairLinearIsometryMeas R)) =
      ∫ p, f (pairLinearIsometryMeas R p) ∂μ :=
        integral_map (pairLinearIsometryMeas R).measurable.aemeasurable
          hI.aestronglyMeasurable
    _ = ∫ p, pairLinearIsometryTest R f p ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact (pairLinearIsometryTest_apply R f p).symm

/-- A compact pairing against an endpoint-swapped measure is integrable and equals the swapped test pairing. -/
theorem integral_pairSwapTest_map (μ : Measure (Plane × Plane))
    [IsLocallyFiniteMeasure μ] (f : C_c(Plane × Plane, ℝ)) :
    Integrable f (μ.map pairSwapMeas) ∧
      ∫ p, f p ∂(μ.map pairSwapMeas) = ∫ p, pairSwapTest f p ∂μ := by
  have hLF : IsLocallyFiniteMeasure (μ.map pairSwapMeas) := by
    simpa only [pairSwapMeas, Homeomorph.toMeasurableEquiv_coe] using
      locallyFinite_map_homeomorph pairSwap μ
  let μ' : RandomMeasure.PositiveRadonMeasure (Plane × Plane) := ⟨μ.map pairSwapMeas, hLF⟩
  have hI : Integrable f (μ.map pairSwapMeas) := RandomMeasure.integrable_vagueTest μ' f
  refine ⟨hI, ?_⟩
  calc
    ∫ p, f p ∂(μ.map pairSwapMeas) = ∫ p, f (pairSwapMeas p) ∂μ :=
      integral_map pairSwapMeas.measurable.aemeasurable hI.aestronglyMeasurable
    _ = ∫ p, pairSwapTest f p ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact (pairSwapTest_apply f p).symm

/-- A common linear isometry transforms the smoothed product pairing by its pulled-back tests and mollifier. -/
theorem smoothedProductPairing_map_linearIsometry (R : Plane ≃ₗᵢ[ℝ] Plane)
    (μ ν : Measure (Plane × Plane)) [SFinite μ] [SFinite ν]
    (w : Plane → ℝ) (hw : Continuous w) (f : C_c(Plane × Plane, ℝ)) :
    smoothedProductPairing (μ.map (pairLinearIsometryMeas R))
      (fun x => w (R.symm x)) (ν.map (pairLinearIsometryMeas R)) f =
    smoothedProductPairing μ w ν (pairLinearIsometryTest R f) := by
  let e := pairLinearIsometryMeas R
  let E := e.prodCongr e
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ :=
    fun q => f (q.1.1, q.2.2) * w (R.symm (q.1.2 - q.2.1))
  have hmap : (μ.map e).prod (ν.map e) = (μ.prod ν).map E := by
    exact Measure.map_prod_map μ ν e.measurable e.measurable
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  unfold smoothedProductPairing
  rw [hmap]
  calc
    ∫ q, F q ∂(Measure.map E (μ.prod ν)) = ∫ q, F (E q) ∂(μ.prod ν) :=
      integral_map E.measurable.aemeasurable hFcont.measurable.aestronglyMeasurable
    _ = ∫ q, (pairLinearIsometryTest R f) (q.1.1, q.2.2) * w (q.1.2 - q.2.1)
        ∂(μ.prod ν) := by
      apply integral_congr_ae
      filter_upwards with q
      have hEapply : E q =
          ((R q.1.1, R q.1.2), (R q.2.1, R q.2.2)) := by
        change (e q.1, e q.2) = _
        rw [pairLinearIsometryMeas_apply, pairLinearIsometryMeas_apply]
      have hsub : R q.1.2 - R q.2.1 = R (q.1.2 - q.2.1) := by
        rw [← R.map_sub]
      rw [hEapply]
      dsimp [F]
      rw [hsub, R.symm_apply_apply, pairLinearIsometryTest_apply]

/-- Exchanging endpoints reverses the order of the smoothed product and reflects its mollifier. -/
theorem smoothedProductPairing_map_pairSwap
    (μ ν : Measure (Plane × Plane)) [SFinite μ] [SFinite ν] (w : Plane → ℝ)
    (hw : Continuous w) (f : C_c(Plane × Plane, ℝ)) :
    smoothedProductPairing (μ.map pairSwapMeas) (fun x => w (-x))
      (ν.map pairSwapMeas) f =
    smoothedProductPairing ν w μ (pairSwapTest f) := by
  let e := pairSwapMeas
  let E := e.prodCongr e
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ :=
    fun q => f (q.1.1, q.2.2) * w (-(q.1.2 - q.2.1))
  have hmap : (μ.map e).prod (ν.map e) = (μ.prod ν).map E :=
    Measure.map_prod_map μ ν e.measurable e.measurable
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  unfold smoothedProductPairing
  rw [hmap]
  calc
    ∫ q, F q ∂(Measure.map E (μ.prod ν)) = ∫ q, F (E q) ∂(μ.prod ν) :=
      integral_map E.measurable.aemeasurable hFcont.measurable.aestronglyMeasurable
    _ = ∫ q, (pairSwapTest f) (q.1.1, q.2.2) * w (q.1.2 - q.2.1) ∂(ν.prod μ) := by
      rw [← Measure.prod_swap]
      change (∫ q, (F ∘ E) q ∂Measure.map Prod.swap (ν.prod μ)) = _
      rw [integral_map measurable_swap.aemeasurable
        ((hFcont.measurable.comp E.measurable).aestronglyMeasurable)]
      apply integral_congr_ae
      filter_upwards with q
      have hEapply : E q.swap = ((q.2.2, q.2.1), (q.1.2, q.1.1)) := by
        change (e q.2, e q.1) = _
        rw [pairSwapMeas_apply, pairSwapMeas_apply]
      change F (E q.swap) = _
      rw [hEapply]
      dsimp [F]
      rw [pairSwapTest_apply]
      congr 1
      congr 1
      simp only [neg_sub]

/-- Exchanging endpoints preserves well-definedness of the reversed smoothed product. -/
theorem smoothedProductWellDefined_map_pairSwap
    (μ ν : Measure (Plane × Plane)) [SFinite μ] [SFinite ν] (w : Plane → ℝ)
    (hdef : SmoothedProductWellDefined ν w μ) :
    SmoothedProductWellDefined (μ.map pairSwapMeas) (fun x => w (-x))
      (ν.map pairSwapMeas) := by
  intro f
  let e := pairSwapMeas
  let E := e.prodCongr e
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ :=
    fun q => f (q.1.1, q.2.2) * w (-(q.1.2 - q.2.1))
  let G : ((Plane × Plane) × (Plane × Plane)) → ℝ :=
    fun q => (pairSwapTest f) (q.1.1, q.2.2) * w (q.1.2 - q.2.1)
  have hG : Integrable G (ν.prod μ) := hdef (pairSwapTest f)
  have hsource : Integrable (fun q => F (E q)) (μ.prod ν) := by
    have hswap : Integrable (G ∘ Prod.swap) (μ.prod ν) :=
      (Measure.measurePreserving_swap (μ := μ) (ν := ν)).integrable_comp_of_integrable hG
    apply hswap.congr
    filter_upwards [] with q
    have hEapply : E q = ((q.1.2, q.1.1), (q.2.2, q.2.1)) := by
      change (e q.1, e q.2) = _
      rw [pairSwapMeas_apply, pairSwapMeas_apply]
    rw [hEapply]
    dsimp [F, G]
    rw [pairSwapTest_apply]
    congr 1
    congr 1
    simp only [neg_sub]
  have hmap : (μ.map e).prod (ν.map e) = (μ.prod ν).map E :=
    Measure.map_prod_map μ ν e.measurable e.measurable
  rw [hmap]
  exact (integrable_map_equiv E F).2 hsource

/-- An integrable pairing transforms under endpoint exchange by swapping its tests. -/
theorem integrable_pairing_map_pairSwap (μ : Measure (Plane × Plane))
    (g g' : Plane → ℝ)
    (hI : Integrable (fun p : Plane × Plane => g' p.1 * g p.2) μ) :
    Integrable (fun p : Plane × Plane => g p.1 * g' p.2) (μ.map pairSwapMeas) ∧
      ∫ p, g p.1 * g' p.2 ∂(μ.map pairSwapMeas) =
        ∫ p, g' p.1 * g p.2 ∂μ := by
  let e := pairSwapMeas
  let F : Plane × Plane → ℝ := fun p => g p.1 * g' p.2
  have hsource : Integrable (fun p => F (e p)) μ := by
    apply hI.congr
    filter_upwards [] with p
    dsimp [F]
    rw [pairSwapMeas_apply]
    exact mul_comm _ _
  have htarget : Integrable F (μ.map e) := (integrable_map_equiv e F).2 hsource
  refine ⟨htarget, ?_⟩
  calc
    ∫ p, F p ∂(μ.map e) = ∫ p, F (e p) ∂μ :=
      integral_map e.measurable.aemeasurable htarget.aestronglyMeasurable
    _ = ∫ p, g' p.1 * g p.2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      dsimp [F]
      rw [pairSwapMeas_apply]
      exact mul_comm _ _

/-- Swapping endpoint tests preserves the moment-kernel pairing; `momentKernel_L2_form_bounded` supplies integrability. -/
theorem integral_momentKernel_pairSwap (n : ℕ) (hn : n ≤ 4) (θ h : ℝ)
    (hh : 0 < h) (g g' : Fin n → Plane → ℝ)
    (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    (∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
      (∏ i, g' i (x i)) * (DeltaBose.momentKernel n θ h x y).toReal *
        ∏ i, g i (y i)) =
    ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
      (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ h x y).toReal *
        ∏ i, g' i (y i) := by
  let F : DeltaBose.Configuration n → DeltaBose.Configuration n → ℝ := fun x y =>
    (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ h x y).toReal * ∏ i, g' i (y i)
  let G : DeltaBose.Configuration n → DeltaBose.Configuration n → ℝ := fun x y =>
    (∏ i, g' i (x i)) * (DeltaBose.momentKernel n θ h x y).toReal * ∏ i, g i (y i)
  have hF : MemLp (fun x : DeltaBose.Configuration n => ∏ i, g i (x i)) 2 :=
    Critical2DKPZ.SHF.Tsai.memLp_configuration_tensor g hg
  have hG : MemLp (fun x : DeltaBose.Configuration n => ∏ i, g' i (x i)) 2 :=
    Critical2DKPZ.SHF.Tsai.memLp_configuration_tensor g' hg'
  have hIF := (DeltaBose.momentKernel_L2_form_bounded n hn θ hh).choose_spec
    (fun x : DeltaBose.Configuration n => ∏ i, g i (x i))
    (fun x : DeltaBose.Configuration n => ∏ i, g' i (x i)) hF hG
  have hIG := (DeltaBose.momentKernel_L2_form_bounded n hn θ hh).choose_spec
    (fun x : DeltaBose.Configuration n => ∏ i, g' i (x i))
    (fun x : DeltaBose.Configuration n => ∏ i, g i (x i)) hG hF
  have hKernelSymm (x y : DeltaBose.Configuration n) :
      F y x = G x y := by
    dsimp [F, G]
    rw [DeltaBose.momentKernel_symm]
    ring
  calc
    (∫ x, ∫ y, G x y ∂(volume : Measure (DeltaBose.Configuration n))
        ∂(volume : Measure (DeltaBose.Configuration n))) =
      ∫ xy, G xy.1 xy.2 ∂((volume : Measure (DeltaBose.Configuration n)).prod volume) :=
        integral_integral hIG.1
    _ = ∫ xy, F xy.2 xy.1 ∂((volume : Measure (DeltaBose.Configuration n)).prod volume) := by
      apply integral_congr_ae
      filter_upwards [] with xy
      exact (hKernelSymm xy.1 xy.2).symm
    _ = ∫ xy, F xy.1 xy.2 ∂((volume : Measure (DeltaBose.Configuration n)).prod volume) := by
      exact integral_prod_swap (fun xy : DeltaBose.Configuration n ×
        DeltaBose.Configuration n => F xy.1 xy.2)
    _ = ∫ x, ∫ y, F x y ∂(volume : Measure (DeltaBose.Configuration n))
        ∂(volume : Measure (DeltaBose.Configuration n)) := (integral_integral hIF.1).symm

/-- Endpoint exchange preserves all dense-time SHF moment identities. -/
theorem momentClause_map_pairSwap {θ : ℝ} {D : Set ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)} (hZ : IsDenseSHF θ D P Z) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ s ∈ D, ∀ t ∈ D, s < t →
      ∀ g g' : Fin n → Plane → ℝ, (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
        (∀ᵐ ω ∂P, ∀ i, Integrable
          (fun p : Plane × Plane => g i p.1 * g' i p.2)
          ((Z s t ω).map pairSwapMeas)) ∧
        Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂
          ((Z s t ω).map pairSwapMeas)) P ∧
        ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂
          ((Z s t ω).map pairSwapMeas)) ∂P =
          ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
            (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
              ∏ i, g' i (y i) := by
  intro n hn hn4 s hs t ht hst g g' hg hg'
  have hsource := hZ.2.2.2 n hn hn4 s hs t ht hst g' g hg' hg
  rcases hsource with ⟨hInt, hProdInt, hMean⟩
  have hPairEq : (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂
      ((Z s t ω).map pairSwapMeas)) =ᵐ[P]
      fun ω => ∏ i, ∫ p, g' i p.1 * g i p.2 ∂Z s t ω := by
    filter_upwards [hInt] with ω hω
    apply Finset.prod_congr rfl
    intro i hi
    exact (integrable_pairing_map_pairSwap (Z s t ω) (g i) (g' i) (hω i)).2
  have hMean' : ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂
      ((Z s t ω).map pairSwapMeas)) ∂P =
      ∫ ω, ∏ i, (∫ p, g' i p.1 * g i p.2 ∂Z s t ω) ∂P :=
    integral_congr_ae hPairEq
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hInt] with ω hω
    intro i
    exact (integrable_pairing_map_pairSwap (Z s t ω) (g i) (g' i) (hω i)).1
  · exact hProdInt.congr hPairEq.symm
  · calc
      ∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂
          ((Z s t ω).map pairSwapMeas)) ∂P =
        ∫ ω, ∏ i, (∫ p, g' i p.1 * g i p.2 ∂Z s t ω) ∂P := hMean'
      _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, g' i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
            ∏ i, g i (y i) := hMean
      _ = ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
          (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
            ∏ i, g' i (y i) := integral_momentKernel_pairSwap n hn4 θ (t - s)
              (sub_pos.mpr hst) g g' hg hg'

/-- A common linear isometry preserves well-definedness of the smoothed product. -/
theorem smoothedProductWellDefined_map_linearIsometry
    (R : Plane ≃ₗᵢ[ℝ] Plane) (μ ν : Measure (Plane × Plane))
    [SFinite μ] [SFinite ν] (w : Plane → ℝ)
    (hdef : SmoothedProductWellDefined μ w ν) :
    SmoothedProductWellDefined (μ.map (pairLinearIsometryMeas R))
      (fun x => w (R.symm x)) (ν.map (pairLinearIsometryMeas R)) := by
  intro f
  let e := pairLinearIsometryMeas R
  let E := e.prodCongr e
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ :=
    fun q => f (q.1.1, q.2.2) * w (R.symm (q.1.2 - q.2.1))
  have hmap : (μ.map e).prod (ν.map e) = (μ.prod ν).map E := by
    exact Measure.map_prod_map μ ν e.measurable e.measurable
  have hsource : Integrable (fun q => F (E q)) (μ.prod ν) := by
    have h := hdef (pairLinearIsometryTest R f)
    apply h.congr
    filter_upwards [] with q
    have hEapply : E q =
        ((R q.1.1, R q.1.2), (R q.2.1, R q.2.2)) := by
      change (e q.1, e q.2) = _
      rw [pairLinearIsometryMeas_apply, pairLinearIsometryMeas_apply]
    have hsub : R q.1.2 - R q.2.1 = R (q.1.2 - q.2.1) := by
      rw [← R.map_sub]
    rw [hEapply]
    dsimp [F]
    rw [hsub, R.symm_apply_apply, pairLinearIsometryTest_apply]
  rw [hmap]
  exact (integrable_map_equiv E F).2 hsource

/-- Pushing a measurable random measure through a homeomorphism gives a measurable random measure. -/
theorem measurable_map_homeomorph {Ω X Y : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y] [BorelSpace Y]
    (e : X ≃ₜ Y) (F : Ω → Measure X) (hF : Measurable F) :
    Measurable (fun ω => (F ω).map e) := by
  exact (Measure.measurable_map e e.continuous.measurable).comp hF

/-- Pushing through a homeomorphism preserves almost-sure local finiteness. -/
theorem ae_locallyFinite_map_homeomorph {Ω X Y : Type*} [MeasurableSpace Ω]
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [OpensMeasurableSpace X] [OpensMeasurableSpace Y] [BorelSpace Y]
    (e : X ≃ₜ Y) (P : Measure Ω) (F : Ω → Measure X)
    (hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (F ω)) :
    ∀ᵐ ω ∂P, IsLocallyFiniteMeasure ((F ω).map e) := by
  filter_upwards [hLF] with ω hω
  exact @locallyFinite_map_homeomorph _ _ _ _ _ _ _ _ _ e (F ω) hω

/-- The common endpoint translation acts coordinatewise. -/
theorem pairTranslate_apply (z : Plane) (p : Plane × Plane) :
    pairTranslate z p = (p.1 + z, p.2 + z) := by
  change ((Homeomorph.addRight z) p.1, (Homeomorph.addRight z) p.2) = _
  simp only [Homeomorph.coe_addRight]

/-- The common endpoint translation acts coordinatewise as a measurable equivalence. -/
theorem pairTranslateMeas_apply (z : Plane) (p : Plane × Plane) :
    pairTranslateMeas z p = (p.1 + z, p.2 + z) := by
  change pairTranslate z p = _
  change ((Homeomorph.addRight z) p.1, (Homeomorph.addRight z) p.2) = _
  simp only [Homeomorph.coe_addRight]

/-- The common endpoint translation acts on a test by composition with the endpoint map. -/
theorem pairTranslateTest_apply (z : Plane) (f : C_c(Plane × Plane, ℝ))
    (p : Plane × Plane) : pairTranslateTest z f p = f (p.1 + z, p.2 + z) := by
  change f (pairTranslate z p) = _
  rw [pairTranslate_apply]

/-- A compact pairing against a translated measure is integrable and equals the translated test pairing. -/
theorem integral_pairTranslateTest_map (z : Plane)
    (μ : Measure (Plane × Plane)) [IsLocallyFiniteMeasure μ]
    (f : C_c(Plane × Plane, ℝ)) :
    Integrable f (μ.map (pairTranslateMeas z)) ∧
      ∫ p, f p ∂(μ.map (pairTranslateMeas z)) =
        ∫ p, pairTranslateTest z f p ∂μ := by
  have hLF : IsLocallyFiniteMeasure (μ.map (pairTranslateMeas z)) := by
    simpa only [pairTranslateMeas, Homeomorph.toMeasurableEquiv_coe] using
      locallyFinite_map_homeomorph (pairTranslate z) μ
  let μ' : RandomMeasure.PositiveRadonMeasure (Plane × Plane) :=
    ⟨μ.map (pairTranslateMeas z), hLF⟩
  have hI : Integrable f (μ.map (pairTranslateMeas z)) :=
    RandomMeasure.integrable_vagueTest μ' f
  refine ⟨hI, ?_⟩
  calc
    ∫ p, f p ∂(μ.map (pairTranslateMeas z)) =
      ∫ p, f (pairTranslateMeas z p) ∂μ :=
        integral_map (pairTranslateMeas z).measurable.aemeasurable hI.aestronglyMeasurable
    _ = ∫ p, pairTranslateTest z f p ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with p
      exact (pairTranslateTest_apply z f p).symm

/-- Common endpoint translation preserves measurability and almost-sure local finiteness. -/
theorem measurable_aeLocallyFinite_pairTranslate {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Ω → Measure (Plane × Plane))
    (hF : Measurable F) (hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (F ω))
    (z : Plane) :
    Measurable (fun ω => (F ω).map (pairTranslateMeas z)) ∧
      ∀ᵐ ω ∂P, IsLocallyFiniteMeasure ((F ω).map (pairTranslateMeas z)) := by
  refine ⟨?_, ?_⟩
  · simpa only [pairTranslateMeas, Homeomorph.toMeasurableEquiv_coe] using
      measurable_map_homeomorph (pairTranslate z) F hF
  · simpa only [pairTranslateMeas, Homeomorph.toMeasurableEquiv_coe] using
      ae_locallyFinite_map_homeomorph (pairTranslate z) P F hLF

/-- A common endpoint isometry preserves measurability and almost-sure local finiteness. -/
theorem measurable_aeLocallyFinite_pairLinearIsometry {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) (F : Ω → Measure (Plane × Plane))
    (hF : Measurable F) (hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (F ω))
    (R : Plane ≃ₗᵢ[ℝ] Plane) :
    Measurable (fun ω => (F ω).map (pairLinearIsometryMeas R)) ∧
      ∀ᵐ ω ∂P, IsLocallyFiniteMeasure ((F ω).map (pairLinearIsometryMeas R)) := by
  refine ⟨?_, ?_⟩
  · simpa only [pairLinearIsometryMeas, Homeomorph.toMeasurableEquiv_coe] using
      measurable_map_homeomorph (pairLinearIsometry R) F hF
  · simpa only [pairLinearIsometryMeas, Homeomorph.toMeasurableEquiv_coe] using
      ae_locallyFinite_map_homeomorph (pairLinearIsometry R) P F hLF

/-- Common endpoint translation preserves independence of random measures. -/
theorem iIndepFun_map_pairTranslate {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : ι → Ω → Measure (Plane × Plane)}
    (hF : iIndepFun F P) (z : Plane) :
    iIndepFun (fun i ω => (F i ω).map (pairTranslateMeas z)) P := by
  apply hF.comp (fun _ μ => μ.map (pairTranslateMeas z))
  intro i
  exact Measure.measurable_map _ (pairTranslateMeas z).measurable

/-- A common endpoint isometry preserves independence of random measures. -/
theorem iIndepFun_map_pairLinearIsometry {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : ι → Ω → Measure (Plane × Plane)}
    (hF : iIndepFun F P) (R : Plane ≃ₗᵢ[ℝ] Plane) :
    iIndepFun (fun i ω => (F i ω).map (pairLinearIsometryMeas R)) P := by
  apply hF.comp (fun _ μ => μ.map (pairLinearIsometryMeas R))
  intro i
  exact Measure.measurable_map _ (pairLinearIsometryMeas R).measurable

/-- Endpoint exchange preserves measurability and almost-sure local finiteness. -/
theorem measurable_aeLocallyFinite_pairSwap {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Ω → Measure (Plane × Plane))
    (hF : Measurable F) (hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (F ω)) :
    Measurable (fun ω => (F ω).map pairSwapMeas) ∧
      ∀ᵐ ω ∂P, IsLocallyFiniteMeasure ((F ω).map pairSwapMeas) := by
  refine ⟨?_, ?_⟩
  · simpa only [pairSwapMeas, Homeomorph.toMeasurableEquiv_coe] using
      measurable_map_homeomorph pairSwap F hF
  · simpa only [pairSwapMeas, Homeomorph.toMeasurableEquiv_coe] using
      ae_locallyFinite_map_homeomorph pairSwap P F hLF

/-- Endpoint exchange preserves independence of random measures. -/
theorem iIndepFun_map_pairSwap {Ω ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {F : ι → Ω → Measure (Plane × Plane)}
    (hF : iIndepFun F P) : iIndepFun (fun i ω => (F i ω).map pairSwapMeas) P := by
  apply hF.comp (fun _ μ => μ.map pairSwapMeas)
  intro i
  exact Measure.measurable_map _ pairSwapMeas.measurable

/-- Equality of random-measure laws transfers almost-sure local finiteness. -/
theorem ae_locallyFinite_of_map_eq {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [BorelSpace X] [T2Space X] [LocallyCompactSpace X]
    [SecondCountableTopology X] (P : Measure Ω) (P' : Measure Ω')
    (F : Ω → Measure X) (F' : Ω' → Measure X) (hF : Measurable F) (hF' : Measurable F')
    (hLaw : P.map F = P'.map F') (hLF : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (F ω)) :
    ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (F' ω) := by
  let K := RandomMeasure.vagueCompactExhaustion X
  let E := {μ : Measure X | IsLocallyFiniteMeasure μ}
  have hE : MeasurableSet E := by
    rw [show E = {μ | IsLocallyFiniteMeasure μ} by rfl]
    exact RandomMeasure.measurableSet_isLocallyFiniteMeasure K id measurable_id
  apply ae_iff.mpr
  change P' (F' ⁻¹' Eᶜ) = 0
  have hnull : P (F ⁻¹' Eᶜ) = 0 := by
    apply ae_iff.mp at hLF
    exact hLF
  have hEqCompl : P (F ⁻¹' Eᶜ) = P' (F' ⁻¹' Eᶜ) := by
    rw [← Measure.map_apply hF hE.compl, ← Measure.map_apply hF' hE.compl, hLaw]
  exact hEqCompl.symm.trans hnull

/-- Equality of finite-dimensional laws implies equality of single-interval laws. -/
theorem map_single_interval_eq_of_fdd
    {D : Set ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'}
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)}
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω))
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    (hmeasZ : Measurable (Z s t)) (hmeasZ' : Measurable (Z' s t)) :
    P.map (Z s t) = P'.map (Z' s t) := by
  have hvec := hfdd 1 (fun _ => s) (fun _ => t) (fun _ => ⟨hs, ht, hst⟩)
  have hEval := congrArg
    (fun ν : Measure (Fin 1 → Measure (Plane × Plane)) => ν.map (fun x => x 0)) hvec
  rw [Measure.map_map (measurable_pi_apply 0) (Measurable.of_eval fun _ => hmeasZ),
    Measure.map_map (measurable_pi_apply 0) (Measurable.of_eval fun _ => hmeasZ')]
    at hEval
  simpa only [Function.comp_def] using hEval

/-- Equality of finite-dimensional laws transfers almost-sure local finiteness to a measurable random-measure field. -/
theorem firstClause_of_fdd_eq {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z) (hmeas : ∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z' s t))
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω)) :
    ∀ s ∈ D, ∀ t ∈ D, s < t →
      Measurable (Z' s t) ∧ ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (Z' s t ω) := by
  intro s hs t ht hst
  have hmeasZ : Measurable (Z s t) := (hZ.1 s hs t ht hst).1
  have hLaw := map_single_interval_eq_of_fdd hfdd hs ht hst (hZ.1 s hs t ht hst).1
    (hmeas s hs t ht hst)
  exact ⟨hmeas s hs t ht hst,
    ae_locallyFinite_of_map_eq P P' (Z s t) (Z' s t) hmeasZ (hmeas s hs t ht hst)
      hLaw (hZ.1 s hs t ht hst).2⟩

/-- Equality of joint laws transfers independence of a finite family. -/
theorem iIndepFun_of_map_eq {Ω Ω' ι X : Type*} [Fintype ι]
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (F : ι → Ω → X) (G : ι → Ω' → X)
    (hF : ∀ i, Measurable (F i)) (hG : ∀ i, Measurable (G i))
    (hLaw : P.map (fun ω i => F i ω) = P'.map (fun ω i => G i ω))
    (hInd : iIndepFun F P) : iIndepFun G P' := by
  have hFaemeas (i : ι) : AEMeasurable (F i) P := (hF i).aemeasurable
  have hGaemeas (i : ι) : AEMeasurable (G i) P' := (hG i).aemeasurable
  have hFvec : Measurable (fun ω i => F i ω) := measurable_pi_iff.mpr hF
  have hGvec : Measurable (fun ω i => G i ω) := measurable_pi_iff.mpr hG
  have hMarg (i : ι) : P.map (F i) = P'.map (G i) := by
    have h := congrArg (Measure.map fun v : ι → X => v i) hLaw
    rw [Measure.map_map (measurable_pi_apply i) hFvec,
      Measure.map_map (measurable_pi_apply i) hGvec] at h
    simpa only [Function.comp_def] using h
  apply (iIndepFun_iff_map_fun_eq_pi_map hGaemeas).2
  calc
    P'.map (fun ω i => G i ω) = P.map (fun ω i => F i ω) := hLaw.symm
    _ = Measure.pi (fun i => P.map (F i)) :=
      (iIndepFun_iff_map_fun_eq_pi_map hFaemeas).mp hInd
    _ = Measure.pi (fun i => P'.map (G i)) := by
      congr 1
      funext i
      exact hMarg i

/-- Equality of finite-dimensional laws preserves independence of SHF increments on disjoint time intervals. -/
theorem independenceClause_of_fdd_eq {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z)
    (hmeas : ∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z' s t))
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω)) :
    ∀ (k : ℕ) (t : Fin (k + 1) → ℝ), StrictMono t → (∀ i, t i ∈ D) →
      iIndepFun (fun i : Fin k => Z' (t i.castSucc) (t i.succ)) P' := by
  intro k t hstrict ht
  let F : Fin k → Ω → Measure (Plane × Plane) :=
    fun i => Z (t i.castSucc) (t i.succ)
  let G : Fin k → Ω' → Measure (Plane × Plane) :=
    fun i => Z' (t i.castSucc) (t i.succ)
  have hF : ∀ i, Measurable (F i) := by
    intro i
    exact (hZ.1 _ (ht _) _ (ht _) (hstrict Fin.castSucc_lt_succ)).1
  have hG : ∀ i, Measurable (G i) := by
    intro i
    exact hmeas _ (ht _) _ (ht _) (hstrict Fin.castSucc_lt_succ)
  have hLaw : P.map (fun ω i => F i ω) = P'.map (fun ω i => G i ω) := by
    exact hfdd k (fun i => t i.castSucc) (fun i => t i.succ) fun i =>
      ⟨ht _, ht _, hstrict Fin.castSucc_lt_succ⟩
  exact iIndepFun_of_map_eq F G hF hG hLaw (hZ.2.2.1 k t hstrict ht)

/-- The difference of the real-valued positive-part and negative-part integral readouts. -/
def measureIntegralReadout {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (μ : Measure X) : ℝ :=
  (∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal -
    (∫⁻ x, ENNReal.ofReal (-f x) ∂μ).toReal

/-- The integral readout of a measurable real test is measurable in the measure. -/
theorem measurable_measureIntegralReadout {X : Type*} [MeasurableSpace X]
    {f : X → ℝ} (hf : Measurable f) :
    Measurable (measureIntegralReadout f : Measure X → ℝ) := by
  unfold measureIntegralReadout
  exact (Measure.measurable_lintegral hf.ennreal_ofReal).ennreal_toReal.sub
    (Measure.measurable_lintegral hf.neg.ennreal_ofReal).ennreal_toReal

/-- For an integrable test, the measure readout agrees with its integral. -/
theorem integral_eq_measureIntegralReadout {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (μ : Measure X) (hI : Integrable f μ) :
    ∫ x, f x ∂μ = measureIntegralReadout f μ := by
  exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part hI

/-- The extended nonnegative integral of the norm of a fixed test against a measure. -/
def measureEnormIntegralReadout {X : Type*} [MeasurableSpace X]
    (f : X → ℝ) (μ : Measure X) : ℝ≥0∞ :=
  ∫⁻ x, ‖f x‖ₑ ∂μ

/-- The norm-integral readout of a measurable test is measurable in the measure. -/
theorem measurable_measureEnormIntegralReadout {X : Type*} [MeasurableSpace X]
    {f : X → ℝ} (hf : Measurable f) :
    Measurable (measureEnormIntegralReadout f : Measure X → ℝ≥0∞) := by
  exact Measure.measurable_lintegral hf.enorm

/-- Equality of random-measure laws transfers almost-sure integrability of a test. -/
theorem ae_integrable_of_map_eq {Ω Ω' X : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X]
    {P : Measure Ω} {P' : Measure Ω'} {F : Ω → Measure X} {G : Ω' → Measure X}
    (f : X → ℝ) (hf : Measurable f) (hF : Measurable F) (hG : Measurable G)
    (hLaw : P.map F = P'.map G)
    (hI : ∀ᵐ ω ∂P, Integrable f (F ω)) :
    ∀ᵐ ω ∂P', Integrable f (G ω) := by
  let N : Measure X → ℝ≥0∞ := measureEnormIntegralReadout f
  have hN : Measurable N := measurable_measureEnormIntegralReadout hf
  have hLawN : P.map (fun ω => N (F ω)) = P'.map (fun ω => N (G ω)) := by
    calc
      P.map (fun ω => N (F ω)) = (P.map F).map N := by
        change P.map (N ∘ F) = _
        exact (Measure.map_map hN hF).symm
      _ = (P'.map G).map N := by rw [hLaw]
      _ = P'.map (fun ω => N (G ω)) := by
        change _ = P'.map (N ∘ G)
        exact Measure.map_map hN hG
  have hsource : ∀ᵐ ω ∂P, N (F ω) < ⊤ := by
    filter_upwards [hI] with ω hω
    exact (hasFiniteIntegral_iff_enorm.mp hω.2)
  have hsourceMap : ∀ᵐ r ∂P.map (fun ω => N (F ω)), r < ⊤ := by
    exact (ae_map_iff (μ := P) (f := fun ω => N (F ω))
      (hN.comp hF).aemeasurable
      (measurableSet_lt measurable_id measurable_const)).2 hsource
  have htargetMap : ∀ᵐ r ∂P'.map (fun ω => N (G ω)), r < ⊤ := by
    rw [← hLawN]
    exact hsourceMap
  have htarget : ∀ᵐ ω ∂P', N (G ω) < ⊤ := by
    exact (ae_map_iff (μ := P') (f := fun ω => N (G ω))
      (hN.comp hG).aemeasurable
      (measurableSet_lt measurable_id measurable_const)).1 htargetMap
  filter_upwards [htarget] with ω hω
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_enorm).2 hω

/-- Equality of random-measure laws transfers integrability and the value of finite pairing moments. -/
theorem finiteProductMoment_of_map_eq {Ω Ω' X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace X] [Fintype ι]
    {P : Measure Ω} {P' : Measure Ω'} {F : Ω → Measure X} {G : Ω' → Measure X}
    (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i)) (hF : Measurable F) (hG : Measurable G)
    (hLaw : P.map F = P'.map G)
    (hInt : ∀ᵐ ω ∂P, ∀ i, Integrable (f i) (F ω))
    (hMoment : Integrable (fun ω => ∏ i, ∫ x, f i x ∂F ω) P) :
    Integrable (fun ω => ∏ i, ∫ x, f i x ∂G ω) P' ∧
      ∫ ω, ∏ i, ∫ x, f i x ∂F ω ∂P =
        ∫ ω, ∏ i, ∫ x, f i x ∂G ω ∂P' := by
  classical
  let Q : Measure X → ι → ℝ := fun μ i => measureIntegralReadout (f i) μ
  have hQ : Measurable Q := by
    exact measurable_pi_iff.mpr fun i => measurable_measureIntegralReadout (hf i)
  let R : (ι → ℝ) → ℝ := fun v => ∏ i, v i
  have hR : Measurable R := by fun_prop
  let qF : Ω → ι → ℝ := fun ω => Q (F ω)
  let qG : Ω' → ι → ℝ := fun ω => Q (G ω)
  have hqF : Measurable qF := hQ.comp hF
  have hqG : Measurable qG := hQ.comp hG
  have hLawQ : P.map qF = P'.map qG := by
    calc
      P.map qF = (P.map F).map Q := by
        change P.map (Q ∘ F) = _
        exact (Measure.map_map hQ hF).symm
      _ = (P'.map G).map Q := by rw [hLaw]
      _ = P'.map qG := by
        change _ = P'.map (Q ∘ G)
        exact Measure.map_map hQ hG
  let rF : Ω → ℝ := fun ω => R (qF ω)
  let rG : Ω' → ℝ := fun ω => R (qG ω)
  have hrF : Measurable rF := hR.comp hqF
  have hrG : Measurable rG := hR.comp hqG
  have hLawR : P.map rF = P'.map rG := by
    calc
      P.map rF = (P.map qF).map R := by
        change P.map (R ∘ qF) = _
        exact (Measure.map_map hR hqF).symm
      _ = (P'.map qG).map R := by rw [hLawQ]
      _ = P'.map rG := by
        change _ = P'.map (R ∘ qG)
        exact Measure.map_map hR hqG
  have hEqF : (fun ω => ∏ i, ∫ x, f i x ∂F ω) =ᵐ[P] rF := by
    filter_upwards [hInt] with ω hω
    apply Finset.prod_congr rfl
    intro i hi
    exact integral_eq_measureIntegralReadout (f i) (F ω) (hω i)
  have hIntF : Integrable rF P := hMoment.congr hEqF
  have hIdF : AEStronglyMeasurable (fun x : ℝ => x) (P.map rF) :=
    measurable_id.aestronglyMeasurable
  have hIdG : AEStronglyMeasurable (fun x : ℝ => x) (P'.map rG) :=
    measurable_id.aestronglyMeasurable
  have hPushF : Integrable (fun x : ℝ => x) (P.map rF) := by
    have h := (integrable_map_measure hIdF hrF.aemeasurable).2 hIntF
    simpa only [Function.comp_def] using h
  have hPushG : Integrable (fun x : ℝ => x) (P'.map rG) := by
    rw [← hLawR]
    exact hPushF
  have hIntG : Integrable rG P' := by
    have h := (integrable_map_measure hIdG hrG.aemeasurable).1 hPushG
    simpa only [Function.comp_def] using h
  have hIntGAll : ∀ᵐ ω ∂P', ∀ i, Integrable (f i) (G ω) := by
    apply ae_all_iff.2
    intro i
    exact ae_integrable_of_map_eq (f i) (hf i) hF hG hLaw (ae_all_iff.mp hInt i)
  have hEqG : (fun ω => ∏ i, ∫ x, f i x ∂G ω) =ᵐ[P'] rG := by
    filter_upwards [hIntGAll] with ω hω
    apply Finset.prod_congr rfl
    intro i hi
    exact integral_eq_measureIntegralReadout (f i) (G ω) (hω i)
  have hActualG : Integrable (fun ω => ∏ i, ∫ x, f i x ∂G ω) P' := hIntG.congr hEqG.symm
  refine ⟨hActualG, ?_⟩
  calc
    ∫ ω, ∏ i, ∫ x, f i x ∂F ω ∂P = ∫ ω, rF ω ∂P := integral_congr_ae hEqF
    _ = ∫ x, x ∂P.map rF :=
      (integral_map hrF.aemeasurable measurable_id.aestronglyMeasurable).symm
    _ = ∫ x, x ∂P'.map rG := by rw [hLawR]
    _ = ∫ ω, rG ω ∂P' := integral_map hrG.aemeasurable measurable_id.aestronglyMeasurable
    _ = ∫ ω, ∏ i, ∫ x, f i x ∂G ω ∂P' := integral_congr_ae hEqG.symm

/-- Equality of finite-dimensional laws transfers the SHF moment identities for measurable L² endpoint tests. -/
theorem momentClause_of_fdd_eq_measurable {θ : ℝ} {D : Set ℝ} {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z)
    (hmeas : ∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z' s t))
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω)) :
    ∀ n : ℕ, 1 ≤ n → n ≤ 4 → ∀ s ∈ D, ∀ t ∈ D, s < t →
      ∀ g g' : Fin n → Plane → ℝ, (∀ i, MemLp (g i) 2) → (∀ i, MemLp (g' i) 2) →
      (∀ i, Measurable (g i)) → (∀ i, Measurable (g' i)) →
        (∀ᵐ ω ∂P', ∀ i, Integrable
          (fun p : Plane × Plane => g i p.1 * g' i p.2) (Z' s t ω)) ∧
        Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂Z' s t ω) P' ∧
        ∫ ω, ∏ i, ∫ p, g i p.1 * g' i p.2 ∂Z' s t ω ∂P' =
          ∫ x : DeltaBose.Configuration n, ∫ y : DeltaBose.Configuration n,
            (∏ i, g i (x i)) * (DeltaBose.momentKernel n θ (t - s) x y).toReal *
              ∏ i, g' i (y i) := by
  intro n hn hn4 s hs t ht hst g g' hg hg' hgm hgm'
  have hLaw := map_single_interval_eq_of_fdd hfdd hs ht hst
    (hZ.1 s hs t ht hst).1 (hmeas s hs t ht hst)
  let f : Fin n → Plane × Plane → ℝ := fun i p => g i p.1 * g' i p.2
  have hfm : ∀ i, Measurable (f i) := by
    intro i
    exact (hgm i).comp measurable_fst |>.mul ((hgm' i).comp measurable_snd)
  have hsource := hZ.2.2.2 n hn hn4 s hs t ht hst g g' hg hg'
  rcases hsource with ⟨hInt, hMoment, hMean⟩
  have hTransfer := finiteProductMoment_of_map_eq f hfm
    (hZ.1 s hs t ht hst).1 (hmeas s hs t ht hst) hLaw hInt hMoment
  have hIntTarget : ∀ᵐ ω ∂P', ∀ i, Integrable (f i) (Z' s t ω) := by
    apply ae_all_iff.2
    intro i
    exact ae_integrable_of_map_eq (f i) (hfm i) (hZ.1 s hs t ht hst).1
      (hmeas s hs t ht hst) hLaw (ae_all_iff.mp hInt i)
  refine ⟨?_, hTransfer.1, ?_⟩
  · simpa only [f] using hIntTarget
  · simpa only [f] using hTransfer.2.symm.trans hMean

/-- A null-set indicator evaluated at a single configuration coordinate vanishes almost everywhere. -/
theorem ae_indicator_null_comp_configOne {A : Set Plane}
    (_hA : MeasurableSet A) (hA0 : volume A = 0) :
    (fun x : DeltaBose.Configuration 1 => A.indicator (fun _ => (1 : ℝ)) (x 0)) =ᵐ[volume]
      0 := by
  have hAout : ∀ᵐ y ∂(volume : Measure Plane), y ∉ A := by
    apply ae_iff.mpr
    change volume {y : Plane | ¬ y ∉ A} = 0
    have hset : {y : Plane | ¬ y ∉ A} = A := by
      ext y
      simp
    rw [hset]
    exact hA0
  have hAfun : A.indicator (fun _ : Plane => (1 : ℝ)) =ᵐ[volume] 0 := by
    filter_upwards [hAout] with y hy
    simp only [Set.indicator_of_notMem hy, Pi.zero_apply]
  have hcoord : MeasurePreserving
      (fun x : DeltaBose.Configuration 1 => x 0)
      (volume : Measure (DeltaBose.Configuration 1)) volume := by
    convert (volume_preserving_funUnique (Fin 1) Plane) using 1
    · funext x
      simp
    · rfl
  have hpush : A.indicator (fun _ : Plane => (1 : ℝ)) =ᵐ[
      Measure.map (fun x : DeltaBose.Configuration 1 => x 0) volume] 0 := by
    rw [hcoord.map_eq]
    exact hAfun
  exact (ae_map_iff (μ := (volume : Measure (DeltaBose.Configuration 1)))
    (f := fun x : DeltaBose.Configuration 1 => x 0) hcoord.measurable.aemeasurable
    (by measurability)).1 hpush

/-- A null first-coordinate indicator makes the one-particle moment-kernel pairing zero. -/
theorem integral_momentKernel_one_indicator_null {θ h : ℝ} {A : Set Plane}
    (hA : MeasurableSet A) (hA0 : volume A = 0) (g' : Plane → ℝ) :
    (∫ x : DeltaBose.Configuration 1, ∫ y : DeltaBose.Configuration 1,
      A.indicator (fun _ => (1 : ℝ)) (x 0) *
        (DeltaBose.momentKernel 1 θ h x y).toReal * g' (y 0)) = 0 := by
  have hx := ae_indicator_null_comp_configOne hA hA0
  apply integral_eq_zero_of_ae
  filter_upwards [hx] with x hx
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  simp only [hx, Pi.zero_apply, zero_mul]

/-- Equality of finite-dimensional laws transfers almost-sure vanishing on null rectangles. -/
theorem ae_measureReal_null_rectangle_of_fdd {θ : ℝ} {D : Set ℝ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z)
    (hmeas : ∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z' s t))
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω))
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    {A B : Set Plane} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : volume A = 0) (hA2 : MemLp (A.indicator (fun _ => (1 : ℝ))) 2)
    (hB2 : MemLp (B.indicator (fun _ => (1 : ℝ))) 2) :
    ∀ᵐ ω ∂P', (Z' s t ω).real (A ×ˢ B) = 0 := by
  let g : Fin 1 → Plane → ℝ := fun _ => A.indicator (fun _ => (1 : ℝ))
  let g' : Fin 1 → Plane → ℝ := fun _ => B.indicator (fun _ => (1 : ℝ))
  have hgm : ∀ i, Measurable (g i) := by
    intro i
    exact Measurable.indicator measurable_const hA
  have hgm' : ∀ i, Measurable (g' i) := by
    intro i
    exact Measurable.indicator measurable_const hB
  have hg : ∀ i, MemLp (g i) 2 := fun _ => hA2
  have hg' : ∀ i, MemLp (g' i) 2 := fun _ => hB2
  have htransfer := momentClause_of_fdd_eq_measurable hZ hmeas hfdd
    1 (by norm_num) (by norm_num) s hs t ht hst g g' hg hg' hgm hgm'
  rcases htransfer with ⟨hInt, hMoment, hMean⟩
  let X : Ω' → ℝ := fun ω =>
    ∫ p : Plane × Plane, A.indicator (fun _ => (1 : ℝ)) p.1 *
      B.indicator (fun _ => (1 : ℝ)) p.2 ∂Z' s t ω
  have hIntX : ∀ᵐ ω ∂P', Integrable (fun p : Plane × Plane =>
      A.indicator (fun _ => (1 : ℝ)) p.1 * B.indicator (fun _ => (1 : ℝ)) p.2)
      (Z' s t ω) := by
    filter_upwards [hInt] with ω hω
    simpa only [g, g'] using hω 0
  have hMomentX : Integrable X P' := by
    simpa only [X, g, g', Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
      using hMoment
  have hnonneg : ∀ᵐ ω ∂P', 0 ≤ X ω := by
    filter_upwards [hIntX] with ω hω
    exact integral_nonneg_of_ae <| Eventually.of_forall fun p =>
      mul_nonneg (by by_cases hp : p.1 ∈ A <;> simp [hp])
        (by by_cases hp : p.2 ∈ B <;> simp [hp])
  have hMeanX : ∫ ω, X ω ∂P' = 0 := by
    calc
      ∫ ω, X ω ∂P' =
          ∫ ω, ∏ i : Fin 1, ∫ p : Plane × Plane,
            g i p.1 * g' i p.2 ∂Z' s t ω ∂P' := by
        apply integral_congr_ae
        filter_upwards [] with ω
        simp only [X, g, g', Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one]
      _ = ∫ x : DeltaBose.Configuration 1, ∫ y : DeltaBose.Configuration 1,
          (∏ i : Fin 1, g i (x i)) *
            (DeltaBose.momentKernel 1 θ (t - s) x y).toReal *
              ∏ i : Fin 1, g' i (y i) := hMean
      _ = 0 := by
        simpa [g, g', Finset.univ_unique] using
          integral_momentKernel_one_indicator_null (θ := θ) (h := t - s) hA hA0
            (B.indicator (fun _ => (1 : ℝ)))
  have hXzero : X =ᵐ[P'] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hMomentX).mp hMeanX
  filter_upwards [hXzero] with ω hω
  have hEq : X ω = (Z' s t ω).real (A ×ˢ B) := by
    dsimp [X]
    rw [← integral_indicator_one (μ := Z' s t ω) (hA.prod hB)]
    congr 1
    funext p
    by_cases hpA : p.1 ∈ A <;> by_cases hpB : p.2 ∈ B <;>
      simp [Set.indicator, hpA, hpB]
  rw [hEq] at hω
  exact hω

/-- The indicator of a null set belongs to L². -/
theorem memLp_indicator_null {A : Set Plane} (hA0 : volume A = 0) :
    MemLp (A.indicator (fun _ => (1 : ℝ))) 2 := by
  have hAout : ∀ᵐ x ∂(volume : Measure Plane), x ∉ A := by
    apply ae_iff.mpr
    change volume {x : Plane | ¬ x ∉ A} = 0
    have hset : {x : Plane | ¬ x ∉ A} = A := by
      ext x
      simp
    rw [hset]
    exact hA0
  have hEq : A.indicator (fun _ : Plane => (1 : ℝ)) =ᵐ[volume] 0 := by
    filter_upwards [hAout] with x hx
    simp only [Set.indicator_of_notMem hx, Pi.zero_apply]
  exact (memLp_congr_ae hEq).2 MemLp.zero

/-- Equality of finite-dimensional laws transfers the almost-sure null-coordinate measure property. -/
theorem ae_nullCoordinateMeasure_of_fdd {θ : ℝ} {D : Set ℝ}
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Z : ℝ → ℝ → Ω → Measure (Plane × Plane)}
    {Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)}
    (hZ : IsDenseSHF θ D P Z)
    (hmeas : ∀ s ∈ D, ∀ t ∈ D, s < t → Measurable (Z' s t))
    (hfdd : ∀ (k : ℕ) (s t : Fin k → ℝ),
      (∀ i, s i ∈ D ∧ t i ∈ D ∧ s i < t i) →
      P.map (fun ω i => Z (s i) (t i) ω) = P'.map (fun ω i => Z' (s i) (t i) ω))
    {s t : ℝ} (hs : s ∈ D) (ht : t ∈ D) (hst : s < t)
    {A : Set Plane} (hA : MeasurableSet A) (hA0 : volume A = 0) :
    ∀ᵐ ω ∂P', (Z' s t ω) (A ×ˢ Set.univ) = 0 := by
  let K := RandomMeasure.vagueCompactExhaustion Plane
  have hLF : ∀ᵐ ω ∂P', IsLocallyFiniteMeasure (Z' s t ω) :=
    (firstClause_of_fdd_eq hZ hmeas hfdd s hs t ht hst).2
  have hrect (m j : ℕ) :
      ∀ᵐ ω ∂P', (Z' s t ω).real ((A ∩ K m) ×ˢ K j) = 0 := by
    exact ae_measureReal_null_rectangle_of_fdd hZ hmeas hfdd hs ht hst
      (hA.inter (K.isCompact m).measurableSet) (K.isCompact j).measurableSet
      (measure_mono_null Set.inter_subset_left hA0) (memLp_indicator_null
        (measure_mono_null Set.inter_subset_left hA0))
      (memLp_indicator_const 2 (K.isCompact j).measurableSet 1 (Or.inr
        (K.isCompact j).measure_ne_top))
  have hrectZero (m j : ℕ) :
      ∀ᵐ ω ∂P', (Z' s t ω) ((A ∩ K m) ×ˢ K j) = 0 := by
    filter_upwards [hrect m j, hLF] with ω hreal hlocal
    have hfiniteComp : IsFiniteMeasureOnCompacts (Z' s t ω) :=
      @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure (Plane × Plane)
        inferInstance inferInstance
        (Z' s t ω) hlocal
    have hcompact : IsCompact (K m ×ˢ K j) := (K.isCompact m).prod (K.isCompact j)
    have hsubset : (A ∩ K m) ×ˢ K j ⊆ K m ×ˢ K j := by
      intro p hp
      exact ⟨hp.1.2, hp.2⟩
    have hfinite : (Z' s t ω) ((A ∩ K m) ×ˢ K j) < ∞ :=
      (measure_mono hsubset).trans_lt
        (hfiniteComp.lt_top_of_isCompact hcompact)
    exact (measureReal_eq_zero_iff hfinite.ne).mp hreal
  have hcover (x : Plane) : ∃ n, x ∈ K n := K.exists_mem x
  have hset : A ×ˢ Set.univ = ⋃ m, ⋃ j, (A ∩ K m) ×ˢ K j := by
    ext p
    constructor
    · rintro ⟨hpA, _⟩
      obtain ⟨m, hpm⟩ := hcover p.1
      obtain ⟨j, hpj⟩ := hcover p.2
      exact Set.mem_iUnion.mpr ⟨m, Set.mem_iUnion.mpr ⟨j, ⟨⟨hpA, hpm⟩, hpj⟩⟩⟩
    · intro hp
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hp
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hm
      exact ⟨hj.1.1, Set.mem_univ _⟩
  have hzero : ∀ᵐ ω ∂P', ∀ m j, (Z' s t ω) ((A ∩ K m) ×ˢ K j) = 0 := by
    apply ae_all_iff.2
    intro m
    apply ae_all_iff.2
    intro j
    exact hrectZero m j
  filter_upwards [hzero] with ω hω
  rw [hset, measure_iUnion_null_iff]
  intro m
  rw [measure_iUnion_null_iff]
  intro j
  exact hω m j


end Critical2DKPZ.SHF.Symmetries

end
