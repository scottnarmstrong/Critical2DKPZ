/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordDiagramL1
public import Critical2DKPZ.SHF.Moments.SinglePairWordDiagramEntrance
public import Critical2DKPZ.SHF.Moments.SinglePairWordDiagramPathIntegral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # The tested two-particle diagram and its continuum entrance -/

@[expose] public noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter DeltaBose
open scoped CompactlySupported Topology

private def diagramSwapHeads {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] : α × (β × γ) ≃ᵐ β × (α × γ) :=
  MeasurableEquiv.prodAssoc.symm |>.trans
    (MeasurableEquiv.prodCongr MeasurableEquiv.prodComm (MeasurableEquiv.refl γ)) |>.trans
    MeasurableEquiv.prodAssoc

private theorem preserving_diagramSwapHeads {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (κ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite κ] :
    MeasurePreserving diagramSwapHeads (μ.prod (ν.prod κ)) (ν.prod (μ.prod κ)) := by
  exact (measurePreserving_prodAssoc ν μ κ).comp
    (((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id κ)).comp
      (measurePreserving_prodAssoc μ ν κ).symm)

private def diagramCycleRight {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] : α × (β × γ) ≃ᵐ γ × (α × β) :=
  MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm

private theorem preserving_diagramCycleRight {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (κ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite κ] :
    MeasurePreserving diagramCycleRight (μ.prod (ν.prod κ)) (κ.prod (μ.prod ν)) := by
  exact (Measure.measurePreserving_swap (μ := μ.prod ν) (ν := κ)).comp
    (measurePreserving_prodAssoc μ ν κ).symm

private def diagramShuffle {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace δ] : (α × β) × (γ × δ) ≃ᵐ (α × γ) × (β × δ) :=
  MeasurableEquiv.prodAssoc |>.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl α) diagramSwapHeads) |>.trans
    MeasurableEquiv.prodAssoc.symm

private theorem preserving_diagramShuffle {α β γ δ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]
    (μ : Measure α) (ν : Measure β) (κ : Measure γ) (τ : Measure δ)
    [SFinite μ] [SFinite ν] [SFinite κ] [SFinite τ] :
    MeasurePreserving diagramShuffle ((μ.prod ν).prod (κ.prod τ))
      ((μ.prod κ).prod (ν.prod τ)) := by
  exact (measurePreserving_prodAssoc μ κ (ν.prod τ)).symm.comp
    (((MeasurePreserving.id μ).prod (preserving_diagramSwapHeads ν κ τ)).comp
      (measurePreserving_prodAssoc μ ν (κ.prod τ)))

private def diagramEntranceSplit :
    (ℝ × (Plane × (Plane × Plane))) ≃ᵐ (Plane × Plane) × (ℝ × Plane) :=
  diagramSwapHeads |>.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Plane) diagramCycleRight) |>.trans
    MeasurableEquiv.prodAssoc.symm

private theorem preserving_diagramEntranceSplit (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving diagramEntranceSplit
      (μ.prod ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume)))
      (((volume : Measure Plane).prod volume).prod (μ.prod (volume : Measure Plane))) := by
  exact (measurePreserving_prodAssoc (volume : Measure Plane) volume
    (μ.prod (volume : Measure Plane))).symm.comp
      (((MeasurePreserving.id (volume : Measure Plane)).prod
        (preserving_diagramCycleRight μ (volume : Measure Plane) volume)).comp
          (preserving_diagramSwapHeads μ (volume : Measure Plane)
            ((volume : Measure Plane).prod volume)))

private def diagramClockRegroup : (ℝ × Plane) × ℝ ≃ᵐ ℝ × (ℝ × Plane) :=
  MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm)

private theorem preserving_diagramClockRegroup (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving diagramClockRegroup
      ((μ.prod (volume : Measure Plane)).prod (volume : Measure ℝ))
      (μ.prod ((volume : Measure ℝ).prod (volume : Measure Plane))) := by
  exact ((MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := (volume : Measure Plane)) (ν := (volume : Measure ℝ)))).comp
      (measurePreserving_prodAssoc μ (volume : Measure Plane) (volume : Measure ℝ))

private def diagramPathRegroup :
    ((ℝ × (Plane × (Plane × Plane))) × (ℝ × (Plane × Plane))) ≃ᵐ
      ((Plane × Plane) × (Plane × Plane)) × (ℝ × (ℝ × Plane)) :=
  (MeasurableEquiv.prodCongr diagramEntranceSplit
    (MeasurableEquiv.refl (ℝ × (Plane × Plane)))) |>.trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ((Plane × Plane) × (ℝ × Plane)))
        MeasurableEquiv.prodComm) |>.trans diagramShuffle |>.trans
          (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ((Plane × Plane) × (Plane × Plane)))
            diagramClockRegroup)

private theorem preserving_diagramPathRegroup (μ : Measure ℝ) [SFinite μ] :
    MeasurePreserving diagramPathRegroup
      ((μ.prod ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume))).prod
        ((volume : Measure ℝ).prod ((volume : Measure Plane).prod volume)))
      ((((volume : Measure Plane).prod volume).prod ((volume : Measure Plane).prod volume)).prod
        (μ.prod ((volume : Measure ℝ).prod (volume : Measure Plane)))) := by
  let P : Measure Plane := volume
  let Q := P.prod P
  have hP : SFinite P := inferInstanceAs (SFinite (volume : Measure Plane))
  have hQ : SFinite Q := by dsimp [Q, P]; infer_instance
  exact ((MeasurePreserving.id (Q.prod Q)).prod (preserving_diagramClockRegroup μ)).comp
    ((preserving_diagramShuffle Q (μ.prod P) Q (volume : Measure ℝ)).comp
      (((MeasurePreserving.id (Q.prod (μ.prod P))).prod
        (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := Q))).comp
          ((preserving_diagramEntranceSplit μ).prod
            (MeasurePreserving.id ((volume : Measure ℝ).prod Q)))))

private def diagramClockDensity (θ T : ℝ) (x y : Configuration 2)
    (p : ℝ × (ℝ × Plane)) : ℝ :=
  {p : ℝ × (ℝ × Plane) | 0 < p.2.1 ∧ p.2.1 < T - p.1}.indicator
    (fun p => 4 * Real.pi *
      (heatKernel p.1 (p.2.2 - x 0) * heatKernel p.1 (p.2.2 - x 1)) *
      (scalarDensity θ p.2.1 *
        (heatKernel (2 * (T - p.1 - p.2.1)) (y 1 - y 0) *
          heatKernel ((T - p.1) / 2) ((1 / 2 : ℝ) • (y 0 + y 1) - p.2.2)))) p

private theorem measurable_diagramClockDensity (θ T : ℝ) (x y : Configuration 2) :
    Measurable (diagramClockDensity θ T x y) := by
  have hρ : Measurable (fun p : ℝ × (ℝ × Plane) => scalarDensity θ p.2.1) :=
    measurable_scalarDensity.comp (measurable_const.prodMk measurable_snd.fst)
  have hh : Measurable (fun p : ℝ × Plane => heatKernel p.1 p.2) := by
    unfold heatKernel
    fun_prop
  have hs : MeasurableSet {p : ℝ × (ℝ × Plane) | 0 < p.2.1 ∧ p.2.1 < T - p.1} :=
    ((isOpen_lt continuous_const continuous_snd.fst).inter
      (isOpen_lt continuous_snd.fst (continuous_const.sub continuous_fst))).measurableSet
  apply Measurable.indicator _ hs
  exact ((measurable_const.mul
    ((hh.comp (measurable_fst.prodMk (measurable_snd.snd.sub measurable_const))).mul
      (hh.comp (measurable_fst.prodMk (measurable_snd.snd.sub measurable_const))))).mul
    (hρ.mul ((hh.comp (show Measurable (fun p : ℝ × (ℝ × Plane) =>
      (2 * (T - p.1 - p.2.1), y 1 - y 0)) by fun_prop)).mul
      (hh.comp (show Measurable (fun p : ℝ × (ℝ × Plane) =>
        ((T - p.1) / 2, (1 / 2 : ℝ) • (y 0 + y 1) - p.2.2)) by fun_prop)))))

private theorem diagramClockDensity_interior (θ T : ℝ) (x y : Configuration 2)
    (r v : ℝ) (z : Plane) (hv : 0 < v) (hvT : v < T - r) :
    diagramClockDensity θ T x y (r, v, z) = 4 * Real.pi *
      ((heatKernel r (z - x 0) * heatKernel r (z - x 1)) *
        pairTwoFutureSpatialProfile θ (T - r) v z y) := by
  rw [diagramClockDensity, Set.indicator_of_mem (show (r, v, z) ∈
    {p : ℝ × (ℝ × Plane) | 0 < p.2.1 ∧ p.2.1 < T - p.1} from ⟨hv, hvT⟩),
    pairTwoFutureSpatialProfile_eq_centerGap hv hvT]
  dsimp only
  ring

private theorem diagramClockDensity_lintegral (θ T : ℝ) (x y : Configuration 2) :
    diagramKernel θ [pairTwo] T x y =
      ∫⁻ p, ENNReal.ofReal (diagramClockDensity θ T x y p)
        ∂((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
          ((volume : Measure ℝ).prod (volume : Measure Plane)) := by
  rw [pairTwo_diagram_eq_entrance_futureSpatialProfile,
    lintegral_prod _ (measurable_diagramClockDensity θ T x y).ennreal_ofReal.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  have hm : Measurable (fun p : ℝ × Plane => diagramClockDensity θ T x y (r, p)) :=
    (measurable_diagramClockDensity θ T x y).comp (measurable_const.prodMk measurable_id)
  rw [lintegral_prod _ hm.ennreal_ofReal.aemeasurable]
  have he : (fun v => ∫⁻ z : Plane, ENNReal.ofReal (diagramClockDensity θ T x y (r, v, z))) =
      (Set.Ioo 0 (T - r)).indicator (fun v => ENNReal.ofReal (4 * Real.pi *
        (∫ z : Plane, (heatKernel r (z - x 0) * heatKernel r (z - x 1)) *
          pairTwoFutureSpatialProfile θ (T - r) v z y))) := by
    funext v
    by_cases hv : v ∈ Set.Ioo 0 (T - r)
    · rw [Set.indicator_of_mem hv]
      simp_rw [diagramClockDensity_interior θ T x y r v _ hv.1 hv.2]
      rw [← integral_const_mul]
      apply (ofReal_integral_eq_lintegral_ofReal
        ((pairTwo_entrance_futureSpatialProfile_integral θ hr.1 hr.2 hv.1 hv.2 x y).1.const_mul
          (4 * Real.pi)) _).symm
      exact Eventually.of_forall fun z => mul_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (heatKernel_nonneg hr.1.le _) (heatKernel_nonneg hr.1.le _))
          (pairTwoFutureSpatialProfile_nonneg θ hv.1 hv.2 z y))
    · simp only [Set.indicator_of_notMem hv]
      have hz (z : Plane) : diagramClockDensity θ T x y (r, v, z) = 0 :=
        by
          apply Set.indicator_of_notMem
          exact hv
      simp only [hz, ENNReal.ofReal_zero, lintegral_zero]
  rw [he, lintegral_indicator measurableSet_Ioo]

private theorem diagram_toReal_eq_clockIntegral (θ T : ℝ) (x y : Configuration 2) :
    (diagramKernel θ [pairTwo] T x y).toReal =
      ∫ p, diagramClockDensity θ T x y p
        ∂((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
          ((volume : Measure ℝ).prod (volume : Measure Plane)) := by
  rw [diagramClockDensity_lintegral]
  rw [← integral_toReal (measurable_diagramClockDensity θ T x y).ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (measurable_diagramClockDensity θ T x y).ennreal_ofReal.ennreal_toReal
    (measurable_diagramClockDensity θ T x y))).mpr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact Eventually.of_forall fun p => by
    rw [ENNReal.toReal_ofReal]
    by_cases hv : 0 < p.1 ∧ p.1 < T - r
    · rw [diagramClockDensity_interior θ T x y r p.1 p.2 hv.1 hv.2]
      exact mul_nonneg (by positivity)
        (mul_nonneg (mul_nonneg (heatKernel_nonneg hr.1.le _) (heatKernel_nonneg hr.1.le _))
          (pairTwoFutureSpatialProfile_nonneg θ hv.1 hv.2 _ _))
    · have hz : diagramClockDensity θ T x y (r, p) = 0 := by
        apply Set.indicator_of_notMem
        exact hv
      exact hz.symm.le

private def diagramRegroupedPath (θ T : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (p : ((Plane × Plane) × (Plane × Plane)) × (ℝ × (ℝ × Plane))) : ℝ :=
  pairTwoContinuumDiagramPath θ T φ (diagramPathRegroup.symm p)

private theorem diagramRegroupedPath_eq (θ T : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (a b c d : Plane) (r v : ℝ) (z : Plane) :
    (φ 0 (a, c) * φ 1 (b, d)) * diagramClockDensity θ T ![a, b] ![c, d] (r, v, z) =
      (4 * Real.pi) * diagramRegroupedPath θ T φ (((a, b), (c, d)), (r, v, z)) := by
  have he : diagramPathRegroup.symm (((a, b), (c, d)), (r, v, z)) =
      ((r, (a, (z, b))), (v, (c, d))) := rfl
  simp only [diagramRegroupedPath, he, pairTwoContinuumDiagramPath, pairTwoFutureDensity]
  by_cases hv : v ∈ Set.Ioo 0 (T - r)
  · rw [diagramClockDensity_interior θ T ![a, b] ![c, d] r v z hv.1 hv.2,
      Set.indicator_of_mem (show (v, (c, d)) ∈ Set.Ioo 0 (T - r) ×ˢ Set.univ from
        ⟨hv, Set.mem_univ _⟩)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hh : heatKernel r (b - z) = heatKernel r (z - b) := by
      rw [← neg_sub z b, heatKernel_neg]
    rw [hh]
    ring
  · have hd : diagramClockDensity θ T ![a, b] ![c, d] (r, v, z) = 0 := by
      apply Set.indicator_of_notMem
      exact hv
    rw [hd, Set.indicator_of_notMem (show (v, (c, d)) ∉ Set.Ioo 0 (T - r) ×ˢ Set.univ
      from fun h => hv h.1)]
    ring

private theorem integrable_diagramRegroupedPath (θ T : ℝ) (hT : 0 < T)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    Integrable (diagramRegroupedPath θ T φ)
      ((((volume : Measure Plane).prod volume).prod ((volume : Measure Plane).prod volume)).prod
        (((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
          ((volume : Measure ℝ).prod (volume : Measure Plane)))) := by
  have hp := MeasurePreserving.symm diagramPathRegroup
    (preserving_diagramPathRegroup ((volume : Measure ℝ).restrict (Set.Ioo 0 T)))
  exact hp.integrable_comp_of_integrable (integrable_pairTwoContinuumDiagramPath θ T hT φ)

private theorem tested_diagram_pair_eq (θ T : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (X Y : Plane × Plane) :
    (φ 0 (X.1, Y.1) * φ 1 (X.2, Y.2)) *
      (diagramKernel θ [pairTwo] T ![X.1, X.2] ![Y.1, Y.2]).toReal =
    (4 * Real.pi) * (∫ p, diagramRegroupedPath θ T φ ((X, Y), p)
      ∂((volume : Measure ℝ).restrict (Set.Ioo 0 T)).prod
        ((volume : Measure ℝ).prod (volume : Measure Plane))) := by
  rw [diagram_toReal_eq_clockIntegral, ← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun p => diagramRegroupedPath_eq θ T φ X.1 X.2 Y.1 Y.2 p.1 p.2.1 p.2.2

/-- The tested single-pair diagram equals the full continuum entrance.
Joint integrability is supplied by `integrable_tested_pairTwo_diagram` and
`integrable_pairTwoContinuumDiagramPath`. -/
theorem tested_pairTwo_diagram_eq_continuum_entrance
    (θ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    (∫ x : Configuration 2, ∫ y : Configuration 2,
      (∏ i, φ i (x i, y i)) * (diagramKernel θ [pairTwo] T x y).toReal) =
    (1 / 4 : ℝ) * (∫ p : ℝ × (Plane × (Plane × Plane)),
      (heatKernel p.1 (p.2.2.1 - p.2.1) * heatKernel p.1 (p.2.2.2 - p.2.2.1)) *
        pairTwoContinuumFuture θ (T - p.1) φ ![p.2.1, p.2.2.2] p.2.2.1
      ∂(volume.restrict (Set.Ioo 0 T)).prod
        ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume))) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 T)
  let P : Measure Plane := volume
  let Q : Measure (Plane × Plane) := P.prod P
  have hP : SFinite P := inferInstanceAs (SFinite (volume : Measure Plane))
  have hQ : SFinite Q := by dsimp [Q, P]; infer_instance
  have hμ : SFinite μ := inferInstanceAs (SFinite (volume.restrict (Set.Ioo 0 T)))
  let f : (Plane × Plane) × (Plane × Plane) → ℝ := fun q =>
    (φ 0 (q.1.1, q.2.1) * φ 1 (q.1.2, q.2.2)) *
      (diagramKernel θ [pairTwo] T ![q.1.1, q.1.2] ![q.2.1, q.2.2]).toReal
  let E : (Configuration 2 × Configuration 2) ≃ᵐ ((Plane × Plane) × (Plane × Plane)) :=
    MeasurableEquiv.prodCongr MeasurableEquiv.finTwoArrow MeasurableEquiv.finTwoArrow
  have hE : MeasurePreserving E (volume.prod volume) (Q.prod Q) :=
    (volume_preserving_finTwoArrow Plane).prod (volume_preserving_finTwoArrow Plane)
  have he : (∫ x : Configuration 2, ∫ y : Configuration 2,
      (∏ i, φ i (x i, y i)) * (diagramKernel θ [pairTwo] T x y).toReal) =
      ∫ q, f q ∂Q.prod Q := by
    rw [← integral_prod _ (integrable_tested_pairTwo_diagram θ hT φ)]
    convert hE.integral_comp' f using 1
    congr 1
    funext q
    simp only [f, Fin.prod_univ_two]
    change _ = (φ 0 (q.1 0, q.2 0) * φ 1 (q.1 1, q.2 1)) *
      (diagramKernel θ [pairTwo] T ![q.1 0, q.1 1] ![q.2 0, q.2 1]).toReal
    congr 2
  rw [he, pairTwo_continuum_entrance_eq_diagramPath_integral θ T hT φ]
  have hreg := preserving_diagramPathRegroup μ
  have hi := integrable_diagramRegroupedPath θ T hT φ
  have hf : (∫ q, f q ∂Q.prod Q) = (4 * Real.pi) *
      (∫ q, diagramRegroupedPath θ T φ q
        ∂(Q.prod Q).prod (μ.prod ((volume : Measure ℝ).prod P))) := by
    rw [integral_prod _ hi, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun q => tested_diagram_pair_eq θ T φ q.1 q.2
  rw [hf]
  have hp := (MeasurePreserving.symm diagramPathRegroup hreg).integral_comp'
    (pairTwoContinuumDiagramPath θ T φ)
  change (4 * Real.pi) * (∫ q, diagramRegroupedPath θ T φ q
      ∂(Q.prod Q).prod (μ.prod ((volume : Measure ℝ).prod P))) = _
  rw [show (∫ q, diagramRegroupedPath θ T φ q
      ∂(Q.prod Q).prod (μ.prod ((volume : Measure ℝ).prod P))) = _ from hp]
  ring

end Critical2DKPZ.SHF.Moments
