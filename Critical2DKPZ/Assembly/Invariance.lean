/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Assembly.RegularizedInvariance
public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
public import Critical2DKPZ.RandomMeasure.GeneralRandom
public import Critical2DKPZ.CovarianceKernel.RegularizedSpecification
import Mathlib.Tactic

/-! # Invariance of the critical KPZ process under translations, rotations and scaling -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BoundedContinuousFunction ENNReal Topology

universe u v

namespace Critical2DKPZ.Assembly

open Critical2DKPZ.LocalSobolev Critical2DKPZ.SHF.Limit

/-- The flat centring constant `E log 𝒵_{t-δ}(1, g_δ)` of the regularized field. -/
private def cen {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) : ℝ :=
  ∫ ω, Real.log (shfPairing Z 0 (t - δ) (fun _ => 1) (fun y => heatKernel δ y) ω) ∂P

/-- The logarithm of the heat pairing of a measure on the plane pair with the second marginal. -/
private def logPair (δ : ℝ) (μ : Measure (Plane × Plane)) : ℝ :=
  Real.log (∫ p, (1 : ℝ) * heatKernel δ p.2 ∂μ)

/-- The regularized field, tested against `φ`, as a deterministic functional of the measure
`Z 0 (t - δ)`, with centring constant `c`. -/
private def fieldFn (δ c : ℝ) (φ : TestFn) (μ : Measure (Plane × Plane)) : ℝ :=
  ∫ x, φ x * (Real.log (∫ p, heatKernel δ (p.1 - x) * 1 ∂(μ.map Prod.swap)) - c)

/-- The vector of tested regularized fields as a functional of a vector of measures. -/
private def fieldVec (δ : ℝ) {k : ℕ} (c : Fin k → ℝ) (φ : Fin k → TestFn)
    (m : Fin k → Measure (Plane × Plane)) : Fin k → ℝ :=
  fun i => fieldFn δ (c i) (φ i) (m i)

/-- `logPair` is a measurable function of the measure. -/
private theorem measurable_logPair (δ : ℝ) (hδ : 0 < δ) : Measurable (logPair δ) := by
  have hg : Measurable (fun p : Plane × Plane => heatKernel δ p.2) :=
    (measurable_heatKernel δ).comp measurable_snd
  have hF : Measurable (fun p : Plane × Plane => ENNReal.ofReal (heatKernel δ p.2)) :=
    ENNReal.measurable_ofReal.comp hg
  have hlin := Measure.measurable_lintegral hF
  have heq : logPair δ =
      fun μ => Real.log ((∫⁻ p, ENNReal.ofReal (heatKernel δ p.2) ∂μ).toReal) := by
    funext μ
    unfold logPair
    congr 1
    simp only [one_mul]
    exact integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun p => heatKernel_nonneg hδ.le _) hg.aestronglyMeasurable
  rw [heq]
  exact Real.measurable_log.comp hlin.ennreal_toReal

/-- The tested regularized field is `fieldFn` of the measure `Z 0 (t - δ) ω`. -/
private theorem regField_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (φ : TestFn) (ω : Ω) :
    ∫ x, φ x * kpzRegularized P Z t δ 0 x ω =
      fieldFn δ (cen P Z t δ) φ (Z 0 (t - δ) ω) := by
  unfold fieldFn kpzRegularized cen
  congr 1
  funext x
  congr 2
  have hm : Measurable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * 1) :=
    ((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).mul measurable_const
  rw [integral_map measurable_swap.aemeasurable hm.aestronglyMeasurable]
  congr 2
  simp [shfPairing]

/-- A measure on the space of measures that is a.s. locally finite makes `fieldFn` a.e.
measurable. -/
private theorem aemeasurable_fieldFn (ν : Measure (Measure (Plane × Plane))) [SFinite ν]
    (hloc : ∀ᵐ μ ∂ν, IsLocallyFiniteMeasure μ) {δ : ℝ} (hδ : 0 < δ) (c : ℝ) (φ : TestFn) :
    AEMeasurable (fieldFn δ c φ) ν := by
  have hloc' : ∀ᵐ μ ∂ν, IsLocallyFiniteMeasure (μ.map Prod.swap) := by
    filter_upwards [hloc] with μ hμ
    exact CovarianceKernel.locallyFinite_map_homeomorph (Homeomorph.prodComm Plane Plane) μ hμ
  exact JointConvergence.aemeasurable_integral_log_heatPairing ν
    (fun μ => μ.map Prod.swap) (Measure.measurable_map _ measurable_swap) hloc' δ c hδ
    (fun _ => 1) φ measurable_const (fun _ => zero_le_one) φ.continuous.measurable

/-- Almost sure local finiteness of a random measure passes to its law. -/
private theorem ae_locallyFinite_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : Ω → Measure (Plane × Plane)) (hM : Measurable M)
    (h : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (M ω)) :
    ∀ᵐ μ ∂(P.map M), IsLocallyFiniteMeasure μ := by
  have hS := RandomMeasure.measurableSet_isLocallyFiniteMeasure
    (CompactExhaustion.choice (Plane × Plane)) (id : Measure (Plane × Plane) → _) measurable_id
  exact (ae_map_iff hM.aemeasurable hS).2 h

/-- One tested regularized field is a.e. measurable. -/
private theorem aemeasurable_regField (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {t δ : ℝ} (hδ : 0 < δ) (hδt : δ < t) (φ : TestFn) :
    AEMeasurable (fun ω => ∫ x, φ x * kpzRegularized P Z t δ 0 x ω) P := by
  have hT : 0 < t - δ := sub_pos.2 hδt
  have hm : Measurable (Z 0 (t - δ)) := hZ.1 0 (t - δ) le_rfl hT
  have hloc := ae_locallyFinite_map P (Z 0 (t - δ)) hm
    ((hZ.2.1 0 (t - δ) le_rfl hT).mono fun ω h => h.1)
  have h := aemeasurable_fieldFn (P.map (Z 0 (t - δ))) hloc hδ (cen P Z t δ) φ
  exact (h.comp_aemeasurable hm.aemeasurable).congr
    (Eventually.of_forall fun ω => (regField_eq P Z t δ φ ω).symm)

/-- The vector of measures `(Z 0 (t i - δ))_i`. -/
private def measVec {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (δ : ℝ) {k : ℕ}
    (t : Fin k → ℝ) (ω : Ω) : Fin k → Measure (Plane × Plane) :=
  fun i => Z 0 (t i - δ) ω

/-- The vector of measures is measurable. -/
private theorem measurable_measVec (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {δ : ℝ} {k : ℕ} (t : Fin k → ℝ) (hδt : ∀ i, δ < t i) :
    Measurable (measVec Z δ t) :=
  Measurable.of_eval fun i => hZ.1 0 (t i - δ) le_rfl (sub_pos.2 (hδt i))

/-- `fieldVec` is a.e. measurable for the law of the vector of measures. -/
private theorem aemeasurable_fieldVec (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) {δ : ℝ} (hδ : 0 < δ) {k : ℕ} (t : Fin k → ℝ)
    (hδt : ∀ i, δ < t i) (c : Fin k → ℝ) (φ : Fin k → TestFn) :
    AEMeasurable (fieldVec δ c φ) (P.map (measVec Z δ t)) := by
  have hTm := measurable_measVec ϑ P Z hZ t hδt
  refine AEMeasurable.of_eval fun i => ?_
  have hmi : Measurable (Z 0 (t i - δ)) := hZ.1 0 (t i - δ) le_rfl (sub_pos.2 (hδt i))
  have hmap : (P.map (measVec Z δ t)).map (fun m => m i) = P.map (Z 0 (t i - δ)) :=
    Measure.map_map (measurable_pi_apply i) hTm
  have hloc := ae_locallyFinite_map P (Z 0 (t i - δ)) hmi
    ((hZ.2.1 0 (t i - δ) le_rfl (sub_pos.2 (hδt i))).mono fun ω h => h.1)
  have h := aemeasurable_fieldFn ((P.map (measVec Z δ t)).map (fun m => m i))
    (by rw [hmap]; exact hloc) hδ (c i) (φ i)
  exact h.comp_aemeasurable (measurable_pi_apply i).aemeasurable

/-- The vector of tested fields is `fieldVec` of the vector of measures. -/
private theorem regVec_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (δ : ℝ) {k : ℕ} (t : Fin k → ℝ)
    (φ : Fin k → TestFn) :
    (fun ω i => ∫ x, φ i x * kpzRegularized P Z (t i) δ 0 x ω) =
      fun ω => fieldVec δ (fun i => cen P Z (t i) δ) φ (measVec Z δ t ω) := by
  funext ω i
  exact regField_eq P Z (t i) δ (φ i) ω

/-- Two critical SHFs have the same law at a single time pair. -/
private theorem law1_of_fdd (ϑ : ℝ) {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hZ' : IsCriticalSHF ϑ P' Z') (hfdd : CriticalSHFFddUnique.{u, v}) {T : ℝ} (hT : 0 < T) :
    P.map (Z 0 T) = P'.map (Z' 0 T) := by
  have h := hfdd ϑ P P' Z Z' hZ hZ' 1 (fun _ => 0) (fun _ => T) (fun _ => ⟨le_rfl, hT⟩)
  have h1 := congrArg (fun ν => ν.map (fun m : Fin 1 → Measure (Plane × Plane) => m 0)) h
  rw [Measure.map_map (measurable_pi_apply 0)
      (Measurable.of_eval fun _ => hZ.1 0 T le_rfl hT),
    Measure.map_map (measurable_pi_apply 0)
      (Measurable.of_eval fun _ => hZ'.1 0 T le_rfl hT)] at h1
  exact h1

/-- Equal one-time laws give equal centring constants. -/
private theorem cen_eq_of_law1 {Ω : Type*} {Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω')
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane))
    {t δ : ℝ} (hδ : 0 < δ) (hm : Measurable (Z 0 (t - δ))) (hm' : Measurable (Z' 0 (t - δ)))
    (h : P.map (Z 0 (t - δ)) = P'.map (Z' 0 (t - δ))) : cen P Z t δ = cen P' Z' t δ := by
  have h1 : cen P Z t δ = ∫ m, logPair δ m ∂(P.map (Z 0 (t - δ))) :=
    (integral_map hm.aemeasurable (measurable_logPair δ hδ).aestronglyMeasurable).symm
  have h2 : cen P' Z' t δ = ∫ m, logPair δ m ∂(P'.map (Z' 0 (t - δ))) :=
    (integral_map hm'.aemeasurable (measurable_logPair δ hδ).aestronglyMeasurable).symm
  rw [h1, h2, h]

/-- **Law determination.** For two critical SHFs with the same parameter, the joint law of the
vector of tested regularized fields `(∫ φ_i · kpzRegularized (t_i) δ 0)_i` is the same (it is a
measurable functional of the vector of measures `(Z 0 (t_i - δ))_i`, whose law is determined by
`CriticalSHFFddUnique`, and of the centring constants, which are determined by the one-time laws);
moreover both vectors are a.e. measurable. -/
private theorem regVec_law_eq (ϑ : ℝ) {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hZ' : IsCriticalSHF ϑ P' Z') (hfdd : CriticalSHFFddUnique.{u, v}) {δ : ℝ} (hδ : 0 < δ)
    {k : ℕ} (t : Fin k → ℝ) (hδt : ∀ i, δ < t i) (φ : Fin k → TestFn) :
    AEMeasurable (fun ω i => ∫ x, φ i x * kpzRegularized P Z (t i) δ 0 x ω) P ∧
    AEMeasurable (fun ω i => ∫ x, φ i x * kpzRegularized P' Z' (t i) δ 0 x ω) P' ∧
    P.map (fun ω i => ∫ x, φ i x * kpzRegularized P Z (t i) δ 0 x ω) =
      P'.map (fun ω i => ∫ x, φ i x * kpzRegularized P' Z' (t i) δ 0 x ω) := by
  have hν : P.map (measVec Z δ t) = P'.map (measVec Z' δ t) :=
    hfdd ϑ P P' Z Z' hZ hZ' k (fun _ => 0) (fun i => t i - δ)
      (fun i => ⟨le_rfl, sub_pos.2 (hδt i)⟩)
  have hc : (fun i => cen P Z (t i) δ) = fun i => cen P' Z' (t i) δ := by
    funext i
    have hT : 0 < t i - δ := sub_pos.2 (hδt i)
    exact cen_eq_of_law1 P P' Z Z' hδ (hZ.1 0 _ le_rfl hT) (hZ'.1 0 _ le_rfl hT)
      (law1_of_fdd ϑ P P' Z Z' hZ hZ' hfdd hT)
  have hTm := measurable_measVec ϑ P Z hZ t hδt
  have hTm' := measurable_measVec ϑ P' Z' hZ' t hδt
  have hΘ := aemeasurable_fieldVec ϑ P Z hZ hδ t hδt (fun i => cen P Z (t i) δ) φ
  have hΘ' : AEMeasurable (fieldVec δ (fun i => cen P Z (t i) δ) φ)
      (P'.map (measVec Z' δ t)) := by rw [← hν]; exact hΘ
  rw [regVec_eq P Z δ t φ, regVec_eq P' Z' δ t φ, ← hc]
  refine ⟨hΘ.comp_aemeasurable hTm.aemeasurable, hΘ'.comp_aemeasurable hTm'.aemeasurable, ?_⟩
  have e1 := AEMeasurable.map_map_of_aemeasurable hΘ hTm.aemeasurable
  have e2 := AEMeasurable.map_map_of_aemeasurable hΘ' hTm'.aemeasurable
  have e3 : (P.map (measVec Z δ t)).map (fieldVec δ (fun i => cen P Z (t i) δ) φ) =
      (P'.map (measVec Z' δ t)).map (fieldVec δ (fun i => cen P Z (t i) δ) φ) := by rw [hν]
  exact e1.symm.trans (e3.trans e2)

/-- Convergence in measure of each coordinate gives convergence in measure of the vector. -/
private theorem tendstoInMeasure_pi {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {l : Filter ι} {k : ℕ} {U : ι → Ω → Fin k → ℝ} {W : Ω → Fin k → ℝ}
    (h : ∀ i, TendstoInMeasure P (fun n ω => U n ω i) l (fun ω => W ω i)) :
    TendstoInMeasure P U l W := by
  intro ε hε
  have hbound : ∀ n, P {ω | ε ≤ edist (U n ω) (W ω)} ≤
      ∑ i, P {ω | ε ≤ edist (U n ω i) (W ω i)} := by
    intro n
    calc P {ω | ε ≤ edist (U n ω) (W ω)}
        ≤ P (⋃ i, {ω | ε ≤ edist (U n ω i) (W ω i)}) := by
          apply measure_mono
          intro ω hω
          simp only [Set.mem_ofPred_eq, edist_pi_def] at hω
          rw [Finset.le_sup_iff (bot_lt_iff_ne_bot.2 (ne_of_gt hε))] at hω
          obtain ⟨i, -, hi⟩ := hω
          exact Set.mem_iUnion.2 ⟨i, hi⟩
      _ ≤ _ := measure_iUnion_fintype_le _ _
  have hsum : Tendsto (fun n => ∑ i, P {ω | ε ≤ edist (U n ω i) (W ω i)}) l (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ (fun i _ => h i ε hε)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun _ => zero_le)
    hbound

/-- Limits in measure of vectors with equal laws have equal laws. -/
private theorem law_eq_of_tendstoInMeasure {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] {k : ℕ} (U : ℕ → Ω → Fin k → ℝ) (U' : ℕ → Ω' → Fin k → ℝ)
    (W : Ω → Fin k → ℝ) (W' : Ω' → Fin k → ℝ) (hU : ∀ n, AEMeasurable (U n) P)
    (hU' : ∀ n, AEMeasurable (U' n) P') (hW : TendstoInMeasure P U atTop W)
    (hW' : TendstoInMeasure P' U' atTop W') (heq : ∀ n, P.map (U n) = P'.map (U' n)) :
    P.map W = P'.map W' := by
  have h1 := hW.tendstoInDistribution hU
  have h2 := hW'.tendstoInDistribution hU'
  have h2' : TendstoInDistribution U atTop W' (fun _ => P) P' :=
    ⟨hU, h2.aemeasurable_limit,
      h2.tendsto.congr (fun n => Subtype.ext (heq n).symm)⟩
  exact tendstoInDistribution_unique U h1 h2'

/-- A sequence of positive widths below all the times, tending to `0⁺`. -/
private theorem exists_widths {k : ℕ} (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) :
    ∃ ds : ℕ → ℝ, (∀ n, 0 < ds n) ∧ (∀ n i, ds n < t i) ∧
      Tendsto ds atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 < m ∧ ∀ i, m ≤ t i := by
    rcases isEmpty_or_nonempty (Fin k) with hk | hk
    · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
    · obtain ⟨i₀, hi₀⟩ := Finite.exists_min t
      exact ⟨t i₀, ht i₀, hi₀⟩
  have hpos : ∀ n : ℕ, 0 < m / ((n : ℝ) + 2) := fun n => by positivity
  refine ⟨fun n => m / ((n : ℝ) + 2), hpos, fun n i => ?_, ?_⟩
  · have : m / ((n : ℝ) + 2) < m := div_lt_self hm0 (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    exact this.trans_le (hm i)
  · refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall hpos⟩
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)

/-- Positive multiples of widths tending to `0⁺` tend to `0⁺`. -/
private theorem tendsto_widths_mul {ds : ℕ → ℝ} {a : ℝ} (ha : 0 < a)
    (h : Tendsto ds atTop (nhdsWithin 0 (Set.Ioi 0))) :
    Tendsto (fun n => a * ds n) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
  obtain ⟨h1, h2⟩ := tendsto_nhdsWithin_iff.1 h
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · simpa using h1.const_mul a
  · filter_upwards [h2] with n hn using mul_pos ha hn

/-- Affine transport of the regularized field, exact for the total-function conventions when the centring constants
of the transported process and of `Z` agree. -/
private theorem field_compAffine_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (z : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (φ : TestFn) (ω : Ω)
    (hc : cen P (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2)) t δ =
      cen P Z t δ) :
    ∫ y, (φ.compAffine z R) y * kpzRegularized P Z t δ 0 y ω =
      ∫ y, φ y * kpzRegularized P
        (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2)) t δ 0 y ω := by
  let A : Plane ≃ₜ Plane := R.toHomeomorph.trans (Homeomorph.addLeft z)
  have hA : MeasurePreserving A.toMeasurableEquiv volume volume := by
    change MeasurePreserving (fun y : Plane => z + R y) volume volume
    exact (measurePreserving_add_left volume z).comp R.measurePreserving
  let F := fun y => kpzRegularized P Z t δ 0 y ω
  have hAinv (y : Plane) : A.toMeasurableEquiv.symm y = R.symm y - R.symm z := by
    change A.symm y = _
    apply A.injective
    rw [A.apply_symm_apply]
    simp [A, map_sub]
  have hpoint (y : Plane) : kpzRegularized P
      (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2)) t δ 0 y ω =
        F (A.toMeasurableEquiv.symm y) := by
    have hp := kpzRegularized_compAffine_pointwise P Z t δ z R y ω
    rw [hAinv, hp]
    change F (R.symm y - R.symm z) + cen P Z t δ -
      cen P (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2)) t δ = _
    rw [hc]
    ring
  simp_rw [hpoint]
  have hc' := hA.integral_comp' (fun y => φ y * F (A.toMeasurableEquiv.symm y))
  rw [← hc']
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  change φ (z + R y) * F y = φ (A.toMeasurableEquiv y) *
    F (A.toMeasurableEquiv.symm (A.toMeasurableEquiv y))
  rw [MeasurableEquiv.symm_apply_apply]
  rfl

/-- Transport step: if the affinely transported process is again critical with the same
parameter, then the limit field of `φ.compAffine z R` has the law of that of `φ`. -/
private theorem invariance_transport (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hfdd' : CriticalSHFFddUnique.{u, u})
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {k : ℕ} (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) (φ : Fin k → TestFn) (z : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane)
    (hg : IsCriticalSHF ϑ P (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2))) :
    P.map (fun ω i => H (t i) 0 ω ((φ i).compAffine z R)) =
      P.map (fun ω i => H (t i) 0 ω (φ i)) := by
  obtain ⟨ds, hpos, hlt, hds⟩ := exists_widths t ht
  have hcen (n : ℕ) (i : Fin k) :
      cen P (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2)) (t i) (ds n) =
        cen P Z (t i) (ds n) := by
    have hT : 0 < t i - ds n := sub_pos.2 (hlt n i)
    exact cen_eq_of_law1 P P _ Z (hpos n) (hg.1 0 _ le_rfl hT) (hZ.1 0 _ le_rfl hT)
      (law1_of_fdd ϑ P P _ Z hg hZ hfdd' hT)
  refine law_eq_of_tendstoInMeasure P P
    (fun n ω i => ∫ x, ((φ i).compAffine z R) x * kpzRegularized P Z (t i) (ds n) 0 x ω)
    (fun n ω i => ∫ x, φ i x * kpzRegularized P Z (t i) (ds n) 0 x ω)
    (fun ω i => H (t i) 0 ω ((φ i).compAffine z R)) (fun ω i => H (t i) 0 ω (φ i))
    (fun n => AEMeasurable.of_eval fun i =>
      aemeasurable_regField ϑ P Z hZ (hpos n) (hlt n i) _)
    (fun n => AEMeasurable.of_eval fun i =>
      aemeasurable_regField ϑ P Z hZ (hpos n) (hlt n i) _)
    (tendstoInMeasure_pi fun i => (hH (t i) (ht i) 0 ((φ i).compAffine z R)).comp hds)
    (tendstoInMeasure_pi fun i => (hH (t i) (ht i) 0 (φ i)).comp hds) ?_
  intro n
  have hlaw := (regVec_law_eq ϑ P P _ Z hg hZ hfdd' (hpos n) t (hlt n) φ).2.2
  have hfun : (fun ω i => ∫ x, ((φ i).compAffine z R) x *
      kpzRegularized P Z (t i) (ds n) 0 x ω) = fun ω i => ∫ x, φ i x * kpzRegularized P
        (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2)) (t i) (ds n) 0 x ω := by
    funext ω i
    exact field_compAffine_eq P Z (t i) (ds n) z R (φ i) ω (hcen n i)
  rw [hfun]
  exact hlaw

/-- Flat KPZ test pairings are measurable and their joint laws are invariant under
translations, rotations and parabolic scaling, under SHF symmetries and law uniqueness. -/
theorem criticalKPZ_invariance_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hfdd : CriticalSHFFddUnique.{u, v})
    (hfdd' : CriticalSHFFddUnique.{u, u})
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (k : ℕ) (t : Fin k → ℝ) (ht : ∀ i, 0 < t i) (φ : Fin k → TestFn) :
    (∀ i, AEMeasurable (fun ω => H (t i) 0 ω (φ i)) P) ∧
    (∀ (z : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane),
      LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 →
      P.map (fun ω i => H (t i) 0 ω ((φ i).compAffine z R)) =
        P.map (fun ω i => H (t i) 0 ω (φ i))) ∧
    (∀ a : ℝ, 0 < a → ∀ {Ω' : Type v} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P']
      (Z' : ℝ → ℝ → Ω' → Measure (Plane × Plane)), IsCriticalSHF (ϑ + Real.log a) P' Z' →
      ∀ H' : ℝ → (Plane →ᵇ ℝ) → Ω' → Distr, IsCriticalKPZ P' Z' H' →
        P.map (fun ω i => H (a * t i) 0 ω ((φ i).scale a)) =
          P'.map (fun ω i => H' (t i) 0 ω (φ i))) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    obtain ⟨ds, hpos, hlt, hds⟩ := exists_widths (fun _ : Fin 1 => t i) (fun _ => ht i)
    exact ((hH (t i) (ht i) 0 (φ i)).comp hds).aemeasurable fun n =>
      aemeasurable_regField ϑ P Z hZ (hpos n) (hlt n 0) _
  · intro z R hdet
    have hsplit (ψ : TestFn) : ψ.compAffine z R =
        (ψ.compAffine z (LinearIsometryEquiv.refl ℝ Plane)).compAffine 0 R := by
      apply DFunLike.ext
      intro y
      change ψ (z + R y) = ψ (z + (LinearIsometryEquiv.refl ℝ Plane) (0 + R y))
      simp
    have hR : IsCriticalSHF ϑ P (fun s u ω => (Z s u ω).map fun p =>
        ((0 : Plane) + R p.1, (0 : Plane) + R p.2)) := by
      have h := hsym.2.1 R hdet
      simpa only [zero_add] using h
    have hτ : IsCriticalSHF ϑ P (fun s u ω => (Z s u ω).map fun p =>
        (z + (LinearIsometryEquiv.refl ℝ Plane) p.1,
          z + (LinearIsometryEquiv.refl ℝ Plane) p.2)) := by
      have h := hsym.1 z
      simpa only [LinearIsometryEquiv.coe_refl, id_eq, add_comm] using h
    have e : (fun ω i => H (t i) 0 ω ((φ i).compAffine z R)) = fun ω i => H (t i) 0 ω
        (((φ i).compAffine z (LinearIsometryEquiv.refl ℝ Plane)).compAffine 0 R) := by
      funext ω i
      rw [hsplit]
    rw [e]
    exact (invariance_transport ϑ P Z hZ hfdd' H hH t ht
      (fun i => (φ i).compAffine z (LinearIsometryEquiv.refl ℝ Plane)) 0 R hR).trans
      (invariance_transport ϑ P Z hZ hfdd' H hH t ht φ z (LinearIsometryEquiv.refl ℝ Plane) hτ)
  · intro a ha Ω' _ P' _ Z' hZ' H' hH'
    obtain ⟨ds, hpos, hlt, hds⟩ := exists_widths t ht
    have hZa := hsym.2.2.2.1 a ha
    have hdsa := tendsto_widths_mul ha hds
    refine law_eq_of_tendstoInMeasure P P'
      (fun n ω i => ∫ x, ((φ i).scale a) x *
        kpzRegularized P Z (a * t i) (a * ds n) 0 x ω)
      (fun n ω i => ∫ x, φ i x * kpzRegularized P' Z' (t i) (ds n) 0 x ω)
      (fun ω i => H (a * t i) 0 ω ((φ i).scale a)) (fun ω i => H' (t i) 0 ω (φ i))
      (fun n => AEMeasurable.of_eval fun i =>
        aemeasurable_regField ϑ P Z hZ (mul_pos ha (hpos n))
          (mul_lt_mul_of_pos_left (hlt n i) ha) _)
      (fun n => AEMeasurable.of_eval fun i =>
        aemeasurable_regField (ϑ + Real.log a) P' Z' hZ' (hpos n) (hlt n i) _)
      (tendstoInMeasure_pi fun i =>
        (hH (a * t i) (mul_pos ha (ht i)) 0 ((φ i).scale a)).comp hdsa)
      (tendstoInMeasure_pi fun i => (hH' (t i) (ht i) 0 (φ i)).comp hds) ?_
    intro n
    have hlaw := (regVec_law_eq (ϑ + Real.log a) P P' _ Z' hZa hZ' hfdd (hpos n) t (hlt n) φ).2.2
    have hfun : (fun ω i => ∫ x, ((φ i).scale a) x *
        kpzRegularized P Z (a * t i) (a * ds n) 0 x ω) = fun ω i => ∫ x, φ i x *
          kpzRegularized P (fun s u ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * u) ω).map
            fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2)) (t i) (ds n) 0 x ω := by
      funext ω i
      exact kpzRegularized_scale P Z ha (t i) (ds n) (φ i) ω
    rw [hfun]
    exact hlaw

end Critical2DKPZ.Assembly

end

end
