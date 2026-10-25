/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.TimeContinuity.ProjectionModulus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Sequential one-slab L² continuity -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Bornology
open scoped CompactlySupported Topology
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Flow

namespace Critical2DKPZ.SHF.TimeContinuity

private theorem integrable_slabMeanKernel_test (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (s s' : ℝ) (ν : Measure (Plane × Plane))
    (hν : IsLocallyFiniteMeasure ν) (Φ : C_c(Plane × Plane, ℝ)) :
    Integrable
      (fun q : Plane × (Plane × Plane) =>
        Φ (q.1, q.2.2) * slabMeanKernel ϑ N s s' q.1 q.2.1)
      ((volume : Measure Plane).prod ν) := by
  classical
  let K : Set (Plane × Plane) := tsupport Φ
  let Kx : Set Plane := Prod.fst '' K
  let Kz : Set Plane := Prod.snd '' K
  have hKx : IsCompact Kx := Φ.hasCompactSupport.image continuous_fst
  have hKz : IsCompact Kz := Φ.hasCompactSupport.image continuous_snd
  let S : Set Site := latticePoint N '' Kx
  have hS : S.Finite := finite_latticePoint_image_of_bounded hKx.isBounded
  let m := evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)
  let U : Finset Site := hS.toFinset.biUnion fun w => Critical2DKPZ.Polymer.endpoints w m
  let Y : Set Plane := ⋃ w ∈ U, cell N w
  have hcellBounded (w : Site) : IsBounded (cell N w) := by
    apply (Metric.isBounded_iff_subset_closedBall
      (Critical2DKPZ.latticeRepresentative N w)).2
    refine ⟨2, ?_⟩
    intro x hx
    change dist x (Critical2DKPZ.latticeRepresentative N w) ≤ 2
    rw [dist_comm, ← Critical2DKPZ.cellSample_eq_of_mem_cell hx]
    exact Critical2DKPZ.dist_cellSample_le_two hN x
  have hYbounded : IsBounded Y :=
    (isBounded_biUnion_finset U).2 fun w _ => hcellBounded w
  have hbothBounded : IsBounded (Y ∪ Kz) := hYbounded.union hKz.isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hbothBounded
  let Kball : Set Plane := Metric.closedBall 0 R
  have hYball : Y ⊆ Kball := fun _ hy => hR (Set.mem_union_left _ hy)
  have hKzball : Kz ⊆ Kball := fun _ hz => hR (Set.mem_union_right _ hz)
  have hKball : IsCompact Kball := isCompact_closedBall (0 : Plane) R
  have hνball : ν (Kball ×ˢ Kball) < ⊤ := by
    have hνfc : IsFiniteMeasureOnCompacts ν :=
      @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
        (Plane × Plane) _ _ ν hν
    exact @IsCompact.measure_lt_top (Plane × Plane) _ _ ν hνfc
      (Kball ×ˢ Kball) (hKball.prod hKball)
  let E : Set (Plane × (Plane × Plane)) := Kx ×ˢ (Kball ×ˢ Kball)
  have hE : MeasurableSet E := hKx.measurableSet.prod
    (hKball.measurableSet.prod hKball.measurableSet)
  have hμE : ((volume : Measure Plane).prod ν) E < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top hKx.measure_lt_top hνball
  have hκFmeas : Measurable (fun q : Plane × (Plane × Plane) =>
      slabMeanKernel ϑ N s s' q.1 q.2.1) := by
    have hsitesbase : Measurable (fun q : Plane × (Plane × Plane) =>
        ((latticePoint N ∘ Prod.fst ∘ Prod.snd) q, (latticePoint N ∘ Prod.fst) q)) :=
      ((measurable_latticePoint N).comp (measurable_fst.comp measurable_snd)).prodMk
        ((measurable_latticePoint N).comp measurable_fst)
    have hsites : Measurable (fun q : Plane × (Plane × Plane) =>
        (latticePoint N q.2.1, latticePoint N q.1)) := by
      convert hsitesbase using 1
      funext q
      rfl
    have hkernel : Measurable (fun wz : Site × Site =>
        Critical2DKPZ.srwKernel m (wz.1 - wz.2)) := measurable_of_countable _
    have hbase : Measurable (fun q : Plane × (Plane × Plane) =>
        (N : ℝ) / 4 * Critical2DKPZ.srwKernel m
          (latticePoint N q.2.1 - latticePoint N q.1)) :=
      (hkernel.comp hsites).const_mul ((N : ℝ) / 4)
    have heq : (fun q : Plane × (Plane × Plane) =>
        slabMeanKernel ϑ N s s' q.1 q.2.1) = fun q =>
        (N : ℝ) / 4 * Critical2DKPZ.srwKernel m
          (latticePoint N q.2.1 - latticePoint N q.1) := by
      funext q
      exact slabMeanKernel_eq_srwKernel ϑ N s s' q.1 q.2.1
    rw [heq]
    exact hbase
  have hFmeas : Measurable (fun q : Plane × (Plane × Plane) =>
      Φ (q.1, q.2.2) * slabMeanKernel ϑ N s s' q.1 q.2.1) := by
    have hΦmeas : Measurable (fun q : Plane × (Plane × Plane) => Φ (q.1, q.2.2)) := by
      fun_prop
    exact hΦmeas.mul hκFmeas
  have hκbound (x y : Plane) :
      ‖slabMeanKernel ϑ N s s' x y‖ ≤ (N : ℝ) / 4 := by
    rw [Real.norm_eq_abs, slabMeanKernel_eq_srwKernel]
    rw [abs_of_nonneg (mul_nonneg (by positivity)
      (Critical2DKPZ.srwKernel_nonneg m (latticePoint N y - latticePoint N x)))]
    have hN4 : (0 : ℝ) ≤ (N : ℝ) / 4 :=
      div_nonneg (Nat.cast_nonneg N) (by norm_num)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      (Critical2DKPZ.Polymer.srwKernel_le_one m (latticePoint N y - latticePoint N x)) hN4
  let C : ℝ := ‖Φ.toBoundedContinuousFunction‖ * ((N : ℝ) / 4)
  have hC : 0 ≤ C := by positivity
  have hbound (q : Plane × (Plane × Plane)) :
      ‖Φ (q.1, q.2.2) * slabMeanKernel ϑ N s s' q.1 q.2.1‖ ≤ C := by
    rw [norm_mul]
    exact mul_le_mul (Φ.toBoundedContinuousFunction.norm_coe_le_norm (q.1, q.2.2))
      (hκbound q.1 q.2.1)
      (norm_nonneg _) (by positivity)
  have hzero (q : Plane × (Plane × Plane)) (hq : q ∉ E) :
      Φ (q.1, q.2.2) * slabMeanKernel ϑ N s s' q.1 q.2.1 = 0 := by
    by_contra hne
    have hΦ : Φ (q.1, q.2.2) ≠ 0 := by
      intro h
      exact hne (by simp [h])
    have hp : (q.1, q.2.2) ∈ K :=
      subset_closure (Function.mem_support.mpr hΦ)
    have hxK : q.1 ∈ Kx := ⟨(q.1, q.2.2), hp, rfl⟩
    have hzK : q.2.2 ∈ Kz := ⟨(q.1, q.2.2), hp, rfl⟩
    have hκ : slabMeanKernel ϑ N s s' q.1 q.2.1 ≠ 0 := by
      intro h
      exact hne (by simp [h])
    have hxS : latticePoint N q.1 ∈ S := ⟨q.1, hxK, rfl⟩
    have hyU : latticePoint N q.2.1 ∈ U := by
      by_contra hy
      have hnot : latticePoint N q.2.1 ∉
          Critical2DKPZ.Polymer.endpoints (latticePoint N q.1) m := by
        intro he
        exact hy (Finset.mem_biUnion.mpr
          ⟨latticePoint N q.1, hS.mem_toFinset.mpr hxS, he⟩)
      have hwalk := Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem m
        (latticePoint N q.1) (latticePoint N q.2.1) hnot
      apply hκ
      rw [slabMeanKernel_eq_srwKernel, hwalk]
      simp
    have hyY : q.2.1 ∈ Y := by
      exact Set.mem_iUnion₂.mpr ⟨latticePoint N q.2.1, hyU,
        mem_cell_latticePoint N q.2.1⟩
    have hyball : q.2.1 ∈ Kball := hYball hyY
    have hzball : q.2.2 ∈ Kball := hKzball hzK
    exact hq ⟨hxK, hyball, hzball⟩
  have hconst : IntegrableOn (fun _ : Plane × (Plane × Plane) => C) E
      ((volume : Measure Plane).prod ν) := integrableOn_const hμE.ne
  have hindicator : Integrable (fun q => E.indicator (fun _ => C) q)
      ((volume : Measure Plane).prod ν) := hconst.integrable_indicator hE
  apply hindicator.mono' hFmeas.aestronglyMeasurable
  filter_upwards [] with q
  by_cases hq : q ∈ E
  · simpa [Set.indicator_of_mem hq] using hbound q
  · simp [hq, hzero q hq]

private theorem sfinite_polymerMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder) :
    SFinite (polymerMeasure ϑ N s t ω) := by
  dsimp [polymerMeasure]
  infer_instance

attribute [local instance] sfinite_polymerMeasure

/-- Close moving initial times give polymer pairings whose mean squared difference tends to zero along every strictly increasing sequence of lattice scales. Integrability of the squared differences is included in `integral_sq_sub_startSlab`. -/
theorem polymerPairing_startSlab_sq_tendsto_zero
    (ϑ : ℝ) (hPolymerMovingMomentInput : PolymerMovingMomentLimit ϑ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (T : ℝ)
    (Nseq : ℕ → ℕ) (hNseq : StrictMono Nseq)
    (sN s'N tN : ℕ → ℝ)
    (hsN : Tendsto sN atTop (𝓝 s)) (hs'N : Tendsto s'N atTop (𝓝 s))
    (htN : Tendsto tN atTop (𝓝 t)) (hsN0 : ∀ k, 0 ≤ sN k)
    (hstart : ∀ k, sN k ≤ s'N k ∧ s'N k < tN k)
    (htNle : ∀ k, tN k ≤ T) (Φ : C_c(Plane × Plane, ℝ)) :
    Tendsto (fun k => ∫ ω,
      (∫ p, Φ p ∂(polymerMeasure ϑ (Nseq k) (sN k) (tN k) ω) -
        ∫ p, Φ p ∂(polymerMeasure ϑ (Nseq k) (s'N k) (tN k) ω)) ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := by
  classical
  let A : ℕ → Disorder → ℝ := fun k ω =>
    ∫ p, Φ p ∂(polymerMeasure ϑ (Nseq k) (sN k) (tN k) ω)
  let B : ℕ → Disorder → ℝ := fun k ω =>
    ∫ p, Φ p ∂(polymerMeasure ϑ (Nseq k) (s'N k) (tN k) ω)
  let C : ℕ → Disorder → ℝ := fun k ω =>
    ∫ q, (∫ x, Φ (x, q.2) * slabMeanKernel ϑ (Nseq k) (sN k) (s'N k) x q.1)
      ∂(polymerMeasure ϑ (Nseq k) (s'N k) (tN k) ω)
  have hsNext := extend_subsequence_real hNseq hsN hs hsN0
  obtain ⟨sExt, hsExt, hsExtEq, hsExt0⟩ := hsNext
  have hs'Nnonneg : ∀ k, 0 ≤ s'N k := fun k => (hsN0 k).trans (hstart k).1
  have hs'Ext := extend_subsequence_real hNseq hs'N hs hs'Nnonneg
  obtain ⟨s'Ext, hs'ExtT, hs'ExtEq, hs'Ext0⟩ := hs'Ext
  have htNnonneg : ∀ k, 0 ≤ tN k := by
    intro k
    exact ((hsN0 k).trans (hstart k).1).trans (hstart k).2.le
  have ht0 : 0 ≤ t := hs.trans hst.le
  have htExtResult := extend_subsequence_real hNseq htN ht0 htNnonneg
  obtain ⟨tExt, htExt, htExtEq, _htExt0⟩ := htExtResult
  let L : ℝ := ∫ x : DeltaBose.Configuration 2, ∫ y : DeltaBose.Configuration 2,
    (∏ i, Φ (x i, y i)) *
      (DeltaBose.momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal
  have hAmoving := polymerPairing_sq_tendsto_moving ϑ hPolymerMovingMomentInput hs hst sExt tExt
    hsExt htExt hsExt0 Φ
  have hBmoving := polymerPairing_sq_tendsto_moving ϑ hPolymerMovingMomentInput hs hst s'Ext tExt
    hs'ExtT htExt hs'Ext0 Φ
  have hA : Tendsto (fun k => ∫ ω, A k ω ^ 2 ∂disorderLaw) atTop (𝓝 L) := by
    have hcomp := hAmoving.comp hNseq.tendsto_atTop
    have hseq : (fun k => ∫ ω, A k ω ^ 2 ∂disorderLaw) =
        (fun N => ∫ ω,
          (∫ p, Φ p ∂(polymerMeasure ϑ N (sExt N) (tExt N) ω)) ^ 2 ∂disorderLaw) ∘ Nseq := by
      funext k
      simp only [A, Function.comp_apply]
      rw [← hsExtEq k, ← htExtEq k]
    rw [hseq]
    simpa only [L] using hcomp
  have hB : Tendsto (fun k => ∫ ω, B k ω ^ 2 ∂disorderLaw) atTop (𝓝 L) := by
    have hcomp := hBmoving.comp hNseq.tendsto_atTop
    have hseq : (fun k => ∫ ω, B k ω ^ 2 ∂disorderLaw) =
        (fun N => ∫ ω,
          (∫ p, Φ p ∂(polymerMeasure ϑ N (s'Ext N) (tExt N) ω)) ^ 2 ∂disorderLaw) ∘ Nseq := by
      funext k
      simp only [B, Function.comp_apply]
      rw [← hs'ExtEq k, ← htExtEq k]
    rw [hseq]
    simpa only [L] using hcomp
  obtain ⟨Cenv, hCenv⟩ := polymerMeasure_expEnvelope_sq_integral_le ϑ T
  let Kenv : ℝ := max Cenv 0
  have hKenv : 0 ≤ Kenv := by dsimp [Kenv]; exact le_max_right _ _
  have hEnvAt : ∀ᶠ k : ℕ in atTop, ∀ s₀ t₀ : ℝ, 0 ≤ s₀ → s₀ < t₀ → t₀ ≤ T →
      Integrable (fun ω =>
        (∫ p, Real.exp (-(‖p.1‖ + ‖p.2‖))
          ∂(polymerMeasure ϑ (Nseq k) s₀ t₀ ω)) ^ 2) disorderLaw ∧
      ∫ ω, (∫ p, Real.exp (-(‖p.1‖ + ‖p.2‖))
        ∂(polymerMeasure ϑ (Nseq k) s₀ t₀ ω)) ^ 2 ∂disorderLaw ≤ Kenv := by
    filter_upwards [hNseq.tendsto_atTop.eventually hCenv] with k hk
    intro s₀ t₀ hs₀ hs₀t₀ ht₀
    obtain ⟨hint, hbound⟩ := hk s₀ t₀ hs₀ hs₀t₀ ht₀
    exact ⟨hint, hbound.trans (le_max_left _ _)⟩
  have hgap : Tendsto (fun k => s'N k - sN k) atTop (𝓝 0) := by
    have h := hs'N.sub hsN
    simpa only [sub_self] using h
  have hD : Tendsto (fun k => ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := min 1 (ε / (2 * (Kenv + 1)))
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hδone : δ ≤ 1 := by dsimp [δ]; exact min_le_left _ _
    have hδε : δ ≤ ε / (2 * (Kenv + 1)) := by dsimp [δ]; exact min_le_right _ _
    have hδbound : δ ^ 2 * Kenv < ε := by
      have hmul : δ * Kenv ≤ ε / 2 := by
        calc
          δ * Kenv ≤ (ε / (2 * (Kenv + 1))) * Kenv :=
            mul_le_mul_of_nonneg_right hδε hKenv
          _ = ε * (Kenv / (2 * (Kenv + 1))) := by ring
          _ ≤ ε * (1 / 2) := by
            apply mul_le_mul_of_nonneg_left _ hε.le
            apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (Kenv + 1))).2
            nlinarith [hKenv]
          _ = ε / 2 := by ring
      have hδKnonneg : 0 ≤ δ * Kenv := mul_nonneg (le_of_lt hδ) hKenv
      calc
        δ ^ 2 * Kenv = (δ * Kenv) * δ := by ring
        _ ≤ (δ * Kenv) * 1 := mul_le_mul_of_nonneg_left hδone hδKnonneg
        _ = δ * Kenv := by ring
        _ ≤ ε / 2 := hmul
        _ < ε := by linarith
    obtain ⟨η, hη, N₀, hweight⟩ := slabMeanKernel_test_weighted_error ϑ Φ δ hδ
    have hNweight : ∀ᶠ k : ℕ in atTop, N₀ ≤ Nseq k :=
      hNseq.tendsto_atTop.eventually (eventually_atTop.2 ⟨N₀, fun _ h => h⟩)
    have hNpositive : ∀ᶠ k : ℕ in atTop, 1 ≤ Nseq k :=
      hNseq.tendsto_atTop.eventually (eventually_atTop.2 ⟨1, fun _ h => h⟩)
    have hgapSmall : ∀ᶠ k : ℕ in atTop, s'N k - sN k ≤ η := by
      have hevent := (Metric.tendsto_nhds.mp hgap) η hη
      filter_upwards [hevent] with k hk
      have hk' : |(s'N k - sN k) - 0| < η := by simpa only [Real.dist_eq] using hk
      have hnonneg : 0 ≤ s'N k - sN k := sub_nonneg.mpr (hstart k).1
      rw [sub_zero, abs_of_nonneg hnonneg] at hk'
      exact hk'.le
    filter_upwards [hNweight, hNpositive, hgapSmall, hEnvAt] with k hNk hNpos hgapk henv
    let μ : Disorder → Measure (Plane × Plane) :=
      polymerMeasure ϑ (Nseq k) (s'N k) (tN k)
    let F : Plane × Plane → ℝ := fun p =>
      slabSmoothedTest ϑ (Nseq k) (sN k) (s'N k) Φ p.1 p.2
    let G : Plane × Plane → ℝ := Φ
    let H : Plane × Plane → ℝ := fun p => Real.exp (-(‖p.1‖ + ‖p.2‖))
    have hpoint (p : Plane × Plane) : ‖F p - G p‖ ≤ δ * H p := by
      have h := hweight (Nseq k) hNk (sN k) (s'N k) p.1 p.2
        (hsN0 k) (hstart k).1 hgapk
      simpa only [F, G, H, Real.norm_eq_abs] using h
    have hFG : ∀ᵐ ω ∂disorderLaw, Integrable F (μ ω) ∧ Integrable G (μ ω) := by
      filter_upwards [] with ω
      have hprod := integrable_slabMeanKernel_test ϑ (N := Nseq k) (by omega)
        (sN k) (s'N k) (μ ω)
        (isLocallyFiniteMeasure_polymerMeasure ϑ (Nseq k) (s'N k) (tN k) ω) Φ
      have hFint : Integrable F (μ ω) := by
        have hiter := hprod.integral_prod_right
        simpa [F, slabSmoothedTest] using hiter
      have hGint : Integrable G (μ ω) := by
        have hloc := isLocallyFiniteMeasure_polymerMeasure ϑ (Nseq k) (s'N k) (tN k) ω
        have hfc : IsFiniteMeasureOnCompacts (μ ω) :=
          @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
            (Plane × Plane) _ _ (μ ω) hloc
        have hK : IsCompact (tsupport Φ) := Φ.hasCompactSupport
        have hKfinite : (μ ω) (tsupport Φ) < ⊤ :=
          @IsCompact.measure_lt_top (Plane × Plane) _ _ (μ ω) hfc
            (tsupport Φ) hK
        have hOn : IntegrableOn G (tsupport Φ) (μ ω) := by
          exact Φ.continuous.continuousOn.integrableOn_of_subset_isCompact
            hK hK.measurableSet Set.Subset.rfl hKfinite.ne
        exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport Φ)).mp hOn
      exact ⟨hFint, hGint⟩
    have hH : ∀ᵐ ω ∂disorderLaw, Integrable H (μ ω) :=
      expEnvelope_integrable_ae ϑ (by omega) (s'N k) (tN k)
    have hSlab := integral_sq_sub_startSlab ϑ (Nseq k) (hsN0 k)
      (hstart k).1 (hstart k).2 Φ
    have hDint : Integrable (fun ω => (C k ω - B k ω) ^ 2) disorderLaw := by
      simpa [C, B] using hSlab.2.2.1
    have hE : Integrable (fun ω => (∫ p, H p ∂μ ω) ^ 2) disorderLaw := by
      simpa [H, μ] using (henv (s'N k) (tN k) (hs'Nnonneg k) (hstart k).2 (htNle k)).1
    have hScaled := integral_sq_sub_le_scaled_envelope F G H μ δ (le_of_lt hδ)
      (fun p => le_of_lt (Real.exp_pos _)) hpoint hFG hH hDint hE
    have hScaledBound : ∫ ω, (∫ p, H p ∂μ ω) ^ 2 ∂disorderLaw ≤ Kenv :=
      (henv (s'N k) (tN k) (hs'Nnonneg k) (hstart k).2 (htNle k)).2
    have hvalue : ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw ≤ δ ^ 2 * Kenv := by
      calc
        _ = ∫ ω, (∫ p, F p ∂μ ω - ∫ p, G p ∂μ ω) ^ 2 ∂disorderLaw := by
          simp [C, B, F, G, μ, slabSmoothedTest]
        _ ≤ δ ^ 2 * ∫ ω, (∫ p, H p ∂μ ω) ^ 2 ∂disorderLaw := by
          simpa [C, B, F, G, μ, slabSmoothedTest] using hScaled
        _ ≤ δ ^ 2 * Kenv := mul_le_mul_of_nonneg_left hScaledBound (sq_nonneg δ)
    have hnonneg : 0 ≤ ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (C k ω - B k ω))
    have hlt : ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw < ε :=
      lt_of_le_of_lt hvalue hδbound
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hlt
  have hC2 : ∀ k, Integrable (fun ω => C k ω ^ 2) disorderLaw := by
    intro k
    exact (integral_sq_sub_startSlab ϑ (Nseq k) (hsN0 k)
      (hstart k).1 (hstart k).2 Φ).2.1
  have hD2 : ∀ k, Integrable (fun ω => (C k ω - B k ω) ^ 2) disorderLaw := by
    intro k
    simpa [C, B] using (integral_sq_sub_startSlab ϑ (Nseq k) (hsN0 k)
      (hstart k).1 (hstart k).2 Φ).2.2.1
  have hB2 : ∀ k, Integrable (fun ω => B k ω ^ 2) disorderLaw := by
    intro k
    have hmem := memLp_polymerPairing_two ϑ (Nseq k) (s'N k) (tN k) Φ
    have hpow := hmem.integrable_norm_pow'
    apply hpow.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hproj (k : ℕ) : ∫ ω, (A k ω - B k ω) ^ 2 ∂disorderLaw =
      (∫ ω, A k ω ^ 2 ∂disorderLaw - ∫ ω, C k ω ^ 2 ∂disorderLaw) +
        ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw := by
    simpa [A, B, C] using (integral_sq_sub_startSlab ϑ (Nseq k) (hsN0 k)
      (hstart k).1 (hstart k).2 Φ).2.2.2
  have hDlimit : Tendsto (fun k => ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := hD
  exact projection_difference_sq_tendsto_zero A B C hB2 hC2 hD2 hproj hA hB hDlimit

end Critical2DKPZ.SHF.TimeContinuity

end
