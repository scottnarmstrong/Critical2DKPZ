/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.TimeContinuity.ProjectionModulus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Sequential terminal-slab L² continuity -/

@[expose] public noncomputable section

open MeasureTheory Filter
open Bornology
open scoped CompactlySupported Topology
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Flow

namespace Critical2DKPZ.SHF.TimeContinuity

private theorem integrable_slabMeanKernel_test_right (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (s s' : ℝ) (μ : Measure (Plane × Plane))
    (hμ : IsLocallyFiniteMeasure μ) (Φ : C_c(Plane × Plane, ℝ)) :
    Integrable
      (fun q : (Plane × Plane) × Plane =>
        Φ (q.1.1, q.2) * slabMeanKernel ϑ N s s' q.1.2 q.2)
      (μ.prod (volume : Measure Plane)) := by
  classical
  let K : Set (Plane × Plane) := tsupport Φ
  let Kx : Set Plane := Prod.fst '' K
  let Kz : Set Plane := Prod.snd '' K
  have hKx : IsCompact Kx := Φ.hasCompactSupport.image continuous_fst
  have hKz : IsCompact Kz := Φ.hasCompactSupport.image continuous_snd
  let S : Set Site := latticePoint N '' Kz
  have hS : S.Finite := finite_latticePoint_image_of_bounded hKz.isBounded
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
  have hbothBounded : IsBounded (Y ∪ Kx) := hYbounded.union hKx.isBounded
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hbothBounded
  let Kball : Set Plane := Metric.closedBall 0 R
  have hYball : Y ⊆ Kball := fun _ hy => hR (Set.mem_union_left _ hy)
  have hKxball : Kx ⊆ Kball := fun _ hx => hR (Set.mem_union_right _ hx)
  have hKball : IsCompact Kball := isCompact_closedBall (0 : Plane) R
  have hμball : μ (Kball ×ˢ Kball) < ⊤ := by
    have hμfc : IsFiniteMeasureOnCompacts μ :=
      @isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
        (Plane × Plane) _ _ μ hμ
    exact @IsCompact.measure_lt_top (Plane × Plane) _ _ μ hμfc
      (Kball ×ˢ Kball) (hKball.prod hKball)
  let E : Set ((Plane × Plane) × Plane) := (Kball ×ˢ Kball) ×ˢ Kz
  have hE : MeasurableSet E :=
    (hKball.measurableSet.prod hKball.measurableSet).prod hKz.measurableSet
  have hμE : (μ.prod (volume : Measure Plane)) E < ⊤ := by
    rw [Measure.prod_prod]
    exact ENNReal.mul_lt_top hμball hKz.measure_lt_top
  have hκmeas : Measurable (fun q : (Plane × Plane) × Plane =>
      slabMeanKernel ϑ N s s' q.1.2 q.2) := by
    have hsitesBase : Measurable (fun q : (Plane × Plane) × Plane =>
        ((latticePoint N ∘ Prod.snd ∘ Prod.fst) q, (latticePoint N ∘ Prod.snd) q)) :=
      ((measurable_latticePoint N).comp (measurable_snd.comp measurable_fst)).prodMk
        ((measurable_latticePoint N).comp measurable_snd)
    have hsites : Measurable (fun q : (Plane × Plane) × Plane =>
        (latticePoint N q.1.2, latticePoint N q.2)) := by
      convert hsitesBase using 1
      funext q
      rfl
    have hkernel : Measurable (fun wz : Site × Site =>
        (N : ℝ) / 4 * Critical2DKPZ.srwKernel m (wz.2 - wz.1)) := measurable_of_countable _
    have hbase : Measurable (fun q : (Plane × Plane) × Plane =>
        (N : ℝ) / 4 * Critical2DKPZ.srwKernel m
          (latticePoint N q.2 - latticePoint N q.1.2)) := by
      convert hkernel.comp hsites using 1
      funext q
      rfl
    have heq : (fun q : (Plane × Plane) × Plane =>
        slabMeanKernel ϑ N s s' q.1.2 q.2) = fun q =>
        (N : ℝ) / 4 * Critical2DKPZ.srwKernel m
          (latticePoint N q.2 - latticePoint N q.1.2) := by
      funext q
      exact slabMeanKernel_eq_srwKernel ϑ N s s' q.1.2 q.2
    rw [heq]
    exact hbase
  have hΦmeas : Measurable (fun q : (Plane × Plane) × Plane => Φ (q.1.1, q.2)) := by
    fun_prop
  have hFmeas : Measurable (fun q : (Plane × Plane) × Plane =>
      Φ (q.1.1, q.2) * slabMeanKernel ϑ N s s' q.1.2 q.2) := hΦmeas.mul hκmeas
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
  have hbound (q : (Plane × Plane) × Plane) :
      ‖Φ (q.1.1, q.2) * slabMeanKernel ϑ N s s' q.1.2 q.2‖ ≤ C := by
    rw [norm_mul]
    exact mul_le_mul (Φ.toBoundedContinuousFunction.norm_coe_le_norm (q.1.1, q.2))
      (hκbound q.1.2 q.2) (norm_nonneg _) (by positivity)
  have hzero (q : (Plane × Plane) × Plane) (hq : q ∉ E) :
      Φ (q.1.1, q.2) * slabMeanKernel ϑ N s s' q.1.2 q.2 = 0 := by
    by_contra hne
    have hΦ : Φ (q.1.1, q.2) ≠ 0 := by
      intro h
      exact hne (by simp [h])
    have hp : (q.1.1, q.2) ∈ K :=
      subset_closure (Function.mem_support.mpr hΦ)
    have hxK : q.1.1 ∈ Kx := ⟨(q.1.1, q.2), hp, rfl⟩
    have hzK : q.2 ∈ Kz := ⟨(q.1.1, q.2), hp, rfl⟩
    have hκ : slabMeanKernel ϑ N s s' q.1.2 q.2 ≠ 0 := by
      intro h
      exact hne (by simp [h])
    have hzS : latticePoint N q.2 ∈ S := ⟨q.2, hzK, rfl⟩
    have hyU : latticePoint N q.1.2 ∈ U := by
      by_contra hy
      have hnot : latticePoint N q.1.2 ∉
          Critical2DKPZ.Polymer.endpoints (latticePoint N q.2) m := by
        intro he
        exact hy (Finset.mem_biUnion.mpr
          ⟨latticePoint N q.2, hS.mem_toFinset.mpr hzS, he⟩)
      have hwalk := Critical2DKPZ.Polymer.srwKernel_eq_zero_of_not_mem m
        (latticePoint N q.2) (latticePoint N q.1.2) hnot
      have harg : latticePoint N q.1.2 - latticePoint N q.2 =
          -(latticePoint N q.2 - latticePoint N q.1.2) := by abel
      rw [harg, Critical2DKPZ.Polymer.srwKernel_neg] at hwalk
      apply hκ
      rw [slabMeanKernel_eq_srwKernel, hwalk]
      simp
    have hyY : q.1.2 ∈ Y := by
      exact Set.mem_iUnion₂.mpr ⟨latticePoint N q.1.2, hyU,
        mem_cell_latticePoint N q.1.2⟩
    have hyball : q.1.2 ∈ Kball := hYball hyY
    have hxball : q.1.1 ∈ Kball := hKxball hxK
    exact hq ⟨⟨hxball, hyball⟩, hzK⟩
  have hconst : IntegrableOn (fun _ : (Plane × Plane) × Plane => C) E
      (μ.prod (volume : Measure Plane)) := integrableOn_const hμE.ne
  have hindicator : Integrable (fun q => E.indicator (fun _ => C) q)
      (μ.prod (volume : Measure Plane)) := hconst.integrable_indicator hE
  apply hindicator.mono' hFmeas.aestronglyMeasurable
  filter_upwards [] with q
  by_cases hq : q ∈ E
  · simpa [Set.indicator_of_mem hq] using hbound q
  · simp [hq, hzero q hq]

private theorem sfinite_polymerMeasure_end (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder) :
    SFinite (polymerMeasure ϑ N s t ω) := by
  dsimp [polymerMeasure]
  infer_instance

attribute [local instance] sfinite_polymerMeasure_end

private def transposeCCTest (Φ : C_c(Plane × Plane, ℝ)) : C_c(Plane × Plane, ℝ) where
  toFun p := Φ (p.2, p.1)
  continuous_toFun := Φ.continuous.comp (continuous_snd.prodMk continuous_fst)
  hasCompactSupport' := by
    let S : Set (Plane × Plane) := (fun p => (p.2, p.1)) '' tsupport Φ
    have hS : IsCompact S :=
      Φ.hasCompactSupport.image (continuous_snd.prodMk continuous_fst)
    apply HasCompactSupport.of_support_subset_isCompact hS
    intro p hp
    have hneq : Φ (p.2, p.1) ≠ 0 := by
      simpa only [Function.mem_support] using hp
    exact ⟨(p.2, p.1), subset_closure (Function.mem_support.mpr hneq), rfl⟩

private theorem slabMeanKernel_symmetric (ϑ : ℝ) (N : ℕ) (s t : ℝ) (x y : Plane) :
    slabMeanKernel ϑ N s t x y = slabMeanKernel ϑ N s t y x := by
  rw [slabMeanKernel_eq_srwKernel, slabMeanKernel_eq_srwKernel]
  exact congrArg (fun r : ℝ => ((N : ℝ) / 4) * r)
    (Critical2DKPZ.Polymer.srwKernel_sub_swap
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
      (latticePoint N y) (latticePoint N x))

/-- Close moving terminal times give polymer pairings whose mean squared difference tends to zero along every strictly increasing sequence of lattice scales. Integrability of the squared differences is included in `integral_sq_sub_endSlab`. -/
theorem polymerPairing_endSlab_sq_tendsto_zero
    (ϑ : ℝ) (hPolymerMovingMomentInput : PolymerMovingMomentLimit ϑ)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (T : ℝ)
    (Nseq : ℕ → ℕ) (hNseq : StrictMono Nseq)
    (sN tN t'N : ℕ → ℝ)
    (hsN : Tendsto sN atTop (𝓝 s)) (htN : Tendsto tN atTop (𝓝 t))
    (ht'N : Tendsto t'N atTop (𝓝 t)) (hsN0 : ∀ k, 0 ≤ sN k)
    (hend : ∀ k, sN k < tN k ∧ tN k ≤ t'N k)
    (ht'Nle : ∀ k, t'N k ≤ T) (Φ : C_c(Plane × Plane, ℝ)) :
    Tendsto (fun k => ∫ ω,
      (∫ p, Φ p ∂(polymerMeasure ϑ (Nseq k) (sN k) (t'N k) ω) -
        ∫ p, Φ p ∂(polymerMeasure ϑ (Nseq k) (sN k) (tN k) ω)) ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := by
  classical
  let A : ℕ → Disorder → ℝ := fun k ω =>
    ∫ p, Φ p ∂(polymerMeasure ϑ (Nseq k) (sN k) (t'N k) ω)
  let B : ℕ → Disorder → ℝ := fun k ω =>
    ∫ p, Φ p ∂(polymerMeasure ϑ (Nseq k) (sN k) (tN k) ω)
  let C : ℕ → Disorder → ℝ := fun k ω =>
    ∫ q, (∫ z, Φ (q.1, z) * slabMeanKernel ϑ (Nseq k) (tN k) (t'N k) q.2 z)
      ∂(polymerMeasure ϑ (Nseq k) (sN k) (tN k) ω)
  have htNnonneg : ∀ k, 0 ≤ tN k := by
    intro k
    exact (hsN0 k).trans (hend k).1.le
  have ht'Nnonneg : ∀ k, 0 ≤ t'N k := by
    intro k
    exact (htNnonneg k).trans (hend k).2
  have htNle : ∀ k, tN k ≤ T := fun k => (hend k).2.trans (ht'Nle k)
  have hsExtResult := extend_subsequence_real hNseq hsN hs hsN0
  obtain ⟨sExt, hsExt, hsExtEq, hsExt0⟩ := hsExtResult
  have htExtResult := extend_subsequence_real hNseq htN (le_trans hs hst.le) htNnonneg
  obtain ⟨tExt, htExt, htExtEq, _htExt0⟩ := htExtResult
  have ht'ExtResult := extend_subsequence_real hNseq ht'N (le_trans hs hst.le) ht'Nnonneg
  obtain ⟨t'Ext, ht'Ext, ht'ExtEq, _ht'Ext0⟩ := ht'ExtResult
  let L : ℝ := ∫ x : DeltaBose.Configuration 2, ∫ y : DeltaBose.Configuration 2,
    (∏ i, Φ (x i, y i)) *
      (DeltaBose.momentKernel 2 (ϑ - Real.eulerMascheroniConstant) (t - s) x y).toReal
  have hAmoving := polymerPairing_sq_tendsto_moving ϑ hPolymerMovingMomentInput hs hst sExt t'Ext
    hsExt ht'Ext hsExt0 Φ
  have hBmoving := polymerPairing_sq_tendsto_moving ϑ hPolymerMovingMomentInput hs hst sExt tExt
    hsExt htExt hsExt0 Φ
  have hA : Tendsto (fun k => ∫ ω, A k ω ^ 2 ∂disorderLaw) atTop (𝓝 L) := by
    have hcomp := hAmoving.comp hNseq.tendsto_atTop
    have hseq : (fun k => ∫ ω, A k ω ^ 2 ∂disorderLaw) =
        (fun N => ∫ ω,
          (∫ p, Φ p ∂(polymerMeasure ϑ N (sExt N) (t'Ext N) ω)) ^ 2 ∂disorderLaw) ∘ Nseq := by
      funext k
      simp only [A, Function.comp_apply]
      rw [← hsExtEq k, ← ht'ExtEq k]
    rw [hseq]
    simpa only [L] using hcomp
  have hB : Tendsto (fun k => ∫ ω, B k ω ^ 2 ∂disorderLaw) atTop (𝓝 L) := by
    have hcomp := hBmoving.comp hNseq.tendsto_atTop
    have hseq : (fun k => ∫ ω, B k ω ^ 2 ∂disorderLaw) =
        (fun N => ∫ ω,
          (∫ p, Φ p ∂(polymerMeasure ϑ N (sExt N) (tExt N) ω)) ^ 2 ∂disorderLaw) ∘ Nseq := by
      funext k
      simp only [B, Function.comp_apply]
      rw [← hsExtEq k, ← htExtEq k]
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
  have hgap : Tendsto (fun k => t'N k - tN k) atTop (𝓝 0) := by
    have h := ht'N.sub htN
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
    obtain ⟨η, hη, N₀, hweight⟩ :=
      slabMeanKernel_test_weighted_error ϑ (transposeCCTest Φ) δ hδ
    have hNweight : ∀ᶠ k : ℕ in atTop, N₀ ≤ Nseq k :=
      hNseq.tendsto_atTop.eventually (eventually_atTop.2 ⟨N₀, fun _ h => h⟩)
    have hNpositive : ∀ᶠ k : ℕ in atTop, 1 ≤ Nseq k :=
      hNseq.tendsto_atTop.eventually (eventually_atTop.2 ⟨1, fun _ h => h⟩)
    have hgapSmall : ∀ᶠ k : ℕ in atTop, t'N k - tN k ≤ η := by
      have hevent := (Metric.tendsto_nhds.mp hgap) η hη
      filter_upwards [hevent] with k hk
      have hk' : |(t'N k - tN k) - 0| < η := by simpa only [Real.dist_eq] using hk
      have hnonneg : 0 ≤ t'N k - tN k := sub_nonneg.mpr (hend k).2
      rw [sub_zero, abs_of_nonneg hnonneg] at hk'
      exact hk'.le
    filter_upwards [hNweight, hNpositive, hgapSmall, hEnvAt] with k hNk hNpos hgapk henv
    let μ : Disorder → Measure (Plane × Plane) :=
      polymerMeasure ϑ (Nseq k) (sN k) (tN k)
    let F : Plane × Plane → ℝ := fun p =>
      slabSmoothedTest ϑ (Nseq k) (tN k) (t'N k) (transposeCCTest Φ) p.2 p.1
    let G : Plane × Plane → ℝ := Φ
    let H : Plane × Plane → ℝ := fun p => Real.exp (-(‖p.1‖ + ‖p.2‖))
    have hFinner (q : Plane × Plane) :
        (∫ z, Φ (q.1, z) * slabMeanKernel ϑ (Nseq k) (tN k) (t'N k) q.2 z) = F q := by
      dsimp [F, slabSmoothedTest, transposeCCTest]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        exact congrArg (fun κ : ℝ => Φ (q.1, z) * κ)
          (slabMeanKernel_symmetric ϑ (Nseq k) (tN k) (t'N k) q.2 z)
    have hpoint (p : Plane × Plane) : ‖F p - G p‖ ≤ δ * H p := by
      have h := hweight (Nseq k) hNk (tN k) (t'N k) p.2 p.1
        (htNnonneg k) (hend k).2 hgapk
      simpa [F, G, H, transposeCCTest, add_comm] using h
    have hFG : ∀ᵐ ω ∂disorderLaw, Integrable F (μ ω) ∧ Integrable G (μ ω) := by
      filter_upwards [] with ω
      have hprod := integrable_slabMeanKernel_test_right ϑ (N := Nseq k) (by omega)
        (tN k) (t'N k) (μ ω)
        (isLocallyFiniteMeasure_polymerMeasure ϑ (Nseq k) (sN k) (tN k) ω) Φ
      have hFint : Integrable F (μ ω) := by
        have hiter := hprod.integral_prod_left
        exact hiter.congr (Filter.Eventually.of_forall hFinner)
      have hGint : Integrable G (μ ω) := by
        have hloc := isLocallyFiniteMeasure_polymerMeasure ϑ (Nseq k) (sN k) (tN k) ω
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
    have hFpair (ω : Disorder) : C k ω = ∫ p, F p ∂μ ω := by
      dsimp [C, μ]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => hFinner q
    have hBpair (ω : Disorder) : B k ω = ∫ p, G p ∂μ ω := by
      rfl
    have hH : ∀ᵐ ω ∂disorderLaw, Integrable H (μ ω) :=
      expEnvelope_integrable_ae ϑ (by omega) (sN k) (tN k)
    have hSlab := integral_sq_sub_endSlab ϑ (Nseq k) (hsN0 k)
      (hend k).1 (hend k).2 Φ
    have hDint : Integrable (fun ω => (C k ω - B k ω) ^ 2) disorderLaw := by
      simpa [C, B] using hSlab.2.2.1
    have hDintFG : Integrable (fun ω =>
        ((∫ p, F p ∂μ ω) - ∫ p, G p ∂μ ω) ^ 2) disorderLaw := by
      apply hDint.congr
      filter_upwards [] with ω
      rw [hFpair ω, hBpair ω]
    have hsNlt : sN k < tN k := (hend k).1
    have hE : Integrable (fun ω => (∫ p, H p ∂μ ω) ^ 2) disorderLaw := by
      simpa [H, μ] using (henv (sN k) (tN k) (hsN0 k) hsNlt (htNle k)).1
    have hScaled := integral_sq_sub_le_scaled_envelope F G H μ δ (le_of_lt hδ)
      (fun p => le_of_lt (Real.exp_pos _)) hpoint hFG hH hDintFG hE
    have hScaledBound : ∫ ω, (∫ p, H p ∂μ ω) ^ 2 ∂disorderLaw ≤ Kenv :=
      (henv (sN k) (tN k) (hsN0 k) hsNlt (htNle k)).2
    have hvalue : ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw ≤ δ ^ 2 * Kenv := by
      calc
        _ = ∫ ω, (∫ p, F p ∂μ ω - ∫ p, G p ∂μ ω) ^ 2 ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω => by
            change (C k ω - B k ω) ^ 2 = _
            rw [hFpair ω, hBpair ω]
        _ ≤ δ ^ 2 * ∫ ω, (∫ p, H p ∂μ ω) ^ 2 ∂disorderLaw := by
          simpa [B, G, μ] using hScaled
        _ ≤ δ ^ 2 * Kenv := mul_le_mul_of_nonneg_left hScaledBound (sq_nonneg δ)
    have hnonneg : 0 ≤ ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw :=
      integral_nonneg_of_ae (Filter.Eventually.of_forall fun ω => sq_nonneg (C k ω - B k ω))
    have hlt : ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw < ε :=
      lt_of_le_of_lt hvalue hδbound
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] using hlt
  have hC2 : ∀ k, Integrable (fun ω => C k ω ^ 2) disorderLaw := by
    intro k
    exact (integral_sq_sub_endSlab ϑ (Nseq k) (hsN0 k)
      (hend k).1 (hend k).2 Φ).2.1
  have hD2 : ∀ k, Integrable (fun ω => (C k ω - B k ω) ^ 2) disorderLaw := by
    intro k
    simpa [C, B] using (integral_sq_sub_endSlab ϑ (Nseq k) (hsN0 k)
      (hend k).1 (hend k).2 Φ).2.2.1
  have hB2 : ∀ k, Integrable (fun ω => B k ω ^ 2) disorderLaw := by
    intro k
    have hmem := memLp_polymerPairing_two ϑ (Nseq k) (sN k) (tN k) Φ
    have hpow := hmem.integrable_norm_pow'
    apply hpow.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, sq_abs]
  have hproj (k : ℕ) : ∫ ω, (A k ω - B k ω) ^ 2 ∂disorderLaw =
      (∫ ω, A k ω ^ 2 ∂disorderLaw - ∫ ω, C k ω ^ 2 ∂disorderLaw) +
        ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw := by
    simpa [A, B, C] using (integral_sq_sub_endSlab ϑ (Nseq k) (hsN0 k)
      (hend k).1 (hend k).2 Φ).2.2.2
  have hDlimit : Tendsto (fun k => ∫ ω, (C k ω - B k ω) ^ 2 ∂disorderLaw)
      atTop (𝓝 0) := hD
  exact projection_difference_sq_tendsto_zero A B C hB2 hC2 hD2 hproj hA hB hDlimit

end Critical2DKPZ.SHF.TimeContinuity

end
