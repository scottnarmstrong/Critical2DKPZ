/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SlabProductsIdentities
public import Critical2DKPZ.SHF.TimeContinuity.ProjectionIdentity
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Annealing the initial and terminal polymer slabs -/

@[expose] public noncomputable section

open MeasureTheory
open Bornology
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Flow
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.TimeContinuity

/-- At zero duration the first endpoint marginal of the polymer measure is Lebesgue measure. -/
theorem map_fst_polymerMeasure_zero (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N) (s : ℝ)
    (ω : Disorder) :
    (polymerMeasure ϑ N s s ω).map Prod.fst = (volume : Measure Plane) := by
  rw [map_fst_polymerMeasure ϑ hN s s ω]
  have hplane (x : Plane) : rescaledP2Plane ϑ N s s x ω = 1 := by
    simp [rescaledP2Plane]
  simp_rw [hplane, ENNReal.ofReal_one]
  simp

private theorem lintegral_zeroPolymerDensity_fst (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s : ℝ) (ω : Disorder) (y : Plane) :
    ∫⁻ x : Plane, ENNReal.ofReal (rescaledP2P ϑ N s s (x, y) ω) = 1 := by
  classical
  let z := latticePoint N y
  have hNpos : 0 < N := by omega
  have hz : z ∈ evenLattice := by dsimp [z]; exact latticePoint_mem_evenLattice N y
  have hcover : (⋃ w : Site, cell N w) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨latticePoint N x, mem_cell_latticePoint N x⟩
  have hterm (w : Site) :
      ∫⁻ x in cell N w, ENNReal.ofReal (rescaledP2P ϑ N s s (x, y) ω) =
        if w = z then 1 else 0 := by
    by_cases hw : w = z
    · subst w
      have hconst : (fun x : Plane => ENNReal.ofReal
          (rescaledP2P ϑ N s s (x, y) ω)) =ᵐ[volume.restrict (cell N z)]
            (fun _ => ENNReal.ofReal ((N : ℝ) / 4)) := by
        filter_upwards [ae_restrict_mem (measurableSet_cell N z)] with x hx
        rw [mem_cell_iff] at hx
        simp [rescaledP2P, Polymer.pointToPoint_zero, hx, z]
      calc
        _ = ∫⁻ x in cell N z, ENNReal.ofReal ((N : ℝ) / 4) := lintegral_congr_ae hconst
        _ = 1 := by
          rw [lintegral_const, Measure.restrict_apply_univ, volume_cell hNpos hz]
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (N : ℝ) / 4)]
          field_simp
          norm_num
      simp
    · by_cases hwEven : w ∈ evenLattice
      · have hconst : (fun x : Plane => ENNReal.ofReal
            (rescaledP2P ϑ N s s (x, y) ω)) =ᵐ[volume.restrict (cell N w)]
              (fun _ : Plane => (0 : ENNReal)) := by
          filter_upwards [ae_restrict_mem (measurableSet_cell N w)] with x hx
          rw [mem_cell_iff] at hx
          change ENNReal.ofReal ((N : ℝ) / 4 *
          Critical2DKPZ.pointToPoint (criticalBeta ϑ N) (evenCeil (N * s))
              (evenCeil (N * s) - evenCeil (N * s))
              (latticePoint N x) (latticePoint N y) ω) = 0
          rw [hx, Nat.sub_self, Critical2DKPZ.Polymer.pointToPoint_zero]
          have hnot : w ≠ latticePoint N y := by
            intro heq
            exact hw (by simpa [z] using heq)
          simp [hnot]
        rw [lintegral_congr_ae hconst]
        simp [hw]
      · rw [cell_eq_empty_of_not_even hwEven]
        simp [hw]
  calc
    _ = ∫⁻ x in ⋃ w : Site, cell N w,
        ENNReal.ofReal (rescaledP2P ϑ N s s (x, y) ω) := by rw [hcover]; simp
    _ = ∑' w : Site, ∫⁻ x in cell N w,
        ENNReal.ofReal (rescaledP2P ϑ N s s (x, y) ω) :=
      lintegral_iUnion (fun w => measurableSet_cell N w) (pairwise_disjoint_cell N) _
    _ = ∑' w : Site, if w = z then 1 else 0 := by
      apply tsum_congr
      intro w
      exact hterm w
    _ = 1 := by
      have hzero (w : Site) (hw : w ≠ z) : (if w = z then (1 : ENNReal) else 0) = 0 := by
        simp [hw]
      rw [tsum_eq_single z hzero]
      simp

/-- At zero duration the second endpoint marginal is also Lebesgue measure. -/
theorem map_snd_polymerMeasure_zero (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N) (s : ℝ)
    (ω : Disorder) :
    (polymerMeasure ϑ N s s ω).map Prod.snd = (volume : Measure Plane) := by
  classical
  apply Measure.ext
  intro A hA
  let B : Set (Plane × Plane) := Prod.snd ⁻¹' A
  have hB : MeasurableSet B := hA.preimage measurable_snd
  have hden : Measurable (fun p : Plane × Plane => ENNReal.ofReal
      (rescaledP2P ϑ N s s p ω)) :=
    ENNReal.measurable_ofReal.comp
      (SHF.Moments.measurable_uncurry_rescaledP2P ϑ N s s |>.of_uncurry_right)
  have hprod : Measurable (fun p : Plane × Plane =>
      B.indicator (fun p => ENNReal.ofReal (rescaledP2P ϑ N s s p ω)) p) := hden.indicator hB
  rw [Measure.map_apply measurable_snd hA, polymerMeasure,
    withDensity_apply _ hB]
  rw [Measure.volume_eq_prod, ← lintegral_indicator hB,
    lintegral_prod_symm _ hprod.aemeasurable]
  calc
    _ = ∫⁻ y : Plane, A.indicator (fun _ => (1 : ENNReal)) y ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [] with y
      by_cases hy : y ∈ A
      · simpa [B, hy] using lintegral_zeroPolymerDensity_fst ϑ hN s ω y
      · simp [B, hy]
    _ = volume A := by
      simpa using (lintegral_indicator_const (μ := (volume : Measure Plane)) hA 1)

private theorem latticePoint_eq_ae_zero_polymer (ϑ : ℝ) {N : ℕ} (s : ℝ)
    (ω : Disorder) :
    ∀ᵐ p ∂(polymerMeasure ϑ N s s ω), latticePoint N p.1 = latticePoint N p.2 := by
  let Bad : Set (Plane × Plane) := {p | latticePoint N p.1 ≠ latticePoint N p.2}
  have hBad : MeasurableSet Bad := by
    dsimp [Bad]
    exact (measurableSet_eq_fun
      ((measurable_latticePoint N).comp measurable_fst)
      ((measurable_latticePoint N).comp measurable_snd)).compl
  have hzero : (polymerMeasure ϑ N s s ω) Bad = 0 := by
    rw [polymerMeasure, withDensity_apply _ hBad]
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem hBad] with p hp
    have hne : latticePoint N p.1 ≠ latticePoint N p.2 := hp
    simp [rescaledP2P, Polymer.pointToPoint_zero, hne]
  rw [ae_iff]
  simpa [Bad] using hzero

private theorem sfinite_polymerMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder) :
    SFinite (polymerMeasure ϑ N s t ω) := by
  dsimp [polymerMeasure]
  infer_instance

attribute [local instance] sfinite_polymerMeasure

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

private theorem measurable_slabMeanKernel_test_right (ϑ : ℝ) (N : ℕ) (s s' : ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) :
    Measurable (fun q : (Plane × Plane) × Plane =>
      Φ (q.1.1, q.2) * slabMeanKernel ϑ N s s' q.1.2 q.2) := by
  have hsitesBase : Measurable (fun q : (Plane × Plane) × Plane =>
      ((latticePoint N ∘ Prod.snd ∘ Prod.fst) q, (latticePoint N ∘ Prod.snd) q)) :=
    ((measurable_latticePoint N).comp (measurable_snd.comp measurable_fst)).prodMk
      ((measurable_latticePoint N).comp measurable_snd)
  have hsites : Measurable (fun q : (Plane × Plane) × Plane =>
      (latticePoint N q.1.2, latticePoint N q.2)) := by
    convert hsitesBase using 1
    funext q
    rfl
  let m := evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)
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
  have hΦmeas : Measurable (fun q : (Plane × Plane) × Plane => Φ (q.1.1, q.2)) := by
    fun_prop
  have hκmeas : Measurable (fun q : (Plane × Plane) × Plane =>
      slabMeanKernel ϑ N s s' q.1.2 q.2) := by
    rw [heq]
    exact hbase
  exact hΦmeas.mul hκmeas

private theorem measurable_slabMeanKernel (ϑ : ℝ) (N : ℕ) (s s' : ℝ) :
    Measurable (Function.uncurry (slabMeanKernel ϑ N s s')) := by
  change Measurable (fun p : Plane × Plane => slabMeanKernel ϑ N s s' p.1 p.2)
  have hsitesBase : Measurable (fun p : Plane × Plane =>
      ((latticePoint N ∘ Prod.fst) p, (latticePoint N ∘ Prod.snd) p)) :=
    ((measurable_latticePoint N).comp measurable_fst).prodMk
      ((measurable_latticePoint N).comp measurable_snd)
  have hsites : Measurable (fun p : Plane × Plane =>
      (latticePoint N p.1, latticePoint N p.2)) := by
    convert hsitesBase using 1
    funext p
    rfl
  let m := evenCeil ((N : ℝ) * s') - evenCeil ((N : ℝ) * s)
  have hkernel : Measurable (fun wz : Site × Site =>
      (N : ℝ) / 4 * Critical2DKPZ.srwKernel m (wz.2 - wz.1)) := measurable_of_countable _
  have hbase : Measurable (fun p : Plane × Plane =>
      (N : ℝ) / 4 * Critical2DKPZ.srwKernel m
        (latticePoint N p.2 - latticePoint N p.1)) := by
    convert hkernel.comp hsites using 1
    funext p
    rfl
  have heq : (fun p : Plane × Plane => slabMeanKernel ϑ N s s' p.1 p.2) =
      fun p => (N : ℝ) / 4 * Critical2DKPZ.srwKernel m
        (latticePoint N p.2 - latticePoint N p.1) := by
    funext p
    exact slabMeanKernel_eq_srwKernel ϑ N s s' p.1 p.2
  rw [heq]
  exact hbase

private theorem measurable_polymerPairing_of_block_le (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (a b : ℕ) (ha : a = evenCeil ((N : ℝ) * s)) (hb : b = evenCeil ((N : ℝ) * t))
    (hab : a ≤ b) (m : MeasurableSpace Disorder)
    (hblock : Gaussian.disorderBlock a b ≤ m) (Φ : C_c(Plane × Plane, ℝ)) :
    Measurable[m] (fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) := by
  classical
  let S : Finset (Site × Site) := (finite_support_cellPairTest N Φ).toFinset
  let cellTest : Site × Site → ℝ := fun q =>
    ∫ p in cell N q.1 ×ˢ cell N q.2, Φ p
  have hcellzero {q : Site × Site} (hq : q ∉ S) : cellTest q = 0 := by
    dsimp [cellTest, S] at *
    by_contra hne
    exact hq ((finite_support_cellPairTest N Φ).mem_toFinset.mpr hne)
  have hsum (ω : Disorder) :
      (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) =
        ∑ q ∈ S, cellTest q * ((N : ℝ) / 4 *
          pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
            q.1 q.2 ω) := by
    rw [integral_polymerMeasure_cellTsum]
    rw [tsum_eq_sum (s := S) (fun q hq => by
      have hz := hcellzero hq
      change (∫ p in cell N q.1 ×ˢ cell N q.2, Φ p) = 0 at hz
      rw [hz]
      simp)]
  have hEq : (fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) =
      fun ω => ∑ q ∈ S, cellTest q * ((N : ℝ) / 4 *
        pointToPoint (criticalBeta ϑ N)
          (evenCeil ((N : ℝ) * s))
          (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
          q.1 q.2 ω) := by
    funext ω
    exact hsum ω
  rw [hEq]
  apply S.measurable_fun_sum
  intro q hq
  have hptp : Measurable[m] (fun ω => pointToPoint (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) q.1 q.2 ω) := by
    have hbase := Polymer.measurable_pointToPoint_block (criticalBeta ϑ N) a (b - a) q.1 q.2
    have hbase' : Measurable[Gaussian.disorderBlock a b]
        (fun ω => pointToPoint (criticalBeta ϑ N) a (b - a) q.1 q.2 ω) := by
      convert hbase using 1
      rw [Nat.add_sub_of_le hab]
    have hmono := hbase'.mono hblock le_rfl
    convert hmono using 1
    rw [ha, hb]
  exact measurable_const.mul (measurable_const.mul hptp)

private theorem kernelProductPairing_zeroStart_eq_iterated
    (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N) (s s' t : ℝ) (ω : Disorder)
    (κ : Plane → Plane → ℝ) (hκm : Measurable (Function.uncurry κ))
    (hκcell : ∀ x x' y, latticePoint N x = latticePoint N x' → κ x y = κ x' y)
    (Φ : C_c(Plane × Plane, ℝ))
    (hFint : Integrable
      (fun q : Plane × (Plane × Plane) => Φ (q.1, q.2.2) * κ q.1 q.2.1)
      ((volume : Measure Plane).prod (polymerMeasure ϑ N s' t ω))) :
    kernelProductPairing (polymerMeasure ϑ N s s ω) κ
        (polymerMeasure ϑ N s' t ω) Φ =
      ∫ q, (∫ x, Φ (x, q.2) * κ x q.1) ∂(polymerMeasure ϑ N s' t ω) := by
  let μ₀ := polymerMeasure ϑ N s s ω
  let ν := polymerMeasure ϑ N s' t ω
  let E : (Plane × Plane) × (Plane × Plane) → Plane × (Plane × Plane) :=
    fun q => (q.1.1, q.2)
  have hE : Measurable E := by
    exact measurable_fst.comp measurable_fst |>.prodMk measurable_snd
  have hEfun : E = Prod.map Prod.fst id := by
    funext q
    rfl
  have hmap : (μ₀.map Prod.fst).prod ν = (μ₀.prod ν).map E := by
    rw [hEfun]
    calc
      _ = (μ₀.map Prod.fst).prod (ν.map id) := by simp
      _ = _ := Measure.map_prod_map μ₀ ν measurable_fst measurable_id
  have hpairSet : MeasurableSet {q : (Plane × Plane) × (Plane × Plane) |
      latticePoint N q.1.1 = latticePoint N q.1.2} := by
    exact measurableSet_eq_fun
      ((measurable_latticePoint N).comp (measurable_fst.comp measurable_fst))
      ((measurable_latticePoint N).comp (measurable_snd.comp measurable_fst))
  have hpair : ∀ᵐ q : (Plane × Plane) × (Plane × Plane) ∂(μ₀.prod ν),
      latticePoint N q.1.1 = latticePoint N q.1.2 := by
    rw [Measure.ae_prod_iff_ae_ae hpairSet]
    filter_upwards [latticePoint_eq_ae_zero_polymer ϑ (N := N) s ω] with p hp
    exact Filter.Eventually.of_forall fun _ => hp
  have hEq : (fun q : (Plane × Plane) × (Plane × Plane) =>
        Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1) =ᵐ[μ₀.prod ν]
      (fun q => Φ (q.1.1, q.2.2) * κ q.1.1 q.2.1) := by
    filter_upwards [hpair] with q hq
    rw [hκcell q.1.2 q.1.1 q.2.1 hq.symm]
  have hFmeas : Measurable (fun q : Plane × (Plane × Plane) =>
      Φ (q.1, q.2.2) * κ q.1 q.2.1) := by
    exact (Φ.measurable.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).mul
      (hκm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
  calc
    _ = ∫ q, Φ (q.1.1, q.2.2) * κ q.1.1 q.2.1 ∂(μ₀.prod ν) := by
      rw [kernelProductPairing]
      exact integral_congr_ae hEq
    _ = ∫ q, Φ (q.1, q.2.2) * κ q.1 q.2.1 ∂((μ₀.map Prod.fst).prod ν) := by
      rw [hmap]
      exact (integral_map hE.aemeasurable hFmeas.aestronglyMeasurable).symm
    _ = ∫ q, Φ (q.1, q.2.2) * κ q.1 q.2.1
        ∂((volume : Measure Plane).prod ν) := by
      rw [map_fst_polymerMeasure_zero ϑ hN s ω]
    _ = ∫ q, (∫ x, Φ (x, q.2) * κ x q.1) ∂ν :=
      integral_prod_symm _ hFint

private theorem kernelProductPairing_zeroEnd_eq_iterated
    (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N) (s t t' : ℝ) (ω : Disorder)
    (κ : Plane → Plane → ℝ)
    (hκcell : ∀ x y y', latticePoint N y = latticePoint N y' → κ x y = κ x y')
    (Φ : C_c(Plane × Plane, ℝ))
    (hFmeas : Measurable (fun q : (Plane × Plane) × Plane =>
      Φ (q.1.1, q.2) * κ q.1.2 q.2))
    (hFint : Integrable
      (fun q : (Plane × Plane) × Plane => Φ (q.1.1, q.2) * κ q.1.2 q.2)
      ((polymerMeasure ϑ N s t ω).prod (volume : Measure Plane))) :
    kernelProductPairing (polymerMeasure ϑ N s t ω) κ
        (polymerMeasure ϑ N t' t' ω) Φ =
      ∫ q, (∫ z, Φ (q.1, z) * κ q.2 z) ∂(polymerMeasure ϑ N s t ω) := by
  let μ := polymerMeasure ϑ N s t ω
  let μ₀ := polymerMeasure ϑ N t' t' ω
  let E : (Plane × Plane) × (Plane × Plane) → (Plane × Plane) × Plane :=
    fun q => (q.1, q.2.2)
  have hE : Measurable E := measurable_fst.prodMk
    (measurable_snd.comp measurable_snd)
  have hEfun : E = Prod.map id Prod.snd := by
    funext q
    rfl
  have hmap : μ.prod (μ₀.map Prod.snd) = (μ.prod μ₀).map E := by
    rw [hEfun]
    calc
      _ = (μ.map id).prod (μ₀.map Prod.snd) := by simp
      _ = _ := Measure.map_prod_map μ μ₀ measurable_id measurable_snd
  have hpairSet : MeasurableSet {q : (Plane × Plane) × (Plane × Plane) |
      latticePoint N q.2.1 = latticePoint N q.2.2} := by
    exact measurableSet_eq_fun
      ((measurable_latticePoint N).comp (measurable_fst.comp measurable_snd))
      ((measurable_latticePoint N).comp (measurable_snd.comp measurable_snd))
  have hpair : ∀ᵐ q : (Plane × Plane) × (Plane × Plane) ∂(μ.prod μ₀),
      latticePoint N q.2.1 = latticePoint N q.2.2 := by
    rw [Measure.ae_prod_iff_ae_ae hpairSet]
    filter_upwards [] with p
    filter_upwards [latticePoint_eq_ae_zero_polymer ϑ (N := N) t' ω] with r hr
    exact hr
  have hEq : (fun q : (Plane × Plane) × (Plane × Plane) =>
      Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1) =ᵐ[μ.prod μ₀]
      (fun q => Φ (q.1.1, q.2.2) * κ q.1.2 q.2.2) := by
    filter_upwards [hpair] with q hq
    rw [hκcell q.1.2 q.2.1 q.2.2 hq]
  have hFmeas' : Measurable (fun q : (Plane × Plane) × Plane =>
      Φ (q.1.1, q.2) * κ q.1.2 q.2) := hFmeas
  calc
    _ = ∫ q, Φ (q.1.1, q.2.2) * κ q.1.2 q.2.2 ∂(μ.prod μ₀) := by
      rw [kernelProductPairing]
      exact integral_congr_ae hEq
    _ = ∫ q, Φ (q.1.1, q.2) * κ q.1.2 q.2
        ∂((μ.prod μ₀).map E) := by
      rw [integral_map hE.aemeasurable hFmeas'.aestronglyMeasurable]
    _ = ∫ q, Φ (q.1.1, q.2) * κ q.1.2 q.2
        ∂(μ.prod (μ₀.map Prod.snd)) := by
      rw [hmap]
    _ = ∫ q, Φ (q.1.1, q.2) * κ q.1.2 q.2
        ∂(μ.prod (volume : Measure Plane)) := by
      rw [map_snd_polymerMeasure_zero ϑ hN t' ω]
    _ = ∫ q, (∫ z, Φ (q.1, z) * κ q.2 z) ∂μ :=
      integral_prod _ hFint

/-- Conditioning on the disorder outside the terminal slab decomposes the mean squared difference between the full and shorter pairings into the conditional projection loss and the remaining squared difference. All squared terms are integrable. -/
theorem integral_sq_sub_endSlab (ϑ : ℝ) (N : ℕ) {s t t' : ℝ} (_hs : 0 ≤ s)
    (hst : s < t) (htt' : t ≤ t') (Φ : C_c(Plane × Plane, ℝ)) :
    Integrable (fun ω => (∫ p, Φ p ∂(polymerMeasure ϑ N s t' ω)) ^ 2) disorderLaw ∧
    Integrable (fun ω => (∫ q, (∫ z, Φ (q.1, z) * slabMeanKernel ϑ N t t' q.2 z)
      ∂(polymerMeasure ϑ N s t ω)) ^ 2) disorderLaw ∧
    Integrable (fun ω => ((∫ q, (∫ z, Φ (q.1, z) * slabMeanKernel ϑ N t t' q.2 z)
      ∂(polymerMeasure ϑ N s t ω)) - ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) ^ 2)
      disorderLaw ∧
    ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s t' ω) -
      ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) ^ 2 ∂disorderLaw =
      (∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s t' ω)) ^ 2 ∂disorderLaw -
        ∫ ω, (∫ q, (∫ z, Φ (q.1, z) * slabMeanKernel ϑ N t t' q.2 z)
          ∂(polymerMeasure ϑ N s t ω)) ^ 2 ∂disorderLaw) +
      ∫ ω, ((∫ q, (∫ z, Φ (q.1, z) * slabMeanKernel ϑ N t t' q.2 z)
          ∂(polymerMeasure ϑ N s t ω)) -
        ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) ^ 2 ∂disorderLaw := by
  classical
  by_cases hN0 : N = 0
  · subst N
    simp [polymerMeasure_zero_at_zero]
  · have hN : 0 < N := Nat.pos_of_ne_zero hN0
    let a := evenCeil ((N : ℝ) * s)
    let b := evenCeil ((N : ℝ) * t)
    let c := evenCeil ((N : ℝ) * t')
    let Y : Disorder → ℝ := fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t' ω)
    let C : Disorder → ℝ := fun ω =>
      ∫ q, (∫ z, Φ (q.1, z) * slabMeanKernel ϑ N t t' q.2 z)
        ∂(polymerMeasure ϑ N s t ω)
    let B : Disorder → ℝ := fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)
    let κ : Plane → Plane → ℝ := slabMeanKernel ϑ N t t'
    have hab : a ≤ b := by
      dsimp [a, b]
      exact Critical2DKPZ.evenCeil_mono
        (mul_le_mul_of_nonneg_left (le_of_lt hst) (Nat.cast_nonneg N))
    have hbc : b ≤ c := by
      dsimp [b, c]
      exact Critical2DKPZ.evenCeil_mono
        (mul_le_mul_of_nonneg_left htt' (Nat.cast_nonneg N))
    have hY : MemLp Y 2 disorderLaw := by
      dsimp [Y]
      exact memLp_polymerPairing_two ϑ N s t' Φ
    have hYm : Measurable Y := by
      dsimp [Y]
      exact measurable_polymerPairing ϑ N s t' Φ
    have hYint : Integrable Y disorderLaw := hY.integrable (by norm_num)
    let m : MeasurableSpace Disorder :=
      Gaussian.coordinateSigma (fun _ : ℕ × Site => ℝ) (Gaussian.timeBlock b c)ᶜ
    have hm : m ≤ MeasurableSpace.pi := by
      dsimp only [m]
      exact Gaussian.coordinateSigma_le (fun _ : ℕ × Site => ℝ) (Gaussian.timeBlock b c)ᶜ
    have hCEbase := Gaussian.condExp_coordinateSigma_ae_eq
      (fun _ : ℕ × Site => ProbabilityTheory.gaussianReal 0 1)
      (Gaussian.timeBlock b c)ᶜ hYm hYint
    have hCE : disorderLaw[Y | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c)ᶜ ω η) ∂disorderLaw := by
      simpa only [disorderLaw, m] using hCEbase
    have hCEresample : disorderLaw[Y | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw := by
      filter_upwards [hCE] with ω hω
      rw [hω]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun η => congrArg Y
        (resample_compl_eq_swapped (Gaussian.timeBlock b c) ω η)
    have hκcell : ∀ x y y', latticePoint N y = latticePoint N y' →
        κ x y = κ x y' := by
      intro x y y' hyy'
      dsimp [κ]
      rw [slabMeanKernel_eq_srwKernel, slabMeanKernel_eq_srwKernel, hyy']
    have hFmeas : Measurable (fun q : (Plane × Plane) × Plane =>
        Φ (q.1.1, q.2) * κ q.1.2 q.2) := by
      simpa only [κ] using measurable_slabMeanKernel_test_right ϑ N t t' Φ
    have hbridge (ω : Disorder) :
        (∫ η, Y (Gaussian.resample (Gaussian.timeBlock b c) η ω) ∂disorderLaw) = C ω := by
      dsimp [Y, C, κ]
      calc
        _ = kernelProductPairing (polymerMeasure ϑ N s t ω)
              (slabMeanKernel ϑ N t t') (polymerMeasure ϑ N t' t' ω) Φ :=
          integral_polymerPairing_resample_slab_eq_kernelProductPairing
            ϑ N hN (le_of_lt hst) htt' le_rfl Φ ω
        _ = ∫ q, (∫ z, Φ (q.1, z) * slabMeanKernel ϑ N t t' q.2 z)
              ∂(polymerMeasure ϑ N s t ω) :=
          kernelProductPairing_zeroEnd_eq_iterated ϑ (N := N) hN s t t' ω
            (slabMeanKernel ϑ N t t') hκcell Φ hFmeas
            (integrable_slabMeanKernel_test_right ϑ (N := N) hN t t'
              (polymerMeasure ϑ N s t ω)
              (isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω) Φ)
    have hCce : C =ᵐ[disorderLaw] disorderLaw[Y | m] := by
      filter_upwards [hCEresample] with ω hω
      exact (hω.trans (hbridge ω)).symm
    have hC : MemLp C 2 disorderLaw := by
      have hcond : MemLp (disorderLaw[Y | m]) 2 disorderLaw := hY.condExp (by norm_num)
      exact hcond.ae_eq hCce.symm
    have hCE2 := hY.condExpL2_ae_eq_condExp (E := ℝ) (𝕜 := ℝ)
      (m₀ := MeasurableSpace.pi) hm
    have hCE2C :
        (fun ω => (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω) =ᵐ[disorderLaw] C :=
      hCE2.trans hCce.symm
    have hCmCE : AEStronglyMeasurable[m]
        (fun ω => (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω) disorderLaw :=
      aestronglyMeasurable_condExpL2 hm _
    have hCm : AEStronglyMeasurable[m] C disorderLaw := hCmCE.congr hCE2C
    have hB : MemLp B 2 disorderLaw := by
      dsimp [B]
      exact memLp_polymerPairing_two ϑ N s t Φ
    have hsubset : Gaussian.timeBlock a b ⊆ (Gaussian.timeBlock b c)ᶜ := by
      intro i hi hinside
      simp only [Gaussian.timeBlock, Set.mem_ofPred_eq] at hi hinside
      omega
    have hmBlock : Gaussian.disorderBlock a b ≤ m := by
      dsimp [Gaussian.disorderBlock, m]
      exact Gaussian.coordinateSigma_mono _ hsubset
    have hBmeas : Measurable[m] B := by
      dsimp [B]
      exact measurable_polymerPairing_of_block_le ϑ N s t a b rfl rfl hab
        m hmBlock Φ
    have hBm : AEStronglyMeasurable[m] B disorderLaw := hBmeas.aestronglyMeasurable
    rcases integral_sq_sub_condExp_add_measurable hm hY hC hB hCm hBm hCce with
      ⟨hYsq, hCsq, hCBsq, _, heq⟩
    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
    · simpa only [Y] using hYsq
    · simpa only [C] using hCsq
    · simpa only [C, B] using hCBsq
    · simpa only [Y, C, B] using heq

/-- Conditioning on the disorder outside the initial slab decomposes the mean squared difference between the full and shorter pairings into the conditional projection loss and the remaining squared difference. All squared terms are integrable. -/
theorem integral_sq_sub_startSlab (ϑ : ℝ) (N : ℕ) {s s' t : ℝ} (_hs : 0 ≤ s)
    (hss' : s ≤ s') (hs't : s' < t) (Φ : C_c(Plane × Plane, ℝ)) :
    Integrable (fun ω => (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) ^ 2) disorderLaw ∧
    Integrable (fun ω => (∫ q, (∫ x, Φ (x, q.2) * slabMeanKernel ϑ N s s' x q.1)
      ∂(polymerMeasure ϑ N s' t ω)) ^ 2) disorderLaw ∧
    Integrable (fun ω => ((∫ q, (∫ x, Φ (x, q.2) * slabMeanKernel ϑ N s s' x q.1)
      ∂(polymerMeasure ϑ N s' t ω)) - ∫ p, Φ p ∂(polymerMeasure ϑ N s' t ω)) ^ 2)
      disorderLaw ∧
    ∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω) -
      ∫ p, Φ p ∂(polymerMeasure ϑ N s' t ω)) ^ 2 ∂disorderLaw =
      (∫ ω, (∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)) ^ 2 ∂disorderLaw -
        ∫ ω, (∫ q, (∫ x, Φ (x, q.2) * slabMeanKernel ϑ N s s' x q.1)
          ∂(polymerMeasure ϑ N s' t ω)) ^ 2 ∂disorderLaw) +
      ∫ ω, ((∫ q, (∫ x, Φ (x, q.2) * slabMeanKernel ϑ N s s' x q.1)
          ∂(polymerMeasure ϑ N s' t ω)) -
        ∫ p, Φ p ∂(polymerMeasure ϑ N s' t ω)) ^ 2 ∂disorderLaw := by
  classical
  by_cases hN0 : N = 0
  · subst N
    simp [polymerMeasure_zero_at_zero]
  · have hN : 0 < N := Nat.pos_of_ne_zero hN0
    let a := evenCeil ((N : ℝ) * s)
    let b := evenCeil ((N : ℝ) * s')
    let d := evenCeil ((N : ℝ) * t)
    let Y : Disorder → ℝ := fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s t ω)
    let C : Disorder → ℝ := fun ω =>
      ∫ q, (∫ x, Φ (x, q.2) * slabMeanKernel ϑ N s s' x q.1)
        ∂(polymerMeasure ϑ N s' t ω)
    let B : Disorder → ℝ := fun ω => ∫ p, Φ p ∂(polymerMeasure ϑ N s' t ω)
    let κ : Plane → Plane → ℝ := slabMeanKernel ϑ N s s'
    have hab : a ≤ b := by
      dsimp [a, b]
      exact Critical2DKPZ.evenCeil_mono
        (mul_le_mul_of_nonneg_left hss' (Nat.cast_nonneg N))
    have hbd : b ≤ d := by
      dsimp [b, d]
      exact Critical2DKPZ.evenCeil_mono
        (mul_le_mul_of_nonneg_left hs't.le (Nat.cast_nonneg N))
    have hY : MemLp Y 2 disorderLaw := by
      dsimp [Y]
      exact memLp_polymerPairing_two ϑ N s t Φ
    have hYm : Measurable Y := by
      dsimp [Y]
      exact measurable_polymerPairing ϑ N s t Φ
    have hYint : Integrable Y disorderLaw := hY.integrable (by norm_num)
    let m : MeasurableSpace Disorder :=
      Gaussian.coordinateSigma (fun _ : ℕ × Site => ℝ) (Gaussian.timeBlock a b)ᶜ
    have hm : m ≤ MeasurableSpace.pi := by
      dsimp only [m]
      exact Gaussian.coordinateSigma_le (fun _ : ℕ × Site => ℝ) (Gaussian.timeBlock a b)ᶜ
    have hCEbase := Gaussian.condExp_coordinateSigma_ae_eq
      (fun _ : ℕ × Site => ProbabilityTheory.gaussianReal 0 1)
      (Gaussian.timeBlock a b)ᶜ hYm hYint
    have hCE : disorderLaw[Y | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, Y (Gaussian.resample (Gaussian.timeBlock a b)ᶜ ω η) ∂disorderLaw := by
      simpa only [disorderLaw, m] using hCEbase
    have hCEresample : disorderLaw[Y | m] =ᵐ[disorderLaw]
        fun ω => ∫ η, Y (Gaussian.resample (Gaussian.timeBlock a b) η ω) ∂disorderLaw := by
      filter_upwards [hCE] with ω hω
      rw [hω]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun η => congrArg Y
        (resample_compl_eq_swapped (Gaussian.timeBlock a b) ω η)
    have hκm : Measurable (Function.uncurry κ) := by
      dsimp [κ]
      exact measurable_slabMeanKernel ϑ N s s'
    have hκcell : ∀ x x' y, latticePoint N x = latticePoint N x' →
        κ x y = κ x' y := by
      intro x x' y hxx'
      dsimp [κ]
      rw [slabMeanKernel_eq_srwKernel, slabMeanKernel_eq_srwKernel, hxx']
    have hbridge (ω : Disorder) :
        (∫ η, Y (Gaussian.resample (Gaussian.timeBlock a b) η ω) ∂disorderLaw) = C ω := by
      dsimp [Y, C, κ]
      calc
        _ = kernelProductPairing (polymerMeasure ϑ N s s ω)
              (slabMeanKernel ϑ N s s') (polymerMeasure ϑ N s' t ω) Φ :=
          integral_polymerPairing_resample_slab_eq_kernelProductPairing
            ϑ N hN (s := s) (t := s) (t' := s') (u := t)
            le_rfl hss' hs't.le Φ ω
        _ = ∫ q, (∫ x, Φ (x, q.2) * slabMeanKernel ϑ N s s' x q.1)
              ∂(polymerMeasure ϑ N s' t ω) :=
          kernelProductPairing_zeroStart_eq_iterated ϑ (N := N) hN s s' t ω
            (slabMeanKernel ϑ N s s') hκm hκcell
            Φ
            (integrable_slabMeanKernel_test ϑ (N := N) hN s s'
              (polymerMeasure ϑ N s' t ω)
              (isLocallyFiniteMeasure_polymerMeasure ϑ N s' t ω) Φ)
    have hCce : C =ᵐ[disorderLaw] disorderLaw[Y | m] := by
      filter_upwards [hCEresample] with ω hω
      exact (hω.trans (hbridge ω)).symm
    have hC : MemLp C 2 disorderLaw := by
      have hcond : MemLp (disorderLaw[Y | m]) 2 disorderLaw := hY.condExp (by norm_num)
      exact hcond.ae_eq hCce.symm
    have hCE2 := hY.condExpL2_ae_eq_condExp (E := ℝ) (𝕜 := ℝ)
      (m₀ := MeasurableSpace.pi) hm
    have hCE2C :
        (fun ω => (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω) =ᵐ[disorderLaw] C :=
      hCE2.trans hCce.symm
    have hCmCE : AEStronglyMeasurable[m]
        (fun ω => (condExpL2 ℝ ℝ hm (hY.toLp Y) : Disorder → ℝ) ω) disorderLaw :=
      aestronglyMeasurable_condExpL2 hm _
    have hCm : AEStronglyMeasurable[m] C disorderLaw := hCmCE.congr hCE2C
    have hB : MemLp B 2 disorderLaw := by
      dsimp [B]
      exact memLp_polymerPairing_two ϑ N s' t Φ
    have hsubset : Gaussian.timeBlock b d ⊆ (Gaussian.timeBlock a b)ᶜ := by
      intro i hi hinside
      simp only [Gaussian.timeBlock, Set.mem_ofPred_eq] at hi hinside
      omega
    have hmBlock : Gaussian.disorderBlock b d ≤ m := by
      dsimp [Gaussian.disorderBlock, m]
      exact Gaussian.coordinateSigma_mono _ hsubset
    have hBmeas : Measurable[m] B := by
      dsimp [B]
      exact measurable_polymerPairing_of_block_le ϑ N s' t b d rfl rfl hbd
        m hmBlock Φ
    have hBm : AEStronglyMeasurable[m] B disorderLaw := hBmeas.aestronglyMeasurable
    rcases integral_sq_sub_condExp_add_measurable hm hY hC hB hCm hBm hCce with
      ⟨hYsq, hCsq, hCBsq, _, heq⟩
    refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
    · simpa only [Y] using hYsq
    · simpa only [C] using hCsq
    · simpa only [C, B] using hCBsq
    · simpa only [Y, C, B] using heq

end Critical2DKPZ.SHF.TimeContinuity

end
