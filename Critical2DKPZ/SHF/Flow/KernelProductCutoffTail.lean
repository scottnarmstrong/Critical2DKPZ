/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Blocks.ArrivalKernel
public import Critical2DKPZ.PolymerCalculus.KernelReversal
public import Critical2DKPZ.SHF.Flow.SlabProductsCore
public import Critical2DKPZ.SHF.Flow.TerminalRandomWeightAnnealing
public import Critical2DKPZ.SHF.Flow.KernelProductCutoffBound
public import Critical2DKPZ.SHF.Flow.CutoffTailMoments
public import Critical2DKPZ.SHF.Flow.FiniteScaleBlocks
public import Critical2DKPZ.SHF.Flow.SlabSmoothedConnector
public import Critical2DKPZ.SHF.Limit.PolymerSixthMoment
public import Critical2DKPZ.SHF.Positivity.HeatClockBounds
public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Critical2DKPZ.SHF.Limit.SubseqLimit
import Mathlib.MeasureTheory.Measure.Prod

/-! # Annealed cutoff tails for separated polymer blocks -/

@[expose] public section

open MeasureTheory
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.Blocks
open Critical2DKPZ.SHF.Limit
open Critical2DKPZ.SHF.Tsai

/-- The polymer measure has finite mass when its first coordinate is restricted to a compact set. -/
theorem polymerMeasure_finite_first_compact (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (ω : Disorder) (A : Set Plane) (hA : IsCompact A) :
    polymerMeasure ϑ N s t ω (A ×ˢ (Set.univ : Set Plane)) < ⊤ := by
  classical
  by_cases hN0 : N = 0
  · subst N
    have hzero : polymerMeasure ϑ 0 s t ω = 0 := by
      rw [polymerMeasure]
      ext E hE
      simp [rescaledP2P]
    rw [hzero]
    simp
  · have hN : 0 < N := Nat.pos_of_ne_zero hN0
    let a := evenCeil ((N : ℝ) * s)
    let b := evenCeil ((N : ℝ) * t)
    let n := b - a
    let β := criticalBeta ϑ N
    let Sx : Set Site := latticePoint N '' A
    have hSx : Sx.Finite := finite_latticePoint_image_of_bounded hA.isBounded
    let Sy : Finset Site := hSx.toFinset.biUnion fun x => Polymer.endpoints x n
    let scale : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹
    let centers : Set Plane := (fun z : Site => scale • siteToPlane z) '' (Sy : Set Site)
    have hcenters : centers.Finite := Sy.finite_toSet.image _
    obtain ⟨M, hM⟩ := (hcenters.image fun x : Plane => ‖x‖).bddAbove
    let R := max 0 (M + scale)
    let K : Set (Plane × Plane) := A ×ˢ Metric.closedBall (0 : Plane) R
    have hR : 0 ≤ R := le_max_left _ _
    have hMR : M + scale ≤ R := le_max_right _ _
    have hball : IsCompact (Metric.closedBall (0 : Plane) R) := isCompact_closedBall _ _
    have hK : IsCompact K := hA.prod hball
    have hS : MeasurableSet (A ×ˢ (Set.univ : Set Plane)) :=
      hA.measurableSet.prod MeasurableSet.univ
    have hKm : MeasurableSet K := hK.measurableSet
    have hzero (p : Plane × Plane) (hp : p ∈ A ×ˢ (Set.univ : Set Plane))
        (hpK : p ∉ K) : rescaledP2P ϑ N s t p ω = 0 := by
      rcases hp with ⟨hpA, _⟩
      have hxS : latticePoint N p.1 ∈ Sx := ⟨p.1, hpA, rfl⟩
      have hnotball : p.2 ∉ Metric.closedBall (0 : Plane) R := by
        intro h
        exact hpK ⟨hpA, h⟩
      have hnormlarge : R < ‖p.2‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hnotball
      have hpoint : pointToPoint β a n (latticePoint N p.1)
          (latticePoint N p.2) ω = 0 := by
        by_contra hne
        have hreach : Polymer.Reachable n (latticePoint N p.1) (latticePoint N p.2) := by
          by_contra hnreach
          exact hne ((Polymer.pointToPoint_eq_zero_iff β a n
            (latticePoint N p.1) (latticePoint N p.2) ω).2 hnreach)
        have hy : latticePoint N p.2 ∈ Sy := by
          apply Finset.mem_biUnion.mpr
          refine ⟨latticePoint N p.1, ?_, ?_⟩
          · exact hSx.mem_toFinset.mpr hxS
          · exact (Polymer.mem_endpoints_iff _ _ _).2 hreach
        have hcenter : ‖scale • siteToPlane (latticePoint N p.2)‖ ≤ M := by
          apply hM
          exact ⟨scale • siteToPlane (latticePoint N p.2),
            ⟨latticePoint N p.2, hy, rfl⟩, rfl⟩
        have hmesh := Critical2DKPZ.norm_sub_latticePoint_le hN p.2
        rw [(mem_cell_iff N (latticePoint N p.2) p.2).mp
          (mem_cell_latticePoint N p.2)] at hmesh
        have hpbound : ‖p.2‖ ≤ M + scale := by
          calc
            ‖p.2‖ ≤ ‖p.2 - scale • siteToPlane (latticePoint N p.2)‖ +
                ‖scale • siteToPlane (latticePoint N p.2)‖ := norm_le_norm_sub_add _ _
            _ ≤ scale + M := add_le_add hmesh hcenter
            _ = M + scale := by ring
        have : ‖p.2‖ ≤ R := hpbound.trans hMR
        exact (not_lt_of_ge this) hnormlarge
      change ((N : ℝ) / 4) *
          pointToPoint β a n (latticePoint N p.1) (latticePoint N p.2) ω = 0
      rw [hpoint]
      ring
    let S : Set (Plane × Plane) := A ×ˢ (Set.univ : Set Plane)
    have hKS : K ⊆ S := by
      rintro p ⟨hpA, hpB⟩
      exact ⟨hpA, Set.mem_univ _⟩
    have hmass : polymerMeasure ϑ N s t ω S ≤
        polymerMeasure ϑ N s t ω K := by
      rw [polymerMeasure, withDensity_apply _ (by simpa only [S] using hS),
        withDensity_apply _ hKm]
      rw [← lintegral_indicator hS, ← lintegral_indicator hKm]
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ S
      · by_cases hpK : p ∈ K
        · have hp' : p ∈ A ×ˢ (Set.univ : Set Plane) := by simpa only [S] using hp
          rw [Set.indicator_of_mem hp', Set.indicator_of_mem hpK]
        · have hp' : p ∈ A ×ˢ (Set.univ : Set Plane) := by simpa only [S] using hp
          rw [Set.indicator_of_mem hp', Set.indicator_of_notMem hpK]
          rw [hzero p hp' hpK]
          norm_num
      · have hp' : p ∉ A ×ˢ (Set.univ : Set Plane) := by simpa only [S] using hp
        have hpK : p ∉ K := by
          intro h
          exact hp (hKS h)
        rw [Set.indicator_of_notMem hp', Set.indicator_of_notMem hpK]
    have hLF := isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω
    obtain ⟨U, hKU, _, hUfinite⟩ :=
      hK.exists_open_superset_measure_lt_top' (fun x _ => hLF.finiteAtNhds x)
    exact lt_of_le_of_lt hmass (lt_of_le_of_lt (measure_mono hKU) hUfinite)

/-- The polymer measure has finite mass when its second coordinate is restricted to a compact set. -/
theorem polymerMeasure_finite_second_compact (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (ω : Disorder) (B : Set Plane) (hB : IsCompact B) :
    polymerMeasure ϑ N s t ω ((Set.univ : Set Plane) ×ˢ B) < ⊤ := by
  classical
  by_cases hN0 : N = 0
  · subst N
    have hzero : polymerMeasure ϑ 0 s t ω = 0 := by
      rw [polymerMeasure]
      ext E hE
      simp [rescaledP2P]
    rw [hzero]
    simp
  · have hN : 0 < N := Nat.pos_of_ne_zero hN0
    let a := evenCeil ((N : ℝ) * s)
    let b := evenCeil ((N : ℝ) * t)
    let n := b - a
    let β := criticalBeta ϑ N
    let Sz : Set Site := latticePoint N '' B
    have hSz : Sz.Finite := finite_latticePoint_image_of_bounded hB.isBounded
    let Sx : Finset Site := hSz.toFinset.biUnion fun z => Polymer.endpoints z n
    let scale : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹
    let centers : Set Plane := (fun z : Site => scale • siteToPlane z) '' (Sx : Set Site)
    have hcenters : centers.Finite := Sx.finite_toSet.image _
    obtain ⟨M, hM⟩ := (hcenters.image fun x : Plane => ‖x‖).bddAbove
    let R := max 0 (M + scale)
    let K : Set (Plane × Plane) := Metric.closedBall (0 : Plane) R ×ˢ B
    have hR : 0 ≤ R := le_max_left _ _
    have hMR : M + scale ≤ R := le_max_right _ _
    have hball : IsCompact (Metric.closedBall (0 : Plane) R) := isCompact_closedBall _ _
    have hK : IsCompact K := hball.prod hB
    have hS : MeasurableSet ((Set.univ : Set Plane) ×ˢ B) :=
      MeasurableSet.univ.prod hB.measurableSet
    have hKm : MeasurableSet K := hK.measurableSet
    have hzero (p : Plane × Plane) (hp : p ∈ (Set.univ : Set Plane) ×ˢ B)
        (hpK : p ∉ K) : rescaledP2P ϑ N s t p ω = 0 := by
      rcases hp with ⟨_, hpB⟩
      have hyS : latticePoint N p.2 ∈ Sz := ⟨p.2, hpB, rfl⟩
      have hnotball : p.1 ∉ Metric.closedBall (0 : Plane) R := by
        intro h
        exact hpK ⟨h, hpB⟩
      have hnormlarge : R < ‖p.1‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hnotball
      have hpoint : pointToPoint β a n (latticePoint N p.1)
          (latticePoint N p.2) ω = 0 := by
        by_contra hne
        have hreach : Polymer.Reachable n (latticePoint N p.1) (latticePoint N p.2) := by
          by_contra hnreach
          exact hne ((Polymer.pointToPoint_eq_zero_iff β a n
            (latticePoint N p.1) (latticePoint N p.2) ω).2 hnreach)
        have hyend : latticePoint N p.2 ∈
            Polymer.endpoints (latticePoint N p.1) n :=
          (Polymer.mem_endpoints_iff _ _ _).2 hreach
        have hxend : latticePoint N p.1 ∈
            Polymer.endpoints (latticePoint N p.2) n := mem_endpoints_reverse hyend
        have hx : latticePoint N p.1 ∈ Sx := by
          apply Finset.mem_biUnion.mpr
          exact ⟨latticePoint N p.2, hSz.mem_toFinset.mpr hyS, hxend⟩
        have hcenter : ‖scale • siteToPlane (latticePoint N p.1)‖ ≤ M := by
          apply hM
          exact ⟨scale • siteToPlane (latticePoint N p.1),
            ⟨latticePoint N p.1, hx, rfl⟩, rfl⟩
        have hmesh := Critical2DKPZ.norm_sub_latticePoint_le hN p.1
        rw [(mem_cell_iff N (latticePoint N p.1) p.1).mp
          (mem_cell_latticePoint N p.1)] at hmesh
        have hpbound : ‖p.1‖ ≤ M + scale := by
          calc
            ‖p.1‖ ≤ ‖p.1 - scale • siteToPlane (latticePoint N p.1)‖ +
                ‖scale • siteToPlane (latticePoint N p.1)‖ := norm_le_norm_sub_add _ _
            _ ≤ scale + M := add_le_add hmesh hcenter
            _ = M + scale := by ring
        have : ‖p.1‖ ≤ R := hpbound.trans hMR
        exact (not_lt_of_ge this) hnormlarge
      change ((N : ℝ) / 4) *
          pointToPoint β a n (latticePoint N p.1) (latticePoint N p.2) ω = 0
      rw [hpoint]
      ring
    let S : Set (Plane × Plane) := (Set.univ : Set Plane) ×ˢ B
    have hKS : K ⊆ S := by
      rintro p ⟨hpA, hpB⟩
      exact ⟨Set.mem_univ _, hpB⟩
    have hmass : polymerMeasure ϑ N s t ω S ≤
        polymerMeasure ϑ N s t ω K := by
      rw [polymerMeasure, withDensity_apply _ (by simpa only [S] using hS),
        withDensity_apply _ hKm]
      rw [← lintegral_indicator hS, ← lintegral_indicator hKm]
      apply lintegral_mono
      intro p
      by_cases hp : p ∈ S
      · by_cases hpK : p ∈ K
        · have hp' : p ∈ (Set.univ : Set Plane) ×ˢ B := by simpa only [S] using hp
          rw [Set.indicator_of_mem hp', Set.indicator_of_mem hpK]
        · have hp' : p ∈ (Set.univ : Set Plane) ×ˢ B := by simpa only [S] using hp
          rw [Set.indicator_of_mem hp', Set.indicator_of_notMem hpK]
          rw [hzero p hp' hpK]
          norm_num
      · have hp' : p ∉ (Set.univ : Set Plane) ×ˢ B := by simpa only [S] using hp
        have hpK : p ∉ K := by
          intro h
          exact hp (hKS h)
        rw [Set.indicator_of_notMem hp', Set.indicator_of_notMem hpK]
    have hLF := isLocallyFiniteMeasure_polymerMeasure ϑ N s t ω
    obtain ⟨U, hKU, _, hUfinite⟩ :=
      hK.exists_open_superset_measure_lt_top' (fun x _ => hLF.finiteAtNhds x)
    exact lt_of_le_of_lt hmass (lt_of_le_of_lt (measure_mono hKU) hUfinite)

private theorem exists_start_cutoff_for_terminal_support (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s t : ℝ) (ω : Disorder)
    (ψ : C_c(Plane, ℝ)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x y : Plane,
      ψ y ≠ 0 →
      pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
        (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
        (latticePoint N x) (latticePoint N y) ω ≠ 0 → ‖x‖ ≤ R := by
  classical
  have hNpos : 0 < N := by omega
  let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let Sy : Set Site := latticePoint N '' tsupport ψ
  have hSy : Sy.Finite := finite_latticePoint_image_of_bounded ψ.hasCompactSupport.isBounded
  let Sx : Finset Site := hSy.toFinset.biUnion fun z => Polymer.endpoints z n
  let scale : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹
  let centers : Set Plane := (fun z : Site => scale • siteToPlane z) '' (Sx : Set Site)
  have hcenters : centers.Finite := Sx.finite_toSet.image _
  obtain ⟨M, hM⟩ := (hcenters.image fun z : Plane => ‖z‖).bddAbove
  let R := max 0 (M + scale)
  have hR : 0 ≤ R := le_max_left _ _
  have hMR : M + scale ≤ R := le_max_right _ _
  refine ⟨R, hR, ?_⟩
  intro x y hy hptp
  have hyS : latticePoint N y ∈ Sy := ⟨y, subset_tsupport ψ (Function.mem_support.mpr hy), rfl⟩
  have hreach : Polymer.Reachable n (latticePoint N x) (latticePoint N y) := by
    by_contra hnreach
    exact hptp ((Polymer.pointToPoint_eq_zero_iff (criticalBeta ϑ N)
      (evenCeil ((N : ℝ) * s)) n (latticePoint N x) (latticePoint N y)
      ω).2 hnreach)
  have hxend : latticePoint N x ∈ Sx := by
    apply Finset.mem_biUnion.mpr
    exact ⟨latticePoint N y, hSy.mem_toFinset.mpr hyS,
      mem_endpoints_reverse ((Polymer.mem_endpoints_iff _ _ _).2 hreach)⟩
  have hcenter : ‖scale • siteToPlane (latticePoint N x)‖ ≤ M := by
    apply hM
    exact ⟨scale • siteToPlane (latticePoint N x), ⟨latticePoint N x, hxend, rfl⟩, rfl⟩
  have hmesh := Critical2DKPZ.norm_sub_latticePoint_le hNpos x
  rw [(mem_cell_iff N (latticePoint N x) x).mp (mem_cell_latticePoint N x)] at hmesh
  have hxbound : ‖x‖ ≤ M + scale := by
    calc
      ‖x‖ ≤ ‖x - scale • siteToPlane (latticePoint N x)‖ +
          ‖scale • siteToPlane (latticePoint N x)‖ := norm_le_norm_sub_add _ _
      _ ≤ scale + M := add_le_add hmesh hcenter
      _ = M + scale := by ring
  exact hxbound.trans hMR

private theorem integral_secondMarginal_cutoff_eq_tensor
    (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder)
    (ψ : C_c(Plane, ℝ)) (R : ℝ) (hR : 0 ≤ R)
    (hreach : ∀ x y : Plane, ψ y ≠ 0 →
      pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
        (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
        (latticePoint N x) (latticePoint N y) ω ≠ 0 → ‖x‖ ≤ R) :
    ∫ y, ψ y ∂((polymerMeasure ϑ N s t ω).map Prod.snd) =
      ∫ p, compactTensorTest (polymerTailCutoff R hR) ψ p
        ∂(polymerMeasure ϑ N s t ω) := by
  calc
    _ = ∫ p, ψ p.2 ∂(polymerMeasure ϑ N s t ω) := by
      exact integral_map measurable_snd.aemeasurable
        ψ.continuous.measurable.aestronglyMeasurable
    _ = _ := by
      rw [integral_polymerMeasure, integral_polymerMeasure]
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hψ : ψ p.2 = 0
      · simp [compactTensorTest_apply, hψ]
      · by_cases hptp : pointToPoint (criticalBeta ϑ N)
            (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
            (latticePoint N p.1) (latticePoint N p.2) ω = 0
        · simp [rescaledP2P, compactTensorTest_apply, hptp]
        · have hbound := hreach p.1 p.2 hψ hptp
          have hcut := polymerTailCutoff_eq_one R hR p.1 hbound
          simp [compactTensorTest_apply, hcut]

private theorem integral_compactTensor_cell_eq_product
    (N : ℕ) (hN : 0 < N) (g g' : C_c(Plane, ℝ)) (a b : Site)
    (hg : ∀ x, |g x| ≤ 1) (hg' : ∀ x, |g' x| ≤ 1) :
    ∫ p in cell N a ×ˢ cell N b, compactTensorTest g g' p =
      (∫ x in cell N a, g x) * (∫ y in cell N b, g' y) := by
  have hbound (p : Plane × Plane) :
      ‖compactTensorTest g g' p‖ ≤ 1 := by
    rw [compactTensorTest_apply, Real.norm_eq_abs, abs_mul]
    calc
      |g p.1| * |g' p.2| ≤ |g p.1| * 1 :=
        mul_le_mul_of_nonneg_left (hg' p.2) (abs_nonneg _)
      _ ≤ 1 := by simpa using hg p.1
  rw [integral_cellPair_eq_iterated N hN
    (compactTensorTest g g') (compactTensorTest g g').continuous.measurable 1 hbound a b]
  calc
    (∫ x in cell N a, ∫ y in cell N b, compactTensorTest g g' (x, y)) =
        ∫ x in cell N a, g x * (∫ y in cell N b, g' y) := by
          apply setIntegral_congr_fun (measurableSet_cell N a)
          intro x _
          have hfun : (fun y : Plane => compactTensorTest g g' (x, y)) =
              fun y => g x * g' y := by
            funext y
            exact compactTensorTest_apply g g' (x, y)
          have hIntegral :
              (∫ y in cell N b, compactTensorTest g g' (x, y)) =
                ∫ y in cell N b, g x * g' y := by
            apply integral_congr_ae
            exact Filter.Eventually.of_forall fun y => congrFun hfun y
          change
            (∫ y in cell N b, compactTensorTest g g' (x, y)) =
              g x * (∫ y in cell N b, g' y)
          rw [hIntegral, integral_const_mul]
    _ = (∫ x in cell N a, g x) * (∫ y in cell N b, g' y) := by
          rw [integral_mul_const]

private theorem integral_latticeStep_compactTest_cellSum
    (N : ℕ) (ψ : C_c(Plane, ℝ)) (G : Site → ℝ) :
    ∫ x, ψ x * G (latticePoint N x) =
      ∑ z ∈ (finite_latticePoint_image_of_bounded (N := N)
          ψ.hasCompactSupport.isBounded).toFinset,
        (∫ x in cell N z, ψ x) * G z := by
  classical
  let S : Finset Site :=
    (finite_latticePoint_image_of_bounded (N := N)
      ψ.hasCompactSupport.isBounded).toFinset
  let Gcut : Site → ℝ := fun z => if z ∈ S then G z else 0
  let C : ℝ := ∑ z ∈ S, |G z|
  have hGcut (z : Site) : ‖Gcut z‖ ≤ C := by
    dsimp only [Gcut, C]
    split_ifs with hz
    · rw [Real.norm_eq_abs]
      exact Finset.single_le_sum (fun y hy => abs_nonneg (G y)) hz
    · rw [norm_zero]
      exact Finset.sum_nonneg fun y hy => abs_nonneg (G y)
  have hfun (x : Plane) : ψ x * G (latticePoint N x) =
      ψ x * Gcut (latticePoint N x) := by
    by_cases hψ : ψ x = 0
    · simp [hψ]
    · have hts : x ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hψ)
      have hsite : latticePoint N x ∈ latticePoint N '' tsupport ψ := ⟨x, hts, rfl⟩
      have hS : latticePoint N x ∈ S := by
        exact (finite_latticePoint_image_of_bounded (N := N)
          ψ.hasCompactSupport.isBounded).mem_toFinset.mpr hsite
      simp [Gcut, hS]
  have hsum := integral_latticeStep_eq_cellTsum N ψ Gcut C hGcut
  calc
    _ = ∫ x, ψ x * Gcut (latticePoint N x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hfun
    _ = ∑' z, (∫ x in cell N z, ψ x) * Gcut z := hsum
    _ = ∑ z ∈ S, (∫ x in cell N z, ψ x) * Gcut z := by
      apply tsum_eq_sum (s := S)
      intro z hz
      simp [Gcut, hz]
    _ = ∑ z ∈ S, (∫ x in cell N z, ψ x) * G z := by
      apply Finset.sum_congr rfl
      intro z hz
      simp [Gcut, hz]
    _ = _ := by simp [S]

private theorem integral_flatFirstMarginal_eq_endpointProfile
    (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N) (n : ℕ) (hn : Even n)
    (ψ : C_c(Plane, ℝ)) (hψ : ∀ x, 0 ≤ ψ x) (ω : Disorder) :
    ∫ x, |ψ x| ∂((polymerMeasure ϑ N 0 ((n : ℝ) / N) ω).map Prod.fst) =
      ∑ z ∈ (finite_latticePoint_image_of_bounded (N := N)
          ψ.hasCompactSupport.isBounded).toFinset,
        (∫ x in cell N z, ψ x) *
          pointToPlane (criticalBeta ϑ N) 0 n z ω := by
  have hNpos : 0 < N := by omega
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hscale : (N : ℝ) * ((n : ℝ) / N) = n := by
    field_simp
  have hnclock : evenCeil ((N : ℝ) * ((n : ℝ) / N)) = n := by
    rw [hscale]
    rcases hn with ⟨k, hk⟩
    rw [hk]
    simp [evenCeil]
    ring
  have hprofile := integral_latticeStep_compactTest_cellSum N ψ
    (fun z => pointToPlane (criticalBeta ϑ N) 0 n z ω)
  calc
    _ = ∫ x, ψ x ∂((polymerMeasure ϑ N 0 ((n : ℝ) / N) ω).map Prod.fst) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => abs_of_nonneg (hψ x)
    _ = ∫ x, ψ x * rescaledP2Plane ϑ N 0 ((n : ℝ) / N) x ω :=
      integral_map_fst_polymerMeasure ϑ hN 0 ((n : ℝ) / N) ω ψ
    _ = ∫ x, ψ x *
          pointToPlane (criticalBeta ϑ N) 0 n (latticePoint N x) ω := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp [rescaledP2Plane, hnclock]
    _ = _ := hprofile

private theorem integral_secondMarginal_cutoff_eq_endpointProfile
    (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N) (s t : ℝ) (hst : s ≤ t) (ω : Disorder)
    (R : ℝ) (hR : 0 ≤ R) :
    ∫ y, polymerTailCutoff R hR y
        ∂((polymerMeasure ϑ N s t ω).map Prod.snd) =
      ∑ z ∈ (finite_latticePoint_image_of_bounded (N := N)
          (polymerTailCutoff R hR).hasCompactSupport.isBounded).toFinset,
        (∫ y in cell N z, polymerTailCutoff R hR y) *
          ∑ x ∈ Polymer.endpoints z
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)),
              pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
                (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) x z ω := by
  classical
  let ψ : C_c(Plane, ℝ) := polymerTailCutoff R hR
  let β := criticalBeta ϑ N
  let a := evenCeil ((N : ℝ) * s)
  let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let Z : Finset Site :=
    (finite_latticePoint_image_of_bounded (N := N) ψ.hasCompactSupport.isBounded).toFinset
  obtain ⟨Rstart, hRstart, hreach⟩ :=
    exists_start_cutoff_for_terminal_support ϑ hN s t ω ψ
  let g : C_c(Plane, ℝ) := polymerTailCutoff Rstart hRstart
  have hgnorm : ∀ x, |g x| ≤ 1 := by
    intro x
    change |polymerTailCutoff Rstart hRstart x| ≤ 1
    rw [abs_of_nonneg (polymerTailCutoff_nonneg Rstart hRstart x)]
    exact polymerTailCutoff_le_one Rstart hRstart x
  have hψnorm : ∀ x, |ψ x| ≤ 1 := by
    intro x
    change |polymerTailCutoff R hR x| ≤ 1
    rw [abs_of_nonneg (polymerTailCutoff_nonneg R hR x)]
    exact polymerTailCutoff_le_one R hR x
  have hTensor := integral_secondMarginal_cutoff_eq_tensor
    ϑ N s t ω ψ Rstart hRstart hreach
  let Q : Finset (Site × Site) :=
    Z.biUnion fun z => (Polymer.endpoints z n).image fun x => (x, z)
  have hcellzero (z : Site) (hz : z ∉ Z) :
      ∫ y in cell N z, ψ y = 0 := by
    calc
      _ = ∫ y in cell N z, (0 : ℝ) := by
        apply setIntegral_congr_fun (measurableSet_cell N z)
        intro y hy
        by_contra hψy
        have hyts : y ∈ tsupport ψ := subset_tsupport ψ (Function.mem_support.mpr hψy)
        have hzimage : latticePoint N y ∈
            latticePoint N '' tsupport ψ := ⟨y, hyts, rfl⟩
        have hyz : latticePoint N y = z := (mem_cell_iff N z y).mp hy
        apply hz
        apply (finite_latticePoint_image_of_bounded (N := N)
          ψ.hasCompactSupport.isBounded).mem_toFinset.mpr
        rw [← hyz]
        exact hzimage
      _ = 0 := by simp
  have hcell (x z : Site) :
      ∫ p in cell N x ×ˢ cell N z, compactTensorTest g ψ p =
        (∫ p in cell N x, g p) * (∫ p in cell N z, ψ p) :=
    integral_compactTensor_cell_eq_product N (by omega) g ψ x z hgnorm hψnorm
  have htermzero (q : Site × Site) (hq : q ∉ Q) :
      (∫ p in cell N q.1 ×ˢ cell N q.2, compactTensorTest g ψ p) *
        ((N : ℝ) / 4 * pointToPoint β a n q.1 q.2 ω) = 0 := by
    rcases q with ⟨x, z⟩
    rw [hcell]
    by_cases hz : z ∈ Z
    · have hx : x ∉ Polymer.endpoints z n := by
        intro hx
        apply hq
        exact Finset.mem_biUnion.mpr ⟨z, hz,
          Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
      have hptp : pointToPoint β a n x z ω = 0 := by
        by_contra hpne
        have hforward : z ∈ Polymer.endpoints x n := by
          apply (Polymer.mem_endpoints_iff x z n).2
          by_contra hnot
          exact hpne ((Polymer.pointToPoint_eq_zero_iff β a n x z ω).2 hnot)
        have hreverse := mem_endpoints_reverse hforward
        exact hx hreverse
      rw [hptp]
      ring
    · rw [hcellzero z hz]
      ring
  have hsumQ :
      ∑' q : Site × Site,
        (∫ p in cell N q.1 ×ˢ cell N q.2, compactTensorTest g ψ p) *
          ((N : ℝ) / 4 * pointToPoint β a n q.1 q.2 ω) =
        ∑ q ∈ Q,
          (∫ p in cell N q.1 ×ˢ cell N q.2, compactTensorTest g ψ p) *
            ((N : ℝ) / 4 * pointToPoint β a n q.1 q.2 ω) :=
    tsum_eq_sum (s := Q) htermzero
  have hterminalSupport (z : Site) (hz : z ∈ Z)
      (hc : (∫ y in cell N z, ψ y) ≠ 0) :
      ∃ y ∈ cell N z, ψ y ≠ 0 := by
    by_contra h
    push Not at h
    have hzero' : ∫ y in cell N z, ψ y = 0 := by
      calc
        _ = ∫ y in cell N z, (0 : ℝ) := by
          apply setIntegral_congr_fun (measurableSet_cell N z)
          intro y hy
          exact h y hy
        _ = 0 := by simp
    exact hc hzero'
  have hfactor (x z : Site) (hz : z ∈ Z) (hx : x ∈ Polymer.endpoints z n)
      (hc : (∫ y in cell N z, ψ y) ≠ 0)
      (hp : pointToPoint β a n x z ω ≠ 0) :
      (∫ p in cell N x, g p) * (∫ p in cell N z, ψ p) *
          ((N : ℝ) / 4 * pointToPoint β a n x z ω) =
        (∫ y in cell N z, ψ y) * pointToPoint β a n x z ω := by
    obtain ⟨y, hycell, hyψ⟩ := hterminalSupport z hz hc
    have hzEven : z ∈ evenLattice := by
      rw [← (mem_cell_iff N z y).mp hycell]
      exact latticePoint_mem_evenLattice N y
    have hnEven : Even n := by
      dsimp [n]
      exact Critical2DKPZ.Smoothing.evenCeil_sub_even
        (mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N))
    have hxEven : x ∈ evenLattice := by
      apply even_mem_endpoints_of_even hzEven hnEven
      exact hx
    have hgcell : ∫ p in cell N x, g p = 4 / (N : ℝ) := by
      calc
        _ = ∫ p in cell N x, (1 : ℝ) := by
          apply setIntegral_congr_fun (measurableSet_cell N x)
          intro p hpCell
          have hptp' : pointToPoint (criticalBeta ϑ N)
              (evenCeil ((N : ℝ) * s))
              (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
              (latticePoint N p) (latticePoint N y) ω ≠ 0 := by
            simpa [a, n, (mem_cell_iff N x p).mp hpCell,
              (mem_cell_iff N z y).mp hycell] using hp
          exact polymerTailCutoff_eq_one Rstart hRstart p (hreach p y hyψ hptp')
        _ = (volume (cell N x)).toReal := by simp [measureReal_def]
        _ = 4 / (N : ℝ) := volume_cell_toReal (by omega) hxEven
    rw [hgcell]
    have hNne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < N))
    field_simp [hNne]
  have hrewrite :
      (∑ q ∈ Q,
        (∫ p in cell N q.1 ×ˢ cell N q.2, compactTensorTest g ψ p) *
          ((N : ℝ) / 4 * pointToPoint β a n q.1 q.2 ω)) =
      ∑ z ∈ Z,
        (∫ y in cell N z, ψ y) *
          ∑ x ∈ Polymer.endpoints z n, pointToPoint β a n x z ω := by
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro z hz
      rw [Finset.sum_image]
      · calc
          (∑ x ∈ Polymer.endpoints z n,
              (∫ p in cell N (x, z).1 ×ˢ cell N (x, z).2, compactTensorTest g ψ p) *
                ((N : ℝ) / 4 * pointToPoint β a n (x, z).1 (x, z).2 ω)) =
              ∑ x ∈ Polymer.endpoints z n,
                (∫ y in cell N z, ψ y) * pointToPoint β a n x z ω := by
            apply Finset.sum_congr rfl
            intro x hx
            rw [hcell]
            by_cases hc : (∫ y in cell N z, ψ y) = 0
            · simp [hc]
            · by_cases hp : pointToPoint β a n x z ω = 0
              · simp [hp]
              · exact hfactor x z hz hx hc hp
          _ = (∫ y in cell N z, ψ y) *
              ∑ x ∈ Polymer.endpoints z n, pointToPoint β a n x z ω := by
            rw [Finset.mul_sum]
      · intro x hx y hy hxy
        exact congrArg Prod.fst hxy
    · intro z hz z' hz' hzz'
      apply Finset.disjoint_left.mpr
      intro q hq hq'
      rcases Finset.mem_image.mp hq with ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hq' with ⟨x', hx', hxx'⟩
      exact hzz' (congrArg Prod.snd hxx').symm
  calc
    _ = ∫ p, compactTensorTest g ψ p ∂(polymerMeasure ϑ N s t ω) := hTensor
    _ = ∑' q : Site × Site,
          (∫ p in cell N q.1 ×ˢ cell N q.2, compactTensorTest g ψ p) *
            ((N : ℝ) / 4 * pointToPoint β a n q.1 q.2 ω) :=
      integral_polymerMeasure_cellTsum ϑ N s t ω (compactTensorTest g ψ)
    _ = ∑ q ∈ Q,
          (∫ p in cell N q.1 ×ˢ cell N q.2, compactTensorTest g ψ p) *
            ((N : ℝ) / 4 * pointToPoint β a n q.1 q.2 ω) := hsumQ
    _ = ∑ z ∈ Z,
          (∫ y in cell N z, ψ y) *
            ∑ x ∈ Polymer.endpoints z n, pointToPoint β a n x z ω := hrewrite
    _ = ∑ z ∈ (finite_latticePoint_image_of_bounded (N := N)
          (polymerTailCutoff R hR).hasCompactSupport.isBounded).toFinset,
          (∫ y in cell N z, polymerTailCutoff R hR y) *
            ∑ x ∈ Polymer.endpoints z
              (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)),
                pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
                  (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) x z ω := by
        simp [ψ, β, a, n, Z]


private theorem polymerMeasure_compact_first_mass_le_flatCutoff
    (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder)
    (A : Set Plane) (hA : IsCompact A) (B : ℝ) (hB : 0 ≤ B)
    (hAbox : ∀ x ∈ A, ‖x‖ ≤ B) :
    (polymerMeasure ϑ N s t ω (A ×ˢ (Set.univ : Set Plane))).toReal ≤
      ∫ x, |polymerTailCutoff B hB x| ∂((polymerMeasure ϑ N s t ω).map Prod.fst) := by
  let S : Set (Plane × Plane) := A ×ˢ (Set.univ : Set Plane)
  let μ := polymerMeasure ϑ N s t ω
  let m := μ.map Prod.fst
  have hAmeas : MeasurableSet A := hA.measurableSet
  have hSmeas : MeasurableSet S := hAmeas.prod MeasurableSet.univ
  have hpre : Prod.fst ⁻¹' A = S := by
    ext p
    simp [S]
  have hmass : μ S < ⊤ := by
    simpa only [S] using polymerMeasure_finite_first_compact ϑ N s t ω A hA
  have hmap : m A = μ S := by
    rw [Measure.map_apply measurable_fst hAmeas, hpre]
  have hmA : m A < ⊤ := by rw [hmap]; exact hmass
  have hsubset : S ⊆ Prod.fst ⁻¹' A := by
    rintro ⟨x, y⟩ hp
    exact hp.1
  have hmassLe : μ S ≤ m A := by
    calc
      μ S ≤ μ (Prod.fst ⁻¹' A) := measure_mono hsubset
      _ = m A := (Measure.map_apply measurable_fst hAmeas).symm
  have hmassReal : (μ S).toReal ≤ (m A).toReal :=
    ENNReal.toReal_mono hmA.ne hmassLe
  let χ : C_c(Plane, ℝ) := polymerTailCutoff B hB
  let K : Set Plane := tsupport (χ : Plane → ℝ)
  have hK : IsCompact K := χ.hasCompactSupport
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hKmass : m K < ⊤ := by
    rw [Measure.map_apply measurable_fst hKmeas]
    have hpreK : Prod.fst ⁻¹' K = K ×ˢ (Set.univ : Set Plane) := by
      ext p
      simp
    rw [hpreK]
    exact polymerMeasure_finite_first_compact ϑ N s t ω K hK
  have hmajorOn : IntegrableOn (fun _ : Plane => (1 : ℝ)) K m :=
    integrableOn_const hKmass.ne
  have hmajor : Integrable (K.indicator (fun _ : Plane => (1 : ℝ))) m :=
    hmajorOn.integrable_indicator hKmeas
  have hχint : Integrable (fun x => |χ x|) m := by
    apply hmajor.mono' (χ.continuous.abs.aestronglyMeasurable)
    filter_upwards [] with x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      simpa [χ, Real.norm_eq_abs, abs_abs,
        abs_of_nonneg (polymerTailCutoff_nonneg B hB x)] using
        (polymerTailCutoff_le_one B hB x)
    · have hχzero : χ x = 0 := by
        by_contra hne
        exact hx (subset_tsupport χ (Function.mem_support.mpr hne))
      simp [Set.indicator, hx, hχzero]
  have hIndicatorInt :
      Integrable (A.indicator (fun _ : Plane => (1 : ℝ))) m := by
    rw [integrable_indicator_iff hAmeas]
    exact integrableOn_const hmA.ne
  have hpoint (x : Plane) :
      A.indicator (fun _ : Plane => (1 : ℝ)) x ≤ |χ x| := by
    by_cases hx : x ∈ A
    · rw [Set.indicator_of_mem hx]
      have hχone : χ x = 1 := polymerTailCutoff_eq_one B hB x (hAbox x hx)
      rw [hχone]
      norm_num
    · rw [Set.indicator_of_notMem hx]
      exact abs_nonneg _
  have hpairing : m.real A ≤ ∫ x, |χ x| ∂m := by
    rw [← integral_indicator_one hAmeas]
    exact integral_mono hIndicatorInt hχint hpoint
  calc
    _ = (μ S).toReal := rfl
    _ ≤ (m A).toReal := hmassReal
    _ = m.real A := rfl
    _ ≤ _ := by simpa only [m, χ] using hpairing

/-- A compact terminal mass is bounded by its flat terminal cutoff integral. -/
theorem polymerMeasure_compact_second_mass_le_flatCutoff
    (ϑ : ℝ) (N : ℕ) (s t : ℝ) (ω : Disorder)
    (Bset : Set Plane) (hBset : IsCompact Bset) (R : ℝ) (hR : 0 ≤ R)
    (hBbox : ∀ y ∈ Bset, ‖y‖ ≤ R) :
    (polymerMeasure ϑ N s t ω ((Set.univ : Set Plane) ×ˢ Bset)).toReal ≤
      ∫ y, |polymerTailCutoff R hR y| ∂((polymerMeasure ϑ N s t ω).map Prod.snd) := by
  let S : Set (Plane × Plane) := (Set.univ : Set Plane) ×ˢ Bset
  let μ := polymerMeasure ϑ N s t ω
  let m := μ.map Prod.snd
  have hBmeas : MeasurableSet Bset := hBset.measurableSet
  have hSmeas : MeasurableSet S := MeasurableSet.univ.prod hBmeas
  have hpre : Prod.snd ⁻¹' Bset = S := by
    ext p
    simp [S]
  have hmass : μ S < ⊤ := by
    simpa only [S] using polymerMeasure_finite_second_compact ϑ N s t ω Bset hBset
  have hmap : m Bset = μ S := by
    rw [Measure.map_apply measurable_snd hBmeas, hpre]
  have hmB : m Bset < ⊤ := by rw [hmap]; exact hmass
  have hmassLe : μ S ≤ m Bset := by
    rw [hmap]
  have hmassReal : (μ S).toReal ≤ (m Bset).toReal :=
    ENNReal.toReal_mono hmB.ne hmassLe
  let χ : C_c(Plane, ℝ) := polymerTailCutoff R hR
  let K : Set Plane := tsupport (χ : Plane → ℝ)
  have hK : IsCompact K := χ.hasCompactSupport
  have hKmeas : MeasurableSet K := hK.measurableSet
  have hKmass : m K < ⊤ := by
    rw [Measure.map_apply measurable_snd hKmeas]
    have hpreK : Prod.snd ⁻¹' K = (Set.univ : Set Plane) ×ˢ K := by
      ext p
      simp
    rw [hpreK]
    exact polymerMeasure_finite_second_compact ϑ N s t ω K hK
  have hmajorOn : IntegrableOn (fun _ : Plane => (1 : ℝ)) K m :=
    integrableOn_const hKmass.ne
  have hmajor : Integrable (K.indicator (fun _ : Plane => (1 : ℝ))) m :=
    hmajorOn.integrable_indicator hKmeas
  have hχint : Integrable (fun y => |χ y|) m := by
    apply hmajor.mono' (χ.continuous.abs.aestronglyMeasurable)
    filter_upwards [] with y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
      simpa [χ, Real.norm_eq_abs, abs_abs,
        abs_of_nonneg (polymerTailCutoff_nonneg R hR y)] using
        (polymerTailCutoff_le_one R hR y)
    · have hχzero : χ y = 0 := by
        by_contra hne
        exact hy (subset_tsupport χ (Function.mem_support.mpr hne))
      simp [Set.indicator, hy, hχzero]
  have hIndicatorInt :
      Integrable (Bset.indicator (fun _ : Plane => (1 : ℝ))) m := by
    rw [integrable_indicator_iff hBmeas]
    exact integrableOn_const hmB.ne
  have hpoint (y : Plane) :
      Bset.indicator (fun _ : Plane => (1 : ℝ)) y ≤ |χ y| := by
    by_cases hy : y ∈ Bset
    · rw [Set.indicator_of_mem hy]
      have hχone : χ y = 1 := polymerTailCutoff_eq_one R hR y (hBbox y hy)
      rw [hχone]
      norm_num
    · rw [Set.indicator_of_notMem hy]
      exact abs_nonneg _
  have hpairing : m.real Bset ≤ ∫ y, |χ y| ∂m := by
    rw [← integral_indicator_one hBmeas]
    exact integral_mono hIndicatorInt hχint hpoint
  calc
    _ = (μ S).toReal := rfl
    _ ≤ (m Bset).toReal := hmassReal
    _ = m.real Bset := rfl
    _ ≤ _ := by simpa only [m, χ] using hpairing

/-- Restrict both outer coordinates to sets containing the support of the compact test. -/
theorem kernelProductPairing_restrict_outer_support
    (μ ν : Measure (Plane × Plane)) (κ : Plane → Plane → ℝ)
    (Φ : C_c(Plane × Plane, ℝ)) (A B : Set Plane)
    [SFinite μ] [SFinite ν]
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (houter : ∀ p, Φ p ≠ 0 → p.1 ∈ A ∧ p.2 ∈ B) :
    kernelProductPairing μ κ ν Φ =
      kernelProductPairing (μ.restrict (A ×ˢ Set.univ)) κ
        (ν.restrict (Set.univ ×ˢ B)) Φ := by
  let S : Set ((Plane × Plane) × (Plane × Plane)) :=
    (A ×ˢ (Set.univ : Set Plane)) ×ˢ ((Set.univ : Set Plane) ×ˢ B)
  let F : ((Plane × Plane) × (Plane × Plane)) → ℝ := fun q =>
    Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1
  have hS : MeasurableSet S := by
    exact (hA.prod MeasurableSet.univ).prod (MeasurableSet.univ.prod hB)
  have hF (q : (Plane × Plane) × (Plane × Plane)) :
      Set.indicator S F q = F q := by
    by_cases hq : q ∈ S
    · simp [hq]
    · have hΦ : Φ (q.1.1, q.2.2) = 0 := by
        by_contra hne
        have hout := houter (q.1.1, q.2.2) hne
        exact hq ⟨⟨hout.1, Set.mem_univ _⟩, ⟨Set.mem_univ _, hout.2⟩⟩
      simp [F, hΦ]
  rw [kernelProductPairing, kernelProductPairing, Measure.prod_restrict]
  rw [← integral_indicator hS]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun q => (hF q).symm

/-- Squaring the deterministic Gaussian cutoff estimate separates the two random mass
products. This is the estimate used after restricting both polymer measures to the compact
outer support of the test. -/
theorem sq_kernelProductPairing_cutoff_error_le_leftTail_add_gaussian
    (μ ν : Measure (Plane × Plane)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Plane → Plane → ℝ) (hκm : Measurable (fun p : Plane × Plane => κ p.1 p.2))
    (C c : ℝ) (hC : 0 ≤ C) (hc : 0 < c)
    (hκ : ∀ x y, |κ x y| ≤ C * Real.exp (-c * ‖x - y‖ ^ 2))
    (Φ : C_c(Plane × Plane, ℝ)) (M : ℝ) (hM : 0 ≤ M)
    (hΦ : ∀ p, |Φ p| ≤ M) (R : ℝ) (hR : 0 ≤ R) :
    (kernelProductPairing μ κ ν Φ -
      ∫ q, Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 *
        ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂(μ.prod ν)) ^ 2 ≤
      2 * (M * C) ^ 2 *
          (μ.real (kernelProductSecondTail (R / 2)) * ν.real Set.univ) ^ 2 +
        2 * (M * C) ^ 2 *
          (Real.exp (-c * (R / 2) ^ 2) * μ.real Set.univ * ν.real Set.univ) ^ 2 := by
  let X := μ.real (kernelProductSecondTail (R / 2)) * ν.real Set.univ
  let Y := Real.exp (-c * (R / 2) ^ 2) * μ.real Set.univ * ν.real Set.univ
  have hX : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (ENNReal.toReal_nonneg) (ENNReal.toReal_nonneg)
  have hY : 0 ≤ Y := by
    dsimp [Y]
    positivity
  have hdet := abs_kernelProductPairing_cutoff_error_le_leftTail_add_gaussian
    μ ν κ hκm C c hC hc hκ Φ M hM hΦ R hR
  have herror :
      |kernelProductPairing μ κ ν Φ -
        ∫ q, Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 *
          ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂(μ.prod ν)| ≤
        M * C * (X + Y) := by
    simpa only [X, Y, mul_assoc] using hdet
  have hsum : 0 ≤ X + Y := add_nonneg hX hY
  have hcoef : 0 ≤ M * C := mul_nonneg hM hC
  let E := kernelProductPairing μ κ ν Φ -
    ∫ q, Φ (q.1.1, q.2.2) * κ q.1.2 q.2.1 *
      ballCutoff R q.1.2 * ballCutoff R q.2.1 ∂(μ.prod ν)
  have hboundNonneg : 0 ≤ M * C * (X + Y) := mul_nonneg hcoef hsum
  have herror' : |E| ≤ M * C * (X + Y) := by simpa [E] using herror
  have herrorSq : E ^ 2 ≤ (M * C * (X + Y)) ^ 2 := by
    have hmul := mul_le_mul herror' herror' (abs_nonneg E) hboundNonneg
    have hEabs : |E| * |E| = E ^ 2 := by
      rw [← sq_abs]
      ring
    calc
      E ^ 2 = |E| * |E| := hEabs.symm
      _ ≤ M * C * (X + Y) * (M * C * (X + Y)) := hmul
      _ = (M * C * (X + Y)) ^ 2 := by ring
  have hadd : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by
    nlinarith [sq_nonneg (X - Y)]
  calc
    _ ≤ (M * C * (X + Y)) ^ 2 := herrorSq
    _ = (M * C) ^ 2 * (X + Y) ^ 2 := by ring
    _ ≤ (M * C) ^ 2 * (2 * X ^ 2 + 2 * Y ^ 2) :=
      mul_le_mul_of_nonneg_left hadd (sq_nonneg (M * C))
    _ = 2 * (M * C) ^ 2 * X ^ 2 + 2 * (M * C) ^ 2 * Y ^ 2 := by ring
    _ = _ := by rfl

/-- Summing the arrival kernel over its terminal site removes the final unweighted walk step. -/
theorem tsum_preTerminalKernel_eq_pointToPlane (β : ℝ) (a n : ℕ) (w : Site)
    (ω : Disorder) :
    ∑' y, preTerminalKernel β a n w y ω = pointToPlane β a n w ω := by
  classical
  let S : Finset Site := Polymer.endpoints w n
  let T : Finset Site := S.biUnion (fun z => Polymer.endpoints z 1)
  have hzero (y : Site) (hy : y ∉ T) :
      preTerminalKernel β a n w y ω = 0 := by
    rw [preTerminalKernel]
    have hterm (z : Site) :
        pointToPoint β a n w z ω * srwKernel 1 (y - z) = 0 := by
      by_cases hz : z ∈ S
      · have hyz : y ∉ Polymer.endpoints z 1 := by
          intro hmem
          exact hy (Finset.mem_biUnion.mpr ⟨z, hz, hmem⟩)
        rw [Polymer.srwKernel_eq_zero_of_not_mem 1 z y hyz]
        simp
      · rw [Polymer.pointToPoint_eq_zero_of_not_mem β a n w z ω (by simpa [S] using hz)]
        simp
    have heq : (fun z => pointToPoint β a n w z ω * srwKernel 1 (y - z)) =
        fun _ => (0 : ℝ) := funext hterm
    rw [heq, tsum_zero]
  have hsum :
      (∑' y : Site, preTerminalKernel β a n w y ω) =
        ∑ y ∈ T, preTerminalKernel β a n w y ω :=
    tsum_eq_sum (s := T) hzero
  have hinner (y : Site) :
      preTerminalKernel β a n w y ω =
        ∑ z ∈ S, pointToPoint β a n w z ω * srwKernel 1 (y - z) := by
    rw [preTerminalKernel, Polymer.tsum_pointToPoint_mul_eq_sum β a n w
      (fun z => srwKernel 1 (y - z)) ω]
  rw [hsum]
  calc
    (∑ y ∈ T, preTerminalKernel β a n w y ω) =
        ∑ y ∈ T, ∑ z ∈ S,
          pointToPoint β a n w z ω * srwKernel 1 (y - z) := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [hinner]
    _ = ∑ z ∈ S, pointToPoint β a n w z ω *
          (∑ y ∈ T, srwKernel 1 (y - z)) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro z hz
            rw [Finset.mul_sum]
    _ = ∑ z ∈ S, pointToPoint β a n w z ω := by
          apply Finset.sum_congr rfl
          intro z hz
          have hsubset : Polymer.endpoints z 1 ⊆ T := by
            intro y hy
            exact Finset.mem_biUnion.mpr ⟨z, hz, hy⟩
          have hkernel :
              (∑ y ∈ T, srwKernel 1 (y - z)) = 1 := by
            calc
              _ = ∑ y ∈ Polymer.endpoints z 1, srwKernel 1 (y - z) := by
                symm
                apply Finset.sum_subset hsubset
                intro y hyT hyNot
                exact Polymer.srwKernel_eq_zero_of_not_mem 1 z y hyNot
              _ = 1 := Polymer.sum_srwKernel_endpoints 1 z
          rw [hkernel, mul_one]
    _ = pointToPlane β a n w ω := by
          rw [← Polymer.tsum_pointToPoint]
          symm
          exact tsum_eq_sum (s := S) (fun z hz =>
            Polymer.pointToPoint_eq_zero_of_not_mem β a n w z ω (by simpa [S] using hz))

/-- Reversing a point-to-point kernel and summing its initial site leaves a single fresh
Gaussian boundary factor times the preceding point-to-plane profile. -/
theorem sum_pointToPoint_initial_endpoint_timeReversal (β : ℝ) {a n : ℕ}
    (hn : 1 ≤ n) (z : Site) (ω : Disorder) :
    (∑ x ∈ Polymer.endpoints z n, pointToPoint β a n x z ω) =
      Real.exp (β * ω (a + n, z) - β ^ 2 / 2) *
        pointToPlane β 0 (n - 1) z (PolymerCalculus.reversedDisorder (a + n) ω) := by
  classical
  let ρ : Disorder := PolymerCalculus.reversedDisorder (a + n) ω
  have hpoint (x : Site) (hx : x ∈ Polymer.endpoints z n) :
      pointToPoint β a n x z ω =
        Real.exp (β * ω (a + n, z) - β ^ 2 / 2) *
          preTerminalKernel β 0 (n - 1) z x ρ := by
    have hrev := PolymerCalculus.pointToPoint_time_reversal β (a + n) a n
      (by omega) x z ω
    have hrev0 : Real.exp (β * ω (a, x)) * pointToPoint β a n x z ω =
        Real.exp (β * ω (a + n, z)) * pointToPoint β 0 n z x ρ := by
      simpa [ρ, Nat.sub_self] using hrev
    have hnoise : ρ (n, x) = ω (a, x) := by
      simp [ρ, PolymerCalculus.reversedDisorder, Gaussian.reindexDisorder,
        PolymerCalculus.timeReversalIndex, PolymerCalculus.reflectedTime]
    have hterminal := pointToPoint_terminalFactor β 0 (n - 1) z x ρ
    have htime : n - 1 + 1 = n := by omega
    simp only [Nat.zero_add] at hterminal
    rw [htime] at hterminal
    have hboltz : Polymer.boltzmann β (n, x) ρ =
        Real.exp (β * ω (a, x) - β ^ 2 / 2) := by
      simp only [Polymer.boltzmann]
      rw [hnoise]
    have hcancel : Real.exp (β * ω (a, x)) *
        (Real.exp (β * ω (a + n, z) - β ^ 2 / 2) *
          preTerminalKernel β 0 (n - 1) z x ρ) =
        Real.exp (β * ω (a + n, z)) *
          (preTerminalKernel β 0 (n - 1) z x ρ *
            Polymer.boltzmann β (n, x) ρ) := by
      rw [hboltz]
      calc
        _ = (Real.exp (β * ω (a, x)) *
              Real.exp (β * ω (a + n, z) - β ^ 2 / 2)) *
              preTerminalKernel β 0 (n - 1) z x ρ := by ring
        _ = Real.exp (β * ω (a, x) +
              (β * ω (a + n, z) - β ^ 2 / 2)) *
              preTerminalKernel β 0 (n - 1) z x ρ := by
              rw [← Real.exp_add]
        _ = Real.exp (β * ω (a + n, z) +
              (β * ω (a, x) - β ^ 2 / 2)) *
              preTerminalKernel β 0 (n - 1) z x ρ := by
              rw [show β * ω (a, x) + (β * ω (a + n, z) - β ^ 2 / 2) =
                β * ω (a + n, z) + (β * ω (a, x) - β ^ 2 / 2) by ring]
        _ = (Real.exp (β * ω (a + n, z)) *
              Real.exp (β * ω (a, x) - β ^ 2 / 2)) *
              preTerminalKernel β 0 (n - 1) z x ρ := by
              rw [Real.exp_add]
        _ = _ := by ring
    have hmul : Real.exp (β * ω (a, x)) * pointToPoint β a n x z ω =
        Real.exp (β * ω (a, x)) *
          (Real.exp (β * ω (a + n, z) - β ^ 2 / 2) *
            preTerminalKernel β 0 (n - 1) z x ρ) := by
      calc
        Real.exp (β * ω (a, x)) * pointToPoint β a n x z ω =
            Real.exp (β * ω (a + n, z)) * pointToPoint β 0 n z x ρ := hrev0
        _ = Real.exp (β * ω (a + n, z)) *
              (preTerminalKernel β 0 (n - 1) z x ρ *
                Polymer.boltzmann β (n, x) ρ) := by rw [hterminal]
        _ = Real.exp (β * ω (a, x)) *
              (Real.exp (β * ω (a + n, z) - β ^ 2 / 2) *
                preTerminalKernel β 0 (n - 1) z x ρ) := hcancel.symm
    exact mul_left_cancel₀ (Real.exp_ne_zero _) hmul
  calc
    (∑ x ∈ Polymer.endpoints z n, pointToPoint β a n x z ω) =
        ∑ x ∈ Polymer.endpoints z n,
          Real.exp (β * ω (a + n, z) - β ^ 2 / 2) *
            preTerminalKernel β 0 (n - 1) z x ρ := by
              apply Finset.sum_congr rfl
              intro x hx
              exact hpoint x hx
    _ = Real.exp (β * ω (a + n, z) - β ^ 2 / 2) *
          ∑ x ∈ Polymer.endpoints z n, preTerminalKernel β 0 (n - 1) z x ρ := by
            rw [Finset.mul_sum]
    _ = Real.exp (β * ω (a + n, z) - β ^ 2 / 2) *
          ∑' x, preTerminalKernel β 0 (n - 1) z x ρ := by
            congr 1
            symm
            exact tsum_eq_sum (s := Polymer.endpoints z n) (fun x hx =>
              preTerminalKernel_eq_zero_of_not_mem β 0 (n - 1) z x ρ (by
                simpa [show n - 1 + 1 = n by omega] using hx))
    _ = _ := by rw [tsum_preTerminalKernel_eq_pointToPlane]

/-- A Gaussian factor on time zero has the same sixth-moment bound as a fresh terminal
factor, when the profiles use only the positive-time block. The estimate is invariant under
a law-preserving permutation exchanging the independent time layers. -/
theorem integral_sixth_initialWeightedBoundaryProfile_le (β : ℝ) (n : ℕ)
    (S : Finset Site) (a : Site → ℝ) (P : Site → Disorder → ℝ)
    (ha : ∀ z ∈ S, 0 ≤ a z)
    (hPblock : ∀ z ∈ S, Measurable[Gaussian.disorderBlock 0 n] (P z))
    (hPnonneg : ∀ z ∈ S, ∀ ω, 0 ≤ P z ω)
    (hQ6 : Integrable (fun ω => (∑ z ∈ S, a z * P z ω) ^ 6) disorderLaw) :
    Integrable (fun ω =>
      (∑ z ∈ S, a z * Real.exp (β * ω (0, z) - β ^ 2 / 2) * P z ω) ^ 6)
        disorderLaw ∧
    ∫ ω, (∑ z ∈ S, a z * Real.exp (β * ω (0, z) - β ^ 2 / 2) * P z ω) ^ 6
        ∂disorderLaw ≤
      Real.exp (15 * β ^ 2) * ∫ ω, (∑ z ∈ S, a z * P z ω) ^ 6 ∂disorderLaw := by
  classical
  let f : ℕ × Site → ℕ × Site := fun p =>
    if p.1 = 0 then (n + 1, p.2) else if p.1 = n + 1 then (0, p.2) else p
  have hfinvol : Function.Involutive f := by
    intro p
    rcases p with ⟨t, z⟩
    by_cases h0 : t = 0
    · subst t
      simp [f]
    · by_cases hn : t = n + 1
      · subst t
        simp [f]
      · simp [f, h0, hn]
  let e : (ℕ × Site) ≃ (ℕ × Site) := Equiv.ofBijective f ⟨
    (fun p q hpq => by
      have h := congrArg f hpq
      simpa only [hfinvol p, hfinvol q] using h),
    (fun q => ⟨f q, hfinvol q⟩)⟩
  let τ : Disorder → Disorder := fun ω => Gaussian.reindexDisorder e ω
  let τeq : Disorder ≃ᵐ Disorder :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ) e.symm
  have hτeq : τ = τeq := by
    funext ω p
    simp [τ, τeq, Gaussian.reindexDisorder, MeasurableEquiv.piCongrLeft,
      Equiv.piCongrLeft]
  have hτmeas : MeasurableEmbedding τ := hτeq ▸ τeq.measurableEmbedding
  have hres (ω : Disorder) :
      Gaussian.resample (Gaussian.timeBlock 0 n) ω (τ ω) = τ ω := by
    funext p
    by_cases hp : p ∈ Gaussian.timeBlock 0 n
    · have hfp : f p = p := by
        rcases p with ⟨t, z⟩
        have hp' : 0 < t ∧ t ≤ n := by simpa [Gaussian.timeBlock] using hp
        simp [f, ne_of_gt hp'.1,
          ne_of_lt (lt_of_le_of_lt hp'.2 (Nat.lt_succ_self n))]
      have hτp : τ ω p = ω p := by
        change ω (f p) = ω p
        rw [hfp]
      simp [Gaussian.resample, hp, hτp]
    · simp [Gaussian.resample, hp]
  have hPτ (z : Site) (hz : z ∈ S) (ω : Disorder) :
      P z (τ ω) = P z ω := by
    calc
      P z (τ ω) = P z (Gaussian.resample (Gaussian.timeBlock 0 n) ω (τ ω)) := by
        rw [hres]
      _ = P z ω := Blocks.blockMeasurable_resample_keep (hPblock z hz) ω (τ ω)
  have hboundary (ω : Disorder) (z : Site) : τ ω (n + 1, z) = ω (0, z) := by
    change ω (f (n + 1, z)) = ω (0, z)
    simp [f]
  let F : Disorder → ℝ := fun ω =>
    ∑ z ∈ S, a z * Real.exp (β * ω (0, z) - β ^ 2 / 2) * P z ω
  let G : Disorder → ℝ := fun ω =>
    ∑ z ∈ S, a z * Real.exp (β * ω (n + 1, z) - β ^ 2 / 2) * P z ω
  have hFG (ω : Disorder) : F ω = G (τ ω) := by
    dsimp [F, G]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hboundary, hPτ z hz]
  have hbound := integral_sixth_randomWeightedBoundaryProfile_le β n S a P
    ha hPblock hPnonneg hQ6
  have hMP : MeasurePreserving τ disorderLaw disorderLaw :=
    Gaussian.measurePreserving_reindexDisorder e
  refine ⟨?_, ?_⟩
  · have hcomp : Integrable (fun ω => G (τ ω) ^ 6) disorderLaw :=
      (hMP.integrable_comp_emb hτmeas (g := fun ω => G ω ^ 6)).mpr hbound.1
    have hEq : (fun ω => F ω ^ 6) = fun ω => G (τ ω) ^ 6 := by
      funext ω
      exact congrArg (fun x : ℝ => x ^ 6) (hFG ω)
    rw [hEq]
    exact hcomp
  · calc
      ∫ ω, F ω ^ 6 ∂disorderLaw = ∫ ω, G (τ ω) ^ 6 ∂disorderLaw := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => congrArg (fun x : ℝ => x ^ 6) (hFG ω)
      _ = ∫ ω, G ω ^ 6 ∂disorderLaw :=
        hMP.integral_comp hτmeas (fun ω => G ω ^ 6)
      _ ≤ Real.exp (15 * β ^ 2) * ∫ ω, (∑ z ∈ S, a z * P z ω) ^ 6 ∂disorderLaw := hbound.2


private theorem integral_sixth_endpointProfile_le (β : ℝ) {a n : ℕ}
    (hn : 1 ≤ n) (S : Finset Site) (c : Site → ℝ)
    (hc : ∀ z ∈ S, 0 ≤ c z) :
    Integrable (fun ω =>
      (∑ z ∈ S, c z * ∑ x ∈ Polymer.endpoints z n,
        pointToPoint β a n x z ω) ^ 6) disorderLaw ∧
    ∫ ω, (∑ z ∈ S, c z * ∑ x ∈ Polymer.endpoints z n,
        pointToPoint β a n x z ω) ^ 6 ∂disorderLaw ≤
      Real.exp (15 * β ^ 2) *
        ∫ ω, (∑ z ∈ S, c z * pointToPlane β 0 n z ω) ^ 6 ∂disorderLaw := by
  classical
  let P : Site → Disorder → ℝ := fun z ω => pointToPlane β 0 (n - 1) z ω
  let Qpre : Disorder → ℝ := fun ω => ∑ z ∈ S, c z * pointToPlane β 0 (n - 1) z ω
  let Q : Disorder → ℝ := fun ω => ∑ z ∈ S, c z * pointToPlane β 0 n z ω
  let F : Disorder → ℝ := fun ω =>
    ∑ z ∈ S, c z * Real.exp (β * ω (0, z) - β ^ 2 / 2) * P z ω
  let W : Disorder → ℝ := fun ω =>
    ∑ z ∈ S, c z * ∑ x ∈ Polymer.endpoints z n,
      pointToPoint β a n x z ω
  have hQnonneg (ω : Disorder) : 0 ≤ Q ω := by
    dsimp [Q]
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hc z hz) (Polymer.pointToPlane_pos β 0 n z ω).le
  have hQmem : MemLp Q 6 disorderLaw := by
    apply memLp_finsetSum (s := S)
    intro z hz
    exact (Polymer.memLp_pointToPlane β 0 n z 6 (by norm_num)).const_mul (c z)
  have hQ6 : Integrable (fun ω => Q ω ^ 6) disorderLaw := by
    apply hQmem.integrable_norm_pow'.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hQnonneg ω)]
  have hQpreNonneg (ω : Disorder) : 0 ≤ Qpre ω := by
    dsimp [Qpre]
    apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hc z hz) (Polymer.pointToPlane_pos β 0 (n - 1) z ω).le
  have hQpreMem : MemLp Qpre 6 disorderLaw := by
    apply memLp_finsetSum (s := S)
    intro z hz
    exact (Polymer.memLp_pointToPlane β 0 (n - 1) z 6 (by norm_num)).const_mul (c z)
  have hQpre6 : Integrable (fun ω => Qpre ω ^ 6) disorderLaw := by
    apply hQpreMem.integrable_norm_pow'.congr
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hQpreNonneg ω)]
  have hPblock : ∀ z ∈ S, Measurable[Gaussian.disorderBlock 0 n] (P z) := by
    intro z hz
    have h := Polymer.measurable_pointToPlane_block β 0 (n - 1) z
    have hle := Gaussian.disorderBlock_le 0 n
    have hsub : Gaussian.disorderBlock 0 (0 + (n - 1)) ≤ Gaussian.disorderBlock 0 n := by
      exact Gaussian.disorderBlock_mono (by omega) (by omega)
    exact h.mono hsub le_rfl
  have hPnonneg : ∀ z ∈ S, ∀ ω, 0 ≤ P z ω := by
    intro z hz ω
    exact (Polymer.pointToPlane_pos β 0 (n - 1) z ω).le
  have hInitial := integral_sixth_initialWeightedBoundaryProfile_le
    β n S c P hc hPblock hPnonneg hQpre6
  let ρ : Disorder → Disorder := fun ω => PolymerCalculus.reversedDisorder (a + n) ω
  let ρeq : Disorder ≃ᵐ Disorder :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ × Site => ℝ)
      (PolymerCalculus.timeReversalIndex (a + n)).symm
  have hρeq : ρ = ρeq := by
    funext ω p
    simp [ρ, ρeq, PolymerCalculus.reversedDisorder, Gaussian.reindexDisorder,
      MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]
  have hρmeas : MeasurableEmbedding ρ := hρeq ▸ ρeq.measurableEmbedding
  have hρMP : MeasurePreserving ρ disorderLaw disorderLaw :=
    PolymerCalculus.measurePreserving_reversedDisorder (a + n)
  have hboundary (ω : Disorder) (z : Site) : ρ ω (0, z) = ω (a + n, z) := by
    simp [ρ, PolymerCalculus.reversedDisorder, Gaussian.reindexDisorder,
      PolymerCalculus.timeReversalIndex, PolymerCalculus.reflectedTime]
  have hW (ω : Disorder) : W ω = F (ρ ω) := by
    dsimp [W, F, P]
    apply Finset.sum_congr rfl
    intro z hz
    rw [sum_pointToPoint_initial_endpoint_timeReversal β hn z ω]
    rw [hboundary]
    simp only [ρ]
    ring
  have hWint : Integrable (fun ω => W ω ^ 6) disorderLaw := by
    have hcomp : Integrable (fun ω => F (ρ ω) ^ 6) disorderLaw :=
      (hρMP.integrable_comp_emb hρmeas (g := fun ω => F ω ^ 6)).mpr hInitial.1
    apply hcomp.congr
    filter_upwards [] with ω
    exact congrArg (fun x : ℝ => x ^ 6) (hW ω).symm
  refine ⟨hWint, ?_⟩
  have hJensen := integral_sixth_weightedPointToPlane_sub_horizon_le
    β hn S c hc
  calc
    ∫ ω, W ω ^ 6 ∂disorderLaw = ∫ ω, F (ρ ω) ^ 6 ∂disorderLaw := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        congrArg (fun x : ℝ => x ^ 6) (hW ω)
    _ = ∫ ω, F ω ^ 6 ∂disorderLaw := hρMP.integral_comp hρmeas (fun ω => F ω ^ 6)
    _ ≤ Real.exp (15 * β ^ 2) * ∫ ω, Qpre ω ^ 6 ∂disorderLaw := by
      simpa [Qpre, P] using hInitial.2
    _ ≤ Real.exp (15 * β ^ 2) * ∫ ω, Q ω ^ 6 ∂disorderLaw := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      simpa [Qpre, Q] using hJensen
    _ = Real.exp (15 * β ^ 2) *
        ∫ ω, (∑ z ∈ S, c z * pointToPlane β 0 n z ω) ^ 6 ∂disorderLaw := by
      rfl

/-- Terminal cutoff masses have eventually bounded integrable sixth powers. -/
theorem eventually_secondCutoff_sixth_integrable_le
    (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
      Integrable (fun ω =>
        (∫ y, polymerTailCutoff R hR y
          ∂((polymerMeasure ϑ N s t ω).map Prod.snd)) ^ 6) disorderLaw ∧
      ∫ ω, (∫ y, polymerTailCutoff R hR y
          ∂((polymerMeasure ϑ N s t ω).map Prod.snd)) ^ 6 ∂disorderLaw ≤ C := by
  let d : ℝ := t - s
  let ψ : C_c(Plane, ℝ) := polymerTailCutoff R hR
  obtain ⟨Cflat, hflat⟩ := SHF.Limit.polymerMeasure_flat_sixth_moment_le
    ϑ ψ (τ := d / 2) (T := d + 2) (half_pos (by dsimp [d]; linarith))
  have hd : 0 < d := by dsimp [d]; linarith
  have hclock := SHF.Positivity.eventually_evenClock_duration_bounds hs hst
  have hlarge : ∀ᶠ N : ℕ in Filter.atTop, 4 / d < (N : ℝ) := by
    exact tendsto_natCast_atTop_atTop.eventually_gt_atTop (4 / d)
  have hβsmall : ∀ᶠ N : ℕ in Filter.atTop, criticalBeta ϑ N ^ 2 ≤ 1 := by
    have hβ := SHF.Moments.tendsto_criticalBeta_zero ϑ
    filter_upwards [hβ.eventually (Metric.ball_mem_nhds (0 : ℝ)
        (by norm_num : 0 < (1 : ℝ)))]
      with N hN
    have hnorm : |criticalBeta ϑ N| < 1 := by
      simpa only [Real.dist_eq, sub_zero] using hN
    calc
      criticalBeta ϑ N ^ 2 = |criticalBeta ϑ N| ^ 2 := (sq_abs _).symm
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hnorm.le 2
      _ = 1 := by norm_num
  let C := Real.exp 15 * max Cflat 0
  refine ⟨C, ?_⟩
  filter_upwards [hflat, hclock, hlarge, hβsmall, Filter.eventually_ge_atTop 1]
    with N hflatN hclockN hlargeN hβsmallN hN
  let a := evenCeil ((N : ℝ) * s)
  let b := evenCeil ((N : ℝ) * t)
  let n := b - a
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hnEven : Even n := by
    dsimp only [n, a, b]
    exact Critical2DKPZ.Smoothing.evenCeil_sub_even
      (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N))
  have hcast : (n : ℝ) =
      (evenCeil ((N : ℝ) * t) : ℝ) - evenCeil ((N : ℝ) * s) := by
    dsimp [n, b, a]
    exact Nat.cast_sub (evenCeil_mono
      (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N)))
  have hnlow : d / 2 ≤ (n : ℝ) / N := by
    have hsN : 0 ≤ (N : ℝ) * s := mul_nonneg (Nat.cast_nonneg N) hs
    have htN : 0 ≤ (N : ℝ) * t :=
      mul_nonneg (Nat.cast_nonneg N) (le_trans hs hst.le)
    have hround := evenCeil_duration_error hsN htN
    have hround' : |(n : ℝ) - (N : ℝ) * d| < 2 := by
      rw [hcast, show (N : ℝ) * d = (N : ℝ) * t - (N : ℝ) * s by
        dsimp [d]; ring]
      exact hround
    have hND : 4 < (N : ℝ) * d := (div_lt_iff₀ hd).mp hlargeN
    have hbelow := (abs_lt.mp hround').1
    apply (le_div_iff₀ hNpos).2
    dsimp [d] at hND hbelow ⊢
    nlinarith
  have hnupper : (n : ℝ) / N ≤ d + 2 := by
    apply (div_le_iff₀ hNpos).2
    rw [hcast]
    simpa [d] using hclockN.2.2
  have hflatMoment := hflatN 0 ((n : ℝ) / N) (by norm_num)
    (by simpa using hnlow) hnupper
  let S : Finset Site :=
    (finite_latticePoint_image_of_bounded (N := N)
      ψ.hasCompactSupport.isBounded).toFinset
  let c : Site → ℝ := fun z => ∫ y in cell N z, ψ y
  have hc : ∀ z ∈ S, 0 ≤ c z := by
    intro z hz
    dsimp [c, ψ]
    exact setIntegral_nonneg (measurableSet_cell N z) fun y hy =>
      polymerTailCutoff_nonneg R hR y
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    rw [hcast]
    exact hclockN.2.1
  have hnpos : 1 ≤ n := by exact_mod_cast hnreal
  have hprofile := integral_sixth_endpointProfile_le (criticalBeta ϑ N)
    (a := a) (n := n) hnpos S c hc
  have hmass (ω : Disorder) :
      (∫ y, polymerTailCutoff R hR y
        ∂((polymerMeasure ϑ N s t ω).map Prod.snd)) =
      ∑ z ∈ S, c z * ∑ x ∈ Polymer.endpoints z n,
        pointToPoint (criticalBeta ϑ N) a n x z ω := by
    simpa only [ψ, S, c, n, a, b] using
      integral_secondMarginal_cutoff_eq_endpointProfile ϑ hN s t hst.le ω R hR
  have hmassInt : Integrable (fun ω =>
      (∫ y, polymerTailCutoff R hR y
        ∂((polymerMeasure ϑ N s t ω).map Prod.snd)) ^ 6) disorderLaw := by
    apply hprofile.1.congr
    filter_upwards [] with ω
    exact congrArg (fun x : ℝ => x ^ 6) (hmass ω).symm
  have hprofileMoment :
      ∫ ω, (∫ y, polymerTailCutoff R hR y
        ∂((polymerMeasure ϑ N s t ω).map Prod.snd)) ^ 6 ∂disorderLaw ≤
      Real.exp (15 * (criticalBeta ϑ N) ^ 2) *
        ∫ ω, (∑ z ∈ S, c z * pointToPlane (criticalBeta ϑ N) 0 n z ω) ^ 6
          ∂disorderLaw := by
    calc
      _ = ∫ ω, (∑ z ∈ S, c z *
            ∑ x ∈ Polymer.endpoints z n,
              pointToPoint (criticalBeta ϑ N) a n x z ω) ^ 6 ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω =>
            congrArg (fun x : ℝ => x ^ 6) (hmass ω)
      _ ≤ _ := hprofile.2
  have hflatEq (ω : Disorder) :
      ∫ x, |ψ x| ∂((polymerMeasure ϑ N 0 ((n : ℝ) / N) ω).map Prod.fst) =
        ∑ z ∈ S, c z * pointToPlane (criticalBeta ϑ N) 0 n z ω := by
    simpa only [ψ, S, c] using integral_flatFirstMarginal_eq_endpointProfile
      ϑ hN n hnEven ψ (by intro x; exact polymerTailCutoff_nonneg R hR x) ω
  have hprofileFlat :
      ∫ ω, (∑ z ∈ S, c z * pointToPlane (criticalBeta ϑ N) 0 n z ω) ^ 6
        ∂disorderLaw ≤ max Cflat 0 := by
    calc
      _ = ∫ ω, (∫ x, |ψ x| ∂
            ((polymerMeasure ϑ N 0 ((n : ℝ) / N) ω).map Prod.fst)) ^ 6
              ∂disorderLaw := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun ω =>
            congrArg (fun x : ℝ => x ^ 6) (hflatEq ω).symm
      _ ≤ Cflat := hflatMoment
      _ ≤ max Cflat 0 := le_max_left _ _
  refine ⟨hmassInt, ?_⟩
  calc
    _ ≤ Real.exp (15 * (criticalBeta ϑ N) ^ 2) * max Cflat 0 :=
      hprofileMoment.trans (mul_le_mul_of_nonneg_left hprofileFlat
        (Real.exp_nonneg _))
    _ ≤ Real.exp 15 * max Cflat 0 := by
      apply mul_le_mul_of_nonneg_right _ (le_max_right _ _)
      apply Real.exp_le_exp.mpr
      nlinarith

/-- The real mass of a measurable set is measurable in the disorder. -/
theorem measurable_polymerMeasure_real_mass
    (ϑ : ℝ) (N : ℕ) (s t : ℝ) (A : Set (Plane × Plane))
    (hA : MeasurableSet A) :
    Measurable (fun ω => (polymerMeasure ϑ N s t ω A).toReal) := by
  exact ENNReal.measurable_toReal.comp
    ((Measure.measurable_coe hA).comp (measurable_polymerMeasure ϑ N s t))

/-- Compact initial masses have eventually bounded integrable sixth powers. -/
theorem eventually_firstCompact_mass_sixth_integrable_le
    (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (A : Set Plane) (hA : IsCompact A) (B : ℝ) (hB : 0 ≤ B)
    (hAbox : ∀ x ∈ A, ‖x‖ ≤ B) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in Filter.atTop,
      Integrable (fun ω =>
        ((polymerMeasure ϑ N s t ω (A ×ˢ (Set.univ : Set Plane))).toReal) ^ 6)
        disorderLaw ∧
      ∫ ω,
        ((polymerMeasure ϑ N s t ω (A ×ˢ (Set.univ : Set Plane))).toReal) ^ 6
          ∂disorderLaw ≤ C := by
  let d : ℝ := t - s
  let χ : C_c(Plane, ℝ) := polymerTailCutoff B hB
  obtain ⟨Cflat, hflat⟩ := SHF.Limit.polymerMeasure_flat_sixth_moment_le
    ϑ χ (τ := d / 2) (T := t + 1) (half_pos (by dsimp [d]; linarith))
  let C := max Cflat 0
  refine ⟨C, ?_⟩
  filter_upwards [hflat] with N hflatN
  have hflatBound := hflatN s t hs (by dsimp [d]; linarith) (by linarith)
  let S : Set (Plane × Plane) := A ×ˢ (Set.univ : Set Plane)
  have hS : MeasurableSet S := hA.measurableSet.prod MeasurableSet.univ
  let X : Disorder → ℝ := fun ω => (polymerMeasure ϑ N s t ω S).toReal
  let Z : Disorder → ℝ := fun ω =>
    ∫ x, |χ x| ∂((polymerMeasure ϑ N s t ω).map Prod.fst)
  have hXm : Measurable X := by
    dsimp [X, S]
    exact measurable_polymerMeasure_real_mass ϑ N s t _ hS
  have hXnonneg (ω : Disorder) : 0 ≤ X ω := by
    exact ENNReal.toReal_nonneg
  have hZnonneg (ω : Disorder) : 0 ≤ Z ω :=
    integral_nonneg fun x => abs_nonneg (χ x)
  have hXleZ (ω : Disorder) : X ω ≤ Z ω := by
    dsimp [X, Z, S]
    exact polymerMeasure_compact_first_mass_le_flatCutoff ϑ N s t ω A hA B hB hAbox
  have hZint : Integrable (fun ω => Z ω ^ 6) disorderLaw := by
    dsimp [Z, χ]
    exact SHF.Limit.integrable_flat_polymerMeasure_pow ϑ N s t
      (polymerTailCutoff B hB) 6
  have hXint : Integrable (fun ω => X ω ^ 6) disorderLaw := by
    apply hZint.mono' (hXm.pow_const 6).aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hXnonneg ω) 6)]
    exact pow_le_pow_left₀ (hXnonneg ω) (hXleZ ω) 6
  have hmoment : ∫ ω, X ω ^ 6 ∂disorderLaw ≤ C := by
    calc
      _ ≤ ∫ ω, Z ω ^ 6 ∂disorderLaw :=
        integral_mono_ae hXint hZint (Filter.Eventually.of_forall fun ω =>
          pow_le_pow_left₀ (hXnonneg ω) (hXleZ ω) 6)
      _ ≤ Cflat := hflatBound
      _ ≤ max Cflat 0 := le_max_left _ _
  refine ⟨?_, ?_⟩
  · simpa [X, S] using hXint
  · simpa [X, S] using hmoment


end Critical2DKPZ.SHF.Flow

end
