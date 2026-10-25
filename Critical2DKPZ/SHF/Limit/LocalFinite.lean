/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.Marginal
public import Critical2DKPZ.Analysis.Lattice.Sampling
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Tactic

/-! # Local finiteness of polymer measures -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Critical2DKPZ.SHF.Limit

private theorem abs_siteToPlane_apply_le_norm (z : Site) (i : Fin 2) :
    |(siteToPlane z i : ℝ)| ≤ ‖siteToPlane z‖ := by
  have hnorm := Critical2DKPZ.plane_norm_sq (siteToPlane z)
  have hsquare : |(siteToPlane z i : ℝ)| ^ 2 ≤ ‖siteToPlane z‖ ^ 2 := by
    have hcoord : (siteToPlane z i : ℝ) ^ 2 ≤ ‖siteToPlane z‖ ^ 2 := by
      rw [hnorm]
      fin_cases i
      · exact le_add_of_nonneg_right (sq_nonneg (siteToPlane z 1))
      · exact le_add_of_nonneg_left (sq_nonneg (siteToPlane z 0))
    simpa only [sq_abs] using hcoord
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hsquare

private theorem finite_siteToPlane_norm_le (C : ℝ) :
    {z : Site | ‖siteToPlane z‖ ≤ C}.Finite := by
  classical
  let B : ℤ := ⌈C⌉
  have hCB : C ≤ (B : ℝ) := by
    dsimp [B]
    exact_mod_cast (Int.le_ceil C)
  let S : Set Site := Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (-B) B)
  have hS : S.Finite := Set.Finite.pi fun _ : Fin 2 => Set.finite_Icc (-B) B
  apply hS.subset
  intro z hz
  simp only [S, Set.mem_pi, Set.mem_univ, Set.mem_Icc] at hz ⊢
  intro i _
  have hcoord : |(z i : ℝ)| ≤ C := by
    simpa [siteToPlane] using (abs_siteToPlane_apply_le_norm z i).trans hz
  have hcoord' : ((|z i| : ℤ) : ℝ) ≤ (B : ℝ) := by
    simpa only [Int.cast_abs] using hcoord.trans hCB
  have hcoord'' : |z i| ≤ B := by exact_mod_cast hcoord'
  exact abs_le.mp hcoord''

/-- A bounded part of the plane meets only finitely many lattice cells. -/
theorem finite_latticePoint_image_of_bounded {N : ℕ} {s : Set Plane}
    (hs : Bornology.IsBounded s) : (latticePoint N '' s).Finite := by
  classical
  by_cases hN : N = 0
  · apply (Set.finite_singleton (0 : Site)).subset
    rintro z ⟨x, hx, rfl⟩
    simp [latticePoint, hN, nearestEven]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Plane)).mp hs
    let R := max R₀ 0
    have hR : 0 ≤ R := le_max_right _ _
    let C := Real.sqrt ((N : ℝ) / 2) * (R + 2)
    have hscale : 0 < Real.sqrt ((N : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
    have hfinite := finite_siteToPlane_norm_le C
    apply hfinite.subset
    rintro z ⟨x, hx, rfl⟩
    have hxnorm : ‖x‖ ≤ R := by
      have h := hR₀ hx
      rw [Metric.mem_closedBall, dist_zero_right] at h
      exact h.trans (le_max_left _ _)
    have hsample := Critical2DKPZ.norm_cellSample_le hR hxnorm N
    have hsample' : ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ •
        siteToPlane (latticePoint N x)‖ ≤ R + 2 := by
      simpa only [Critical2DKPZ.cellSample, latticeRepresentative] using hsample
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr hscale.le)] at hsample'
    have hrep : (Real.sqrt ((N : ℝ) / 2))⁻¹ *
        ‖siteToPlane (latticePoint N x)‖ ≤ R + 2 := by
      exact hsample'
    calc
      ‖siteToPlane (latticePoint N x)‖ = Real.sqrt ((N : ℝ) / 2) *
          ((Real.sqrt ((N : ℝ) / 2))⁻¹ * ‖siteToPlane (latticePoint N x)‖) := by
            field_simp [hscale.ne']
      _ ≤ C := by
          dsimp [C]
          exact mul_le_mul_of_nonneg_left hrep hscale.le

/-- The polymer measure is finite on compact sets, hence locally finite. -/
theorem isLocallyFiniteMeasure_polymerMeasure (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (ω : Disorder) : IsLocallyFiniteMeasure (polymerMeasure ϑ N s t ω) := by
  classical
  have hfinite : IsFiniteMeasureOnCompacts (polymerMeasure ϑ N s t ω) := by
    refine ⟨fun K hK => ?_⟩
    have hfst : IsCompact (Prod.fst '' K) := hK.image continuous_fst
    have hsnd : IsCompact (Prod.snd '' K) := hK.image continuous_snd
    have hfstFinite := finite_latticePoint_image_of_bounded (N := N) hfst.isBounded
    have hsndFinite := finite_latticePoint_image_of_bounded (N := N) hsnd.isBounded
    let sites : Set (Site × Site) :=
      (latticePoint N '' (Prod.fst '' K)) ×ˢ (latticePoint N '' (Prod.snd '' K))
    have hsites : sites.Finite := hfstFinite.prod hsndFinite
    let β := criticalBeta ϑ N
    let a := evenCeil ((N : ℝ) * s)
    let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
    let values : Set ℝ := (fun z : Site × Site => pointToPoint β a n z.1 z.2 ω) '' sites
    have hvalues : values.Finite := hsites.image _
    obtain ⟨M, hM⟩ := hvalues.bddAbove
    let C := max M 0
    have hC : 0 ≤ C := le_max_right _ _
    have hbound (p : Plane × Plane) (hp : p ∈ K) :
        rescaledP2P ϑ N s t p ω ≤ (N : ℝ) / 4 * C := by
      have hsitesp : (latticePoint N p.1, latticePoint N p.2) ∈ sites := by
        exact ⟨⟨p.1, ⟨p, hp, rfl⟩, rfl⟩, ⟨p.2, ⟨p, hp, rfl⟩, rfl⟩⟩
      have hval : pointToPoint β a n (latticePoint N p.1) (latticePoint N p.2) ω ≤ C := by
        apply le_max_of_le_left
        exact hM ⟨(latticePoint N p.1, latticePoint N p.2), hsitesp, rfl⟩
      rw [rescaledP2P]
      exact mul_le_mul_of_nonneg_left hval (by positivity)
    calc
      polymerMeasure ϑ N s t ω K =
          ∫⁻ p in K, ENNReal.ofReal (rescaledP2P ϑ N s t p ω) := by
            rw [polymerMeasure, withDensity_apply _ hK.measurableSet]
      _ ≤ ∫⁻ p in K, ENNReal.ofReal ((N : ℝ) / 4 * C) := by
            apply lintegral_mono_ae
            filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
            exact ENNReal.ofReal_le_ofReal (hbound p hp)
      _ = ENNReal.ofReal ((N : ℝ) / 4 * C) * volume K := by
            rw [lintegral_const, Measure.restrict_apply_univ]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  refine ⟨fun x => ?_⟩
  obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
  exact ⟨K, hx, hfinite.lt_top_of_isCompact hK⟩

/-- The first marginal of a finite-scale polymer measure is locally finite. -/
theorem isLocallyFiniteMeasure_polymerMarginal (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (ω : Disorder) :
    IsLocallyFiniteMeasure ((polymerMeasure ϑ N s t ω).map Prod.fst) := by
  classical
  by_cases hN0 : N = 0
  · subst N
    have hzero : polymerMeasure ϑ 0 s t ω = 0 := by
      rw [polymerMeasure]
      ext A hA
      simp [rescaledP2P]
    rw [hzero, Measure.map_zero]
    infer_instance
  · have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hN0
    rw [map_fst_polymerMeasure ϑ hN s t ω]
    have hfinite : IsFiniteMeasureOnCompacts
        ((volume : Measure Plane).withDensity fun x =>
          ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω)) := by
      refine ⟨fun K hK => ?_⟩
      let S : Set Site := latticePoint N '' K
      have hS : S.Finite := finite_latticePoint_image_of_bounded hK.isBounded
      let β := criticalBeta ϑ N
      let a := evenCeil ((N : ℝ) * s)
      let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
      let values : Set ℝ := (fun z : Site => pointToPlane β a n z ω) '' S
      have hvalues : values.Finite := hS.image _
      obtain ⟨M, hM⟩ := hvalues.bddAbove
      let C := max M 0
      have hC : 0 ≤ C := le_max_right _ _
      have hbound (x : Plane) (hx : x ∈ K) :
          rescaledP2Plane ϑ N s t x ω ≤ C := by
        have hval : pointToPlane β a n (latticePoint N x) ω ≤ C := by
          apply le_max_of_le_left
          exact hM ⟨latticePoint N x, ⟨x, hx, rfl⟩, rfl⟩
        rw [rescaledP2Plane]
        exact hval
      calc
        ((volume : Measure Plane).withDensity fun x =>
            ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω)) K =
            ∫⁻ x in K, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω) ∂volume := by
              rw [withDensity_apply _ hK.measurableSet]
        _ ≤ ∫⁻ x in K, ENNReal.ofReal C ∂volume := by
              apply lintegral_mono_ae
              filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
              exact ENNReal.ofReal_le_ofReal (hbound x hx)
        _ = ENNReal.ofReal C * volume K := by
              rw [lintegral_const, Measure.restrict_apply_univ]
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
    refine ⟨fun x => ?_⟩
    obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds x
    exact ⟨K, hx, hfinite.lt_top_of_isCompact hK⟩

end Critical2DKPZ.SHF.Limit

end
