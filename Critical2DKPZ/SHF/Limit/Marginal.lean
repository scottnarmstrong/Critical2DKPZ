/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.Measurability
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.Polymer.Endpoints
public import Critical2DKPZ.SHF.Moments.FirstMoment
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

/-! # The point-to-plane marginal of the polymer measure -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Critical2DKPZ.SHF.Limit

private theorem lintegral_polymerDensity_snd (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s t : ℝ) (x : Plane) (ω : Disorder) :
    ∫⁻ y : Plane, ENNReal.ofReal (rescaledP2P ϑ N s t (x, y) ω) =
      ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω) := by
  classical
  let a := evenCeil ((N : ℝ) * s)
  let n := evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)
  let w := latticePoint N x
  let β := criticalBeta ϑ N
  have hNpos : 0 < N := Nat.zero_lt_of_lt hN
  have hn : Even n := by
    dsimp [n]
    exact SHF.Moments.even_evenCeil_sub _ _
  have hw : w ∈ evenLattice := by
    dsimp [w]
    exact latticePoint_mem_evenLattice N x
  have hcover : (⋃ z : Site, cell N z) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact Set.mem_iUnion.mpr ⟨latticePoint N y, mem_cell_latticePoint N y⟩
  have hsum : Summable (fun z : Site => pointToPoint β a n w z ω) := by
    apply summable_of_ne_finset_zero (s := Polymer.endpoints w n)
    intro z hz
    exact Polymer.pointToPoint_eq_zero_of_not_mem β a n w z ω hz
  have htimeEven : Even (n : ℤ) := by exact_mod_cast hn
  have hterm (z : Site) :
      ∫⁻ y in cell N z, ENNReal.ofReal (rescaledP2P ϑ N s t (x, y) ω) =
        ENNReal.ofReal (pointToPoint β a n w z ω) := by
    by_cases hz : z ∈ evenLattice
    · have hconst :
          (fun y : Plane => ENNReal.ofReal (rescaledP2P ϑ N s t (x, y) ω)) =ᵐ[
            volume.restrict (cell N z)]
            (fun _ => ENNReal.ofReal ((N : ℝ) / 4 *
              pointToPoint β a n w z ω)) := by
        filter_upwards [ae_restrict_mem (measurableSet_cell N z)] with y hy
        rw [mem_cell_iff] at hy
        change ENNReal.ofReal ((N : ℝ) / 4 *
          pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
            (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
            (latticePoint N x) (latticePoint N y) ω) = _
        rw [hy]
      calc
        _ = ∫⁻ y in cell N z,
            ENNReal.ofReal ((N : ℝ) / 4 * pointToPoint β a n w z ω) :=
              lintegral_congr_ae hconst
        _ = ENNReal.ofReal (pointToPoint β a n w z ω) := by
          rw [lintegral_const, Measure.restrict_apply_univ, volume_cell hNpos hz]
          rw [← ENNReal.ofReal_mul (mul_nonneg (by positivity)
            (Polymer.pointToPoint_nonneg β a n w z ω))]
          congr 1
          field_simp
    · have hempty : cell N z = ∅ := cell_eq_empty_of_not_even hz
      have htarget : Even (w 0 + w 1 + (n : ℤ)) := by
        exact hw.add htimeEven
      have hnot : ¬ Int.ModEq 2 (z 0 + z 1) (w 0 + w 1 + (n : ℤ)) := by
        intro hzmod
        apply hz
        have htargetMod : Int.ModEq 2 (w 0 + w 1 + (n : ℤ)) 0 := by
          simpa [Int.ModEq] using Int.even_iff.mp htarget
        apply Int.even_iff.mpr
        simpa [Int.ModEq] using hzmod.trans htargetMod
      have hzero := Polymer.pointToPoint_eq_zero_of_parity β a n w z ω hnot
      rw [hempty, hzero]
      simp
  calc
    ∫⁻ y : Plane, ENNReal.ofReal (rescaledP2P ϑ N s t (x, y) ω)
        = ∫⁻ y in ⋃ z : Site, cell N z,
            ENNReal.ofReal (rescaledP2P ϑ N s t (x, y) ω) := by
              rw [hcover]
              simp
    _ = ∑' z : Site, ∫⁻ y in cell N z,
          ENNReal.ofReal (rescaledP2P ϑ N s t (x, y) ω) :=
        lintegral_iUnion (fun z => measurableSet_cell N z) (pairwise_disjoint_cell N)
          (fun y => ENNReal.ofReal (rescaledP2P ϑ N s t (x, y) ω))
    _ = ∑' z : Site, ENNReal.ofReal (pointToPoint β a n w z ω) := by
          apply tsum_congr
          exact hterm
    _ = ENNReal.ofReal (pointToPlane β a n w ω) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun z => Polymer.pointToPoint_nonneg β a n w z ω) hsum,
            Polymer.tsum_pointToPoint]
    _ = ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω) := by
          simp [rescaledP2Plane, a, n, w, β]

private theorem measurable_rescaledP2Plane_fixed (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (ω : Disorder) : Measurable (fun x : Plane => rescaledP2Plane ϑ N s t x ω) := by
  have hsite : Measurable (fun z : Site =>
      pointToPlane (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
        (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) z ω) :=
    measurable_of_countable _
  exact hsite.comp (measurable_latticePoint N)

/-- The rescaled point-to-plane density is nonnegative. -/
theorem rescaledP2Plane_nonneg (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (x : Plane) (ω : Disorder) : 0 ≤ rescaledP2Plane ϑ N s t x ω := by
  exact (Polymer.pointToPlane_pos (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
    (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) (latticePoint N x) ω).le

/-- The annealed point-to-plane density has unit mean at every scale. -/
theorem integral_rescaledP2Plane (ϑ : ℝ) (N : ℕ) (s t : ℝ) (x : Plane) :
    ∫ ω, rescaledP2Plane ϑ N s t x ω ∂disorderLaw = 1 := by
  change ∫ ω, pointToPlane (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
    (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) (latticePoint N x) ω
      ∂disorderLaw = 1
  exact Polymer.integral_pointToPlane (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
    (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s)) (latticePoint N x)

/-- At positive lattice scale, integrating the polymer density in its second endpoint gives the rescaled point-to-plane density. -/
theorem map_fst_polymerMeasure (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N) (s t : ℝ)
    (ω : Disorder) :
    (polymerMeasure ϑ N s t ω).map Prod.fst =
      (volume : Measure Plane).withDensity fun x =>
        ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω) := by
  classical
  apply Measure.ext
  intro A hA
  let B : Set (Plane × Plane) := Prod.fst ⁻¹' A
  have hB : MeasurableSet B := hA.preimage measurable_fst
  have hpair : Measurable (fun q : (Plane × Plane) × Disorder =>
      rescaledP2P ϑ N s t q.1 q.2) :=
    SHF.Moments.measurable_uncurry_rescaledP2P ϑ N s t
  have hden : Measurable (fun p : Plane × Plane => ENNReal.ofReal
      (rescaledP2P ϑ N s t p ω)) :=
    ENNReal.measurable_ofReal.comp hpair.of_uncurry_right
  have hprod : Measurable (fun p : Plane × Plane =>
      B.indicator (fun p => ENNReal.ofReal (rescaledP2P ϑ N s t p ω)) p) :=
    hden.indicator hB
  rw [Measure.map_apply measurable_fst hA, polymerMeasure,
    withDensity_apply _ hB, withDensity_apply _ hA]
  calc
    ∫⁻ p in B, ENNReal.ofReal (rescaledP2P ϑ N s t p ω)
        = ∫⁻ x : Plane, ∫⁻ y : Plane,
            B.indicator (fun p => ENNReal.ofReal (rescaledP2P ϑ N s t p ω)) (x, y)
              ∂volume ∂volume := by
                rw [Measure.volume_eq_prod, ← lintegral_indicator hB,
                  lintegral_prod _ hprod.aemeasurable]
    _ = ∫⁻ x in A, ENNReal.ofReal (rescaledP2Plane ϑ N s t x ω) := by
          rw [← lintegral_indicator hA]
          apply lintegral_congr_ae
          filter_upwards [] with x
          by_cases hx : x ∈ A
          · simp [B, hx, lintegral_polymerDensity_snd ϑ hN s t x ω]
          · simp [B, hx]

/-- Pairing the first marginal against a real function is integration against the point-to-plane density. -/
theorem integral_map_fst_polymerMeasure (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (s t : ℝ) (ω : Disorder) (f : Plane → ℝ) :
    ∫ x, f x ∂((polymerMeasure ϑ N s t ω).map Prod.fst) =
      ∫ x, f x * rescaledP2Plane ϑ N s t x ω := by
  have hdens : Measurable (fun x : Plane => ENNReal.ofReal
      (rescaledP2Plane ϑ N s t x ω)) :=
    ENNReal.measurable_ofReal.comp (measurable_rescaledP2Plane_fixed ϑ N s t ω)
  rw [map_fst_polymerMeasure ϑ hN s t ω,
    integral_withDensity_eq_integral_toReal_smul hdens
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (rescaledP2Plane_nonneg ϑ N s t x ω), smul_eq_mul,
    mul_comm]

end Critical2DKPZ.SHF.Limit

end
