/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureContinuity
import Mathlib.Tactic

/-! # Moving-horizon continuity of the complete two-particle future -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

private def futureIntegrand (θ : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (p : ℝ × (Fin 2 → Plane) × Plane) (u : ℝ) : ℝ :=
  (Set.Ioo 0 p.1).indicator
    (fun u => pairTwoTestedSpatialProfile θ u (p.1 - u) φ p.2.1 p.2.2) u

private theorem futureIntegrand_integrable (θ : ℝ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (p : ℝ × (Fin 2 → Plane) × Plane) :
    Integrable (futureIntegrand θ φ p) := by
  exact ((integrableOn_pairTwoTestedSpatialProfile_time θ p.1 φ p.2.1 p.2.2).mono_set
    Set.Ioo_subset_Icc_self).integrable_indicator measurableSet_Ioo

private theorem continuousAt_futureIntegrand (θ : ℝ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (p : ℝ × (Fin 2 → Plane) × Plane)
    (u : ℝ) (hu : u ≠ p.1) :
    ContinuousAt (fun p' => futureIntegrand θ φ p' u) p := by
  by_cases hpos : 0 < u
  · by_cases hlt : u < p.1
    · have he : ∀ᶠ p' : ℝ × (Fin 2 → Plane) × Plane in 𝓝 p, u < p'.1 :=
        continuous_fst.continuousAt.tendsto.eventually (Ioi_mem_nhds hlt)
      have hc := continuousAt_pairTwoTestedSpatialProfile θ φ
        ((u, p.1 - u), p.2.1, p.2.2) hpos (sub_pos.mpr hlt)
      have harg : ContinuousAt (fun p' : ℝ × (Fin 2 → Plane) × Plane =>
          ((u, p'.1 - u), p'.2.1, p'.2.2)) p :=
        (continuousAt_const.prodMk (continuousAt_fst.sub continuousAt_const)).prodMk
          continuousAt_snd
      have hcomp := ContinuousAt.comp'
        (f := fun p' : ℝ × (Fin 2 → Plane) × Plane => ((u, p'.1 - u), p'.2.1, p'.2.2))
        (g := fun q : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
          pairTwoTestedSpatialProfile θ q.1.1 q.1.2 φ q.2.1 q.2.2) hc harg
      apply hcomp.congr
      filter_upwards [he] with p' hp'
      simp only [futureIntegrand, Set.indicator_of_mem (show u ∈ Set.Ioo 0 p'.1 from ⟨hpos, hp'⟩)]
    · have hgt : p.1 < u := lt_of_le_of_ne (le_of_not_gt hlt) hu.symm
      have he : ∀ᶠ p' : ℝ × (Fin 2 → Plane) × Plane in 𝓝 p, p'.1 < u :=
        continuous_fst.continuousAt.tendsto.eventually (Iio_mem_nhds hgt)
      apply (continuousAt_const : ContinuousAt (fun _ : ℝ × (Fin 2 → Plane) × Plane => (0 : ℝ)) p).congr
      filter_upwards [he] with p' hp'
      simp only [futureIntegrand, Set.indicator_of_notMem
        (show u ∉ Set.Ioo 0 p'.1 from fun h => (not_lt_of_ge hp'.le) h.2)]
  · have he : (fun p' : ℝ × (Fin 2 → Plane) × Plane => futureIntegrand θ φ p' u) =
        fun _ => (0 : ℝ) := by
      funext p'
      exact Set.indicator_of_notMem (fun h => hpos h.1) _
    rw [he]
    exact continuousAt_const

/-- The complete continuum future is jointly continuous in its positive
horizon, incoming locations, and collision location. -/
theorem continuousAt_pairTwoContinuumFuture
    (θ : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (p : ℝ × (Fin 2 → Plane) × Plane) (hp : 0 < p.1) :
    ContinuousAt (fun p' : ℝ × (Fin 2 → Plane) × Plane =>
      pairTwoContinuumFuture θ p'.1 φ p'.2.1 p'.2.2) p := by
  let K : ℝ := 16 * Real.pi * ‖(φ 0).toBoundedContinuousFunction‖ *
    ‖(φ 1).toBoundedContinuousFunction‖
  let T : ℝ := p.1 + 1
  let B : ℝ → ℝ := (Set.Ioo 0 T).indicator (fun u => K * DeltaBose.scalarDensity θ u)
  have hmajor : IntegrableOn (fun u => K * DeltaBose.scalarDensity θ u) (Set.Ioo 0 T) :=
    ((Renewal.integrableOn_scalarDensity_Ioc θ T).mono_set Set.Ioo_subset_Ioc_self).const_mul K
  have hB : Integrable B := hmajor.integrable_indicator measurableSet_Ioo
  have hnear : ∀ᶠ p' : ℝ × (Fin 2 → Plane) × Plane in 𝓝 p, 0 < p'.1 ∧ p'.1 < T :=
    continuous_fst.continuousAt.tendsto.eventually
      (Ioo_mem_nhds hp (by dsimp [T]; linarith))
  have hc : ContinuousAt (fun p' => ∫ u, futureIntegrand θ φ p' u) p := by
    apply continuousAt_of_dominated (bound := B)
    · exact Eventually.of_forall fun p' => (futureIntegrand_integrable θ φ p').aestronglyMeasurable
    · filter_upwards [hnear] with p' hp'
      apply Eventually.of_forall
      intro u
      by_cases hu : u ∈ Set.Ioo 0 p'.1
      · have huT : u ∈ Set.Ioo 0 T := ⟨hu.1, hu.2.trans hp'.2⟩
        rw [futureIntegrand, Set.indicator_of_mem hu, Real.norm_eq_abs]
        rw [show B u = K * DeltaBose.scalarDensity θ u by exact Set.indicator_of_mem huT _]
        have hb := (pairTwoTestedSpatialProfile_integrable_bound θ u (p'.1 - u)
          hu.1 (sub_pos.mpr hu.2) φ p'.2.1 p'.2.2).2
        convert hb using 1
        dsimp [K]
        ring
      · rw [futureIntegrand, Set.indicator_of_notMem hu, norm_zero]
        apply Set.indicator_nonneg
        intro v hv
        exact mul_nonneg (by dsimp [K]; positivity)
          (DeltaBose.scalarDensity_pos θ hv.1).le
    · exact hB
    · have hne : ∀ᵐ u : ℝ, u ≠ p.1 := by
        rw [ae_iff]
        simpa only [not_not, Set.ofPred_eq_eq_singleton] using (measure_singleton p.1 : volume {p.1} = 0)
      filter_upwards [hne] with u hu
      exact continuousAt_futureIntegrand θ φ p u hu
  apply hc.congr
  filter_upwards [hnear] with p' hp'
  rw [pairTwoContinuumFuture, intervalIntegral.integral_of_le hp'.1.le,
    integral_Ioc_eq_integral_Ioo]
  exact integral_indicator measurableSet_Ioo

end Critical2DKPZ.SHF.Moments
