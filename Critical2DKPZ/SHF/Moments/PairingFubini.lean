/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.AnnealedPairing
public import Critical2DKPZ.Polymer.Profiles
public import Critical2DKPZ.Polymer.SummableCovariance
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Integrable random pairings and first-moment limits

Joint measurability and absolute integrability allow disorder expectations to commute with compactly supported spatial pairings, giving convergence of first pairing moments. -/

public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

open Polymer

/-- The rescaled point-to-point polymer kernel is nonnegative. -/
theorem rescaledP2P_nonneg (ϑ : ℝ) (N : ℕ) (s t : ℝ) (p : Plane × Plane) (ω : Disorder) :
    0 ≤ rescaledP2P ϑ N s t p ω :=
  mul_nonneg (by positivity) (pointToPoint_nonneg _ _ _ _ _ _)

/-- The point-to-point polymer kernel is jointly measurable in its endpoints and disorder. -/
theorem measurable_uncurry_pointToPoint (β : ℝ) (a n : ℕ) :
    Measurable (fun q : (Site × Site) × Disorder => pointToPoint β a n q.1.1 q.1.2 q.2) :=
  measurable_from_prod_countable_right (fun wz => measurable_pointToPoint β a n wz.1 wz.2)

/-- The rescaled polymer kernel is jointly measurable in its continuum endpoints and disorder. -/
theorem measurable_uncurry_rescaledP2P (ϑ : ℝ) (N : ℕ) (s t : ℝ) :
    Measurable (fun q : (Plane × Plane) × Disorder => rescaledP2P ϑ N s t q.1 q.2) := by
  have h := measurable_uncurry_pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
    (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
  have hsites : Measurable (fun q : (Plane × Plane) × Disorder =>
      ((latticePoint N q.1.1, latticePoint N q.1.2), q.2)) :=
    ((((measurable_latticePoint N).comp (measurable_fst.comp measurable_fst)).prodMk
      ((measurable_latticePoint N).comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd)
  change Measurable (fun q : (Plane × Plane) × Disorder => (N : ℝ) / 4 *
    pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
      (latticePoint N q.1.1) (latticePoint N q.1.2) q.2)
  exact (h.comp hsites).const_mul ((N : ℝ) / 4)


/-- The annealed rescaled point-to-point kernel is bounded by one quarter of the lattice scale. -/
theorem annealed_rescaledP2P_bound (ϑ : ℝ) (N : ℕ) (s t : ℝ) (p : Plane × Plane) :
    (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) ≤ (N : ℝ) / 4 := by
  rw [integral_rescaledP2P]
  exact mul_le_of_le_one_right (by positivity) (Critical2DKPZ.Polymer.srwKernel_le_one _ _)

/-- Absolute integrability of the random pairing on the product of space and disorder. -/
theorem integrable_pairing_rescaledP2P (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    {φ : Plane × Plane → ℝ} (hφ : Continuous φ) (hφs : HasCompactSupport φ) :
    Integrable (fun q : (Plane × Plane) × Disorder =>
      φ q.1 * rescaledP2P ϑ N s t q.1 q.2) (volume.prod disorderLaw) := by
  have hm := (hφ.measurable.comp measurable_fst).mul
    (measurable_uncurry_rescaledP2P ϑ N s t)
  apply (integrable_prod_iff hm.aestronglyMeasurable).2
  constructor
  · apply Filter.Eventually.of_forall
    intro p
    change Integrable (fun ω => φ p * ((N : ℝ) / 4 *
      pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
        (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
        (latticePoint N p.1) (latticePoint N p.2) ω)) disorderLaw
    exact ((integrable_pointToPoint (criticalBeta ϑ N) (evenCeil ((N : ℝ) * s))
      (evenCeil ((N : ℝ) * t) - evenCeil ((N : ℝ) * s))
      (latticePoint N p.1) (latticePoint N p.2)).const_mul ((N : ℝ) / 4)).const_mul (φ p)
  · have heq (p : Plane × Plane) :
        (∫ ω, ‖φ p * rescaledP2P ϑ N s t p ω‖ ∂disorderLaw) =
          |φ p| * (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) := by
      simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (rescaledP2P_nonneg ϑ N s t p _)]
      rw [integral_const_mul]
    change Integrable (fun p : Plane × Plane =>
      ∫ ω, ‖φ p * rescaledP2P ϑ N s t p ω‖ ∂disorderLaw) volume
    simp_rw [heq]
    apply (((hφ.integrable_of_hasCompactSupport hφs).norm.const_mul ((N : ℝ) / 4))).mono'
    · exact (hφ.measurable.norm.mul (measurable_integral_rescaledP2P ϑ N s t)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun p => by
        have hnonneg : 0 ≤ (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) :=
          integral_nonneg (fun ω => rescaledP2P_nonneg ϑ N s t p ω)
        rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg hnonneg, mul_comm ((N : ℝ) / 4)]
        exact mul_le_mul_of_nonneg_left (annealed_rescaledP2P_bound ϑ N s t p) (abs_nonneg _)

/-- Spatial integration of a compact polymer pairing commutes with disorder expectation at every lattice scale. -/
theorem integral_pairing_rescaledP2P (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    {φ : Plane × Plane → ℝ} (hφ : Continuous φ) (hφs : HasCompactSupport φ) :
    (∫ ω, (∫ p : Plane × Plane, φ p * rescaledP2P ϑ N s t p ω) ∂disorderLaw) =
      ∫ p : Plane × Plane, φ p * (∫ ω, rescaledP2P ϑ N s t p ω ∂disorderLaw) := by
  rw [← integral_integral_swap (integrable_pairing_rescaledP2P ϑ N s t hφ hφs)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => integral_const_mul _ _

/-- The first moment of a compactly tested polymer kernel converges to the corresponding heat-kernel pairing. -/
theorem firstMoment_pairing_limit (ϑ : ℝ) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t)
    {φ : Plane × Plane → ℝ} (hφ : Continuous φ) (hφs : HasCompactSupport φ) :
    Tendsto (fun N : ℕ => ∫ ω,
      (∫ p : Plane × Plane, φ p * rescaledP2P ϑ N s t p ω) ∂disorderLaw)
      atTop (𝓝 (∫ p : Plane × Plane, φ p * heatKernel (t - s) (p.2 - p.1))) := by
  simp_rw [integral_pairing_rescaledP2P ϑ _ s t hφ hφs]
  exact tendsto_pairing_annealed_rescaledP2P ϑ hs hst hφ hφs

end Critical2DKPZ.SHF.Moments
