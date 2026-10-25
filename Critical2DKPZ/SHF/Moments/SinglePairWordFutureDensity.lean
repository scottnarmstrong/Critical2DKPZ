/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureAbsoluteMass
import Mathlib.Tactic

/-! # A fixed-measure density for the complete two-particle future -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported

/-- The tested future density on a fixed renewal-time and terminal-location
space. The open-time indicator represents both moving renewal endpoints. -/
def pairTwoFutureDensity (θ q : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (a : Fin 2 → Plane) (z : Plane) (p : ℝ × (Plane × Plane)) : ℝ :=
  (Set.Ioo 0 q ×ˢ Set.univ).indicator
    (fun p : ℝ × (Plane × Plane) =>
      φ 0 (a 0, p.2.1) * φ 1 (a 1, p.2.2) *
        pairTwoFutureSpatialProfile θ q p.1 z ![p.2.1, p.2.2]) p

/-- The density is integrable over a fixed product measure, even though its
renewal-time support depends on the remaining horizon. -/
theorem integrable_pairTwoFutureDensity
    (θ q : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    Integrable (pairTwoFutureDensity θ q φ a z)
      ((volume : Measure ℝ).prod ((volume : Measure Plane).prod volume)) := by
  have hi := integrable_pairTwo_testedFuture_time_terminal θ q φ a z
  have hi' : IntegrableOn (fun p : ℝ × (Plane × Plane) =>
      φ 0 (a 0, p.2.1) * φ 1 (a 1, p.2.2) *
        pairTwoFutureSpatialProfile θ q p.1 z ![p.2.1, p.2.2])
      (Set.Ioo 0 q ×ˢ Set.univ)
      ((volume : Measure ℝ).prod ((volume : Measure Plane).prod volume)) := by
    change Integrable _ _
    rw [← Measure.restrict_prod_eq_prod_univ]
    exact hi
  exact hi'.integrable_indicator (measurableSet_Ioo.prod MeasurableSet.univ)

/-- The fixed-measure density integrates to the original complete future. -/
theorem pairTwoContinuumFuture_eq_density_integral
    (θ : ℝ) {q : ℝ} (hq : 0 < q) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (a : Fin 2 → Plane) (z : Plane) :
    pairTwoContinuumFuture θ q φ a z =
      (16 * Real.pi) * (∫ p : ℝ × (Plane × Plane), pairTwoFutureDensity θ q φ a z p
        ∂(volume : Measure ℝ).prod ((volume : Measure Plane).prod volume)) := by
  let ν : Measure (Plane × Plane) := (volume : Measure Plane).prod volume
  let F := fun p : ℝ × (Plane × Plane) =>
    φ 0 (a 0, p.2.1) * φ 1 (a 1, p.2.2) *
      pairTwoFutureSpatialProfile θ q p.1 z ![p.2.1, p.2.2]
  have hi : Integrable F ((volume.restrict (Set.Ioo 0 q)).prod ν) :=
    integrable_pairTwo_testedFuture_time_terminal θ q φ a z
  simp only [pairTwoFutureDensity]
  rw [pairTwoContinuumFuture, intervalIntegral.integral_of_le hq.le,
    integral_Ioc_eq_integral_Ioo,
    integral_indicator (measurableSet_Ioo.prod MeasurableSet.univ),
    ← Measure.restrict_prod_eq_prod_univ, integral_prod _ hi, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  dsimp only
  rw [pairTwoTestedSpatialProfile_eq_tested_futureSpatialProfile θ hu.1 hu.2 φ a z]
  congr 1
  exact (integral_prod _ (pairTwoFutureSpatialProfile_test_integrable_bound θ hu.1 hu.2 φ a z).1).symm

/-- The fixed-measure density has exactly the absolute mass of the original
restricted-time density. -/
theorem integral_norm_pairTwoFutureDensity
    (θ q : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    (∫ p : ℝ × (Plane × Plane), ‖pairTwoFutureDensity θ q φ a z p‖
      ∂(volume : Measure ℝ).prod ((volume : Measure Plane).prod volume)) =
    ∫ p : ℝ × (Plane × Plane),
      ‖φ 0 (a 0, p.2.1) * φ 1 (a 1, p.2.2) *
        pairTwoFutureSpatialProfile θ q p.1 z ![p.2.1, p.2.2]‖
      ∂(volume.restrict (Set.Ioo 0 q)).prod ((volume : Measure Plane).prod volume) := by
  simp only [pairTwoFutureDensity, norm_indicator_eq_indicator_norm]
  rw [integral_indicator (measurableSet_Ioo.prod MeasurableSet.univ),
    ← Measure.restrict_prod_eq_prod_univ]

/-- The future of absolute endpoint tests is the absolute mass of the
fixed-measure future density, retaining the exact `16π` factor. -/
theorem pairTwoContinuumFuture_compactAbs_eq_density_mass
    (θ : ℝ) {q : ℝ} (hq : 0 < q) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (a : Fin 2 → Plane) (z : Plane) :
    pairTwoContinuumFuture θ q (fun i => compactAbs (φ i)) a z =
      (16 * Real.pi) * (∫ p : ℝ × (Plane × Plane), ‖pairTwoFutureDensity θ q φ a z p‖
        ∂(volume : Measure ℝ).prod ((volume : Measure Plane).prod volume)) := by
  rw [integral_norm_pairTwoFutureDensity]
  exact pairTwoContinuumFuture_compactAbs_eq_absolute_mass θ hq φ a z

end Critical2DKPZ.SHF.Moments
