/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordTimeFubini
public import Mathlib.Tactic
public import Critical2DKPZ.SHF.Moments.WordDominationTestDomination
import Mathlib.Tactic

/-! # Absolute future mass as the future of absolute tests -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported

/-- The absolute time-terminal mass is exactly the continuum future tested
against the absolute endpoint tests, with the original `16π` normalization.
This supplies an integrable majorant when the remaining horizon moves with
the first entrance time. -/
theorem pairTwoContinuumFuture_compactAbs_eq_absolute_mass
    (θ : ℝ) {q : ℝ} (hq : 0 < q) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (a : Fin 2 → Plane) (z : Plane) :
    pairTwoContinuumFuture θ q (fun i => compactAbs (φ i)) a z =
      (16 * Real.pi) * (∫ p : ℝ × (Plane × Plane),
        ‖φ 0 (a 0, p.2.1) * φ 1 (a 1, p.2.2) *
          pairTwoFutureSpatialProfile θ q p.1 z ![p.2.1, p.2.2]‖
        ∂(volume.restrict (Set.Ioo 0 q)).prod ((volume : Measure Plane).prod volume)) := by
  let ν : Measure (Plane × Plane) := (volume : Measure Plane).prod volume
  let Φ : Fin 2 → C_c(Plane × Plane, ℝ) := fun i => compactAbs (φ i)
  let F := fun p : ℝ × (Plane × Plane) =>
    φ 0 (a 0, p.2.1) * φ 1 (a 1, p.2.2) *
      pairTwoFutureSpatialProfile θ q p.1 z ![p.2.1, p.2.2]
  have hi : Integrable F ((volume.restrict (Set.Ioo 0 q)).prod ν) :=
    integrable_pairTwo_testedFuture_time_terminal θ q φ a z
  have hΦ (i : Fin 2) (p : Plane × Plane) : Φ i p = |φ i p| := rfl
  rw [pairTwoContinuumFuture, intervalIntegral.integral_of_le hq.le,
    integral_Ioc_eq_integral_Ioo, integral_prod _ hi.norm, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro u hu
  change pairTwoTestedSpatialProfile θ u (q - u) Φ a z =
    (16 * Real.pi) * (∫ y : Plane × Plane, ‖F (u, y)‖ ∂ν)
  rw [pairTwoTestedSpatialProfile_eq_tested_futureSpatialProfile θ hu.1 hu.2 Φ a z]
  congr 1
  rw [← integral_prod _ (pairTwoFutureSpatialProfile_test_integrable_bound θ hu.1 hu.2 Φ a z).1]
  apply integral_congr_ae
  filter_upwards [] with y
  dsimp only [F]
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (pairTwoFutureSpatialProfile_nonneg θ hu.1 hu.2 z ![y.1, y.2])]
  rw [hΦ, hΦ]

end Critical2DKPZ.SHF.Moments
