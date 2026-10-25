/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialZero
public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialSupport
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Incoming support of the complete continuum two-particle future -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory
open scoped CompactlySupported

/-- A vanishing incoming section of either terminal test annihilates the
complete continuum future. This is an identity at every horizon. -/
theorem pairTwoContinuumFuture_zero_of_section_zero
    (θ H : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane)
    (i : Fin 2) (hφ : ∀ y : Plane, φ i (a i, y) = 0) (z : Plane) :
    pairTwoContinuumFuture θ H φ a z = 0 := by
  fin_cases i
  · change (∀ y : Plane, φ 0 (a 0, y) = 0) at hφ
    simp only [pairTwoContinuumFuture, pairTwoTestedSpatialProfile,
      pairTwoTerminalConvolution, hφ, zero_mul, mul_zero, integral_zero,
      intervalIntegral.integral_zero]
  · change (∀ y : Plane, φ 1 (a 1, y) = 0) at hφ
    simp only [pairTwoContinuumFuture, pairTwoTestedSpatialProfile,
      pairTwoTerminalConvolution, hφ, zero_mul, mul_zero, integral_zero,
      intervalIntegral.integral_zero]

/-- The continuum future retains the incoming spatial support of the tests. -/
theorem pairTwoContinuumFuture_zero_of_incoming_norm
    (θ H : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane)
    {R : ℝ} (hR : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (i : Fin 2) (hi : R < ‖a i‖) (z : Plane) :
    pairTwoContinuumFuture θ H φ a z = 0 := by
  apply pairTwoContinuumFuture_zero_of_section_zero θ H φ a i
  intro y
  by_contra hne
  exact (not_le_of_gt hi) (hR i (a i, y) hne).1

end Critical2DKPZ.SHF.Moments
