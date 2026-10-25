/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordInitialCutoff
public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureSupport
import Mathlib.Tactic

/-! # The complete incoming integral of cutoff two-particle entrances -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- Incoming locations outside the common support ball give a zero cutoff step. -/
theorem cutoffInitialStep_zero_outside_ball
    (ϑ : ℝ) {N : ℕ} (hN : 0 < N) (L lo hi : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ))
    {R : ℝ} (hR : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (p : Plane × Plane) (hp : R + 4 < ‖p.1‖ ∨ R + 4 < ‖p.2‖) :
    pairTwoCutoffInitialStep ϑ N L lo hi φ η p = 0 := by
  let x : Fin 2 → Site := ![latticePoint N p.1, latticePoint N p.2]
  have hx : ∃ i : Fin 2, x i ∉
      ((SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst) := by
    rcases hp with hp | hp
    · refine ⟨0, ?_⟩
      intro hm
      exact (not_le_of_gt hp) (cellPairTest_initialSupport_sampled_norm_le hN (φ 0) (hR 0) hm)
    · refine ⟨1, ?_⟩
      intro hm
      exact (not_le_of_gt hp) (cellPairTest_initialSupport_sampled_norm_le hN (φ 1) (hR 1) hm)
  obtain ⟨i, hxi⟩ := hx
  have hz (q : ℝ × Plane) : pairTwoFutureSampleProfile ϑ N L φ x q = 0 :=
    pairTwoFutureSampleProfile_zero_of_initial_notSupport ϑ N L φ x i hxi q
  change collisionEntrance N lo hi (x 0) (x 1)
    (fun q => η q * pairTwoFutureSampleProfile ϑ N L φ x q) = 0
  simp only [collisionEntrance, collisionSlice, hz, mul_zero, Finset.sum_const_zero]

/-- The continuum cutoff entrance has the same incoming support ball. -/
theorem continuumCutoffEntrance_zero_outside_ball
    (θ T s t : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (η : C_c(ℝ × Plane, ℝ))
    {R : ℝ} (hR : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (p : Plane × Plane) (hp : R + 4 < ‖p.1‖ ∨ R + 4 < ‖p.2‖) :
    pairTwoContinuumCutoffEntrance θ T s t φ η p = 0 := by
  let a : Fin 2 → Plane := ![p.1, p.2]
  have hz (H : ℝ) (z : Plane) : pairTwoContinuumFuture θ H φ a z = 0 := by
    rcases hp with hp | hp
    · exact pairTwoContinuumFuture_zero_of_incoming_norm θ H φ a hR 0 (by dsimp [a]; linarith only [hp]) z
    · exact pairTwoContinuumFuture_zero_of_incoming_norm θ H φ a hR 1 (by dsimp [a]; linarith only [hp]) z
  change 4 * (∫ u in s..t, heatKernelPairProfileIntegral u p.1 p.2
    (fun q => η q * pairTwoContinuumFuture θ (T - q.1) φ a q.2)) = 0
  simp only [heatKernelPairProfileIntegral, hz, mul_zero, zero_mul, integral_zero,
    intervalIntegral.integral_zero]


end Critical2DKPZ.SHF.Moments
