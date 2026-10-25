/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureGrid
public import Critical2DKPZ.SHF.Moments.SinglePairWordTruncation
public import Critical2DKPZ.SHF.Moments.WordLimitUniformSingleMass
import Mathlib.Tactic

/-! # Uniform tested future bounds on arbitrary bounded horizons -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- The bounded critical run mass controls the complete tested future uniformly over spatial locations at fixed finite diffusive horizons. -/
theorem eventually_pairTwoFutureTestedTail_bdd_horizon
    (ϑ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ n s : ℕ,
      ((n - s : ℕ) : ℝ) ≤ T * N → ∀ x : Fin 2 → Site, ∀ z : Site,
        |(N : ℝ)^2 * pairTwoFutureTestedTail (criticalSigmaSq ϑ N) N n s φ x z| ≤ C := by
  let M : Fin 2 → ℝ := fun i => ‖(φ i).toBoundedContinuousFunction‖
  let P : ℝ := 16 * M 0 * M 1
  have hP : 0 ≤ P := by dsimp [P, M]; positivity
  obtain ⟨B, hB, hb⟩ := eventually_critical_run_mass_le ϑ T hT
  refine ⟨P * B, mul_nonneg hP hB.le, ?_⟩
  filter_upwards [hb, criticalBeta_spec ϑ, Renewal.criticalSigmaSq_eventually_pos ϑ,
    eventually_gt_atTop 0] with N hbN hspec hσ hN
  intro n s htime x z
  have hσeq : sigmaSq (criticalBeta ϑ N) = criticalSigmaSq ϑ N := hspec
  have hmass := hbN (n - s) htime
  rw [hσeq] at hmass
  let J := Finset.range (n - s + 1)
  let k : ℕ → ℕ := fun r => n - s - r
  have he := abs_pairTwo_testedRenewalWindow_le_scalarMass hN (criticalSigmaSq ϑ N)
    hσ.le J k φ x z M (fun i => norm_nonneg _)
    (fun i p => (φ i).toBoundedContinuousFunction.norm_coe_le_norm p)
  have heq : (N : ℝ)^2 * pairTwoFutureTestedTail (criticalSigmaSq ϑ N) N n s φ x z =
      (N : ℝ)^2 * criticalSigmaSq ϑ N * ∑ r ∈ J, ∑ d ∈ endpoints 0 r,
        Collision.spatialRenewal (criticalSigmaSq ϑ N) r d *
          pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 0 *
          pairTwoFutureTerminalCellFactor N (k r) φ x (z + d) 1 := by
    rw [pairTwoFutureTestedTail_remaining, pairTwoFutureTestedTail_eq_displacementSum]
    dsimp only [J, k]
    ring
  rw [heq]
  have hform : 16 * criticalSigmaSq ϑ N * M 0 * M 1 *
      (∑ r ∈ J, Renewal.renewalMass (fun j => criticalSigmaSq ϑ N * Renewal.returnWeight j) r) =
      P * (criticalSigmaSq ϑ N * Renewal.renewalFunction
        (fun j => criticalSigmaSq ϑ N * Renewal.returnWeight j) (n - s)) := by
    dsimp only [J]
    rw [Renewal.sum_renewalMass_range]
    dsimp only [P]
    ring
  exact (he.trans_eq hform).trans (mul_le_mul_of_nonneg_left hmass hP)

/-- The phase-correct sampled future is bounded on every fixed finite
horizon, uniformly over incoming and collision locations. -/
theorem eventually_pairTwoFutureSampleProfile_bdd_horizon
    (ϑ T : ℝ) (hT : 0 < T) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, (L : ℝ) ≤ T * N →
      ∀ x : Fin 2 → Site, ∀ p : ℝ × Plane, |pairTwoFutureSampleProfile ϑ N L φ x p| ≤ C := by
  obtain ⟨C, hC, hb⟩ := eventually_pairTwoFutureTestedTail_bdd_horizon ϑ T hT φ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hb] with N hN L hL x p
  have hrem : ((L - Nat.floor ((N : ℝ) * p.1) : ℕ) : ℝ) ≤ T * N :=
    (show ((L - Nat.floor ((N : ℝ) * p.1) : ℕ) : ℝ) ≤ L by exact_mod_cast Nat.sub_le L _).trans hL
  exact hN _ 0 (by simpa only [Nat.sub_zero] using hrem) x
    (pairTwoFutureSampleSite N (L - Nat.floor ((N : ℝ) * p.1)) p.2)

end Critical2DKPZ.SHF.Moments
