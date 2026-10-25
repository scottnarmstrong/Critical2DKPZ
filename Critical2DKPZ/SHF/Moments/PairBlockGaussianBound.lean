/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.PairBlockLocalLimit
public import Critical2DKPZ.Collision.SpatialRenewalHatGaussian
import Mathlib.Tactic
import Critical2DKPZ.Blocks.StringSumGaussian

/-! # Scalar-mass form of the pair-block Gaussian bound -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

/-- The spatial pair-block kernel is bounded by its scalar renewal mass times a Gaussian envelope. -/
theorem exists_spatialRenewal_le_scalarMass_gaussian :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ (σ2 : ℝ) (n : ℕ), 0 ≤ σ2 → 1 ≤ n → ∀ z : Site,
        Even ((n : ℤ) + z 0 + z 1) →
        Collision.spatialRenewal σ2 n z ≤
          C / n * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) *
            Renewal.renewalMass (fun r => σ2 * Renewal.returnWeight r) n := by
  obtain ⟨c₀, hc₀, huniform⟩ := Blocks.exists_stringGaussian_bounds
  let c : ℝ := c₀ / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hcc : c ≤ c₀ := by dsimp [c]; linarith
  obtain ⟨Cwalk, Crenewal, hCwalkOne, hCrenewalOne, hCwalk, hCrenewal,
    hkernel, hconvolution, hvariance, hbound⟩ := huniform c hc hcc
  refine ⟨Crenewal, c, hCrenewal, hc, ?_⟩
  intro σ2 n hσ hn z hpar
  have hn0 : n ≠ 0 := by omega
  have hmass := tsum_spatialRenewal_eq_renewalMass σ2 n
  have hhat : Collision.hatGaussian c n z =
      (n : ℝ)⁻¹ * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) := by
    simp [Collision.hatGaussian, hn0, hpar]
  calc
    Collision.spatialRenewal σ2 n z ≤
        Crenewal * (∑' x : Site, Collision.spatialRenewal σ2 n x) *
          Collision.hatGaussian c n z := hbound σ2 hσ n hn z
    _ = Crenewal / n * Real.exp (-c * ‖siteToPlane z‖ ^ 2 / n) *
          Renewal.renewalMass (fun r => σ2 * Renewal.returnWeight r) n := by
      rw [hmass, hhat]
      ring

end Critical2DKPZ.SHF.Moments

end
