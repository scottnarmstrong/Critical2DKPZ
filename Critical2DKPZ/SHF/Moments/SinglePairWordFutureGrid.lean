/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureSampling
import Mathlib.Tactic

/-! # Exact grid values of the phase-correct two-particle future test -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

private theorem nearestEven_siteToPlane_of_even {z : Site} (hz : z ∈ evenLattice) :
    nearestEven (siteToPlane z) = z := by
  have h := nearestEven_nearest (siteToPlane z) z hz
  simp only [siteToPlane, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero] at h
  change ((z 0 : ℝ) - nearestEven (siteToPlane z) 0)^2 +
    ((z 1 : ℝ) - nearestEven (siteToPlane z) 1)^2 ≤ 0 at h
  have h₀ : (z 0 : ℝ) - nearestEven (siteToPlane z) 0 = 0 := by
    nlinarith only [h, sq_nonneg ((z 1 : ℝ) - nearestEven (siteToPlane z) 1)]
  have h₁ : (z 1 : ℝ) - nearestEven (siteToPlane z) 1 = 0 := by
    nlinarith only [h, sq_nonneg ((z 0 : ℝ) - nearestEven (siteToPlane z) 0)]
  ext i
  fin_cases i
  · exact_mod_cast (sub_eq_zero.mp h₀).symm
  · exact_mod_cast (sub_eq_zero.mp h₁).symm

/-- Diffusive representatives of even sites round back to the original site. -/
theorem latticePoint_representative_of_even {N : ℕ} (hN : 0 < N)
    {z : Site} (hz : z ∈ evenLattice) :
    latticePoint N (latticeRepresentative N z) = z := by
  have hs : Real.sqrt ((N : ℝ) / 2) ≠ 0 := by positivity
  rw [latticePoint, latticeRepresentative, smul_smul, mul_inv_cancel₀ hs, one_smul]
  exact nearestEven_siteToPlane_of_even hz

/-- The phase-correct sample is exact at every site of the required phase. -/
theorem pairTwoFutureSampleSite_representative {N : ℕ} (hN : 0 < N)
    (r : ℕ) {z : Site} (hz : Even (z 0 + z 1 + (r : ℤ))) :
    pairTwoFutureSampleSite N r (latticeRepresentative N z) = z := by
  let q := entranceParityShift r
  have hq := entranceParityShift_phase r (a := 0) (by change Even ((0 : ℤ) + 0); simp)
  have he : z - q ∈ evenLattice := by
    change Even ((z - q) 0 + (z - q) 1)
    have h := hz.sub hq
    convert h using 1
    simp only [q, Pi.sub_apply, Pi.zero_apply, sub_zero]
    ring
  rw [pairTwoFutureSampleSite, ← latticeRepresentative_sub,
    latticePoint_representative_of_even hN he]
  exact sub_add_cancel z q

/-- Only the remaining duration enters the tested future tail. -/
theorem pairTwoFutureTestedTail_remaining (σ : ℝ) (N L s : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site) (z : Site) :
    pairTwoFutureTestedTail σ N L s φ x z = pairTwoFutureTestedTail σ N (L - s) 0 φ x z := by
  rw [pairTwoFutureTestedTail_eq_terminalFactorSum, pairTwoFutureTestedTail_eq_terminalFactorSum]
  simp only [Nat.sub_zero]

/-- At a collision grid point, the sampled extension equals the original
future test with its full horizon and collision time. -/
theorem pairTwoFutureSampleProfile_grid (ϑ : ℝ) {N : ℕ} (hN : 0 < N)
    (L s : ℕ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site)
    (z : Site) (hz : Even (z 0 + z 1 + ((L - s : ℕ) : ℤ))) :
    pairTwoFutureSampleProfile ϑ N L φ x ((s : ℝ) / N, latticeRepresentative N z) =
      (N : ℝ)^2 * pairTwoFutureTestedTail (criticalSigmaSq ϑ N) N L s φ x z := by
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have ht : Nat.floor ((N : ℝ) * ((s : ℝ) / N)) = s := by
    rw [mul_div_cancel₀ _ hNr, Nat.floor_natCast]
  rw [pairTwoFutureSampleProfile, ht, pairTwoFutureSampleSite_representative hN _ hz]
  exact congrArg (fun b : ℝ => (N : ℝ)^2 * b)
    (pairTwoFutureTestedTail_remaining (criticalSigmaSq ϑ N) N L s φ x z).symm

end Critical2DKPZ.SHF.Moments
