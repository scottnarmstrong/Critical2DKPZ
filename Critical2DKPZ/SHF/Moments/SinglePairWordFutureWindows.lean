/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureLimit
import Mathlib.Tactic

/-! # Renewal-window decompositions of the tested two-particle future -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- A renewal-time window of the tested future tail, with its original `N²`
normalization. This is the same finite block formula restricted to clock sites. -/
def pairTwoTestedRenewalWindow (ϑ : ℝ) (N L : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site) (z : Site)
    (J : Finset ℕ) : ℝ :=
  (N : ℝ) ^ 2 * criticalSigmaSq ϑ N * ∑ r ∈ J, ∑ d ∈ endpoints 0 r,
    Collision.spatialRenewal (criticalSigmaSq ϑ N) r d *
      pairTwoFutureTerminalCellFactor N (L - r) φ x (z + d) 0 *
      pairTwoFutureTerminalCellFactor N (L - r) φ x (z + d) 1

/-- Taking the complete clock range recovers the normalized exact future tail. -/
theorem pairTwoTestedRenewalWindow_full (ϑ : ℝ) (N L : ℕ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site) (z : Site) :
    pairTwoTestedRenewalWindow ϑ N L φ x z (Finset.range (L + 1)) =
      (N : ℝ) ^ 2 * pairTwoFutureTestedTail (criticalSigmaSq ϑ N) N L 0 φ x z := by
  rw [pairTwoFutureTestedTail_eq_displacementSum]
  dsimp [pairTwoTestedRenewalWindow]
  ring

/-- Splitting the complete renewal clock into a bottom strip, an interior
window and a terminal strip is exact. -/
theorem pairTwoTestedRenewalWindow_three_parts (ϑ : ℝ) (N L A B : ℕ)
    (hAB : A ≤ B) (hBL : B ≤ L)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site) (z : Site) :
    pairTwoTestedRenewalWindow ϑ N L φ x z (Finset.range (L + 1)) =
      pairTwoTestedRenewalWindow ϑ N L φ x z (Finset.range (A + 1)) +
      pairTwoTestedRenewalWindow ϑ N L φ x z (Finset.Icc (A + 1) B) +
      pairTwoTestedRenewalWindow ϑ N L φ x z (Finset.Icc (B + 1) L) := by
  let f : ℕ → ℝ := fun r => ∑ d ∈ endpoints 0 r,
    Collision.spatialRenewal (criticalSigmaSq ϑ N) r d *
      pairTwoFutureTerminalCellFactor N (L - r) φ x (z + d) 0 *
      pairTwoFutureTerminalCellFactor N (L - r) φ x (z + d) 1
  have hsum : (∑ r ∈ Finset.range (L + 1), f r) =
      (∑ r ∈ Finset.range (A + 1), f r) +
      (∑ r ∈ Finset.Icc (A + 1) B, f r) +
      (∑ r ∈ Finset.Icc (B + 1) L, f r) := by
    rw [← Finset.sum_range_add_sum_Ico f (show B + 1 ≤ L + 1 by omega),
      ← Finset.sum_range_add_sum_Ico f (show A + 1 ≤ B + 1 by omega)]
    simp only [Finset.Ico_add_one_right_eq_Icc]
  unfold pairTwoTestedRenewalWindow
  change _ * (∑ r ∈ Finset.range (L + 1), f r) = _
  rw [hsum]
  ring

/-- The initial renewal strip is uniformly small, with no condition on the
complete future horizon or on its spatial locations. -/
theorem pairTwoTestedRenewalWindow_initial_small
    (ϑ : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (M : Fin 2 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hφ : ∀ i p, |φ i p| ≤ M i) :
    ∀ ε > 0, ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ᶠ N : ℕ in atTop,
      ∀ K : ℕ, (K : ℝ) ≤ δ * N → ∀ L : ℕ, ∀ x : Fin 2 → Site, ∀ z : Site,
        |pairTwoTestedRenewalWindow ϑ N L φ x z (Finset.range (K + 1))| ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ, hδle, he⟩ := pairTwo_testedRenewalWindow_small_uniform ϑ φ M hM hφ ε hε
  refine ⟨δ, hδ, hδle, ?_⟩
  filter_upwards [he] with N hN
  intro K hK L x z
  exact hN K hK (fun r => L - r) x z


end Critical2DKPZ.SHF.Moments

end
