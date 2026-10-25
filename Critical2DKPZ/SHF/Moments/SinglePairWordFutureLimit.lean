/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordBoundary
import Mathlib.Tactic

/-! # The full tested two-particle future limit -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter Polymer
open scoped CompactlySupported Topology

/-- The exact future tail in displacement coordinates, matching the spatial
and time convolution limits. -/
theorem pairTwoFutureTestedTail_eq_displacementSum
    (σ : ℝ) (N L : ℕ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (x : Fin 2 → Site) (z : Site) :
    pairTwoFutureTestedTail σ N L 0 φ x z =
      σ * ∑ r ∈ Finset.range (L + 1), ∑ d ∈ endpoints 0 r,
        Collision.spatialRenewal σ r d *
          pairTwoFutureTerminalCellFactor N (L - r) φ x (z + d) 0 *
          pairTwoFutureTerminalCellFactor N (L - r) φ x (z + d) 1 := by
  rw [pairTwoFutureTestedTail_eq_terminalFactorSum]
  simp only [Nat.sub_zero, Fin.prod_univ_two]
  apply congrArg (fun a : ℝ => σ * a)
  apply Finset.sum_congr rfl
  intro r hr
  refine Finset.sum_bij (fun w _ => w - z) ?_ ?_ ?_ ?_
  · intro w hw
    exact mem_endpoints_sub.mp hw
  · intro w hw v hv hEq
    exact sub_left_injective hEq
  · intro d hd
    refine ⟨z + d, ?_, ?_⟩
    · apply mem_endpoints_sub.mpr
      simpa only [add_sub_cancel_left] using hd
    · simp
  · intro w hw
    rw [show z + (w - z) = w by abel]
    ring

end Critical2DKPZ.SHF.Moments

end
