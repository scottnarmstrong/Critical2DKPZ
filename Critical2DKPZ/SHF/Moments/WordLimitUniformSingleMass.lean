/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitPairMass
public import Critical2DKPZ.SHF.Moments.EntranceScaling
import Critical2DKPZ.Lattice.Basic
import Mathlib.Tactic

/-! # Uniform one-letter mass away from the starting diagonal -/

@[expose] public noncomputable section

open Filter
open scoped BigOperators Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- The integrated critical run mass is bounded on every fixed diffusive horizon. -/
theorem eventually_critical_run_mass_le (ϑ T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, (L : ℝ) ≤ T * N →
      sigmaSq (criticalBeta ϑ N) * Renewal.renewalFunction
        (fun k => sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight k) L ≤ B := by
  obtain ⟨C, hC, hbound⟩ := Renewal.criticalRenewalFunction_log_bound_zero_horizon ϑ T
  let d := Real.log (1 + 1 / (T + 1))
  have hd : 0 < d := by
    apply Real.log_pos
    have hp : 0 < 1 / (T + 1) := one_div_pos.mpr (by linarith only [hT])
    linarith only [hp]
  refine ⟨C / d, div_pos hC hd, ?_⟩
  filter_upwards [hbound, criticalBeta_spec ϑ, eventually_ge_atTop 1]
    with N hboundN hspec hN
  intro L hL
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hLplus : (L : ℝ) + 1 ≤ (T + 1) * N := by
    calc
      _ ≤ T * N + N := add_le_add hL hNr
      _ = _ := by ring
  have hfrac : 1 / (T + 1) ≤ (N : ℝ) / ((L : ℝ) + 1) := by
    apply (div_le_div_iff₀ (by linarith only [hT]) (by positivity)).mpr
    simpa only [one_mul, mul_comm] using hLplus
  have hlog : d ≤ Real.log (1 + (N : ℝ) / ((L : ℝ) + 1)) :=
    Real.log_le_log (by positivity) (add_le_add le_rfl hfrac)
  change sigmaSq (criticalBeta ϑ N) = criticalSigmaSq ϑ N at hspec
  rw [hspec]
  exact (hboundN L hL).trans (div_le_div_of_nonneg_left hC.le hd hlog)



end Critical2DKPZ.SHF.Moments
