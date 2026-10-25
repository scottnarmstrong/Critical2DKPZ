/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.CriticalWindow
public import Critical2DKPZ.Definitions.PointToPlane
public import Critical2DKPZ.Definitions.DisorderLawIsProbabilityMeasure
import Critical2DKPZ.Polymer.FirstCollision

/-! # Second-moment renewal identities

The first-collision formula identifies the free polymer second moment with the renewal
function for the period-two return kernel `q_{2r}(0)` and the terminal-disorder convention. -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- The free partition-function second moment in the terminal-disorder convention. -/
def freeSecondMoment (β : ℝ) (n : ℕ) : ℝ :=
  ∫ ω, pointToPlane β 0 n 0 ω ^ 2 ∂disorderLaw

/-- The first-collision recurrence, including the free contribution one. -/
theorem freeSecondMoment_recurrence (β : ℝ) (n : ℕ) :
    freeSecondMoment β n = 1 + ∑ r ∈ Finset.Icc 1 n,
      (Real.exp (β ^ 2) - 1) * returnWeight r * freeSecondMoment β (n - r) := by
  have h := Polymer.pointToPlane_firstCollision β 0 n 0 0
  simp only [sub_self, ← pow_two] at h
  change freeSecondMoment β n - 1 = ∑ r ∈ Finset.Icc 1 n,
    returnWeight r * (Real.exp (β ^ 2) - 1) * freeSecondMoment β (n - r) at h
  calc
    freeSecondMoment β n = 1 + (freeSecondMoment β n - 1) := by ring
    _ = _ := by
      rw [h]
      congr 1
      exact Finset.sum_congr rfl fun r _ => by ring

/-- The exact free second moment is the full renewal function. -/
theorem freeSecondMoment_eq_renewalFunction (β : ℝ) :
    freeSecondMoment β = renewalFunction (fun r => (Real.exp (β ^ 2) - 1) * returnWeight r) :=
  eq_renewalFunction_of_recurrence _ _ (freeSecondMoment_recurrence β)

/-- Eventually the Gaussian coupling gives exactly the critical renewal function. -/
theorem eventually_freeSecondMoment_eq_criticalRenewalFunction (ϑ : ℝ) :
    ∀ᶠ N : ℕ in atTop, ∀ n, freeSecondMoment (criticalBeta ϑ N) n = criticalRenewalFunction ϑ N n := by
  filter_upwards [criticalBeta_spec ϑ] with N hN
  intro n
  rw [freeSecondMoment_eq_renewalFunction, hN]
  rfl

/-- The variance-weighted polymer second moment has a uniform inverse-logarithmic bound on the unit time horizon. -/
theorem secondMoment_log_bound (ϑ : ℝ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → k ≤ N →
      criticalSigmaSq ϑ N * ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw ≤
        C / Real.log (1 + (N : ℝ) / k) := by
  obtain ⟨C, _, hbound⟩ := criticalRenewalFunction_log_bound ϑ
  refine ⟨C, ?_⟩
  filter_upwards [hbound, eventually_freeSecondMoment_eq_criticalRenewalFunction ϑ]
    with N hN heq
  intro k hk hkN
  change criticalSigmaSq ϑ N * freeSecondMoment (criticalBeta ϑ N) k ≤ _
  rw [heq k]
  exact hN k hk hkN

/-- The real-horizon second-moment bound, including horizon zero in the `L + 1` form. -/
theorem secondMoment_log_bound_horizon (ϑ T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, (L : ℝ) ≤ T * N →
      criticalSigmaSq ϑ N * ∫ ω, pointToPlane (criticalBeta ϑ N) 0 L 0 ω ^ 2 ∂disorderLaw ≤
        C / Real.log (1 + (N : ℝ) / (L + 1)) := by
  obtain ⟨C, hC, hbound⟩ := criticalRenewalFunction_log_bound_zero_horizon ϑ T
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_freeSecondMoment_eq_criticalRenewalFunction ϑ]
    with N hN heq
  intro L hL
  change criticalSigmaSq ϑ N * freeSecondMoment (criticalBeta ϑ N) L ≤ _
  rw [heq L]
  exact hN L hL

end Critical2DKPZ.Renewal

end
