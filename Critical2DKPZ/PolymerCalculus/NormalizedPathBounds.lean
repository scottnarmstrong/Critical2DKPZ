/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.PathAssociation
public import Critical2DKPZ.PolymerCalculus.ScalarBounds
import Mathlib.Tactic

/-! A normalized positive finite path mass satisfies variance, negative-moment and Gaussianity-defect bounds when its normalized log-MGF is convex. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace Critical2DKPZ.PolymerCalculus

/-- The annealed mass is exactly the sum of deterministic path coefficients. -/
theorem integral_finitePathMass {ι : Type*} [Fintype ι] (β : ℝ) (a n : ℕ)
    (w : ι → Site) (c : ι × (Fin n → Fin 4) → ℝ) :
    ∫ ω, finitePathMass β a n w c ω ∂disorderLaw = ∑ j, c j := by
  change (∫ ω, ∑ j, c j * Polymer.pathWeight β a (w j.1) j.2 ω ∂disorderLaw) = _
  rw [integral_finsetSum _ (fun j _ => (Polymer.integrable_pathWeight β a (w j.1) j.2).const_mul _)]
  simp only [integral_const_mul, Polymer.integral_pathWeight, mul_one]

/-- If the nonnegative path coefficients have total mass one, the exponential of the log mass has expectation one. -/
theorem mgf_log_finitePathMass_one {ι : Type*} [Fintype ι] (β : ℝ) (a n : ℕ)
    (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ j, 0 ≤ c j) (hpos : ∃ j, 0 < c j) (hnorm : ∑ j, c j = 1) :
    mgf (fun ω => Real.log (finitePathMass β a n w c ω)) disorderLaw 1 = 1 := by
  simp only [mgf, one_mul, Real.exp_log (finitePathMass_pos β a n w hc hpos _)]
  rw [integral_finitePathMass, hnorm]

/-- Convexity of the normalized log-MGF gives variance, negative-moment and Gaussianity-defect bounds for a unit-mean positive finite path mass. -/
theorem finitePathMass_bounds_of_logMGFRatio_convex {ι : Type*} [Fintype ι]
    (β : ℝ) (a n : ℕ) (w : ι → Site) {c : ι × (Fin n → Fin 4) → ℝ}
    (hc : ∀ j, 0 ≤ c j) (hpos : ∃ j, 0 < c j) (hnorm : ∑ j, c j = 1)
    (hconv : ConvexOn ℝ (integrableExpSet
      (fun ω => Real.log (finitePathMass β a n w c ω)) disorderLaw)
      (logMGFRatio disorderLaw (fun ω => Real.log (finitePathMass β a n w c ω)))) :
    let F := fun ω => Real.log (finitePathMass β a n w c ω)
    0 ≤ gaussianityDefect disorderLaw F ∧
      Var[F; disorderLaw] ≤ -2 * (∫ ω, F ω ∂disorderLaw) ∧
      -2 * (∫ ω, F ω ∂disorderLaw) ≤ Real.log (mgf F disorderLaw 2) ∧
      (∀ p : ℝ, 0 ≤ p → Real.log (mgf F disorderLaw (-p)) ≤
        -p * (∫ ω, F ω ∂disorderLaw) + p ^ 2 / 2 * Var[F; disorderLaw]) ∧
      gaussianityDefect disorderLaw F ≤
        Real.log (mgf F disorderLaw 2 / mgf F disorderLaw (-1)) := by
  dsimp only
  have hdom := integrableExpSet_log_finitePathMass β a n w hc hpos
  have hmem (q : ℝ) : q ∈ integrableExpSet
      (fun ω => Real.log (finitePathMass β a n w c ω)) disorderLaw := by rw [hdom]; trivial
  have h0 : 0 ∈ interior (integrableExpSet
      (fun ω => Real.log (finitePathMass β a n w c ω)) disorderLaw) := by
    rw [hdom, interior_univ]
    trivial
  have he := mgf_log_finitePathMass_one β a n w hc hpos hnorm
  exact ⟨gaussianityDefect_nonneg_of_convex hconv h0 (hmem 1) he,
    variance_le_neg_two_mean_of_convex hconv h0 (hmem 1) he,
    neg_two_mean_le_log_second_moment_of_convex hconv (hmem 2) he,
    fun p hp => log_negative_moment_le_of_convex hconv h0 hp (hmem (-p)),
    gaussianityDefect_le_log_ratio_of_convex hconv h0 (hmem 2) (hmem (-1)) he⟩

end Critical2DKPZ.PolymerCalculus
