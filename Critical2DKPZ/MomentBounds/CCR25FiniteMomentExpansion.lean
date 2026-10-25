/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25CenteredExpansion
public import Critical2DKPZ.Polymer.Orthogonality
import Mathlib.Tactic

/-! # Finite CCR25 moment expansion in Gaussian coordinate moments -/

@[expose] public section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- Space-time coordinates visited at selected times by one centered chaos
summand. -/
def ccr25ChaosCoordinates {n : ℕ} (a : ℕ) (w : Site)
    (i : Finset ℕ × (Fin n → Fin 4)) : Finset (ℕ × Site) :=
  i.1.image (fun j => (a + j, Critical2DKPZ.walkPosition w i.2 j))

/-- A centered chaos term is its time-space chaos monomial multiplied by the path probability. -/
theorem ccr25CenteredChaosTerm_eq_chaosMonomial {n : ℕ}
    (β : ℝ) (a : ℕ) (w : Site) (i : Finset ℕ × (Fin n → Fin 4))
    (ω : Disorder) :
    ccr25CenteredChaosTerm β a n w i ω =
      (4 : ℝ)⁻¹ ^ n * Critical2DKPZ.Polymer.chaosMonomial β
        (ccr25ChaosCoordinates a w i) ω := by
  classical
  unfold ccr25CenteredChaosTerm Critical2DKPZ.Polymer.chaosMonomial
    ccr25ChaosCoordinates
  congr 1
  rw [Finset.prod_image]
  intro j hj k hk hEq
  exact Nat.add_left_cancel (congrArg Prod.fst hEq)

/-- A finite product of replica chaos monomials has every finite moment. -/
theorem memLp_replicaChaosMonomialProduct {h : ℕ} (β : ℝ)
    (A : Fin h → Finset (ℕ × Site)) :
    ∀ p : ℝ≥0∞, p ≠ ∞ →
      MemLp (fun ω : Disorder =>
        ∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β (A i) ω) p disorderLaw := by
  induction h with
  | zero =>
      intro p hp
      change MemLp (fun _ : Disorder => (1 : ℝ)) p disorderLaw
      exact memLp_const 1
  | succ h ih =>
      intro p hp
      have hp2 : 2 * p ≠ ∞ := ENNReal.mul_ne_top (by norm_num) hp
      have hprod :
          (fun ω : Disorder =>
            ∏ i : Fin (h + 1), Critical2DKPZ.Polymer.chaosMonomial β (A i) ω) =
          fun ω => Critical2DKPZ.Polymer.chaosMonomial β (A 0) ω *
            (∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β (A i.succ) ω) := by
        funext ω
        rw [Fin.prod_univ_succ]
      rw [hprod]
      exact Critical2DKPZ.Polymer.memLp_mul_double p
        (Critical2DKPZ.Polymer.memLp_chaosMonomial β (A 0) (2 * p) hp2)
        (ih (fun i => A i.succ) (2 * p) hp2)

/-- The product of replica chaos monomials is integrable. -/
theorem integrable_replicaChaosMonomialProduct {h : ℕ} (β : ℝ)
    (A : Fin h → Finset (ℕ × Site)) :
    Integrable (fun ω : Disorder =>
      ∏ i : Fin h, Critical2DKPZ.Polymer.chaosMonomial β (A i) ω) disorderLaw := by
  exact memLp_one_iff_integrable.mp
    (memLp_replicaChaosMonomialProduct β A 1 (by simp))






/-- The first centered Gaussian disorder moment vanishes. -/
theorem gaussianDisorderMoment_one_eq_zero (β : ℝ) :
    Critical2DKPZ.MomentBounds.gaussianDisorderMoment β 1 = 0 := by
  change (∫ ω : Disorder, Critical2DKPZ.Polymer.xi β (0, 0) ω ^ 1 ∂disorderLaw) = 0
  simp only [pow_one]
  exact Critical2DKPZ.Polymer.integral_xi β (0, 0)


end

end Critical2DKPZ.MomentBounds
