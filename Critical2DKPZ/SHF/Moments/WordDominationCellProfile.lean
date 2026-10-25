/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationScaledBall
public import Critical2DKPZ.SHF.Moments.WordDominationCellSupport
import Mathlib.Tactic

/-! # Compact cell tests as finite boundary profiles -/

@[expose] public section

noncomputable section

open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

attribute [local instance] Classical.propDecidable

/-- The absolute product of cell test weights is bounded by its cell scale,
and it vanishes unless both endpoint configurations lie in the finite scaled
support ball. -/
theorem abs_prod_cellTestWeight_le_scaledBallIndicators {h N : ℕ}
    (hN : 0 < N) (φ : Fin h → C_c(Plane × Plane, ℝ)) (M R : ℝ)
    (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hφ : ∀ i p, |φ i p| ≤ M)
    (hφR : ∀ i p, φ i p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R)
    (x y : Fin h → Site) :
    |∏ i, cellTestWeight N (φ i) (x i) (y i)| ≤
      (4 * M / N) ^ h *
        (if ∀ i, x i ∈ collisionWordScaledBallSites N R then (1 : ℝ) else 0) *
        (if ∀ i, y i ∈ collisionWordScaledBallSites N R then (1 : ℝ) else 0) := by
  let A : Finset Site := collisionWordScaledBallSites N R
  let c : ℝ := 4 * M / N
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hN1 : 1 ≤ N := by omega
  have hsupport (i : Fin h) {a b : Site}
      (hne : cellTestWeight N (φ i) a b ≠ 0) : a ∈ A ∧ b ∈ A := by
    obtain ⟨ha, hb⟩ := cellTestWeight_ne_zero_imp_scaled_sites_bounded
      hN (φ i) (hφR i) a b hne
    exact ⟨mem_collisionWordScaledBallSites_of_scaledNorm hN1 hR a ha,
      mem_collisionWordScaledBallSites_of_scaledNorm hN1 hR b hb⟩
  by_cases hx : ∀ i, x i ∈ A
  · by_cases hy : ∀ i, y i ∈ A
    · have hcell (i : Fin h) :
          |cellTestWeight N (φ i) (x i) (y i)| ≤ c := by
        dsimp [c]
        exact abs_cellTestWeight_le_four_mul_bound_div hN (φ i) M hM
          (hφ i) (x i) (y i)
      have hprod :
          |∏ i, cellTestWeight N (φ i) (x i) (y i)| ≤ c ^ h := by
        rw [Finset.abs_prod]
        calc
          (∏ i, |cellTestWeight N (φ i) (x i) (y i)|) ≤ ∏ _i : Fin h, c :=
            Finset.prod_le_prod₀ (fun i _ => abs_nonneg _)
              (fun i _ => hcell i)
          _ = c ^ h := by simp
      simpa [A, c, hx, hy] using hprod
    · obtain ⟨i, hi⟩ := not_forall.mp hy
      have hzero : cellTestWeight N (φ i) (x i) (y i) = 0 := by
        by_contra hne
        exact hi (hsupport i hne).2
      have hprod : (∏ i, cellTestWeight N (φ i) (x i) (y i)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) hzero
      simp [A, hx, hy, hprod]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have hzero : cellTestWeight N (φ i) (x i) (y i) = 0 := by
      by_contra hne
      exact hi (hsupport i hne).1
    have hprod : (∏ i, cellTestWeight N (φ i) (x i) (y i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hzero
    simp [A, hx, hprod]

end Critical2DKPZ.SHF.Moments

end
