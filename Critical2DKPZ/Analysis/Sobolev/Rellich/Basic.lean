/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: A. Bou-Rabee, Scott Armstrong
Modified for Critical2DKPZ, 2026.
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Rellich.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Sobolev energies increase with the order, while their dual norms decrease and satisfy scalar and difference bounds.

Adapted from A. Bou-Rabee's Lattice-Probability development (Apache-2.0). -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform

namespace Critical2DKPZ.Analysis.Sobolev.Rellich

/-- For `s₀ ≤ s` the weight `(1 + (2π‖ξ‖)²)^s` dominates the weight at `s₀`,
so the `H^{s₀}` norm of a test function is at most its `H^s` norm. -/
theorem sobolevNormSq_mono {d : ℕ} {s₀ s : ℝ} (h : s₀ ≤ s) (φ : Space d → ℝ) :
    sobolevNormSq d s₀ φ ≤ sobolevNormSq d s φ := by
  apply MeasureTheory.lintegral_mono
  intro ξ
  apply ENNReal.ofReal_le_ofReal
  have hbase : (1 : ℝ) ≤ 1 + (2 * Real.pi * ‖ξ‖) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.pi * ‖ξ‖)]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hbase h) (sq_nonneg _)

/-- The negative Sobolev dual norm decreases as the positive Sobolev order of its test functions increases. -/
theorem negSobolevNorm_anti {d : ℕ} {s₀ s : ℝ} (h : s₀ ≤ s) (D : Set (Space d))
    (F : (Space d → ℝ) → ℝ) :
    negSobolevNorm d s D F ≤ negSobolevNorm d s₀ D F := by
  apply sSup_le_sSup
  rintro v ⟨φ, hφ, hnorm, rfl⟩
  refine ⟨φ, hφ, ?_, rfl⟩
  have hmono : sobolevNormSq d s₀ φ ≤ sobolevNormSq d s φ := sobolevNormSq_mono h φ
  exact le_trans hmono hnorm




/-- The dual norm is subadditive for differences: the norm of a difference of
two functionals is at most the sum of their norms. -/
theorem negSobolevNorm_sub_le {d : ℕ} (s : ℝ) (D : Set (Space d))
    (F G : (Space d → ℝ) → ℝ) :
    negSobolevNorm d s D (fun φ => F φ - G φ)
      ≤ negSobolevNorm d s D F + negSobolevNorm d s D G := by
  unfold negSobolevNorm
  apply sSup_le
  rintro v ⟨φ, hφ, hn, rfl⟩
  have hF : ENNReal.ofReal |F φ| ≤
      sSup {v : ℝ≥0∞ | ∃ ψ : Space d → ℝ,
        IsTestFn D ψ ∧ sobolevNormSq d s ψ ≤ 1 ∧ v = ENNReal.ofReal |F ψ|} :=
    le_sSup ⟨φ, hφ, hn, rfl⟩
  have hG : ENNReal.ofReal |G φ| ≤
      sSup {v : ℝ≥0∞ | ∃ ψ : Space d → ℝ,
        IsTestFn D ψ ∧ sobolevNormSq d s ψ ≤ 1 ∧ v = ENNReal.ofReal |G ψ|} :=
    le_sSup ⟨φ, hφ, hn, rfl⟩
  calc ENNReal.ofReal |F φ - G φ|
      ≤ ENNReal.ofReal (|F φ| + |G φ|) := ENNReal.ofReal_le_ofReal (abs_sub_le_iff.mpr
        ⟨by linarith [le_abs_self (F φ), neg_abs_le (G φ)],
          by linarith [neg_abs_le (F φ), le_abs_self (G φ)]⟩)
    _ = ENNReal.ofReal |F φ| + ENNReal.ofReal |G φ| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ _ := add_le_add hF hG

end Critical2DKPZ.Analysis.Sobolev.Rellich

end
