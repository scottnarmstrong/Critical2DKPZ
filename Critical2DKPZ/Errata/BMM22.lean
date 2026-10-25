/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Endpoint normalization of the two-sided geometric profile in BMM22

Source: arXiv:2007.11030v2, Lemma 7.1.
At q=1 and positive central mass, normalization is infinite, not a real
finite-valued endpoint to which the real intermediate value theorem applies.
-/

@[expose] public noncomputable section
namespace Critical2DKPZ.Errata
open scoped ENNReal

/-- The two-sided geometric profile has infinite total mass at `q = 1`. -/
theorem bmm22_geometric_normalization_at_one {M : ℝ} (hM : 0 < M) :
    (∑' k : ℤ, ENNReal.ofReal ((1 : ℝ) ^ k.natAbs * M)) = ∞ := by
  simp only [one_pow, one_mul]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr hM)

/-- The two-sided geometric profile is not summable at `q = 1`. -/
theorem bmm22_geometric_not_summable_at_one {M : ℝ} (hM : 0 < M) :
    ¬ Summable (fun k : ℤ => (1 : ℝ) ^ k.natAbs * M) := by
  simp only [one_pow, one_mul, summable_const_iff]
  exact hM.ne'

end Critical2DKPZ.Errata
