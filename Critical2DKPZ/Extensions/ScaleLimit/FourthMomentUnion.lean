/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.HarmonicBounds
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Critical2DKPZ.OnePoint.BlockRatioOriginalLawMomentBounds
import Mathlib.Tactic

/-! # The fourth-moment union bound for late blocks -/

@[expose] public section

open MeasureTheory

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Uniform fourth moments of order `j⁻²` control the union of all bad blocks
between a positive lower index and any later upper index. -/
theorem fourth_moment_union_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, 1 ≤ j → Measurable (X j)) {C : ℝ} (hC : 0 ≤ C)
    (hi : ∀ j, 1 ≤ j → Integrable (fun ω => X j ω ^ 4) P)
    (hb : ∀ j, 1 ≤ j → (∫ ω, X j ω ^ 4 ∂P) ≤ C / (j : ℝ) ^ 2)
    {ℓ n : ℕ} (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n) :
    P.real {ω | ∃ j ∈ Finset.Ioc ℓ n, 1 / 2 < |X j ω|} ≤ 16 * C / ℓ := by
  classical
  have htail (j : ℕ) (hj : j ∈ Finset.Ioc ℓ n) :
      P.real {ω | 1 / 2 < |X j ω|} ≤ 16 * (C / (j : ℝ) ^ 2) := by
    have hj1 : 1 ≤ j := by have := (Finset.mem_Ioc.mp hj).1; omega
    have habs (z : ℝ) : |z| ^ 4 = z ^ 4 := (show Even 4 from by decide).pow_abs z
    have h := OnePoint.measure_abs_gt_half_le_integral_four (X j) (hm j hj1)
      (by simpa only [habs] using hi j hj1)
    exact h.trans (mul_le_mul_of_nonneg_left
      (by simpa only [habs] using hb j hj1) (by norm_num))
  have heq : {ω | ∃ j ∈ Finset.Ioc ℓ n, 1 / 2 < |X j ω|} =
      ⋃ j ∈ Finset.Ioc ℓ n, {ω | 1 / 2 < |X j ω|} := by ext ω; simp
  rw [heq]
  calc
    _ ≤ ∑ j ∈ Finset.Ioc ℓ n, P.real {ω | 1 / 2 < |X j ω|} :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.Ioc ℓ n, 16 * (C / (j : ℝ) ^ 2) :=
      Finset.sum_le_sum htail
    _ = (16 * C) * ∑ j ∈ Finset.Ioc ℓ n, 1 / (j : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ ≤ (16 * C) * (1 / (ℓ : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_Ioc_inv_sq_le hℓ hℓn) (by positivity)
    _ = 16 * C / ℓ := by ring

end Critical2DKPZ.Extensions.ScaleLimit
