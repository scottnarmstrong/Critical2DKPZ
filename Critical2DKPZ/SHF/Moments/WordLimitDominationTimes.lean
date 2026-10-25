/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitGapPotential
public import Critical2DKPZ.SHF.Moments.WordLimitUniformSingleMass

/-! # Returning the first-block time sum to the same gap potential -/

@[expose] public noncomputable section

open Filter
open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- An inverse-square-root spectator time and a bounded cumulative run mass
return the entrance/run sum to the original gap potential. -/
theorem sum_entrance_run_inv_sqrt_le_gapPotential (β : ℝ) (n : ℕ) (z : Site) (B : ℝ)
    (hrun : ∀ L : ℕ, L ≤ n → sigmaSq β * Renewal.renewalFunction
      (fun k => sigmaSq β * Renewal.returnWeight k) L ≤ B) :
    (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1),
      srwKernel (2 * s) z * (sigmaSq β * Renewal.renewalMass
        (fun k => sigmaSq β * Renewal.returnWeight k) r) /
          Real.sqrt ((s : ℝ) + r + 1)) ≤ B * wordGapPotential n z := by
  let w : ℕ → ℝ := fun k => sigmaSq β * Renewal.returnWeight k
  have hw (k : ℕ) : 0 ≤ w k := mul_nonneg (sigmaSq_nonneg β) (srwKernel_nonneg _ _)
  have hslice (s : ℕ) :
      (∑ r ∈ Finset.range (n - s + 1), srwKernel (2 * s) z *
        (sigmaSq β * Renewal.renewalMass w r) / Real.sqrt ((s : ℝ) + r + 1)) ≤
        B * (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) := by
    have hsum : (∑ r ∈ Finset.range (n - s + 1), sigmaSq β * Renewal.renewalMass w r) ≤ B := by
      rw [← Finset.mul_sum, Renewal.sum_renewalMass_range]
      exact hrun (n - s) (Nat.sub_le _ _)
    calc
      _ ≤ ∑ r ∈ Finset.range (n - s + 1),
          (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) *
            (sigmaSq β * Renewal.renewalMass w r) := by
        apply Finset.sum_le_sum
        intro r hr
        have hden : Real.sqrt ((s : ℝ) + 1) ≤ Real.sqrt ((s : ℝ) + r + 1) := by
          apply Real.sqrt_le_sqrt
          have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
          linarith only [hr0]
        have hh := div_le_div_of_nonneg_left
          (mul_nonneg (srwKernel_nonneg (2 * s) z)
            (mul_nonneg (sigmaSq_nonneg β) (Renewal.renewalMass_nonneg hw r)))
          (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < s + 1)) hden
        exact hh.trans_eq (by ring)
      _ = (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) *
          ∑ r ∈ Finset.range (n - s + 1), sigmaSq β * Renewal.renewalMass w r :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) * B :=
        mul_le_mul_of_nonneg_left hsum
          (div_nonneg (srwKernel_nonneg _ _) (Real.sqrt_nonneg _))
      _ = _ := mul_comm _ _
  calc
    _ ≤ ∑ s ∈ Finset.Icc 1 n, B * (srwKernel (2 * s) z / Real.sqrt ((s : ℝ) + 1)) :=
      Finset.sum_le_sum (fun s _ => hslice s)
    _ = _ := (Finset.mul_sum _ _ _).symm


end Critical2DKPZ.SHF.Moments
