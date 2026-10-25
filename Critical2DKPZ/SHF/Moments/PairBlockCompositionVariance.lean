/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Collision.SpatialRenewalComposition
public import Mathlib.Analysis.SpecificLimits.Basic
public import Critical2DKPZ.WalkTails.LogConcavity
import Mathlib.Tactic

/-! # Conditional variance of a pair-block composition -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open Filter
open scoped Topology




/-- A squared-binomial increment is the squared one-dimensional walk mass normalized by its doubled-time return probability. -/
theorem hypergeometricIntWeight_eq_srwHeat_sq_div_return
    (m j : ℕ) (hj : j ≤ m) :
    WalkTails.hypergeometricIntWeight m (j : ℤ) =
      (LatticeProb.srwHeat 1 m
        ![(j : ℤ) - ((m - j : ℕ) : ℤ)]) ^ 2 /
        LatticeProb.srwHeat 1 (2 * m) ![(0 : ℤ)] := by
  have hnum := LatticeProb.srwHeat_one_binom m j (m - j) (by omega)
  have hden := LatticeProb.srwHeat_one_binom (2 * m) m m (by omega)
  have hdenSite : (m : ℤ) - (m : ℤ) = 0 := by ring
  rw [hdenSite] at hden
  rw [WalkTails.hypergeometricIntWeight_eq_nat, hnum, hden]
  unfold WalkTails.hypergeometricWeight
  have hpow : (2 : ℝ) ^ (2 * m) = ((2 : ℝ) ^ m) ^ 2 := by
    rw [show 2 * m = m * 2 by omega, pow_mul]
  have hchoose : (Nat.choose (2 * m) m : ℝ) ≠ 0 :=
    ne_of_gt (WalkTails.hypergeometric_denominator_pos m)
  field_simp [hchoose, hpow]
  ring



/-- The total duration of blocks below a cutoff is at most the cutoff times
their number. -/
theorem list_sum_filter_lt_le_length_mul (ks : List ℕ) (mCut : ℕ) :
    (ks.filter (fun k => k < mCut)).sum ≤
      (ks.filter (fun k => k < mCut)).length * mCut := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
      by_cases hk : k < mCut
      · have hcalc : k + (ks.filter (fun k => k < mCut)).sum ≤
            ((ks.filter (fun k => k < mCut)).length + 1) * mCut := by
          calc
            k + (ks.filter (fun k => k < mCut)).sum ≤
                mCut + (ks.filter (fun k => k < mCut)).length * mCut :=
              Nat.add_le_add hk.le ih
            _ = ((ks.filter (fun k => k < mCut)).length + 1) * mCut := by
              rw [Nat.add_mul, one_mul]
              exact Nat.add_comm _ _
        simpa [hk] using hcalc
      · simpa [List.filter_cons, hk] using
          ih











end Critical2DKPZ.SHF.Moments

end
