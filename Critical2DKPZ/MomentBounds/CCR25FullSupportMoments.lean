/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25Operators
import Mathlib.Tactic

/-! # Full-support collision moment bookkeeping for CCR25 -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

/-- In a full-support family of nontrivial collision blocks, the total number
of block incidences is at least both twice the number of blocks and the number
of replica labels. -/
theorem ccr25_fullSupport_block_card_sum_bound {h r : ℕ}
    (blocks : Fin r → Finset (Fin h))
    (hnontrivial : ∀ j, 2 ≤ (blocks j).card)
    (hsupport : ∀ i : Fin h, ∃ j, i ∈ blocks j) :
    Nat.max (2 * r) h ≤ ∑ j : Fin r, (blocks j).card := by
  classical
  have hreplicas : h ≤ ∑ j : Fin r, (blocks j).card := by
    calc
      h = (Finset.univ : Finset (Fin h)).card := by simp
      _ ≤ (Finset.univ.biUnion blocks).card := Finset.card_le_card fun i hi => by
        obtain ⟨j, hj⟩ := hsupport i
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hj⟩
      _ ≤ ∑ j : Fin r, (blocks j).card := by
        simpa using
          (Finset.card_biUnion_le (s := Finset.univ) (t := blocks))
  have htwo : 2 * r ≤ ∑ j : Fin r, (blocks j).card := by
    calc
      2 * r = ∑ j : Fin r, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ j : Fin r, (blocks j).card :=
        Finset.sum_le_sum fun j _ => hnontrivial j
  exact Nat.max_le.mpr ⟨htwo, hreplicas⟩


/-- Product form of the CCR25 full-support exponent count. The parameter `s`
is the standard deviation of one disorder coordinate, constrained to be at
most one. The per-block bound is kept explicit for later Gaussian estimates. -/
theorem ccr25_fullSupport_product_bound {h r : ℕ}
    (blocks : Fin r → Finset (Fin h)) (mom : Fin r → ℝ)
    (C s : ℝ) (hC : 0 ≤ C) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hnontrivial : ∀ j, 2 ≤ (blocks j).card)
    (hsupport : ∀ i : Fin h, ∃ j, i ∈ blocks j)
    (hmom : ∀ j, |mom j| ≤ C * s ^ (blocks j).card) :
    |∏ j : Fin r, mom j| ≤ C ^ r * s ^ Nat.max (2 * r) h := by
  classical
  have hsum := ccr25_fullSupport_block_card_sum_bound blocks hnontrivial hsupport
  have hprod :
      (∏ j : Fin r, |mom j|) ≤ ∏ j : Fin r, C * s ^ (blocks j).card :=
    Finset.prod_le_prod₀
      (fun j _ => abs_nonneg (mom j))
      (fun j _ => hmom j)
  have hprod_eq :
      (∏ j : Fin r, C * s ^ (blocks j).card) =
        C ^ r * s ^ (∑ j : Fin r, (blocks j).card) := by
    simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc
    |∏ j : Fin r, mom j| = ∏ j : Fin r, |mom j| := by rw [Finset.abs_prod]
    _ ≤ ∏ j : Fin r, C * s ^ (blocks j).card := hprod
    _ = C ^ r * s ^ (∑ j : Fin r, (blocks j).card) := hprod_eq
    _ ≤ C ^ r * s ^ Nat.max (2 * r) h :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hs0 hs1 hsum) (pow_nonneg hC r)


end

end Critical2DKPZ.MomentBounds
