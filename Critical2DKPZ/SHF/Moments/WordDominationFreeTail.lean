/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionRunExpansionSupport
public import Critical2DKPZ.MomentBounds.CCR25IndependentDurationSum
import Mathlib.Tactic

/-! # Free tails for collision-word kernels -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.Polymer

/-- The free replica kernel has the exact semigroup property in the terminal
configuration. This is the empty-word case of appending free time. -/
theorem freeReplicaConfigurationKernel_convolution {h n k : ℕ}
    (x z : Fin h → Site) :
    (∑' y : Fin h → Site,
      (∏ i, srwKernel n (y i - x i)) *
        ∏ i, srwKernel k (z i - y i)) =
      ∏ i, srwKernel (n + k) (z i - x i) := by
  classical
  let D : Fin h → Finset Site := fun i => endpoints (x i) n
  have hzero (y : Fin h → Site) (hy : y ∉ Fintype.piFinset D) :
      (∏ i, srwKernel n (y i - x i)) *
        ∏ i, srwKernel k (z i - y i) = 0 := by
    have hmiss : ∃ i, y i ∉ D i := by
      by_contra hn
      apply hy
      exact Fintype.mem_piFinset.mpr (by
        intro i
        by_contra hi
        exact hn ⟨i, hi⟩)
    obtain ⟨i, hi⟩ := hmiss
    have hkernel : srwKernel n (y i - x i) = 0 :=
      srwKernel_eq_zero_of_not_mem n (x i) (y i) hi
    have hprod : (∏ j : Fin h, srwKernel n (y j - x j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hkernel
    simp [hprod]
  have htsum :
      (∑' y : Fin h → Site,
        (∏ i, srwKernel n (y i - x i)) *
          ∏ i, srwKernel k (z i - y i)) =
        ∑ y ∈ Fintype.piFinset D,
          (∏ i, srwKernel n (y i - x i)) *
            ∏ i, srwKernel k (z i - y i) := by
    rw [tsum_eq_sum (s := Fintype.piFinset D)]
    intro y hy
    exact hzero y hy
  rw [htsum]
  calc
    _ = ∑ y ∈ Fintype.piFinset D,
          ∏ i, (srwKernel n (y i - x i) * srwKernel k (z i - y i)) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Finset.prod_mul_distrib]
    _ = ∏ i, ∑ y ∈ D i,
          srwKernel n (y - x i) * srwKernel k (z i - y) := by
      exact Critical2DKPZ.MomentBounds.finite_sum_product_over_piFinset_eq_product_sums
        D (fun i y => srwKernel n (y - x i) * srwKernel k (z i - y))
    _ = ∏ i, srwKernel (n + k) (z i - x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      calc
        _ = ∑' y : Site,
            srwKernel n (y - x i) * srwKernel k (z i - y) := by
          symm
          apply tsum_eq_sum
          intro y hy
          rw [srwKernel_eq_zero_of_not_mem n (x i) y hy]
          simp
        _ = srwKernel (n + k) (z i - x i) := by
          symm
          exact srwKernel_convolution n k (x i) (z i)

/-- Appending a free terminal segment to the empty collision word is exactly
the free replica kernel at the longer time. -/
theorem blockWordKernel_nil_append_free {h n k : ℕ} (σ : ℝ)
    (x z : Fin h → Site) :
    (∑' y : Fin h → Site,
      blockWordKernel σ [] n x y *
        ∏ i, srwKernel k (z i - y i)) =
      blockWordKernel σ [] (n + k) x z := by
  simpa [blockWordKernel] using
    (freeReplicaConfigurationKernel_convolution (n := n) (k := k) x z)

end Critical2DKPZ.SHF.Moments

end
