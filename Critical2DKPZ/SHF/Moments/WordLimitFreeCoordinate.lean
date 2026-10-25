/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordLimitGapPotential
public import Critical2DKPZ.MomentBounds.CCR25IndependentDurationSum

/-! # Testing one coordinate of independent free spectator strands -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Testing one free coordinate integrates all other independent coordinates
to one. The profile may depend on a separately fixed collision center. -/
theorem sum_freeReplicaKernel_oneCoordinate_test {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ℕ) (x : ι → Site) (j : ι) (F : Site → ℝ) :
    (∑ y ∈ Fintype.piFinset (fun i => endpoints (x i) m),
      (∏ i, srwKernel m (y i - x i)) * F (y j)) =
      ∑ z ∈ endpoints (x j) m, srwKernel m (z - x j) * F z := by
  classical
  have hpoint (y : ι → Site) :
      (∏ i, srwKernel m (y i - x i)) * F (y j) =
        ∏ i, srwKernel m (y i - x i) * (if i = j then F (y i) else 1) := by
    rw [Finset.prod_mul_distrib]
    simp
  calc
    _ = ∑ y ∈ Fintype.piFinset (fun i => endpoints (x i) m),
        ∏ i, srwKernel m (y i - x i) * (if i = j then F (y i) else 1) :=
      Finset.sum_congr rfl (fun y _ => hpoint y)
    _ = ∏ i, ∑ z ∈ endpoints (x i) m,
        srwKernel m (z - x i) * (if i = j then F z else 1) :=
      finite_sum_product_over_piFinset_eq_product_sums
        (fun i => endpoints (x i) m)
        (fun i z => srwKernel m (z - x i) * (if i = j then F z else 1))
    _ = _ := by
      rw [Finset.prod_eq_single j]
      · simp
      · intro i hi hij
        simp only [ite_eq_right hij, mul_one, sum_srwKernel_endpoints]
      · intro hj
        exact False.elim (hj (Finset.mem_univ j))

/-- A gap-potential test of any free spectator has the same single-walk
convolution, independent of all the other spectator starting coordinates. -/
theorem sum_freeReplicaKernel_oneGapPotential {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m n : ℕ) (x : ι → Site) (j : ι) (b : Site) :
    (∑ y ∈ Fintype.piFinset (fun i => endpoints (x i) m),
      (∏ i, srwKernel m (y i - x i)) * wordGapPotential n (y j - b)) =
      ∑ k ∈ Finset.Icc 1 n,
        srwKernel (m + 2 * k) (b - x j) / Real.sqrt ((k : ℝ) + 1) := by
  rw [sum_freeReplicaKernel_oneCoordinate_test m x j (fun z => wordGapPotential n (z - b))]
  exact sum_srwKernel_wordGapPotential m n (x j) b

end Critical2DKPZ.SHF.Moments
