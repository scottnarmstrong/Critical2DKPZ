/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.SmoothedCovariance
import Critical2DKPZ.Lattice.Basic
import Mathlib.Tactic

/-! # A free-walk gap potential for the common word domination argument -/

@[expose] public noncomputable section

open scoped BigOperators
open Critical2DKPZ.Polymer

namespace Critical2DKPZ.SHF.Moments

/-- A finite time-summed free-walk potential with an integrable time weight. -/
def wordGapPotential (n : ℕ) (z : Site) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, srwKernel (2 * k) z / Real.sqrt ((k : ℝ) + 1)

theorem wordGapPotential_nonneg (n : ℕ) (z : Site) : 0 ≤ wordGapPotential n z :=
  Finset.sum_nonneg (fun k _ => div_nonneg (srwKernel_nonneg (2 * k) z) (Real.sqrt_nonneg _))

/-- Gap orientation is irrelevant for the potential. -/
theorem wordGapPotential_neg (n : ℕ) (z : Site) :
    wordGapPotential n (-z) = wordGapPotential n z := by
  simp only [wordGapPotential, srwKernel_neg]

/-- Enlarging the remaining horizon only increases the nonnegative potential. -/
theorem wordGapPotential_mono_time (z : Site) {m n : ℕ} (hmn : m ≤ n) :
    wordGapPotential m z ≤ wordGapPotential n z := by
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right hmn)
  intro k hk hnot
  exact div_nonneg (srwKernel_nonneg _ _) (Real.sqrt_nonneg _)


/-- A free spectator acts on the potential by adding its elapsed time to
each walk slice. This identity is independent of the collision center. -/
theorem sum_srwKernel_wordGapPotential (m n : ℕ) (a b : Site) :
    (∑ z ∈ endpoints a m, srwKernel m (z - a) * wordGapPotential n (z - b)) =
      ∑ k ∈ Finset.Icc 1 n,
        srwKernel (m + 2 * k) (b - a) / Real.sqrt ((k : ℝ) + 1) := by
  simp_rw [wordGapPotential, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  congr 1
  have hsymm (z : Site) : srwKernel (2 * k) (z - b) = srwKernel (2 * k) (b - z) := by
    simpa only [neg_sub] using srwKernel_neg (2 * k) (b - z)
  simp_rw [hsymm]
  exact kernel_convolution_finset m (2 * k) a b

/-- The same free-spectator identity with the unrestricted spatial sum. -/
theorem tsum_srwKernel_wordGapPotential (m n : ℕ) (a b : Site) :
    (∑' z : Site, srwKernel m (z - a) * wordGapPotential n (z - b)) =
      ∑ k ∈ Finset.Icc 1 n,
        srwKernel (m + 2 * k) (b - a) / Real.sqrt ((k : ℝ) + 1) := by
  rw [tsum_eq_sum (s := endpoints a m)]
  · exact sum_srwKernel_wordGapPotential m n a b
  · intro z hz
    rw [srwKernel_eq_zero_of_not_mem m a z hz, zero_mul]

end Critical2DKPZ.SHF.Moments
