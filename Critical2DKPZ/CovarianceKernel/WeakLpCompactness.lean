/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.WeakCompactness
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Weak subsequences in separable `L²` spaces -/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace Critical2DKPZ.CovarianceKernel

/-- A norm-bounded sequence in a separable real `L²` space has a weakly convergent subsequence.
The conclusion is expressed through its Hilbert inner products. -/
theorem exists_strictMono_subseq_L2_inner_tendsto_of_norm_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : ℕ → α → ℝ) (hmem : ∀ n, MemLp (f n) 2 μ)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ n, ‖(hmem n).toLp (f n)‖ ≤ B)
    [TopologicalSpace.SeparableSpace (Lp ℝ 2 μ)] :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ v : Lp ℝ 2 μ, ∀ g : Lp ℝ 2 μ,
      Tendsto (fun n => inner ℝ ((hmem (s n)).toLp (f (s n))) g) atTop
        (𝓝 (inner ℝ v g)) := by
  exact exists_strictMono_subseq_inner_tendsto_of_norm_le
    (fun n => (hmem n).toLp (f n)) hB hbound

end Critical2DKPZ.CovarianceKernel

end
