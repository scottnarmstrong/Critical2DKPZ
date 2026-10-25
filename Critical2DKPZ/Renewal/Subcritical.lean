/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.Sequence

/-! # Subcritical renewal estimates

The renewal equation gives the geometric comparison in Claim B.1 of the KPZ paper
for finite sums of nonnegative step weights. -/

@[expose] public noncomputable section

namespace Critical2DKPZ.Renewal

/-- The renewal function is bounded by the corresponding geometric resolvent below criticality. -/
theorem renewalFunction_le_geometric {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (n : ℕ)
    (hsub : (∑ r ∈ Finset.Icc 1 n, w r) < 1) :
    renewalFunction w n ≤ 1 / (1 - ∑ r ∈ Finset.Icc 1 n, w r) := by
  have hbound : renewalFunction w n ≤
      1 + (∑ r ∈ Finset.Icc 1 n, w r) * renewalFunction w n := by
    conv_lhs => rw [renewalFunction_eq]
    apply add_le_add le_rfl
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left
      (renewalFunction_mono_time hw (Nat.sub_le n r)) (hw r)
  apply (le_div_iff₀ (sub_pos.mpr hsub)).mpr
  linarith only [hbound]

/-- The geometric resolvent bounds the renewal function from above below criticality. -/
theorem geometric_sub_renewalFunction_nonneg {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (n : ℕ)
    (hsub : (∑ r ∈ Finset.Icc 1 n, w r) < 1) :
    0 ≤ 1 / (1 - ∑ r ∈ Finset.Icc 1 n, w r) - renewalFunction w n :=
  sub_nonneg.mpr (renewalFunction_le_geometric hw n hsub)


end Critical2DKPZ.Renewal

end
