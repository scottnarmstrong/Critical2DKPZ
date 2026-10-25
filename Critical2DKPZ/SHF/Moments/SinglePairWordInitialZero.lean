/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordFutureSampling
import Mathlib.Tactic

/-! # Initial support of the tested two-particle future -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory
open scoped CompactlySupported

/-- An initial site outside the compact cell-pair support gives zero weight
for every terminal site. -/
theorem cellTestWeight_zero_of_initial_notSupport
    (N : ℕ) (φ : C_c(Plane × Plane, ℝ)) (a : Site)
    (ha : a ∉ ((SHF.Flow.finite_support_cellPairTest N φ).toFinset.image Prod.fst))
    (b : Site) : cellTestWeight N φ a b = 0 := by
  classical
  have hint : (∫ p in cell N a ×ˢ cell N b, φ p) = 0 := by
    by_contra hne
    exact ha (Finset.mem_image.mpr ⟨(a, b),
      (SHF.Flow.finite_support_cellPairTest N φ).mem_toFinset.mpr hne, rfl⟩)
  rw [cellTestWeight, hint, mul_zero]

/-- The complete future tail retains the finite initial support of each test. -/
theorem pairTwoFutureTestedTail_zero_of_initial_notSupport
    (σ : ℝ) (N L s : ℕ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (x : Fin 2 → Site) (i : Fin 2)
    (hx : x i ∉ ((SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst))
    (z : Site) : pairTwoFutureTestedTail σ N L s φ x z = 0 := by
  classical
  rw [pairTwoFutureTestedTail]
  apply Finset.sum_eq_zero
  intro y _hy
  have hweight := cellTestWeight_zero_of_initial_notSupport N (φ i) (x i) hx (y i)
  rw [Finset.prod_eq_zero (Finset.mem_univ i) hweight, zero_mul]

/-- The phase-correct future extension has the same finite initial support. -/
theorem pairTwoFutureSampleProfile_zero_of_initial_notSupport
    (ϑ : ℝ) (N L : ℕ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (x : Fin 2 → Site) (i : Fin 2)
    (hx : x i ∉ ((SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image Prod.fst))
    (p : ℝ × Plane) : pairTwoFutureSampleProfile ϑ N L φ x p = 0 := by
  rw [pairTwoFutureSampleProfile, pairTwoFutureTestedTail_zero_of_initial_notSupport
    _ _ _ _ φ x i hx, mul_zero]

end Critical2DKPZ.SHF.Moments
