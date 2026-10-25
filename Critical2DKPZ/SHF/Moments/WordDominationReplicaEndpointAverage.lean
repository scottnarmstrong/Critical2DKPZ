/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationEndpointAverage
public import Critical2DKPZ.MomentBounds.CCR25IndependentDurationSum
import Mathlib.Tactic

/-! # Common-duration endpoint averaging for replica profiles -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.Polymer Critical2DKPZ.SHF.Flow

/-- If every replica starts in a scaled ball, the independent walks have
probability at least `2⁻ʰ` of all ending in the concentric ball enlarged by two.
The duration is common to every replica, so this estimate can be used inside
one hatted CCR boundary vector. -/
theorem replicaEndpointInside_ball_ge {h N k : ℕ}
    (hN : 0 < N) (hk : k ≤ N) (x : Fin h → Site) (R : ℝ)
    (hstart : ∀ i, ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (x i)‖ ≤ R) :
    (1 / 2 : ℝ) ^ h ≤
      ∑ z ∈ Fintype.piFinset (fun i => endpoints (x i) k),
        (if ∀ i, ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
          ∏ i, srwKernel k (z i - x i) else 0) := by
  classical
  let D : Fin h → Finset Site := fun i => endpoints (x i) k
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hscale : (Real.sqrt ((N : ℝ) / 2))⁻¹ = Real.sqrt 2 / Real.sqrt N := by
    have hleft : (Real.sqrt ((N : ℝ) / 2))⁻¹ ^ 2 = 2 / N := by
      rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (N : ℝ) / 2)]
      field_simp
    have hright : (Real.sqrt 2 / Real.sqrt N) ^ 2 = 2 / N := by
      rw [div_pow, Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ)),
        Real.sq_sqrt hNreal.le]
    have hleft_nonneg : 0 ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ := by positivity
    have hright_nonneg : 0 ≤ Real.sqrt 2 / Real.sqrt N := by positivity
    nlinarith
  let q : Fin h → Site → ℝ := fun i z =>
    if ‖(Real.sqrt 2 / Real.sqrt N) • siteToPlane z‖ ≤ R + 2 then
      srwKernel k (z - x i) else 0
  have hpoint (z : Fin h → Site) :
      (if ∀ i, ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
        ∏ i, srwKernel k (z i - x i) else 0) = ∏ i, q i (z i) := by
    rw [hscale]
    by_cases hall : ∀ i, ‖(Real.sqrt 2 / Real.sqrt N) • siteToPlane (z i)‖ ≤ R + 2
    · have hprod : ∏ i, q i (z i) = ∏ i, srwKernel k (z i - x i) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [q, hall i]
      have hleft :
          (if ∀ i, ‖(Real.sqrt 2 / Real.sqrt N) • siteToPlane (z i)‖ ≤ R + 2 then
            ∏ i, srwKernel k (z i - x i) else 0) = ∏ i, q i (z i) := by
        simp [hall, hprod]
      exact hleft
    · obtain ⟨i, hi⟩ := not_forall.mp hall
      have hleft :
          (if ∀ i, ‖(Real.sqrt 2 / Real.sqrt N) • siteToPlane (z i)‖ ≤ R + 2 then
            ∏ i, srwKernel k (z i - x i) else 0) = 0 := by
        simp [hall]
      have hzero : ∏ i : Fin h, q i (z i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [q, hi])
      rw [hleft, hzero]
  have hfactor :
      (∑ z ∈ Fintype.piFinset D,
        (if ∀ i, ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z i)‖ ≤ R + 2 then
          ∏ i, srwKernel k (z i - x i) else 0)) =
        (∏ i, ∑ z ∈ D i, q i z) := by
    calc
      _ = ∑ z ∈ Fintype.piFinset D, ∏ i, q i (z i) := by
        apply Finset.sum_congr rfl
        intro z hz
        exact hpoint z
      _ = ∏ i, ∑ z ∈ D i, q i z := by
        exact Critical2DKPZ.MomentBounds.finite_sum_product_over_piFinset_eq_product_sums
          D q
  have hscalar (i : Fin h) : (1 / 2 : ℝ) ≤ ∑ z ∈ D i, q i z := by
    simpa [D, q, hscale] using
      srwKernel_scaledEndpointInside_ball_ge_half hN hk (x i) R (hstart i)
  calc
    (1 / 2 : ℝ) ^ h = ∏ _i : Fin h, (1 / 2 : ℝ) := by simp
    _ ≤ ∏ i : Fin h, ∑ z ∈ D i, q i z := by
      apply Finset.prod_le_prod₀
      · intro i hi
        norm_num
      · intro i hi
        exact hscalar i
    _ = _ := hfactor.symm


end Critical2DKPZ.SHF.Moments

end
