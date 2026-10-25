/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Tactic

/-! # Factoring a norm-controlled linear map through a Hilbert space -/

public section
noncomputable section
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A linear map controlled by a Hilbert-space realization factors through a contraction.
The domain needs only its algebraic structure. -/
theorem exists_hilbert_contraction {V H G : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    (A : V →ₗ[ℝ] G) (B : V →ₗ[ℝ] H) (h : ∀ v, ‖A v‖ ≤ ‖B v‖) :
    ∃ T : H →L[ℝ] G, ‖T‖ ≤ 1 ∧ ∀ v, T (B v) = A v := by
  let K : Submodule ℝ H := B.range.topologicalClosure
  let : CompleteSpace K := B.range.isClosed_topologicalClosure.isComplete.completeSpace_coe
  let b : V →ₗ[ℝ] K := B.codRestrict K (fun v => B.range.le_topologicalClosure ⟨v, rfl⟩)
  have hd : DenseRange b := by
    let i : B.range → K := Set.inclusion B.range.le_topologicalClosure
    have hi : DenseRange i := (denseRange_inclusion_iff B.range.le_topologicalClosure).mpr Set.Subset.rfl
    have hr : Function.Surjective (B.rangeRestrict : V → B.range) := by
      rintro ⟨x, v, hv⟩
      exact ⟨v, Subtype.ext hv⟩
    exact hi.comp hr.denseRange (continuous_inclusion B.range.le_topologicalClosure)
  let U : K →L[ℝ] G := A.extendOfNorm b
  have hb (v : V) : ‖A v‖ ≤ 1 * ‖b v‖ := by
    change ‖A v‖ ≤ 1 * ‖B v‖
    simpa only [one_mul] using h v
  have hU (v : V) : U (b v) = A v := LinearMap.extendOfNorm_eq hd ⟨1, hb⟩ v
  have hUn : ‖U‖ ≤ 1 := LinearMap.opNorm_extendOfNorm_le hd zero_le_one hb
  let T : H →L[ℝ] G := U.comp K.orthogonalProjectionOnto
  refine ⟨T, ?_, ?_⟩
  · calc
      ‖T‖ ≤ ‖U‖ * ‖K.orthogonalProjectionOnto‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖U‖ * 1 := mul_le_mul_of_nonneg_left K.orthogonalProjectionOnto_norm_le (norm_nonneg U)
      _ = ‖U‖ := mul_one _
      _ ≤ 1 := hUn
  · intro v
    change U (K.orthogonalProjectionOnto (B v)) = A v
    have hp : K.orthogonalProjectionOnto (B v) = b v :=
      K.orthogonalProjectionOnto_mem_subspace_eq_self (b v)
    rw [hp]
    exact hU v

end Critical2DKPZ.Extensions.ScaleLimit
