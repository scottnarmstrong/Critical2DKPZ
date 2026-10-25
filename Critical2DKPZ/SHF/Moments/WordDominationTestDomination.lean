/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionRunExpansion
import Critical2DKPZ.SHF.Flow.SlabProductsCore
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Domination of signed word coefficients by absolute tests -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

attribute [local instance] Classical.propDecidable

/-- The pointwise absolute value of a compactly supported continuous function. -/
public def compactAbs {α : Type*} [TopologicalSpace α]
    (φ : C_c(α, ℝ)) : C_c(α, ℝ) :=
  ⟨⟨fun x => |φ x|, φ.continuous.abs⟩, φ.hasCompactSupport.abs⟩

/-- The absolute value of a cell average is bounded by the cell average of the absolute test. -/
theorem abs_cellTestWeight_le_abs_test (N : ℕ) (φ : C_c(Plane × Plane, ℝ))
    (w z : Site) :
    |cellTestWeight N φ w z| ≤ cellTestWeight N (compactAbs φ) w z := by
  have hint :
      |∫ p in cell N w ×ˢ cell N z, φ p| ≤
        ∫ p in cell N w ×ˢ cell N z, |φ p| := abs_integral_le_integral_abs
  have hscale : 0 ≤ (N / 4 : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hint hscale
  calc
    |cellTestWeight N φ w z| =
        (N / 4 : ℝ) * |∫ p in cell N w ×ˢ cell N z, φ p| := by
      simp [cellTestWeight, abs_mul, abs_of_nonneg hscale]
    _ ≤ (N / 4 : ℝ) * ∫ p in cell N w ×ˢ cell N z, |φ p| := hscaled
    _ = cellTestWeight N (compactAbs φ) w z := by
      rw [cellTestWeight]
      congr 1

private def sitePairConfigEquiv (h : ℕ) :
    (Fin h → Site × Site) ≃ ((Fin h → Site) × (Fin h → Site)) where
  toFun q := (fun i => (q i).1, fun i => (q i).2)
  invFun xy := fun i => (xy.1 i, xy.2 i)
  left_inv q := by
    funext i
    exact Prod.eta (q i)
  right_inv xy := by
    rcases xy with ⟨x, y⟩
    rfl

private theorem tsum_cellConfig_reindex_on {h : ℕ} (N : ℕ)
    (φ : Fin h → C_c(Plane × Plane, ℝ)) (S : Fin h → Finset (Site × Site))
    (hzero : ∀ i q, q ∉ S i → cellTestWeight N (φ i) q.1 q.2 = 0)
    (G : (Fin h → Site) → (Fin h → Site) → ℝ) :
    (∑' x : Fin h → Site, ∑' y : Fin h → Site,
        (∏ i, cellTestWeight N (φ i) (x i) (y i)) * G x y) =
      ∑ q ∈ Fintype.piFinset S,
        (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
          G (fun i => (q i).1) (fun i => (q i).2) := by
  classical
  let Q : Finset (Fin h → Site × Site) := Fintype.piFinset S
  let e := sitePairConfigEquiv h
  let R : Finset ((Fin h → Site) × (Fin h → Site)) := Q.image e
  let f : ((Fin h → Site) × (Fin h → Site)) → ℝ :=
    fun xy => (∏ i, cellTestWeight N (φ i) (xy.1 i) (xy.2 i)) * G xy.1 xy.2
  have hfzero (xy : (Fin h → Site) × (Fin h → Site)) (hxy : xy ∉ R) : f xy = 0 := by
    by_contra hne
    have hweight : ∀ i, cellTestWeight N (φ i) (xy.1 i) (xy.2 i) ≠ 0 := by
      intro i hi
      apply hne
      dsimp [f]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi]
      simp
    let q : Fin h → Site × Site := fun i => (xy.1 i, xy.2 i)
    have hq : q ∈ Q := by
      apply Fintype.mem_piFinset.mpr
      intro i
      by_contra hi
      exact hweight i (hzero i (q i) hi)
    apply hxy
    refine Finset.mem_image.mpr ⟨q, hq, ?_⟩
    rcases xy with ⟨x, y⟩
    simp [e, sitePairConfigEquiv, q]
  have hsum : Summable f := by
    apply summable_of_hasFiniteSupport
    apply R.finite_toSet.subset
    intro xy hxy
    by_contra hxyR
    exact hxy (hfzero xy hxyR)
  calc
    _ = ∑' xy : (Fin h → Site) × (Fin h → Site), f xy := hsum.tsum_prod.symm
    _ = ∑ xy ∈ R, f xy := by
      rw [tsum_eq_sum (s := R)]
      intro xy hxy
      exact hfzero xy hxy
    _ = ∑ q ∈ Q, f (e q) := by
      dsimp [R]
      rw [Finset.sum_image e.injective.injOn]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [f, e, sitePairConfigEquiv]

private theorem testedBlockWord_eq_cellConfigSum_on {h : ℕ} (ϑ : ℝ) (N : ℕ)
    (s t : ℝ) (φ : Fin h → C_c(Plane × Plane, ℝ))
    (S : Fin h → Finset (Site × Site))
    (hzero : ∀ i q, q ∉ S i → cellTestWeight N (φ i) q.1 q.2 = 0)
    (w : List (CollisionPair h)) :
    testedBlockWord ϑ N s t φ w =
      ∑ q ∈ Fintype.piFinset S,
        (∏ i, cellTestWeight N (φ i) (q i).1 (q i).2) *
          blockWordKernel (sigmaSq (criticalBeta ϑ N)) w
            (evenCeil (N * t) - evenCeil (N * s))
            (fun i => (q i).1) (fun i => (q i).2) := by
  unfold testedBlockWord
  exact tsum_cellConfig_reindex_on N φ S hzero _

/-- For every collision word, taking absolute values of each compact test can
only increase the absolute tested coefficient. -/
theorem abs_testedBlockWord_le_abs_testedBlockWord (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    {h : ℕ} (φ : Fin h → C_c(Plane × Plane, ℝ)) (w : List (CollisionPair h)) :
    |testedBlockWord ϑ N s t φ w| ≤
      testedBlockWord ϑ N s t (fun i => compactAbs (φ i)) w := by
  classical
  let ψ : Fin h → C_c(Plane × Plane, ℝ) := fun i => compactAbs (φ i)
  let S : Fin h → Finset (Site × Site) := fun i =>
    (Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (ψ i)).toFinset
  have hcellzero (i : Fin h) (q : Site × Site) (hq : q ∉ S i) :
      cellTestWeight N (φ i) q.1 q.2 = 0 := by
    have hψzero : cellTestWeight N (ψ i) q.1 q.2 = 0 := by
      dsimp [S] at hq
      by_contra hne
      have hcell : (∫ p in cell N q.1 ×ˢ cell N q.2, ψ i p) ≠ 0 := by
        intro hz
        apply hne
        simp [cellTestWeight, hz]
      exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (ψ i)).mem_toFinset.mpr hcell)
    have habs := abs_cellTestWeight_le_abs_test N (φ i) q.1 q.2
    have hle : |cellTestWeight N (φ i) q.1 q.2| ≤ 0 := by
      simpa [ψ, hψzero] using habs
    have heq : |cellTestWeight N (φ i) q.1 q.2| = 0 :=
      le_antisymm hle (abs_nonneg _)
    exact abs_eq_zero.mp heq
  have hφsum := testedBlockWord_eq_cellConfigSum_on ϑ N s t φ S hcellzero w
  have hψzero (i : Fin h) (q : Site × Site) (hq : q ∉ S i) :
      cellTestWeight N (ψ i) q.1 q.2 = 0 := by
    dsimp [S] at hq
    by_contra hne
    have hcell : (∫ p in cell N q.1 ×ˢ cell N q.2, ψ i p) ≠ 0 := by
      intro hz
      apply hne
      simp [cellTestWeight, hz]
    exact hq ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (ψ i)).mem_toFinset.mpr hcell)
  have hψsum := testedBlockWord_eq_cellConfigSum_on ϑ N s t ψ S hψzero w
  rw [hφsum, hψsum]
  apply le_trans (Finset.abs_sum_le_sum_abs _ _)
  apply Finset.sum_le_sum
  intro q hq
  have hprod :
      |∏ i, cellTestWeight N (φ i) (q i).1 (q i).2| ≤
        ∏ i, cellTestWeight N (ψ i) (q i).1 (q i).2 := by
    rw [Finset.abs_prod]
    apply Finset.prod_le_prod₀
    · intro i hi
      exact abs_nonneg _
    · intro i hi
      exact abs_cellTestWeight_le_abs_test N (φ i) (q i).1 (q i).2
  have hkernel : 0 ≤ blockWordKernel (sigmaSq (criticalBeta ϑ N)) w
      (evenCeil (N * t) - evenCeil (N * s))
      (fun i => (q i).1) (fun i => (q i).2) := by
    have hσ : 0 ≤ sigmaSq (criticalBeta ϑ N) := by
      unfold sigmaSq
      exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
    exact blockWordKernel_nonneg _ hσ w _ _ _
  have hterm := mul_le_mul_of_nonneg_right hprod hkernel
  simpa only [abs_mul, abs_of_nonneg hkernel] using hterm

end Critical2DKPZ.SHF.Moments

end
