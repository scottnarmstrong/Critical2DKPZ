/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitGlobalGaussianWeights
import Mathlib.Tactic

/-! # A global Gaussian envelope for the sampled entrance product -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- The normalized entrance has a fixed Gaussian envelope on the full fused
space, uniformly over bounded initial representatives and unit lattice shifts. -/
theorem exists_scaled_wordEntrance_gaussian_interior {h : ℕ}
    (α : CollisionPair h) {η T R : ℝ} (hη : 0 < η) (hT : 0 < T) (hR : 0 ≤ R) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ {N : ℕ}, 1 ≤ N →
      (Real.sqrt ((N : ℝ) / 2))⁻¹ ≤ 1 → ∀ s : ℕ,
      η * N ≤ (s : ℝ) → (s : ℝ) ≤ T * N →
      ∀ x a : LatticeConfiguration h,
      (∀ i, ‖latticeRepresentative N (x i)‖ ≤ R) →
      (∀ i, ‖siteToPlane (a i)‖ ≤ 1) → ∀ k : ℕ, ∀ p : FusedConfiguration α,
      |((N : ℝ) / 4) ^ h * ∏ i, srwKernel s
        ((wordCollisionPhaseSample N k α p + a) i - x i)| ≤
          A * wordEmbeddingGaussian α c p := by
  obtain ⟨Q, c, hQ, hc, hwalk⟩ := exists_scaled_srwKernel_gaussian_interior hη hT
  let A := Q * Real.exp (c * (R + 2) ^ 2)
  refine ⟨A ^ h, c / 2, pow_pos (mul_pos hQ (Real.exp_pos _)) _, by positivity, ?_⟩
  intro N hN hmesh s hs hsT x a hx ha k p
  have hNp : 0 < N := by omega
  have hterm (i : Fin h) :
      ((N : ℝ) / 4) * srwKernel s
        ((wordCollisionPhaseSample N k α p + a) i - x i) ≤
          A * Real.exp (-(c / 2) * ‖collisionEmbedding α p i‖ ^ 2) := by
    have hb := hwalk hN s hs hsT ((wordCollisionPhaseSample N k α p + a) i - x i)
    have he := norm_sub_shifted_sample_displacement_le hNp k (collisionEmbedding α p i)
      (a i) (x i) (ha i) (hx i) hmesh
    have hg := exp_neg_norm_sq_le_of_norm_sub_le hc.le (by positivity : 0 ≤ R + 2)
      (collisionEmbedding α p i)
      (latticeRepresentative N (pairTwoFutureSampleSite N k (collisionEmbedding α p i) + a i - x i)) he
    simp only [Pi.add_apply, wordCollisionPhaseSample_apply] at hb ⊢
    exact hb.trans (by simpa only [A, mul_assoc] using mul_le_mul_of_nonneg_left hg hQ.le)
  have he : ((N : ℝ) / 4) ^ h * (∏ i, srwKernel s
        ((wordCollisionPhaseSample N k α p + a) i - x i)) =
      ∏ i : Fin h, ((N : ℝ) / 4) * srwKernel s
        ((wordCollisionPhaseSample N k α p + a) i - x i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [he, abs_of_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (by positivity) (srwKernel_nonneg _ _))]
  calc
    _ ≤ ∏ i : Fin h, A * Real.exp (-(c / 2) * ‖collisionEmbedding α p i‖ ^ 2) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact mul_nonneg (by positivity) (srwKernel_nonneg _ _)
      · intro i _; exact hterm i
    _ = _ := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rfl

end Critical2DKPZ.SHF.Moments
