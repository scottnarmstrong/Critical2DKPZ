/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitGlobalEntranceBound
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitGlobalRunBound
import Mathlib.Tactic

/-! # A decoupled Gaussian envelope for the first entrance and collision run -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- The normalized first entrance and run have a single product Gaussian
envelope on all space, uniformly over both phases and bounded lattice shifts. -/
theorem eventually_scaled_wordFirstBlock_gaussian_interior
    (ϑ η T R : ℝ) (hη : 0 < η) (hT : 0 < T) (hR : 0 ≤ R)
    {h : ℕ} (α : CollisionPair h) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (Real.sqrt ((N : ℝ) / 2))⁻¹ ≤ 1 → ∀ s r : ℕ,
      η * N ≤ (s : ℝ) → (s : ℝ) ≤ T * N →
      η * N ≤ (r : ℝ) → (r : ℝ) ≤ T * N →
      ∀ x a : LatticeConfiguration h,
      (∀ i, ‖latticeRepresentative N (x i)‖ ≤ R) →
      (∀ i, ‖siteToPlane (a i)‖ ≤ 1) → ∀ k l : ℕ,
      ∀ p q : FusedConfiguration α,
      |(((N : ℝ) / 4) ^ h * ∏ i, srwKernel s
          ((wordCollisionPhaseSample N k α p + a) i - x i)) *
        (4 * (N : ℝ) * ((N : ℝ) / 4) ^ (h - 1) *
          collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r
            (wordCollisionPhaseSample N k α p + a)
            (wordCollisionPhaseSample N l α q + a))| ≤
        A * wordEmbeddingGaussian α c p * wordEmbeddingGaussian α c q := by
  classical
  obtain ⟨AE, cE, hAE, hcE, he⟩ := exists_scaled_wordEntrance_gaussian_interior α hη hT hR
  obtain ⟨AR, cR, hAR, hcR, hr⟩ := eventually_scaled_pairRun_gaussian_interior ϑ η T hη hT α
  let c := min cE cR
  have hc : 0 < c := lt_min hcE hcR
  refine ⟨AE * AR, c / 3, mul_pos hAE hAR, by positivity, ?_⟩
  filter_upwards [hr, eventually_ge_atTop 1] with N hrun hN
  intro hmesh s r hs hsT hrl hrT x a hx ha k l p q
  by_cases hpair : a α.1.1 = a α.1.2
  · have hentry := he hN hmesh s hs hsT x a hx ha k p
    have hrun' := hrun hmesh r hrl hrT k l p q a hpair
    have hE := wordEmbeddingGaussian_antitone α (min_le_left cE cR) p
    have hR' := wordEmbeddingGaussian_antitone α (min_le_right cE cR) (q - p)
    have hleft : |((N : ℝ) / 4) ^ h * ∏ i, srwKernel s
        ((wordCollisionPhaseSample N k α p + a) i - x i)| ≤ AE * wordEmbeddingGaussian α c p :=
      hentry.trans (mul_le_mul_of_nonneg_left hE hAE.le)
    have hright : |4 * (N : ℝ) * ((N : ℝ) / 4) ^ (h - 1) *
        collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r
          (wordCollisionPhaseSample N k α p + a) (wordCollisionPhaseSample N l α q + a)| ≤
        AR * wordEmbeddingGaussian α c (q - p) :=
      hrun'.trans (mul_le_mul_of_nonneg_left hR' hAR.le)
    rw [abs_mul]
    calc
      _ ≤ (AE * wordEmbeddingGaussian α c p) * (AR * wordEmbeddingGaussian α c (q - p)) :=
        mul_le_mul hleft hright (abs_nonneg _) (mul_nonneg hAE.le (wordEmbeddingGaussian_pos _ _ _).le)
      _ = (AE * AR) * (wordEmbeddingGaussian α c p * wordEmbeddingGaussian α c (q - p)) := by ring
      _ ≤ (AE * AR) * (wordEmbeddingGaussian α (c / 3) p * wordEmbeddingGaussian α (c / 3) q) :=
        mul_le_mul_of_nonneg_left (wordEmbeddingGaussian_mul_sub_le α hc.le p q) (mul_pos hAE hAR).le
      _ = _ := by ring
  · have hu : (wordCollisionPhaseSample N k α p + a) α.1.1 ≠
        (wordCollisionPhaseSample N k α p + a) α.1.2 := by
      simp only [Pi.add_apply, wordCollisionPhaseSample_apply,
        collisionEmbedding_pair_left, collisionEmbedding_pair_right]
      exact fun hh => hpair (add_left_cancel hh)
    have hz : collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r
        (wordCollisionPhaseSample N k α p + a) (wordCollisionPhaseSample N l α q + a) = 0 := by
      simp only [collisionWordUndampedPairRunFactor, hu, false_and, ite_false, zero_mul]
    rw [hz, mul_zero, mul_zero, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_pos hAE hAR).le (wordEmbeddingGaussian_pos _ _ _).le)
      (wordEmbeddingGaussian_pos _ _ _).le

end Critical2DKPZ.SHF.Moments
