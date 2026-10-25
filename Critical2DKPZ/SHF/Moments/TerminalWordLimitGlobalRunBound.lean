/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitGlobalGaussianWeights
import Critical2DKPZ.Blocks.StringSumPropagation
import Mathlib.Tactic

/-! # A global sampled Gaussian envelope for an interior collision run -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- The normalized collision run is bounded by one Gaussian in the
continuum increment, uniformly over its two sampling phases and common
per-coordinate lattice shifts. -/
theorem eventually_scaled_pairRun_gaussian_interior (ϑ η T : ℝ)
    (hη : 0 < η) (hT : 0 < T) {h : ℕ} (α : CollisionPair h) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ᶠ N : ℕ in atTop,
      (Real.sqrt ((N : ℝ) / 2))⁻¹ ≤ 1 → ∀ r : ℕ,
      η * N ≤ (r : ℝ) → (r : ℝ) ≤ T * N → ∀ k l : ℕ,
      ∀ p q : FusedConfiguration α, ∀ a : LatticeConfiguration h,
      a α.1.1 = a α.1.2 →
      |4 * (N : ℝ) * ((N : ℝ) / 4) ^ (h - 1) *
        collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r
          (wordCollisionPhaseSample N k α p + a)
          (wordCollisionPhaseSample N l α q + a)| ≤
            A * wordEmbeddingGaussian α c (q - p) := by
  classical
  obtain ⟨B, b, hB, hb, hrenew⟩ :=
    eventually_scaled_spatialRenewal_le_gaussian_all_parities ϑ η T hη hT
  obtain ⟨Q, d, hQ, hd, hwalk⟩ := exists_scaled_srwKernel_gaussian_interior hη hT
  let c := min (b / 4) (d / 2)
  let B' := B * Real.exp (b * 2 ^ 2)
  let Q' := Q * Real.exp (d * 2 ^ 2)
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  have hcb : 2 * c ≤ b / 2 := by dsimp [c]; linarith only [min_le_left (b / 4) (d / 2)]
  have hcd : c ≤ d / 2 := min_le_right _ _
  have hcrit : ∀ᶠ N : ℕ in atTop, |criticalSigmaSq ϑ N * Real.log N| ≤ Real.pi + 1 := by
    have hh := (Renewal.tendsto_sigma_mul_log ϑ).abs.eventually
      (Iio_mem_nhds (show |Real.pi| < Real.pi + 1 by rw [abs_of_pos Real.pi_pos]; linarith))
    exact hh.mono fun N hN => hN.le
  refine ⟨4 * (Real.pi + 1) * B' * Q' ^ (h - 2), c, by dsimp [B', Q']; positivity, hc, ?_⟩
  filter_upwards [hrenew, hcrit, criticalBeta_spec ϑ, eventually_gt_atTop 1]
    with N hg hcritN hσ hN
  intro hmesh r hr hrT k l p q a ha
  let u := wordCollisionPhaseSample N k α p + a
  let v := wordCollisionPhaseSample N l α q + a
  have hu : u α.1.1 = u α.1.2 := by
    simp only [u, Pi.add_apply, wordCollisionPhaseSample_apply,
      collisionEmbedding_pair_left, collisionEmbedding_pair_right, ha]
  have hv : v α.1.1 = v α.1.2 := by
    simp only [v, Pi.add_apply, wordCollisionPhaseSample_apply,
      collisionEmbedding_pair_left, collisionEmbedding_pair_right, ha]
  have hdiff (i : Fin h) : v i - u i =
      pairTwoFutureSampleSite N l (collisionEmbedding α q i) -
        pairTwoFutureSampleSite N k (collisionEmbedding α p i) := by
    simp only [u, v, Pi.add_apply, wordCollisionPhaseSample_apply]
    abel
  have hNp : 0 < N := by omega
  have hbcenter :
      ((N : ℝ) / 4) * (N / Real.log N) *
        Collision.spatialRenewal (criticalSigmaSq ϑ N) r (v α.1.1 - u α.1.1) ≤
      B' * Real.exp (-(2 * c) * ‖q.1 - p.1‖ ^ 2) := by
    have hh := hg r hr hrT (v α.1.1 - u α.1.1)
    have he := norm_sub_sample_increment_le hNp k l p.1 q.1 hmesh
    have hs := exp_neg_norm_sq_le_of_norm_sub_le hb.le (by norm_num : (0 : ℝ) ≤ 2)
      (q.1 - p.1) (latticeRepresentative N
        (pairTwoFutureSampleSite N l q.1 - pairTwoFutureSampleSite N k p.1)) he
    rw [hdiff, collisionEmbedding_pair_left, collisionEmbedding_pair_left] at hh
    calc
      _ ≤ B * Real.exp (-b * ‖latticeRepresentative N
          (pairTwoFutureSampleSite N l q.1 - pairTwoFutureSampleSite N k p.1)‖ ^ 2) := by
        simpa only [hdiff, collisionEmbedding_pair_left] using hh
      _ ≤ B' * Real.exp (-(b / 2) * ‖q.1 - p.1‖ ^ 2) := by
        simpa only [B', mul_assoc] using mul_le_mul_of_nonneg_left hs hB.le
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (show 0 ≤ B' by dsimp [B']; positivity)
        apply Real.exp_le_exp.mpr
        simpa only [neg_mul] using
          (neg_le_neg (mul_le_mul_of_nonneg_right hcb (sq_nonneg ‖q.1 - p.1‖)))
  have hspec (i : Spectator α) :
      ((N : ℝ) / 4) * srwKernel r (v i.1 - u i.1) ≤
        Q' * Real.exp (-c * ‖q.2 i - p.2 i‖ ^ 2) := by
    have hh := hwalk (show 1 ≤ N by omega) r hr hrT (v i.1 - u i.1)
    have he := norm_sub_sample_increment_le hNp k l (p.2 i) (q.2 i) hmesh
    have hs := exp_neg_norm_sq_le_of_norm_sub_le hd.le (by norm_num : (0 : ℝ) ≤ 2)
      (q.2 i - p.2 i) (latticeRepresentative N
        (pairTwoFutureSampleSite N l (q.2 i) - pairTwoFutureSampleSite N k (p.2 i))) he
    simp only [hdiff, collisionEmbedding_spectator_apply] at hh
    calc
      _ ≤ Q * Real.exp (-d * ‖latticeRepresentative N
          (pairTwoFutureSampleSite N l (q.2 i) - pairTwoFutureSampleSite N k (p.2 i))‖ ^ 2) := by
        simpa only [hdiff, collisionEmbedding_spectator_apply] using hh
      _ ≤ Q' * Real.exp (-(d / 2) * ‖q.2 i - p.2 i‖ ^ 2) := by
        simpa only [Q', mul_assoc] using mul_le_mul_of_nonneg_left hs hQ.le
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (show 0 ≤ Q' by dsimp [Q']; positivity)
        apply Real.exp_le_exp.mpr
        simpa only [neg_mul] using
          (neg_le_neg (mul_le_mul_of_nonneg_right hcd (sq_nonneg ‖q.2 i - p.2 i‖)))
  have hprod : (∏ i : Spectator α, ((N : ℝ) / 4) * srwKernel r (v i.1 - u i.1)) ≤
      Q' ^ (h - 2) * (∏ i : Spectator α, Real.exp (-c * ‖q.2 i - p.2 i‖ ^ 2)) := by
    calc
      _ ≤ ∏ i : Spectator α, Q' * Real.exp (-c * ‖q.2 i - p.2 i‖ ^ 2) := by
        apply Finset.prod_le_prod₀
        · intro i _; exact mul_nonneg (by positivity) (srwKernel_nonneg _ _)
        · intro i _; exact hspec i
      _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_spectator]
  have hegauss : wordEmbeddingGaussian α c (q - p) =
      Real.exp (-(2 * c) * ‖q.1 - p.1‖ ^ 2) *
        (∏ i : Spectator α, Real.exp (-c * ‖q.2 i - p.2 i‖ ^ 2)) := by
    rw [wordEmbeddingGaussian, prod_collision_labels α]
    simp only [collisionEmbedding_pair_left, collisionEmbedding_pair_right,
      collisionEmbedding_spectator_apply, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
    rw [← Real.exp_add]
    congr 2
    ring
  rw [scaled_collisionWordUndampedPairRunFactor_eq ϑ α r u v hσ
    (Real.log_pos (by exact_mod_cast hN)).ne' hu hv]
  have hσ0 : 0 ≤ criticalSigmaSq ϑ N := hσ ▸ sigmaSq_nonneg (criticalBeta ϑ N)
  have hcenter0 : 0 ≤ ((N : ℝ) / 4) * (N / Real.log N) *
      Collision.spatialRenewal (criticalSigmaSq ϑ N) r (v α.1.1 - u α.1.1) := by
    have hl := Real.log_pos (show (1 : ℝ) < N by exact_mod_cast hN)
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) (Blocks.spatialRenewal_nonneg hσ0 _ _)
  rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
    abs_of_nonneg hcenter0,
    abs_of_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (by positivity) (srwKernel_nonneg _ _))]
  calc
    _ ≤ (4 * (Real.pi + 1)) *
        (B' * Real.exp (-(2 * c) * ‖q.1 - p.1‖ ^ 2)) *
          (Q' ^ (h - 2) * ∏ i : Spectator α, Real.exp (-c * ‖q.2 i - p.2 i‖ ^ 2)) := by
      apply mul_le_mul
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hcritN (by norm_num)) hbcenter hcenter0 (by positivity)
      · exact hprod
      · exact Finset.prod_nonneg fun i _ => mul_nonneg (by positivity) (srwKernel_nonneg _ _)
      · dsimp [B']; positivity
    _ = _ := by rw [hegauss]; ring

end Critical2DKPZ.SHF.Moments
