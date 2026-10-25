/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSampleTail
public import Critical2DKPZ.Collision.SpatialRenewalHatGaussian
import Mathlib.Tactic

/-! # Sampled inverse-gap bounds uniform in bounded lattice shifts -/

@[expose] public noncomputable section
open Filter MeasureTheory
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- Unit lattice shifts change the regularized sampled-gap estimate only by
an absolute constant, uniformly in the phase clock and in the sampled points. -/
theorem scaled_norm_sub_le_shifted_sampleGap {N : ℕ} (hN : 0 < N)
    (k : ℕ) (x y : Plane) (a b : Site)
    (ha : ‖siteToPlane a‖ ≤ 1) (hb : ‖siteToPlane b‖ ≤ 1) :
    Real.sqrt (N : ℝ) * ‖y - x‖ ≤
      12 * (1 + ‖siteToPlane ((pairTwoFutureSampleSite N k y + b) -
        (pairTwoFutureSampleSite N k x + a))‖) := by
  let z := pairTwoFutureSampleSite N k y - pairTwoFutureSampleSite N k x
  let z' := (pairTwoFutureSampleSite N k y + b) - (pairTwoFutureSampleSite N k x + a)
  have he : z = z' + (a - b) := by dsimp [z, z']; abel
  have hnorm : ‖siteToPlane z‖ ≤ ‖siteToPlane z'‖ + 2 := by
    have hsub : siteToPlane z = siteToPlane z' + (siteToPlane a - siteToPlane b) := by
      ext i
      simp only [siteToPlane, WithLp.ofLp_add, WithLp.ofLp_sub, WithLp.ofLp_toLp]
      have hi := congrFun he i
      simpa only [Pi.add_apply, Pi.sub_apply, Int.cast_add, Int.cast_sub] using
        congrArg (fun t : ℤ => (t : ℝ)) hi
    rw [hsub]
    have hab : ‖siteToPlane a - siteToPlane b‖ ≤ 2 :=
      (norm_sub_le _ _).trans (by linarith only [ha, hb])
    exact (norm_add_le _ _).trans (add_le_add le_rfl hab)
  calc
    _ ≤ 4 * (1 + ‖siteToPlane z‖) := scaled_norm_sub_le_sampleGap hN k x y
    _ ≤ 12 * (1 + ‖siteToPlane z'‖) := by
      nlinarith only [hnorm, norm_nonneg (siteToPlane z')]

/-- The regularized discrete potential has a fixed inverse-distance
majorant even after two independent unit lattice shifts. -/
theorem exists_scaled_shifted_sampled_wordGapPotential_le_inverse_dist :
    ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ}, 0 < N → ∀ (n k : ℕ) (x y : Plane), x ≠ y →
      ∀ a b : Site, ‖siteToPlane a‖ ≤ 1 → ‖siteToPlane b‖ ≤ 1 →
      Real.sqrt (N : ℝ) * wordGapPotential n
        ((pairTwoFutureSampleSite N k y + b) - (pairTwoFutureSampleSite N k x + a)) ≤
          C / ‖y - x‖ := by
  obtain ⟨B, hB, hbound⟩ := exists_wordGapPotential_regularized_norm_bound
  refine ⟨12 * B, by positivity, ?_⟩
  intro N hN n k x y hxy a b ha hb
  let z := (pairTwoFutureSampleSite N k y + b) - (pairTwoFutureSampleSite N k x + a)
  have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy.symm)
  apply (le_div_iff₀ hd).mpr
  calc
    _ ≤ (Real.sqrt (N : ℝ) * (B / (1 + ‖siteToPlane z‖))) * ‖y - x‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hbound n z) (Real.sqrt_nonneg _)) hd.le
    _ = (B / (1 + ‖siteToPlane z‖)) * (Real.sqrt (N : ℝ) * ‖y - x‖) := by ring
    _ ≤ (B / (1 + ‖siteToPlane z‖)) * (12 * (1 + ‖siteToPlane z‖)) :=
      mul_le_mul_of_nonneg_left (scaled_norm_sub_le_shifted_sampleGap hN k x y a b ha hb)
        (by positivity)
    _ = _ := by field_simp

/-- Potential domination yields a phase- and shift-uniform inverse-gap
majorant for every bounded terminal profile and every remaining clock. -/
theorem eventually_abs_wordTerminalTest_shifted_collisionSample_le_inverse_gap
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    {T : ℝ} (hT : 0 < T) (α β : CollisionPair h) (w : List (CollisionPair h))
    (hw : (β :: w).IsChain (· ≠ ·)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * N →
      ∀ (k : ℕ) (v : FusedConfiguration α),
      collisionEmbedding α v β.1.1 ≠ collisionEmbedding α v β.1.2 →
      ∀ a : LatticeConfiguration h, (∀ i, ‖siteToPlane (a i)‖ ≤ 1) →
      ∀ (Ψ : Configuration h → ℝ) (M : ℝ), 0 ≤ M → (∀ y, |Ψ y| ≤ M) →
        |wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (β :: w) n
          (wordCollisionPhaseSample N k α v + a) Ψ| ≤
            M * C / ‖collisionEmbedding α v β.1.2 - collisionEmbedding α v β.1.1‖ := by
  obtain ⟨B, hB, hword⟩ := eventually_abs_wordTerminalTest_le_potential ϑ hD hT β w hw
  obtain ⟨K, hK, hpot⟩ := exists_scaled_shifted_sampled_wordGapPotential_le_inverse_dist
  refine ⟨B * K, mul_pos hB hK, ?_⟩
  filter_upwards [hword, eventually_gt_atTop 0] with N hb hN
  intro n hn k v hv a ha Ψ M hM hΨ
  have hp := hpot hN n k (collisionEmbedding α v β.1.1) (collisionEmbedding α v β.1.2)
    hv (a β.1.1) (a β.1.2) (ha _) (ha _)
  have ht := hb n hn (wordCollisionPhaseSample N k α v + a) Ψ M hM hΨ
  simp only [Pi.add_apply, wordCollisionPhaseSample_apply] at ht
  calc
    _ ≤ M * B * (Real.sqrt (N : ℝ) * wordGapPotential n
        ((pairTwoFutureSampleSite N k (collisionEmbedding α v β.1.2) + a β.1.2) -
          (pairTwoFutureSampleSite N k (collisionEmbedding α v β.1.1) + a β.1.1))) := by
      simpa only [mul_assoc] using ht
    _ ≤ M * B * (K / ‖collisionEmbedding α v β.1.2 - collisionEmbedding α v β.1.1‖) :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hM hB.le)
    _ = _ := by ring

end Critical2DKPZ.SHF.Moments
