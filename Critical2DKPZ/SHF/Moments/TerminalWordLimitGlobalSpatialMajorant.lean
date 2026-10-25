/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitGlobalBlockBound
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitShiftedPotential
import Mathlib.Tactic

/-! # A global integrable majorant for the interior first-letter recursion -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- A single nonnegative integrable envelope for the full sampled first-letter
summand, uniform over the interior clocks and all unit lattice phase shifts. -/
theorem exists_integrable_majorant_wordConsScaledSummand_interior :
∀ (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : (α :: w).IsChain (· ≠ ·))
    {τ η : ℝ} (hτ : 0 < τ) (hη : 0 < η)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (Ψ : Configuration h → ℝ) (M : ℝ) (hM : 0 ≤ M) (hΨ : ∀ y, |Ψ y| ≤ M),
    ∃ B : FusedConfiguration α × FusedConfiguration α → ℝ,
      Integrable B ∧ (∀ p, 0 ≤ B p) ∧ ∀ᶠ N : ℕ in atTop, ∀ s r : ℕ,
        η * N ≤ (s : ℝ) → η * N ≤ (r : ℝ) → s + r ≤ nN N →
        η * N ≤ ((nN N - s - r : ℕ) : ℝ) →
        ∀ a : LatticeConfiguration h, (∀ i, ‖siteToPlane (a i)‖ ≤ 1) →
        ∀ᵐ p : FusedConfiguration α × FusedConfiguration α,
          |wordConsScaledSummand N (criticalBeta ϑ N) α w (nN N) s r (xN N)
            (wordCollisionPhaseSample N (nN N - s) α p.1 + a)
            (wordCollisionPhaseSample N (nN N - s - r) α p.2 + a) Ψ| ≤ B p := by
  intro ϑ h hD α w hw τ η hτ hη nN hn xN x hx Ψ M hM hΨ
  let T := τ + 1
  let R := ‖x‖ + 1
  have hT : 0 < T := by dsimp [T]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hstarts : ∀ᶠ N : ℕ in atTop, ∀ i, ‖latticeRepresentative N (xN N i)‖ ≤ R := by
    apply eventually_all.mpr
    intro i
    have hi := (hx i).norm.eventually (Iio_mem_nhds (lt_add_one ‖x i‖))
    filter_upwards [hi] with N hN
    exact hN.le.trans (add_le_add (norm_le_pi_norm x i) le_rfl)
  have hclock : ∀ᶠ N : ℕ in atTop, (nN N : ℝ) ≤ T * N := by
    have hh := hn.eventually (Iio_mem_nhds (show τ < T by dsimp [T]; linarith))
    filter_upwards [hh, eventually_gt_atTop 0] with N hh hN
    exact ((div_lt_iff₀ (show (0 : ℝ) < N by exact_mod_cast hN)).mp hh).le
  have hmesh : ∀ᶠ N : ℕ in atTop, (Real.sqrt ((N : ℝ) / 2))⁻¹ ≤ 1 :=
    (tendsto_lattice_mesh.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono fun _ h => h.le
  obtain ⟨A, c, hA, hc, hblock⟩ :=
    eventually_scaled_wordFirstBlock_gaussian_interior ϑ η T R hη hT hR α
  have hbounds : ∀ᶠ N : ℕ in atTop, ∀ s r : ℕ,
      η * N ≤ (s : ℝ) → η * N ≤ (r : ℝ) → s + r ≤ nN N →
      ∀ a : LatticeConfiguration h, (∀ i, ‖siteToPlane (a i)‖ ≤ 1) →
      ∀ p : FusedConfiguration α × FusedConfiguration α,
      |(((N : ℝ) / 4) ^ h * ∏ i, srwKernel s
          ((wordCollisionPhaseSample N (nN N - s) α p.1 + a) i - xN N i)) *
        (4 * (N : ℝ) * ((N : ℝ) / 4) ^ (h - 1) *
          collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r
            (wordCollisionPhaseSample N (nN N - s) α p.1 + a)
            (wordCollisionPhaseSample N (nN N - s - r) α p.2 + a))| ≤
        A * wordEmbeddingGaussian α c p.1 * wordEmbeddingGaussian α c p.2 := by
    filter_upwards [hblock, hstarts, hclock, hmesh] with N hb hxN hnN hmN
    intro s r hs hr hfit a ha p
    have hsT : (s : ℝ) ≤ T * N :=
      (Nat.cast_le.mpr (by omega : s ≤ nN N)).trans hnN
    have hrT : (r : ℝ) ≤ T * N :=
      (Nat.cast_le.mpr (by omega : r ≤ nN N)).trans hnN
    exact hb hmN s r hs hsT hr hrT (xN N) a hxN ha _ _ p.1 p.2
  cases w with
  | nil =>
    let B : FusedConfiguration α × FusedConfiguration α → ℝ := fun p =>
      (A * M) * wordEmbeddingGaussian α c p.1 * wordEmbeddingGaussian α c p.2
    have hi := (integrable_wordEmbeddingGaussian α hc).mul_prod (integrable_wordEmbeddingGaussian α hc)
    refine ⟨B, ?_, ?_, ?_⟩
    · convert hi.const_mul (A * M) using 1
      funext p
      dsimp only [B]
      ring
    · intro p
      exact mul_nonneg (mul_nonneg (mul_nonneg hA.le hM) (wordEmbeddingGaussian_pos _ _ _).le)
        (wordEmbeddingGaussian_pos _ _ _).le
    · filter_upwards [hbounds] with N hb
      intro s r hs hr hfit _hremain a ha
      exact Eventually.of_forall fun p => by
        have ht := abs_wordTerminalTest_le_mass N (sigmaSq_nonneg (criticalBeta ϑ N)) []
          (nN N - s - r) (wordCollisionPhaseSample N (nN N - s - r) α p.2 + a) Ψ hΨ
        simp only [wordTerminalTest_nil_one, mul_one] at ht
        have he := hb s r hs hr hfit a ha p
        unfold wordConsScaledSummand
        rw [abs_mul]
        have hh := mul_le_mul he ht (abs_nonneg _) (by
          exact mul_nonneg (mul_nonneg hA.le (wordEmbeddingGaussian_pos _ _ _).le)
            (wordEmbeddingGaussian_pos _ _ _).le)
        simpa only [B, mul_assoc, mul_comm, mul_left_comm] using hh
  | cons β w =>
    have hne : α ≠ β := (List.isChain_cons_cons.mp hw).1
    have htailChain : (β :: w).IsChain (· ≠ ·) := hw.tail
    obtain ⟨D, hDpos, htail⟩ :=
      eventually_abs_wordTerminalTest_shifted_collisionSample_le_inverse_gap ϑ hD hT α β w htailChain
    let B : FusedConfiguration α × FusedConfiguration α → ℝ := fun p =>
      (A * (M * D)) * (wordEmbeddingGaussian α c p.1 * wordEmbeddingGaussian α c p.2 *
        (1 + ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖⁻¹))
    refine ⟨B, (integrable_wordEmbeddingGaussian_pair_inverse_gap α β hne hc).const_mul _, ?_, ?_⟩
    · intro p
      exact mul_nonneg (mul_nonneg hA.le (mul_nonneg hM hDpos.le))
        (mul_nonneg (mul_nonneg (wordEmbeddingGaussian_pos _ _ _).le (wordEmbeddingGaussian_pos _ _ _).le)
          (add_nonneg zero_le_one (inv_nonneg.mpr (norm_nonneg _))))
    · filter_upwards [hbounds, htail, hclock] with N hb ht hnN
      intro s r hs hr hfit _hremain a ha
      have hae : ∀ᵐ p : FusedConfiguration α × FusedConfiguration α,
          collisionEmbedding α p.2 β.1.1 ≠ collisionEmbedding α p.2 β.1.2 := by
        rw [Measure.volume_eq_prod]
        exact Measure.quasiMeasurePreserving_snd.ae (ae_collisionEmbedding_pair_ne α β hne)
      filter_upwards [hae] with p hp
      have hremainT : ((nN N - s - r : ℕ) : ℝ) ≤ T * N :=
        (Nat.cast_le.mpr ((Nat.sub_le _ _).trans (Nat.sub_le _ _))).trans hnN
      have htt := ht (nN N - s - r) hremainT (nN N - s - r) p.2 hp a ha Ψ M hM hΨ
      have htt' : |wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (β :: w)
          (nN N - s - r) (wordCollisionPhaseSample N (nN N - s - r) α p.2 + a) Ψ| ≤
          (M * D) * (1 + ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖⁻¹) := by
        apply htt.trans
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (by linarith :
          ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖⁻¹ ≤
            1 + ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖⁻¹)
          (mul_nonneg hM hDpos.le)
      have he := hb s r hs hr hfit a ha p
      unfold wordConsScaledSummand
      rw [abs_mul]
      have hh := mul_le_mul he htt' (abs_nonneg _) (by
        exact mul_nonneg (mul_nonneg hA.le (wordEmbeddingGaussian_pos _ _ _).le)
          (wordEmbeddingGaussian_pos _ _ _).le)
      simpa only [B, mul_assoc, mul_comm, mul_left_comm] using hh

end Critical2DKPZ.SHF.Moments
