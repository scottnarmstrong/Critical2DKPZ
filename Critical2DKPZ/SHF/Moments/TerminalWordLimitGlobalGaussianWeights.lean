/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitGlobalGaussianBounds
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitGlobalSpatialL1
import Mathlib.Tactic

/-! # Gaussian envelope weights on the fused coordinates -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators
open Critical2DKPZ.DeltaBose
namespace Critical2DKPZ.SHF.Moments

/-- A Gaussian envelope evaluated on the embedded collision coordinates.
This is a deterministic dominating weight, not an additional evolution kernel. -/
def wordEmbeddingGaussian {h : ℕ} (α : CollisionPair h) (c : ℝ)
    (p : FusedConfiguration α) : ℝ :=
  ∏ i, Real.exp (-c * ‖collisionEmbedding α p i‖ ^ 2)

/-- The embedded Gaussian weight is positive. -/
theorem wordEmbeddingGaussian_pos {h : ℕ} (α : CollisionPair h) (c : ℝ)
    (p : FusedConfiguration α) : 0 < wordEmbeddingGaussian α c p :=
  Finset.prod_pos fun _ _ => Real.exp_pos _

/-- Decreasing the Gaussian rate increases its envelope. -/
theorem wordEmbeddingGaussian_antitone {h : ℕ} (α : CollisionPair h)
    {c d : ℝ} (hcd : c ≤ d) (p : FusedConfiguration α) :
    wordEmbeddingGaussian α d p ≤ wordEmbeddingGaussian α c p := by
  apply Finset.prod_le_prod₀
  · intro i _; positivity
  · intro i _
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hcd
      (sq_nonneg ‖collisionEmbedding α p i‖))

/-- An entrance Gaussian and an increment Gaussian dominate separate
Gaussians in the entrance and terminal locations. -/
theorem exp_norm_sq_mul_increment_le {E : Type*} [NormedAddCommGroup E]
    {c : ℝ} (hc : 0 ≤ c) (p q : E) :
    Real.exp (-c * ‖p‖ ^ 2) * Real.exp (-c * ‖q - p‖ ^ 2) ≤
      Real.exp (-(c / 3) * ‖p‖ ^ 2) * Real.exp (-(c / 3) * ‖q‖ ^ 2) := by
  have ht := norm_le_norm_sub_add q p
  have hs : ‖q‖ ^ 2 ≤ 2 * ‖q - p‖ ^ 2 + 2 * ‖p‖ ^ 2 := by
    have hsq := (sq_le_sq₀ (norm_nonneg q) (by positivity : 0 ≤ ‖q - p‖ + ‖p‖)).mpr ht
    nlinarith only [hsq, sq_nonneg (‖q - p‖ - ‖p‖)]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [mul_nonneg hc (sub_nonneg.mpr hs), mul_nonneg hc (sq_nonneg ‖q - p‖)]

/-- The Gaussian decoupling inequality on all fused coordinates. -/
theorem wordEmbeddingGaussian_mul_sub_le {h : ℕ} (α : CollisionPair h)
    {c : ℝ} (hc : 0 ≤ c) (p q : FusedConfiguration α) :
    wordEmbeddingGaussian α c p * wordEmbeddingGaussian α c (q - p) ≤
      wordEmbeddingGaussian α (c / 3) p * wordEmbeddingGaussian α (c / 3) q := by
  unfold wordEmbeddingGaussian
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i _; positivity
  · intro i _
    have he : collisionEmbedding α (q - p) i = collisionEmbedding α q i - collisionEmbedding α p i := by
      unfold collisionEmbedding
      split_ifs <;> rfl
    rw [he]
    exact exp_norm_sq_mul_increment_le hc _ _

/-- An embedded Gaussian is exactly an incoming Gaussian up to its finite
normalizing constant. -/
theorem wordEmbeddingGaussian_eq_incoming {h : ℕ} (α : CollisionPair h)
    {c : ℝ} (hc : 0 < c) (p : FusedConfiguration α) :
    wordEmbeddingGaussian α c p =
      (2 * Real.pi * (1 / (2 * c))) ^ h * incomingKernel α (1 / (2 * c)) p 0 := by
  have hd : 2 * Real.pi * (1 / (2 * c)) ≠ 0 := by positivity
  have he (z : Plane) : Real.exp (-c * ‖z‖ ^ 2) =
      (2 * Real.pi * (1 / (2 * c))) * heatKernel (1 / (2 * c)) z := by
    unfold heatKernel
    have ht : -‖z‖ ^ 2 / (2 * (1 / (2 * c))) = -c * ‖z‖ ^ 2 := by field_simp
    rw [ht]
    field_simp
  unfold wordEmbeddingGaussian incomingKernel freeKernel
  simp only [Pi.zero_apply, sub_zero]
  simp_rw [he]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The Gaussian weight is integrable on the collision space. -/
theorem integrable_wordEmbeddingGaussian {h : ℕ} (α : CollisionPair h)
    {c : ℝ} (hc : 0 < c) : Integrable (wordEmbeddingGaussian α c) := by
  convert (integrable_incomingKernel_fused α (by positivity : 0 < 1 / (2 * c)) 0).const_mul
    ((2 * Real.pi * (1 / (2 * c))) ^ h) using 1
  funext p
  exact wordEmbeddingGaussian_eq_incoming α hc p

/-- The product Gaussian with the singular next-pair weight is integrable. -/
theorem integrable_wordEmbeddingGaussian_pair_inverse_gap {h : ℕ}
    (α β : CollisionPair h) (hne : α ≠ β) {c : ℝ} (hc : 0 < c) :
    Integrable (fun p : FusedConfiguration α × FusedConfiguration α =>
      wordEmbeddingGaussian α c p.1 * wordEmbeddingGaussian α c p.2 *
        (1 + ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖⁻¹)) := by
  have hi := integrable_incomingKernel_pair_mul_one_add_inverse_gap α β hne
    (by positivity : 0 < 1 / (2 * c))
  have hp := hi.const_mul (((2 * Real.pi * (1 / (2 * c))) ^ h) ^ 2)
  apply hp.congr
  exact Eventually.of_forall fun p => by
    dsimp only
    rw [wordEmbeddingGaussian_eq_incoming α hc, wordEmbeddingGaussian_eq_incoming α hc]
    ring

end Critical2DKPZ.SHF.Moments
