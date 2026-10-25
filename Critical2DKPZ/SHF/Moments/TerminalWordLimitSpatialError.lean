/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialNormalization
import Mathlib.Tactic

/-! # A single-clock spatial cutoff error from its integrable envelope -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- The weighted envelope error bounds the original spatial lattice error
with precisely the inverse two-time-cell normalization. All initial parities
are covered by the canonical bounded translation. -/
theorem wordFirstLetter_spatial_error_le_of_integrable_majorant
    {h N : ℕ} (hN : 0 < N) (β : ℝ) (α : CollisionPair h) (w : List (CollisionPair h))
    (n s r : ℕ) (hfit : s + r ≤ n) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (B : FusedConfiguration α × FusedConfiguration α → ℝ)
    (χ : FusedConfiguration α × FusedConfiguration α → ℝ) (ε : ℝ) :
    let a := wordFusedInitialParityShift n α x
    let d := wordFusedCoordinateRepresentative N α a
    (∀ᵐ p : FusedConfiguration α × FusedConfiguration α,
      |wordConsScaledSummand N β α w n s r x
        (wordCollisionPhaseSample N (n - s) α p.1 + wordFusedSiteEmbedding α a)
        (wordCollisionPhaseSample N (n - s - r) α p.2 + wordFusedSiteEmbedding α a) Ψ| ≤ B p) →
    Integrable (fun p : FusedConfiguration α × FusedConfiguration α =>
      B p * |1 - χ (wordFusedPairRepresentative N (n - s) (n - s - r) α p + (d, d))|) →
    (∫ p : FusedConfiguration α × FusedConfiguration α,
      B p * |1 - χ (wordFusedPairRepresentative N (n - s) (n - s - r) α p + (d, d))|) ≤ ε →
    |∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
      (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
        wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ) *
        (1 - χ ((latticeRepresentative N (u α.1.1),
          fun i : Spectator α => latticeRepresentative N (u i.1)),
          (latticeRepresentative N (v α.1.1),
          fun i : Spectator α => latticeRepresentative N (v i.1))))| ≤ ε / (N : ℝ)^2 := by
  dsimp only
  let a := wordFusedInitialParityShift n α x
  let d := wordFusedCoordinateRepresentative N α a
  intro hmajor hi hsmall
  let F := fun p : FusedConfiguration α × FusedConfiguration α =>
    wordFusedSpatialSummand N β α w n s r x Ψ (fun q => 1 - χ q)
      (wordFusedPairSiteSample N (n - s) (n - s - r) α p + (a, a))
  have hbound : ∀ᵐ p : FusedConfiguration α × FusedConfiguration α,
      ‖F p‖ ≤ B p * |1 - χ (wordFusedPairRepresentative N (n - s) (n - s - r) α p + (d, d))| := by
    filter_upwards [hmajor] with p hp
    dsimp only [F]
    rw [wordFusedSpatialSummand_shifted_sample, Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul_of_nonneg_left hp (abs_nonneg _)).trans_eq (mul_comm _ _)
  have hest : |∫ p, F p| ≤ ε := by
    have hb := norm_integral_le_of_norm_le hi hbound
    have hb' : |∫ p, F p| ≤ ∫ p : FusedConfiguration α × FusedConfiguration α,
        B p * |1 - χ (wordFusedPairRepresentative N (n - s) (n - s - r) α p + (d, d))| := by
      simpa only [Real.norm_eq_abs] using hb
    exact hb'.trans hsmall
  let S : ℝ := ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
    (1 - χ ((latticeRepresentative N (u α.1.1),
      fun i : Spectator α => latticeRepresentative N (u i.1)),
      (latticeRepresentative N (v α.1.1),
      fun i : Spectator α => latticeRepresentative N (v i.1)))) *
      (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
        wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ)
  have he : (∫ p, F p) = (N : ℝ)^2 * S :=
    (integrable_integral_wordFirstLetter_shifted_eq_lattice hN β α w n s r hfit x Ψ
      (fun q => 1 - χ q)).2
  have hS : (∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
      (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
        wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ) *
        (1 - χ ((latticeRepresentative N (u α.1.1),
          fun i : Spectator α => latticeRepresentative N (u i.1)),
          (latticeRepresentative N (v α.1.1),
          fun i : Spectator α => latticeRepresentative N (v i.1))))) = S := by
    apply tsum_congr
    intro u
    apply tsum_congr
    intro v
    exact mul_comm _ _
  rw [hS]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  apply (le_div_iff₀ (sq_pos_of_pos hNr)).mpr
  calc
    |S| * (N : ℝ)^2 = |(N : ℝ)^2 * S| := by
      simp only [abs_mul, abs_of_nonneg (sq_nonneg (N : ℝ))]
      exact mul_comm _ _
    _ = |∫ p, F p| := congrArg abs he.symm
    _ ≤ ε := hest

end Critical2DKPZ.SHF.Moments
