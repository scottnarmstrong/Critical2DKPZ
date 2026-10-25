/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialTranslated
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialLattice
import Mathlib.Tactic

/-! # Parity-independent cancellation of the fused spatial normalizations -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- The lattice normalization cancels both fused cell volumes independently of the initial parities. -/
theorem wordFusedSpatialSummand_tsum_normalization {h N : ℕ} (hN : 0 < N)
    (β : ℝ) (α : CollisionPair h) (w : List (CollisionPair h)) (n s r : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    (4 / (N : ℝ)) ^ (2 * (h - 1)) *
      (∑' z, wordFusedSpatialSummand N β α w n s r x Ψ χ z) =
      (N : ℝ)^2 * ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
        χ ((latticeRepresentative N (u α.1.1), fun i : Spectator α => latticeRepresentative N (u i.1)),
          (latticeRepresentative N (v α.1.1), fun i : Spectator α => latticeRepresentative N (v i.1))) *
          (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
            wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ) := by
  classical
  let G := wordFusedSpatialSummand N β α w n s r x Ψ χ
  let Q : LatticeConfiguration h → LatticeConfiguration h → ℝ := fun u v =>
    χ (wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α u),
      wordFusedCoordinateRepresentative N α (wordFusedSiteProjection α v)) *
      (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
        wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ)
  change _ = (N : ℝ)^2 * ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h, Q u v
  have hpoint (p q : Site × (Spectator α → Site)) :
      G (p, q) = (N : ℝ)^2 * ((N : ℝ) / 4) ^ (2 * (h - 1)) *
        Q (wordFusedSiteEmbedding α p) (wordFusedSiteEmbedding α q) := by
    dsimp only [G, Q]
    rw [wordFusedSpatialSummand, wordConsScaledSummand_eq,
      wordFusedSiteProjection_embedding, wordFusedSiteProjection_embedding]
    ring
  have hsum : Summable G :=
    summable_of_hasFiniteSupport (finite_support_wordFusedSpatialSummand N β α w n s r x Ψ χ)
  have hleft (u v : LatticeConfiguration h) (hu : u α.1.1 ≠ u α.1.2) : Q u v = 0 := by
    have hz : collisionWordUndampedPairRunFactor β α r u v = 0 := by
      simp [collisionWordUndampedPairRunFactor, hu]
    dsimp only [Q]
    rw [hz, mul_zero, zero_mul, mul_zero]
  have hright (u v : LatticeConfiguration h) (hv : v α.1.1 ≠ v α.1.2) : Q u v = 0 := by
    have hz : collisionWordUndampedPairRunFactor β α r u v = 0 := by
      simp [collisionWordUndampedPairRunFactor, hv]
    dsimp only [Q]
    rw [hz, mul_zero, zero_mul, mul_zero]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hcancel : (4 / (N : ℝ)) ^ (2 * (h - 1)) *
      ((N : ℝ) / 4) ^ (2 * (h - 1)) = 1 := by
    rw [← mul_pow, show (4 / (N : ℝ)) * ((N : ℝ) / 4) = 1 by field_simp [hNr], one_pow]
  calc
    _ = (4 / (N : ℝ)) ^ (2 * (h - 1)) *
        ((N : ℝ)^2 * ((N : ℝ) / 4) ^ (2 * (h - 1)) *
          ∑' p : Site × (Spectator α → Site), ∑' q : Site × (Spectator α → Site),
            Q (wordFusedSiteEmbedding α p) (wordFusedSiteEmbedding α q)) := by
      rw [hsum.tsum_prod]
      simp only [hpoint, tsum_mul_left]
    _ = (N : ℝ)^2 * (∑' p : Site × (Spectator α → Site), ∑' q : Site × (Spectator α → Site),
        Q (wordFusedSiteEmbedding α p) (wordFusedSiteEmbedding α q)) := by
      calc
        _ = (N : ℝ)^2 * ((4 / (N : ℝ)) ^ (2 * (h - 1)) *
            ((N : ℝ) / 4) ^ (2 * (h - 1))) *
            (∑' p : Site × (Spectator α → Site), ∑' q : Site × (Spectator α → Site),
              Q (wordFusedSiteEmbedding α p) (wordFusedSiteEmbedding α q)) := by ring
        _ = _ := by rw [hcancel, mul_one]
    _ = _ := congrArg (fun v : ℝ => (N : ℝ)^2 * v)
      (tsum_collision_pair_eq_fusedSites α Q hleft hright)

/-- Every initial parity has an integrable translated cell representation,
with exactly `N²` times the original spatial lattice sum. -/
theorem integrable_integral_wordFirstLetter_shifted_eq_lattice {h N : ℕ} (hN : 0 < N)
    (β : ℝ) (α : CollisionPair h) (w : List (CollisionPair h)) (n s r : ℕ)
    (hfit : s + r ≤ n) (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    let a := wordFusedInitialParityShift n α x
    Integrable (fun p : FusedConfiguration α × FusedConfiguration α =>
      wordFusedSpatialSummand N β α w n s r x Ψ χ
        (wordFusedPairSiteSample N (n - s) (n - s - r) α p + (a, a))) ∧
    (∫ p : FusedConfiguration α × FusedConfiguration α,
      wordFusedSpatialSummand N β α w n s r x Ψ χ
        (wordFusedPairSiteSample N (n - s) (n - s - r) α p + (a, a))) =
      (N : ℝ)^2 * ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
        χ ((latticeRepresentative N (u α.1.1), fun i : Spectator α => latticeRepresentative N (u i.1)),
          (latticeRepresentative N (v α.1.1), fun i : Spectator α => latticeRepresentative N (v i.1))) *
          (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
            wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ) := by
  have hi := integrable_integral_wordFusedSpatialSummand_shifted hN β α w n s r hfit x Ψ χ
  exact ⟨hi.1, hi.2.trans (wordFusedSpatialSummand_tsum_normalization hN β α w n s r x Ψ χ)⟩

end Critical2DKPZ.SHF.Moments
