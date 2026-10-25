/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialShiftCells
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFusedSupport
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitUniformSpatialBound
import Mathlib.Tactic

/-! # Phase-free translated spatial representation of the first block -/

@[expose] public noncomputable section
open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds
namespace Critical2DKPZ.SHF.Moments

/-- Correct the terminal phase of each free collision coordinate. -/
def wordFusedInitialParityShift {h : ℕ} (n : ℕ) (α : CollisionPair h)
    (x : LatticeConfiguration h) : Site × (Spectator α → Site) :=
  (wordCoordinateParityShift n (x α.1.1), fun i => wordCoordinateParityShift n (x i.1))

/-- The embedded free-coordinate correction is bounded by one site in every coordinate. -/
theorem wordFusedInitialParityShift_site_norm_le {h : ℕ} (n : ℕ) (α : CollisionPair h)
    (x : LatticeConfiguration h) (i : Fin h) :
    ‖siteToPlane (wordFusedSiteEmbedding α (wordFusedInitialParityShift n α x) i)‖ ≤ 1 := by
  unfold wordFusedSiteEmbedding wordFusedInitialParityShift
  split_ifs <;> exact norm_siteToPlane_wordCoordinateParityShift_le n _

/-- The continuum correction is at most one mesh in the fused norm. -/
theorem norm_wordFusedInitialParityShift_representative_le {h : ℕ} (N n : ℕ)
    (α : CollisionPair h) (x : LatticeConfiguration h) :
    ‖wordFusedCoordinateRepresentative N α (wordFusedInitialParityShift n α x)‖ ≤
      (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
  have hc (z : Site) (hz : ‖siteToPlane z‖ ≤ 1) :
      ‖latticeRepresentative N z‖ ≤ (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
    rw [latticeRepresentative, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact (mul_le_mul_of_nonneg_left hz (by positivity)).trans_eq (mul_one _)
  rw [Prod.norm_def, max_le_iff]
  refine ⟨hc _ (norm_siteToPlane_wordCoordinateParityShift_le n _), ?_⟩
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro i
  exact hc _ (norm_siteToPlane_wordCoordinateParityShift_le n _)

/-- Lattice collision embedding respects addition. -/
theorem wordFusedSiteEmbedding_add {h : ℕ} (α : CollisionPair h)
    (p q : Site × (Spectator α → Site)) :
    wordFusedSiteEmbedding α (p + q) = wordFusedSiteEmbedding α p + wordFusedSiteEmbedding α q := by
  funext i
  simp only [Pi.add_apply, wordFusedSiteEmbedding, Prod.fst_add, Prod.snd_add]
  split_ifs <;> rfl

/-- The diffusive representative respects addition of fused coordinates. -/
theorem wordFusedCoordinateRepresentative_add {h : ℕ} (N : ℕ) (α : CollisionPair h)
    (p q : Site × (Spectator α → Site)) :
    wordFusedCoordinateRepresentative N α (p + q) =
      wordFusedCoordinateRepresentative N α p + wordFusedCoordinateRepresentative N α q := by
  apply Prod.ext
  · exact latticeRepresentative_add N _ _
  · funext i
    exact latticeRepresentative_add N _ _

/-- Representatives of sampled free lattice coordinates are the canonical fused samples. -/
theorem wordFusedCoordinateRepresentative_sample {h : ℕ} (N k : ℕ) (α : CollisionPair h)
    (p : FusedConfiguration α) :
    wordFusedCoordinateRepresentative N α (wordFusedSiteSample N k α p) =
      wordFusedPhaseRepresentative N k α p := rfl

/-- The translated step is exactly the shifted normalized summand and shifted spatial test. -/
theorem wordFusedSpatialSummand_shifted_sample {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n s r : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ)
    (a : Site × (Spectator α → Site)) (p : FusedConfiguration α × FusedConfiguration α) :
    wordFusedSpatialSummand N β α w n s r x Ψ χ
      (wordFusedPairSiteSample N (n - s) (n - s - r) α p + (a, a)) =
    χ (wordFusedPairRepresentative N (n - s) (n - s - r) α p +
        (wordFusedCoordinateRepresentative N α a, wordFusedCoordinateRepresentative N α a)) *
      wordConsScaledSummand N β α w n s r x
        (wordCollisionPhaseSample N (n - s) α p.1 + wordFusedSiteEmbedding α a)
        (wordCollisionPhaseSample N (n - s - r) α p.2 + wordFusedSiteEmbedding α a) Ψ := by
  simp only [wordFusedSpatialSummand, wordFusedPairSiteSample,
    Prod.fst_add, Prod.snd_add, wordFusedSiteEmbedding_add, wordFusedSiteEmbedding_sample,
    wordFusedCoordinateRepresentative_add, wordFusedCoordinateRepresentative_sample]
  rfl

/-- The shifted fused step represents every initial parity, with the original
cell normalization and no regularity assumption on the terminal profile or spatial weight. -/
theorem integrable_integral_wordFusedSpatialSummand_shifted {h N : ℕ} (hN : 0 < N)
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
      (4 / (N : ℝ)) ^ (2 * (h - 1)) * ∑' z, wordFusedSpatialSummand N β α w n s r x Ψ χ z := by
  let G := wordFusedSpatialSummand N β α w n s r x Ψ χ
  let a := wordFusedInitialParityShift n α x
  have hphase (z) (hz : G z ≠ 0) :
      (Even ((z.1.1 - a.1) 0 + (z.1.1 - a.1) 1 + ((n - s : ℕ) : ℤ)) ∧
        ∀ i, Even ((z.1.2 i - a.2 i) 0 + (z.1.2 i - a.2 i) 1 + ((n - s : ℕ) : ℤ))) ∧
      (Even ((z.2.1 - a.1) 0 + (z.2.1 - a.1) 1 + ((n - s - r : ℕ) : ℤ)) ∧
        ∀ i, Even ((z.2.2 i - a.2 i) 0 + (z.2.2 i - a.2 i) 1 + ((n - s - r : ℕ) : ℤ))) := by
    have ht : wordConsScaledSummand N β α w n s r x
        (wordFusedSiteEmbedding α z.1) (wordFusedSiteEmbedding α z.2) Ψ ≠ 0 :=
      (mul_ne_zero_iff.mp hz).2
    obtain ⟨hu, hv⟩ := wordConsScaledSummand_nonzero_reachable N β α w n s r x _ _ Ψ ht
    have hp := word_shifted_recursion_phases n s r hfit x _ _ hu hv
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa only [a, wordFusedInitialParityShift, wordFusedSiteEmbedding, true_or, ↓reduceDIte] using
        (hp α.1.1).1
    · intro i
      simpa [a, wordFusedInitialParityShift, wordFusedSiteEmbedding, i.2.1, i.2.2] using (hp i.1).1
    · simpa only [a, wordFusedInitialParityShift, wordFusedSiteEmbedding, true_or, ↓reduceDIte] using
        (hp α.1.1).2
    · intro i
      simpa [a, wordFusedInitialParityShift, wordFusedSiteEmbedding, i.2.1, i.2.2] using (hp i.1).2
  exact integrable_integral_shifted_fusedPairPhaseStep hN α (n - s) (n - s - r) a G
    (finite_support_wordFusedSpatialSummand N β α w n s r x Ψ χ) hphase

end Critical2DKPZ.SHF.Moments
