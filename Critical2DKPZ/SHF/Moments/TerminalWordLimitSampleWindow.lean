/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFusedSample
public import Critical2DKPZ.SHF.Moments.EntranceScaling
import Critical2DKPZ.SHF.DeltaBose.PotentialFusedRows
import Mathlib.Tactic

/-! # Spatial windows and phases for sampled collision transitions -/

@[expose] public noncomputable section

open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Moments

/-- A macroscopic representative bound gives a diffusive raw-site bound. -/
theorem norm_siteToPlane_le_of_representative {N : ℕ} (hN : 0 < N)
    {R : ℝ} (hR : 0 ≤ R) (z : Site) (hz : ‖latticeRepresentative N z‖ ≤ R) :
    ‖siteToPlane z‖ ≤ R * Real.sqrt (N : ℝ) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hraw : ‖siteToPlane z‖ ^ 2 =
      ((N : ℝ) / 2) * ‖latticeRepresentative N z‖ ^ 2 := by
    rw [norm_latticeRepresentative_sq]
    field_simp
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [mul_pow, Real.sq_sqrt hNr.le, hraw]
  calc
    _ ≤ ((N : ℝ) / 2) * R ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2) (by positivity)
    _ ≤ _ := by nlinarith only [mul_nonneg hNr.le (sq_nonneg R)]

/-- A compact window for sampled fused representatives bounds the raw
collision-center displacement needed by the normalized run estimate. -/
theorem wordCollisionPhaseSample_center_gap_bound {h N : ℕ} (hN : 0 < N)
    (k l : ℕ) (α : CollisionPair h) (u v : FusedConfiguration α)
    {R : ℝ} (hR : 0 ≤ R)
    (hu : ‖wordFusedPhaseRepresentative N k α u‖ ≤ R)
    (hv : ‖wordFusedPhaseRepresentative N l α v‖ ≤ R) :
    ‖siteToPlane (wordCollisionPhaseSample N l α v α.1.1 -
      wordCollisionPhaseSample N k α u α.1.1)‖ ≤ (2 * R) * Real.sqrt (N : ℝ) := by
  apply norm_siteToPlane_le_of_representative hN (by positivity)
  rw [latticeRepresentative_sub]
  rw [wordCollisionPhaseSample_apply, wordCollisionPhaseSample_apply]
  simp only [collisionEmbedding_pair_left]
  calc
    _ ≤ ‖(wordFusedPhaseRepresentative N l α v).1‖ +
        ‖(wordFusedPhaseRepresentative N k α u).1‖ := norm_sub_le _ _
    _ ≤ R + R := add_le_add ((norm_fst_le _).trans hv) ((norm_fst_le _).trans hu)
    _ = _ := by ring

/-- The two phase clocks on either side of a fitted run force precisely the
run's lattice parity at every coordinate. -/
theorem wordCollisionPhaseSample_run_phase {h : ℕ} (N n s r : ℕ)
    (hfit : s + r ≤ n) (α : CollisionPair h) (u v : FusedConfiguration α) (i : Fin h) :
    Even ((r : ℤ) +
      (wordCollisionPhaseSample N (n - s - r) α v i -
        wordCollisionPhaseSample N (n - s) α u i) 0 +
      (wordCollisionPhaseSample N (n - s - r) α v i -
        wordCollisionPhaseSample N (n - s) α u i) 1) := by
  have hu := wordCollisionPhaseSample_phase N (n - s) α u i
  have hv := wordCollisionPhaseSample_phase N (n - s - r) α v i
  rw [Int.even_iff] at hu hv ⊢
  simp only [Pi.sub_apply]
  omega

end Critical2DKPZ.SHF.Moments
