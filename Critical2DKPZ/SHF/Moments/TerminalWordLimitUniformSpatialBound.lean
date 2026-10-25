/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialIntegrand
import Mathlib.Tactic

/-! # A spatial majorant uniform in the two microscopic clocks -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The sampled spatial cutoff yields one integrable compact majorant,
uniform in every fitted microscopic clock triple and initial state on the
prescribed interior slabs. -/
theorem exists_uniform_integrable_majorant_wordFirstLetterSpatialIntegrand
    (ϑ a T : ℝ) (ha : 0 < a) (haT : a ≤ T) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·))
    {R δ : ℝ}
    (hR : 0 ≤ R) (hδ : 0 < δ)
    (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ))
    (hχR : ∀ p, χ p ≠ 0 → ‖p‖ ≤ R)
    (hχsep : ∀ p, χ p ≠ 0 → ∀ β ∈ w.head?,
      δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖)
    (Ψ : Configuration h → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hΨ : ∀ y, |Ψ y| ≤ M) :
    ∃ B : (FusedConfiguration α × FusedConfiguration α) → ℝ, Integrable B ∧
      ∀ᶠ N : ℕ in atTop, ∀ (n s r : ℕ),
        (n : ℝ) ≤ T * N → a * N ≤ (s : ℝ) → a * N ≤ (r : ℝ) → s + r ≤ n →
        ∀ (x : LatticeConfiguration h) (p : FusedConfiguration α × FusedConfiguration α),
        |wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w n s r x Ψ χ p| ≤ B p := by
  classical
  have : ProperSpace (FusedConfiguration α) := by infer_instance
  have : IsFiniteMeasureOnCompacts (volume : Measure (Spectator α → Plane)) := by infer_instance
  have : IsFiniteMeasureOnCompacts (volume : Measure (FusedConfiguration α)) := by infer_instance
  obtain ⟨C, hC, hbound⟩ := eventually_abs_wordFirstLetterSpatialIntegrand_le
    ϑ a T R δ ha haT hR hδ hD α w hw χ hχR hχsep
  let S := Metric.closedBall (0 : FusedConfiguration α × FusedConfiguration α) (R + 1)
  let L := C * M * ‖χ.toBoundedContinuousFunction‖
  let B := S.indicator (fun _ => L)
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨B, ?_, ?_⟩
  · exact (integrableOn_const (C := L) (isCompact_closedBall _ _).measure_ne_top).integrable_indicator
      (isCompact_closedBall _ _).measurableSet
  · filter_upwards [hbound, tendsto_lattice_mesh.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
        eventually_gt_atTop 0] with N hb hmesh hN
    intro n s r hn hs hr hfit x p
    let q := wordFusedPairRepresentative N (n - s) (n - s - r) α p
    have herr : ‖q - p‖ ≤ 1 := by
      rw [Prod.norm_def, max_le_iff]
      exact ⟨(norm_wordFusedPhaseRepresentative_sub_le hN _ α p.1).trans hmesh.le,
        (norm_wordFusedPhaseRepresentative_sub_le hN _ α p.2).trans hmesh.le⟩
    by_cases hp : p ∈ S
    · rw [show B p = L from Set.indicator_of_mem hp _]
      calc
        _ ≤ C * M * |χ q| := by
          simpa only [mul_assoc, mul_comm, mul_left_comm] using
            hb n s r hn hs hr hfit x Ψ M hM hΨ p
        _ ≤ L := mul_le_mul_of_nonneg_left
          (by exact χ.toBoundedContinuousFunction.norm_coe_le_norm q)
          (mul_nonneg hC.le hM)
    · have hχzero : χ q = 0 := by
        by_contra hne
        have hqnorm := hχR q hne
        have hpbound : ‖p‖ ≤ R + 1 := by
          calc
            _ ≤ ‖p - q‖ + ‖q‖ := norm_le_norm_sub_add _ _
            _ ≤ 1 + R := add_le_add (by simpa only [norm_sub_rev] using herr) hqnorm
            _ = _ := by ring
        exact hp (by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hpbound)
      have hzero : wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w n s r x Ψ χ p = 0 := by
        change χ q * _ = 0
        rw [hχzero, zero_mul]
      rw [hzero, abs_zero, show B p = 0 from Set.indicator_of_notMem hp _]

end Critical2DKPZ.SHF.Moments
