/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSampleWindow
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSummandBound
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

/-! # Sampled spatial cutoffs of the first-letter recursion -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped CompactlySupported
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The fused pair of continuum representatives on the two sides of a run. -/
def wordFusedPairRepresentative {h : ℕ} (N k l : ℕ) (α : CollisionPair h)
    (p : FusedConfiguration α × FusedConfiguration α) :=
  (wordFusedPhaseRepresentative N k α p.1, wordFusedPhaseRepresentative N l α p.2)

/-- A compact spatial cutoff of the normalized first-letter summand, evaluated
on the sampled continuum representatives. -/
def wordFirstLetterSpatialIntegrand {h : ℕ} (N : ℕ) (β : ℝ) (α : CollisionPair h)
    (w : List (CollisionPair h)) (n s r : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ)
    (p : FusedConfiguration α × FusedConfiguration α) : ℝ :=
  χ (wordFusedPairRepresentative N (n - s) (n - s - r) α p) *
    wordConsScaledSummand N β α w n s r x
      (wordCollisionPhaseSample N (n - s) α p.1)
      (wordCollisionPhaseSample N (n - s - r) α p.2) Ψ

private theorem measurable_wordFusedPairRepresentative_cutoff {h : ℕ}
    (N k l : ℕ) (α : CollisionPair h)
    (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ)) :
    Measurable (fun p => χ (wordFusedPairRepresentative N k l α p)) := by
  have : SecondCountableTopology (FusedConfiguration α) := by infer_instance
  have : OpensMeasurableSpace (FusedConfiguration α) := by infer_instance
  have hpair : Measurable (wordFusedPairRepresentative N k l α) :=
    ((measurable_wordFusedPhaseRepresentative N k α).comp measurable_fst).prodMk
      ((measurable_wordFusedPhaseRepresentative N l α).comp measurable_snd)
  exact χ.continuous.measurable.comp hpair

private theorem measurable_wordCollisionPhaseSample_pair_comp {h : ℕ}
    (N k l : ℕ) (α : CollisionPair h)
    (F : LatticeConfiguration h → LatticeConfiguration h → ℝ) :
    Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
      F (wordCollisionPhaseSample N k α p.1) (wordCollisionPhaseSample N l α p.2)) := by
  have hlattice : Measurable (fun p : FusedConfiguration α × FusedConfiguration α =>
      (wordCollisionPhaseSample N k α p.1, wordCollisionPhaseSample N l α p.2)) :=
    ((measurable_wordCollisionPhaseSample N k α).comp measurable_fst).prodMk
      ((measurable_wordCollisionPhaseSample N l α).comp measurable_snd)
  exact (measurable_of_countable (Function.uncurry F)).comp hlattice

/-- The spatially cutoff discrete integrand is measurable even for an
arbitrary terminal profile: it factors through countable lattice states. -/
theorem measurable_wordFirstLetterSpatialIntegrand {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n s r : ℕ)
    (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ)
    (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ)) :
    Measurable (wordFirstLetterSpatialIntegrand N β α w n s r x Ψ χ) := by
  unfold wordFirstLetterSpatialIntegrand
  exact (measurable_wordFusedPairRepresentative_cutoff N (n - s) (n - s - r) α χ).mul
    (measurable_wordCollisionPhaseSample_pair_comp N (n - s) (n - s - r) α
      (fun u v => wordConsScaledSummand N β α w n s r x u v Ψ))

/-- A sampled cutoff enforces its spatial-window and separation bounds
exactly, giving a uniform estimate proportional to the cutoff's value. -/
theorem eventually_abs_wordFirstLetterSpatialIntegrand_le
    (ϑ a T R δ : ℝ) (ha : 0 < a) (haT : a ≤ T) (hR : 0 ≤ R) (hδ : 0 < δ)
    {h : ℕ} (hD : WordPotentialDomination ϑ h) (α : CollisionPair h)
    (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·))
    (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ))
    (hχR : ∀ p, χ p ≠ 0 → ‖p‖ ≤ R)
    (hχsep : ∀ p, χ p ≠ 0 → ∀ β ∈ w.head?,
      δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ (n s r : ℕ),
      (n : ℝ) ≤ T * N → a * N ≤ (s : ℝ) → a * N ≤ (r : ℝ) → s + r ≤ n →
      ∀ (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) (M : ℝ),
      0 ≤ M → (∀ y, |Ψ y| ≤ M) → ∀ p : FusedConfiguration α × FusedConfiguration α,
        |wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w n s r x Ψ χ p| ≤
          |χ (wordFusedPairRepresentative N (n - s) (n - s - r) α p)| * C * M := by
  obtain ⟨C, hC, hbound⟩ := eventually_abs_wordConsScaledSummand_interior_bound
    ϑ a T (2 * R) δ ha haT hδ hD α w hw
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_gt_atTop 0] with N hb hN
  intro n s r hn hs hr hfit x Ψ M hM hΨ p
  let q := wordFusedPairRepresentative N (n - s) (n - s - r) α p
  by_cases hq : χ q = 0
  · simp only [wordFirstLetterSpatialIntegrand, q, hq, zero_mul, abs_zero, le_refl]
  have hnorm := hχR q hq
  have hsep : ∀ β ∈ w.head?, δ ≤ ‖latticeRepresentative N
      (wordCollisionPhaseSample N (n - s - r) α p.2 β.1.2 -
        wordCollisionPhaseSample N (n - s - r) α p.2 β.1.1)‖ := by
    intro β hβ
    rw [latticeRepresentative_sub, ← collisionEmbedding_wordFusedPhaseRepresentative,
      ← collisionEmbedding_wordFusedPhaseRepresentative]
    exact hχsep q hq β hβ
  have hcenter := wordCollisionPhaseSample_center_gap_bound hN (n - s) (n - s - r) α p.1 p.2 hR
    ((norm_fst_le q).trans hnorm) ((norm_snd_le q).trans hnorm)
  have hb' := hb n s r hn hs hr ((Nat.cast_le.mpr (show r ≤ n by omega)).trans hn) x _ _
    (wordCollisionPhaseSample_pair N _ α p.1) (wordCollisionPhaseSample_pair N _ α p.2)
    (wordCollisionPhaseSample_run_phase N n s r hfit α p.1 p.2 α.1.1) hcenter hsep Ψ M hM hΨ
  unfold wordFirstLetterSpatialIntegrand
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_left hb' (abs_nonneg _)).trans_eq (by ring)

end Critical2DKPZ.SHF.Moments
