/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitUniformSpatialBound
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitClocksUniform
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

/-! # Compact interior time windows for the first-letter integral -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Keep the entrance, run, and remaining durations uniformly positive. -/
def wordInteriorTimeWindow (τ ε : ℝ) : Set (ℝ × ℝ) :=
  {q | ε ≤ q.1 ∧ ε ≤ q.2 ∧ q.1 + q.2 ≤ τ - ε}

/-- The interior time window is compact, including when it is empty. -/
theorem isCompact_wordInteriorTimeWindow (τ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IsCompact (wordInteriorTimeWindow τ ε) := by
  have hclosed : IsClosed (wordInteriorTimeWindow τ ε) :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  apply ((isCompact_Icc : IsCompact (Set.Icc ε τ)).prod
    (isCompact_Icc : IsCompact (Set.Icc ε τ))).of_isClosed_subset hclosed
  intro q hq
  exact ⟨⟨hq.1, by linarith only [hq.2.1, hq.2.2, hε]⟩,
    ⟨hq.2.1, by linarith only [hq.1, hq.2.2, hε]⟩⟩

private theorem measurable_wordTimeStep (N : ℕ) (F : ℕ → ℕ → ℝ) :
    Measurable (fun q : ℝ × ℝ => F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊) := by
  have hc : Measurable (fun q : ℝ × ℝ => (wordEntranceClock N q.1, ⌊(N : ℝ) * q.2⌋₊)) :=
    (((measurable_const.mul measurable_fst).nat_floor).add_const 1).prodMk
      ((measurable_const.mul measurable_snd).nat_floor)
  exact (measurable_of_countable (Function.uncurry F)).comp hc

/-- The discrete spatial first-letter integral is a measurable step function of its two time variables. -/
theorem measurable_wordFirstLetterSpatialIntegral_time {h : ℕ} (N : ℕ) (β : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (n : ℕ) (x : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ)) :
    Measurable (fun q : ℝ × ℝ => ∫ p : FusedConfiguration α × FusedConfiguration α,
      wordFirstLetterSpatialIntegrand N β α w n (wordEntranceClock N q.1)
        ⌊(N : ℝ) * q.2⌋₊ x Ψ χ p) := by
  exact measurable_wordTimeStep N (fun s r =>
    ∫ p : FusedConfiguration α × FusedConfiguration α,
      wordFirstLetterSpatialIntegrand N β α w n s r x Ψ χ p)

/-- One bound controls all spatial integrals on an entire interior time
window; every spatial integrand in that bound is integrable. -/
theorem eventually_wordFirstLetterSpatialIntegral_timeWindow_bound
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·))
    {τ ε R δ : ℝ} (hε : 0 < ε) (hετ : ε ≤ τ) (hR : 0 ≤ R) (hδ : 0 < δ)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ))
    (hχR : ∀ p, χ p ≠ 0 → ‖p‖ ≤ R)
    (hχsep : ∀ p, χ p ≠ 0 → ∀ β ∈ w.head?,
      δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖)
    (Ψ : Configuration h → ℝ) (M : ℝ) (hM : 0 ≤ M) (hΨ : ∀ y, |Ψ y| ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ q ∈ wordInteriorTimeWindow τ ε,
      ∀ x : LatticeConfiguration h,
        Integrable (wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
          (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ x Ψ χ) ∧
        |∫ p : FusedConfiguration α × FusedConfiguration α,
          wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
            (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ x Ψ χ p| ≤ C := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_integrable_majorant_wordFirstLetterSpatialIntegrand
    ϑ (ε / 2) (τ + 1) (half_pos hε) (by linarith only [hετ, hε])
    hD α w hw hR hδ χ hχR hχsep Ψ M hM hΨ
  refine ⟨∫ p, ‖B p‖, integral_nonneg (fun p => norm_nonneg _), ?_⟩
  filter_upwards [hbound, wordClocks_interior_uniform hε nN hn] with N hb hc
  intro q hq x
  obtain ⟨hs, hr, hfit⟩ := hc.2 q.1 q.2 hq.1 hq.2.1 hq.2.2
  have hnorm (p : FusedConfiguration α × FusedConfiguration α) :
      ‖wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
        (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ x Ψ χ p‖ ≤ ‖B p‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hb (nN N) _ _ hc.1 hs hr hfit.le x p).trans (le_abs_self _)
  exact ⟨hB.norm.mono'
      (measurable_wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
        (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ x Ψ χ).aestronglyMeasurable
      (Eventually.of_forall hnorm),
    by simpa only [Real.norm_eq_abs] using
      norm_integral_le_of_norm_le hB.norm (Eventually.of_forall hnorm)⟩

end Critical2DKPZ.SHF.Moments
