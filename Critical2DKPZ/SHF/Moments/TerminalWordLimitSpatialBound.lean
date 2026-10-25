/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitUniformSpatialBound
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitClocks
import Mathlib.Tactic

/-! # Compact-cutoff bounds along moving horizons -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- At fixed interior entrance and run times, the sampled spatial integrand
has a bound proportional to its sampled cutoff, uniformly over every start. -/
theorem eventually_abs_wordFirstLetterSpatialIntegrand_moving_le
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·))
    {τ s r R δ : ℝ} (hs : 0 < s) (hr : 0 < r) (hsr : s + r < τ)
    (hR : 0 ≤ R) (hδ : 0 < δ)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ))
    (hχR : ∀ p, χ p ≠ 0 → ‖p‖ ≤ R)
    (hχsep : ∀ p, χ p ≠ 0 → ∀ β ∈ w.head?,
      δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ (x : LatticeConfiguration h) (Ψ : Configuration h → ℝ) (M : ℝ),
      0 ≤ M → (∀ y, |Ψ y| ≤ M) → ∀ p : FusedConfiguration α × FusedConfiguration α,
        |wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
          (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ x Ψ χ p| ≤
          C * M * |χ (wordFusedPairRepresentative N (nN N - wordEntranceClock N s)
            (wordRemainingClock N (nN N) s r) α p)| := by
  let a := min s r / 2
  let T := τ + 1
  have ha : 0 < a := half_pos (lt_min hs hr)
  have has : a < s := by dsimp [a]; linarith only [min_le_left s r, hs]
  have har : a < r := by dsimp [a]; linarith only [min_le_right s r, hr]
  have hτT : τ < T := by dsimp [T]; linarith
  have haT : a ≤ T := by dsimp [T]; linarith only [has, hsr, hr]
  obtain ⟨C, hC, hbound⟩ := eventually_abs_wordFirstLetterSpatialIntegrand_le
    ϑ a T R δ ha haT hR hδ hD α w hw χ hχR hχsep
  have hsclock := (tendsto_wordEntranceClock_scaled hs).eventually (Ioi_mem_nhds has)
  have hrclock := (tendsto_wordRunClock_scaled hr).eventually (Ioi_mem_nhds har)
  have hnclock := hn.eventually (Iio_mem_nhds hτT)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, hsclock, hrclock, hnclock,
      (wordClocks_interior hs hr hsr nN hn).1, eventually_gt_atTop 0]
      with N hb hsc hrc hnc hfit hN
  intro x Ψ M hM hΨ p
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hns : (nN N : ℝ) ≤ T * N := ((div_lt_iff₀ hNr).mp hnc).le
  have hss : a * N ≤ (wordEntranceClock N s : ℝ) := ((lt_div_iff₀ hNr).mp hsc).le
  have hrs : a * N ≤ ((⌊(N : ℝ) * r⌋₊ : ℕ) : ℝ) := ((lt_div_iff₀ hNr).mp hrc).le
  exact (hb (nN N) (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ hns hss hrs hfit.le
    x Ψ M hM hΨ p).trans_eq (by unfold wordRemainingClock; ring)

/-- The sampled spatial cutoff yields one integrable compact majorant,
uniform along any moving horizon and any sequence of initial states. -/
theorem exists_integrable_majorant_wordFirstLetterSpatialIntegrand
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·))
    {τ s r R δ : ℝ} (hs : 0 < s) (hr : 0 < r) (hsr : s + r < τ)
    (hR : 0 ≤ R) (hδ : 0 < δ)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ))
    (hχR : ∀ p, χ p ≠ 0 → ‖p‖ ≤ R)
    (hχsep : ∀ p, χ p ≠ 0 → ∀ β ∈ w.head?,
      δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖)
    (xN : ℕ → LatticeConfiguration h) (Ψ : Configuration h → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hΨ : ∀ y, |Ψ y| ≤ M) :
    ∃ B : (FusedConfiguration α × FusedConfiguration α) → ℝ, Integrable B ∧
      ∀ᶠ N : ℕ in atTop, ∀ p : FusedConfiguration α × FusedConfiguration α,
        |wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
          (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ (xN N) Ψ χ p| ≤ B p := by
  let a := min s r / 2
  let T := τ + 1
  have ha : 0 < a := half_pos (lt_min hs hr)
  have has : a < s := by dsimp [a]; linarith only [min_le_left s r, hs]
  have har : a < r := by dsimp [a]; linarith only [min_le_right s r, hr]
  have hτT : τ < T := by dsimp [T]; linarith
  have haT : a ≤ T := by dsimp [T]; linarith only [has, hsr, hr]
  obtain ⟨B, hB, hbound⟩ := exists_uniform_integrable_majorant_wordFirstLetterSpatialIntegrand
    ϑ a T ha haT hD α w hw hR hδ χ hχR hχsep Ψ M hM hΨ
  have hsclock := (tendsto_wordEntranceClock_scaled hs).eventually (Ioi_mem_nhds has)
  have hrclock := (tendsto_wordRunClock_scaled hr).eventually (Ioi_mem_nhds har)
  have hnclock := hn.eventually (Iio_mem_nhds hτT)
  refine ⟨B, hB, ?_⟩
  filter_upwards [hbound, hsclock, hrclock, hnclock,
      (wordClocks_interior hs hr hsr nN hn).1, eventually_gt_atTop 0]
      with N hb hsc hrc hnc hfit hN
  intro p
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  exact hb (nN N) (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊
    ((div_lt_iff₀ hNr).mp hnc).le ((lt_div_iff₀ hNr).mp hsc).le
    ((lt_div_iff₀ hNr).mp hrc).le hfit.le (xN N) p

end Critical2DKPZ.SHF.Moments
