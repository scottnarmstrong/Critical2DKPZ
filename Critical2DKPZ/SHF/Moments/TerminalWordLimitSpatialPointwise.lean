/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialBound
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitInterior
import Mathlib.Tactic

/-! # Pointwise convergence after compact sampled spatial cutoffs -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The compactly cutoff continuum first-letter integrand. -/
def wordContinuumFirstLetterSpatialIntegrand {h : ℕ} (θ τ s r : ℝ)
    (α : CollisionPair h) (w : List (CollisionPair h)) (x : Configuration h)
    (Ψ : Configuration h → ℝ) (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ))
    (p : FusedConfiguration α × FusedConfiguration α) : ℝ :=
  χ p * (incomingKernel α s p.1 x * collisionKernel α θ r p.1 p.2 *
    (∫ y : Configuration h, Ψ y * (diagramKernel θ w (τ - s - r) (collisionEmbedding α p.2) y).toReal))

/-- Pointwise convergence also holds at zeros of the cutoff, including on the
next-pair diagonal: the uniform cutoff-proportional bound handles those points. -/
theorem tendsto_wordFirstLetterSpatialIntegrand_of_tail
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·))
    (ψ : Fin h → C_c(Plane, ℝ))
    (hTail : ∀ {q : ℝ}, 0 < q → ∀ kN : ℕ → ℕ,
      Tendsto (fun N : ℕ => (kN N : ℝ) / N) atTop (𝓝 q) →
      ∀ (yN : ℕ → Fin h → Site) (y : Configuration h),
      (∀ i, Tendsto (fun N => latticeRepresentative N (yN N i)) atTop (𝓝 (y i))) →
      (∀ i, ∀ᶠ N : ℕ in atTop, Even (yN N i 0 + yN N i 1 + (kN N : ℤ))) →
      (∀ β ∈ w.head?, y β.1.1 ≠ y β.1.2) →
      Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (kN N) (yN N)
        (fun z => ∏ i, ψ i (z i))) atTop
        (𝓝 (∫ z : Configuration h, (∏ i, ψ i (z i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) w q y z).toReal)))
    {τ s r R δ : ℝ} (hs : 0 < s) (hr : 0 < r) (hsr : s + r < τ)
    (hR : 0 ≤ R) (hδ : 0 < δ)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hphase : ∀ i, ∀ᶠ N : ℕ in atTop, Even (xN N i 0 + xN N i 1 + (nN N : ℤ)))
    (χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ))
    (hχR : ∀ p, χ p ≠ 0 → ‖p‖ ≤ R)
    (hχsep : ∀ p, χ p ≠ 0 → ∀ β ∈ w.head?,
      δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖)
    (M : ℝ) (hM : 0 ≤ M) (hψ : ∀ y : Configuration h, |∏ i, ψ i (y i)| ≤ M)
    (p : FusedConfiguration α × FusedConfiguration α) :
    Tendsto (fun N => wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
      (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ (xN N) (fun y => ∏ i, ψ i (y i)) χ p) atTop
      (𝓝 (wordContinuumFirstLetterSpatialIntegrand (ϑ - Real.eulerMascheroniConstant)
        τ s r α w x (fun y => ∏ i, ψ i (y i)) χ p)) := by
  have hsample : Tendsto (fun N => wordFusedPairRepresentative N
      (nN N - wordEntranceClock N s) (wordRemainingClock N (nN N) s r) α p) atTop (𝓝 p) :=
    (tendsto_wordFusedPhaseRepresentative (fun N => nN N - wordEntranceClock N s) α p.1).prodMk_nhds
      (tendsto_wordFusedPhaseRepresentative (fun N => wordRemainingClock N (nN N) s r) α p.2)
  have hcut : Tendsto (fun N => χ (wordFusedPairRepresentative N
      (nN N - wordEntranceClock N s) (wordRemainingClock N (nN N) s r) α p)) atTop (𝓝 (χ p)) :=
    χ.continuous.continuousAt.tendsto.comp hsample
  by_cases hp : χ p = 0
  · obtain ⟨C, hC, hbound⟩ := eventually_abs_wordFirstLetterSpatialIntegrand_moving_le
      ϑ hD α w hw hs hr hsr hR hδ nN hn χ hχR hχsep
    have hzero : Tendsto (fun N => |χ (wordFusedPairRepresentative N
        (nN N - wordEntranceClock N s) (wordRemainingClock N (nN N) s r) α p)|) atTop (𝓝 0) := by
      simpa only [hp, abs_zero] using hcut.abs
    have hnorm := squeeze_zero' (Eventually.of_forall fun N => abs_nonneg
        (wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
          (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ (xN N) (fun y => ∏ i, ψ i (y i)) χ p))
      (hbound.mono fun N hb => hb (xN N) (fun y => ∏ i, ψ i (y i)) M hM hψ p)
      (by simpa only [mul_zero] using hzero.const_mul (C * M))
    have hz : Tendsto (fun N => wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
        (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ (xN N) (fun y => ∏ i, ψ i (y i)) χ p)
        atTop (𝓝 (0 : ℝ)) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [Real.norm_eq_abs] using hnorm
    simpa only [wordContinuumFirstLetterSpatialIntegrand, hp, zero_mul] using hz
  · have hsep : ∀ β ∈ w.head?, collisionEmbedding α p.2 β.1.1 ≠ collisionEmbedding α p.2 β.1.2 := by
      intro β hβ he
      have hd := hχsep p hp β hβ
      rw [he, sub_self, norm_zero] at hd
      exact (not_le_of_gt hδ) hd
    have hpoint := tendsto_wordConsScaledSummand_sampled_of_tail_of_separated
      ϑ α w ψ hTail hs hr hsr nN hn xN x hx hphase p.1 p.2 hsep
    simpa only [wordFirstLetterSpatialIntegrand, wordContinuumFirstLetterSpatialIntegrand,
      wordRemainingClock] using hcut.mul hpoint

end Critical2DKPZ.SHF.Moments
