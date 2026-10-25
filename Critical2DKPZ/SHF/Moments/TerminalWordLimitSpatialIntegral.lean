/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSpatialPointwise
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Dominated convergence for the compact spatial first-letter cutoff -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Under shorter-word convergence, compactly cutoff spatial integrals converge at fixed interior times, with integrable discrete and limiting integrands. -/
theorem integrable_tendsto_integral_wordFirstLetterSpatialIntegrand_of_tail
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
    : Integrable (wordContinuumFirstLetterSpatialIntegrand (ϑ - Real.eulerMascheroniConstant)
        τ s r α w x (fun y => ∏ i, ψ i (y i)) χ) ∧
      (∀ᶠ N : ℕ in atTop, Integrable (wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
        (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ (xN N) (fun y => ∏ i, ψ i (y i)) χ)) ∧
      Tendsto (fun N => ∫ p : FusedConfiguration α × FusedConfiguration α,
        wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
          (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ (xN N) (fun y => ∏ i, ψ i (y i)) χ p) atTop
        (𝓝 (∫ p : FusedConfiguration α × FusedConfiguration α,
          wordContinuumFirstLetterSpatialIntegrand (ϑ - Real.eulerMascheroniConstant)
            τ s r α w x (fun y => ∏ i, ψ i (y i)) χ p)) := by
  let F := fun N => wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
    (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ (xN N) (fun y => ∏ i, ψ i (y i)) χ
  let f := wordContinuumFirstLetterSpatialIntegrand (ϑ - Real.eulerMascheroniConstant)
    τ s r α w x (fun y => ∏ i, ψ i (y i)) χ
  have hmeas (N : ℕ) : AEStronglyMeasurable (F N) :=
    (measurable_wordFirstLetterSpatialIntegrand N (criticalBeta ϑ N) α w (nN N)
      (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ (xN N) (fun y => ∏ i, ψ i (y i)) χ).aestronglyMeasurable
  have hpoint (p : FusedConfiguration α × FusedConfiguration α) :
      Tendsto (fun N => F N p) atTop (𝓝 (f p)) :=
    tendsto_wordFirstLetterSpatialIntegrand_of_tail ϑ hD α w hw ψ hTail hs hr hsr hR hδ
      nN hn xN x hx hphase χ hχR hχsep M hM hψ p
  obtain ⟨B, hB, hbound⟩ := exists_integrable_majorant_wordFirstLetterSpatialIntegrand
    ϑ hD α w hw hs hr hsr hR hδ nN hn χ hχR hχsep xN (fun y => ∏ i, ψ i (y i)) M hM hψ
  have hnorm : ∀ᶠ N : ℕ in atTop, ∀ p, ‖F N p‖ ≤ B p := by
    simpa only [Real.norm_eq_abs] using hbound
  have hlimitBound (p : FusedConfiguration α × FusedConfiguration α) : ‖f p‖ ≤ B p :=
    le_of_tendsto (hpoint p).norm (hnorm.mono fun N hb => hb p)
  have hintf : Integrable f := hB.mono'
    (aestronglyMeasurable_of_tendsto_ae atTop hmeas (Eventually.of_forall hpoint))
    (Eventually.of_forall hlimitBound)
  refine ⟨hintf, hnorm.mono (fun N hb => hB.mono' (hmeas N) (Eventually.of_forall hb)), ?_⟩
  exact tendsto_integral_filter_of_dominated_convergence B (Eventually.of_forall hmeas)
    (hnorm.mono fun N hb => Eventually.of_forall hb) hB (Eventually.of_forall hpoint)

end Critical2DKPZ.SHF.Moments
