/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordPotentialDomination
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitClocks
public import Critical2DKPZ.SHF.Moments.WordLimitFirstBlock
public import Critical2DKPZ.SHF.Moments.WordLimitTerminalFirstBlock
import Critical2DKPZ.SHF.Moments.TerminalWordLimitTimeCells
import Critical2DKPZ.SHF.Moments.TerminalWordLimitInduction

/-! Time-boundary, spatial-cutoff, continuum-action and first-letter estimates imply the moving-start terminal-word limit. -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology ENNReal
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Induction on the collision word combines the four cutoff and kernel-action hypotheses into the moving-start terminal limit. -/
theorem tendsto_wordTerminalTest_of_potentialDomination_of_inputs
    (hTimeBoundary : ∀ (ϑ : ℝ) {h : ℕ} (_hD : WordPotentialDomination ϑ h)
          (α : CollisionPair h) (w : List (CollisionPair h)) (_hw : (α :: w).IsChain (· ≠ ·))
          {τ : ℝ} (_hτ : 0 < τ) (nN : ℕ → ℕ)
          (_hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
          (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
          (_hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
          (_hsep : x α.1.1 ≠ x α.1.2)
          (Ψ : Configuration h → ℝ) (M : ℝ) (_hM : 0 ≤ M) (_hΨ : ∀ y, |Ψ y| ≤ M),
      ∀ ε > 0, ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
            ∀ᶠ N : ℕ in atTop,
              |∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
                if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨
                    ((nN N - s - r : ℕ) : ℝ) < η * N then
                  ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) (xN N),
                    wordFirstBlockKernel (criticalBeta ϑ N) α s r (xN N) v *
                      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N - s - r) v Ψ
                else 0| ≤ ε)
    (hSpatialCutoff : ∀ (ϑ : ℝ) {h : ℕ} (_hD : WordPotentialDomination ϑ h)
          (α : CollisionPair h) (w : List (CollisionPair h)) (_hw : (α :: w).IsChain (· ≠ ·))
          {τ η : ℝ} (_hτ : 0 < τ) (_hη : 0 < η)
          (nN : ℕ → ℕ) (_hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
          (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
          (_hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
          (Ψ : Configuration h → ℝ) (M : ℝ) (_hM : 0 ≤ M) (_hΨ : ∀ y, |Ψ y| ≤ M),
      ∀ ε > 0, ∃ χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ),
            (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
            (∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ p, χ p ≠ 0 →
              ‖p‖ ≤ R ∧ ∀ β ∈ w.head?,
                δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) ∧
            ∀ᶠ N : ℕ in atTop,
              |∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
                if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧
                    η * N ≤ ((nN N - s - r : ℕ) : ℝ) then
                  ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
                    (((∏ i, srwKernel s (u i - xN N i)) *
                      collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r u v) *
                      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N - s - r) v Ψ) *
                    (1 - χ ((latticeRepresentative N (u α.1.1),
                               fun i : Spectator α => latticeRepresentative N (u i.1)),
                             (latticeRepresentative N (v α.1.1),
                               fun i : Spectator α => latticeRepresentative N (v i.1))))
                else 0| ≤ ε)
    (hContinuumAction : ∀ (θ : ℝ) {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
          (_hw : (α :: w).IsChain (· ≠ ·)) {τ : ℝ} (_hτ : 0 < τ)
          (x : Configuration h) (_hsep : x α.1.1 ≠ x α.1.2)
          (ψ : Fin h → C_c(Plane, ℝ)),
      let D : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}
          let A : (ℝ × ℝ) → (FusedConfiguration α × FusedConfiguration α) → ℝ :=
            fun q p => incomingKernel α q.1 p.1 x * collisionKernel α θ q.2 p.1 p.2 *
              (∫ y : Configuration h, (∏ i, ψ i (y i)) *
                (diagramKernel θ w (τ - q.1 - q.2) (collisionEmbedding α p.2) y).toReal)
          Integrable (fun y : Configuration h =>
            (∏ i, ψ i (y i)) * (diagramKernel θ (α :: w) τ x y).toReal) ∧
          (∀ q ∈ D, Integrable (A q)) ∧
          IntegrableOn (fun q => ∫ p, A q p) D ∧
          (∫ y : Configuration h, (∏ i, ψ i (y i)) *
            (diagramKernel θ (α :: w) τ x y).toReal) = ∫ q in D, ∫ p, A q p)
    (hConsClosure : ∀
    (_hTimeCells : ∀ {N : ℕ} (_hN : 0 < N) (n : ℕ)
          (F : ℕ → ℕ → ℝ),
      Integrable (fun q : ℝ × ℝ =>
            if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
            then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) ∧
          (∫ q : ℝ × ℝ,
            if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
            then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) =
            (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), F s r) / (N : ℝ)^2)
    (_hTimeBoundary : ∀ (ϑ : ℝ) {h : ℕ} (_hD : WordPotentialDomination ϑ h)
          (α : CollisionPair h) (w : List (CollisionPair h)) (_hw : (α :: w).IsChain (· ≠ ·))
          {τ : ℝ} (_hτ : 0 < τ) (nN : ℕ → ℕ)
          (_hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
          (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
          (_hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
          (_hsep : x α.1.1 ≠ x α.1.2)
          (Ψ : Configuration h → ℝ) (M : ℝ) (_hM : 0 ≤ M) (_hΨ : ∀ y, |Ψ y| ≤ M),
      ∀ ε > 0, ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η < η₀ →
            ∀ᶠ N : ℕ in atTop,
              |∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
                if (s : ℝ) < η * N ∨ (r : ℝ) < η * N ∨
                    ((nN N - s - r : ℕ) : ℝ) < η * N then
                  ∑ v ∈ collisionWordConfigurationEndpointSet (s + r) (xN N),
                    wordFirstBlockKernel (criticalBeta ϑ N) α s r (xN N) v *
                      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N - s - r) v Ψ
                else 0| ≤ ε)
    (_hSpatialCutoff : ∀ (ϑ : ℝ) {h : ℕ} (_hD : WordPotentialDomination ϑ h)
          (α : CollisionPair h) (w : List (CollisionPair h)) (_hw : (α :: w).IsChain (· ≠ ·))
          {τ η : ℝ} (_hτ : 0 < τ) (_hη : 0 < η)
          (nN : ℕ → ℕ) (_hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
          (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
          (_hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
          (Ψ : Configuration h → ℝ) (M : ℝ) (_hM : 0 ≤ M) (_hΨ : ∀ y, |Ψ y| ≤ M),
      ∀ ε > 0, ∃ χ : C_c(FusedConfiguration α × FusedConfiguration α, ℝ),
            (∀ p, 0 ≤ χ p ∧ χ p ≤ 1) ∧
            (∃ R δ : ℝ, 0 ≤ R ∧ 0 < δ ∧ ∀ p, χ p ≠ 0 →
              ‖p‖ ≤ R ∧ ∀ β ∈ w.head?,
                δ ≤ ‖collisionEmbedding α p.2 β.1.2 - collisionEmbedding α p.2 β.1.1‖) ∧
            ∀ᶠ N : ℕ in atTop,
              |∑ s ∈ Finset.Icc 1 (nN N), ∑ r ∈ Finset.range (nN N - s + 1),
                if η * N ≤ (s : ℝ) ∧ η * N ≤ (r : ℝ) ∧
                    η * N ≤ ((nN N - s - r : ℕ) : ℝ) then
                  ∑' u : LatticeConfiguration h, ∑' v : LatticeConfiguration h,
                    (((∏ i, srwKernel s (u i - xN N i)) *
                      collisionWordUndampedPairRunFactor (criticalBeta ϑ N) α r u v) *
                      wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N - s - r) v Ψ) *
                    (1 - χ ((latticeRepresentative N (u α.1.1),
                               fun i : Spectator α => latticeRepresentative N (u i.1)),
                             (latticeRepresentative N (v α.1.1),
                               fun i : Spectator α => latticeRepresentative N (v i.1))))
                else 0| ≤ ε)
    (_hContinuumAction : ∀ (θ : ℝ) {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
          (_hw : (α :: w).IsChain (· ≠ ·)) {τ : ℝ} (_hτ : 0 < τ)
          (x : Configuration h) (_hsep : x α.1.1 ≠ x α.1.2)
          (ψ : Fin h → C_c(Plane, ℝ)),
      let D : Set (ℝ × ℝ) := {q | 0 < q.1 ∧ 0 < q.2 ∧ q.1 + q.2 < τ}
          let A : (ℝ × ℝ) → (FusedConfiguration α × FusedConfiguration α) → ℝ :=
            fun q p => incomingKernel α q.1 p.1 x * collisionKernel α θ q.2 p.1 p.2 *
              (∫ y : Configuration h, (∏ i, ψ i (y i)) *
                (diagramKernel θ w (τ - q.1 - q.2) (collisionEmbedding α p.2) y).toReal)
          Integrable (fun y : Configuration h =>
            (∏ i, ψ i (y i)) * (diagramKernel θ (α :: w) τ x y).toReal) ∧
          (∀ q ∈ D, Integrable (A q)) ∧
          IntegrableOn (fun q => ∫ p, A q p) D ∧
          (∫ y : Configuration h, (∏ i, ψ i (y i)) *
            (diagramKernel θ (α :: w) τ x y).toReal) = ∫ q in D, ∫ p, A q p)
    (ϑ : ℝ) {h : ℕ} (_hD : WordPotentialDomination ϑ h)
    (α : CollisionPair h) (w : List (CollisionPair h)) (_hw : (α :: w).IsChain (· ≠ ·))
    (ψ : Fin h → C_c(Plane, ℝ))
    (_hTail : ∀ {q : ℝ}, 0 < q → ∀ kN : ℕ → ℕ,
      Tendsto (fun N : ℕ => (kN N : ℝ) / N) atTop (𝓝 q) →
      ∀ (yN : ℕ → Fin h → Site) (y : Configuration h),
      (∀ i, Tendsto (fun N => latticeRepresentative N (yN N i)) atTop (𝓝 (y i))) →
      (∀ i, ∀ᶠ N : ℕ in atTop, Even (yN N i 0 + yN N i 1 + (kN N : ℤ))) →
      (∀ β ∈ w.head?, y β.1.1 ≠ y β.1.2) →
      Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (kN N) (yN N)
        (fun z => ∏ i, ψ i (z i))) atTop
        (𝓝 (∫ z : Configuration h, (∏ i, ψ i (z i)) *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) w q y z).toReal)))
    {τ : ℝ} (_hτ : 0 < τ) (nN : ℕ → ℕ)
    (_hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
    (_hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (_hphase : ∀ i, ∀ᶠ N : ℕ in atTop, Even (xN N i 0 + xN N i 1 + (nN N : ℤ)))
    (_hsep : x α.1.1 ≠ x α.1.2),
    Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) (α :: w) (nN N) (xN N)
      (fun y => ∏ i, ψ i (y i))) atTop
      (𝓝 (∫ y : Configuration h, (∏ i, ψ i (y i)) *
        (diagramKernel (ϑ - Real.eulerMascheroniConstant) (α :: w) τ x y).toReal)) )
    (ϑ : ℝ) {h : ℕ}
    (hD : WordPotentialDomination ϑ h) (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·))
    {τ : ℝ} (hτ : 0 < τ) (nN : ℕ → ℕ)
    (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → Fin h → Site) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hphase : ∀ i, ∀ᶠ N : ℕ in atTop, Even (xN N i 0 + xN N i 1 + (nN N : ℤ)))
    (hsep : ∀ α ∈ w.head?, x α.1.1 ≠ x α.1.2)
    (ψ : Fin h → C_c(Plane, ℝ)) :
    Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N) (xN N)
      (fun y => ∏ i, ψ i (y i))) atTop
      (𝓝 (∫ y : Configuration h, (∏ i, ψ i (y i)) *
        (diagramKernel (ϑ - Real.eulerMascheroniConstant) w τ x y).toReal)) := by
  apply tendsto_wordTerminalTest_of_consStep ϑ ψ ?_ w hw hτ nN hn xN x hx hphase hsep
  intro α v hv hTail q hq kN hk yN y hy hparity hfirst
  exact hConsClosure integrable_integral_wordTimeStep hTimeBoundary hSpatialCutoff
    hContinuumAction ϑ hD α v hv ψ hTail hq kN hk yN y hy hparity hfirst

end Critical2DKPZ.SHF.Moments
