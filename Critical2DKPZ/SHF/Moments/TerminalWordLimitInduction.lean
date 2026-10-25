/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitFromFirstLetterConvergence
import Mathlib.Tactic

/-! The moving terminal-word limit follows by list induction from the empty-word limit and the stated induction step. -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The empty-word limit and the conditional first-letter limit imply moving terminal limits for all collision words. -/
theorem tendsto_wordTerminalTest_of_consStep (ϑ : ℝ) {h : ℕ}
    (ψ : Fin h → C_c(Plane, ℝ))
    (hCons : ∀ (α : CollisionPair h) (w : List (CollisionPair h))
      (_hw : (α :: w).IsChain (· ≠ ·))
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
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) (α :: w) τ x y).toReal)))
    : ∀ (w : List (CollisionPair h)) (_hw : w.IsChain (· ≠ ·))
    {τ : ℝ} (_hτ : 0 < τ) (nN : ℕ → ℕ)
    (_hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → LatticeConfiguration h) (x : Configuration h)
    (_hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (_hphase : ∀ i, ∀ᶠ N : ℕ in atTop, Even (xN N i 0 + xN N i 1 + (nN N : ℤ)))
    (_hsep : ∀ α ∈ w.head?, x α.1.1 ≠ x α.1.2),
    Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w (nN N) (xN N)
      (fun y => ∏ i, ψ i (y i))) atTop
      (𝓝 (∫ y : Configuration h, (∏ i, ψ i (y i)) *
        (diagramKernel (ϑ - Real.eulerMascheroniConstant) w τ x y).toReal)) := by
  intro w
  induction w with
  | nil =>
      intro _hw τ hτ nN hn xN x hx hphase _hsep
      exact tendsto_wordTerminalTest_nil_tensor (fun N => sigmaSq (criticalBeta ϑ N))
        (ϑ - Real.eulerMascheroniConstant) hτ nN hn xN x hx hphase ψ
  | cons α w ih =>
      intro hw τ hτ nN hn xN x hx hphase hsep
      have hwt : w.IsChain (· ≠ ·) := hw.tail
      exact hCons α w hw (ih hwt) hτ nN hn xN x hx hphase (hsep α (by simp))

end Critical2DKPZ.SHF.Moments
