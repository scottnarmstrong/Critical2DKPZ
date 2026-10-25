/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitEntrance
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitRun
public import Critical2DKPZ.SHF.Moments.WordLimitTerminalGeneral
import Mathlib.Tactic

/-! # Normalized first-letter summands and their moving local limit -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The first-letter summand with its two time-cell and two collision-space
normalizations, before summing times and intermediate configurations. -/
def wordConsScaledSummand {h : ℕ} (N : ℕ) (β : ℝ) (α : CollisionPair h)
    (w : List (CollisionPair h)) (n s r : ℕ) (x u v : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) : ℝ :=
  (((N : ℝ) / 4) ^ h * ∏ i, srwKernel s (u i - x i)) *
    (4 * (N : ℝ) * ((N : ℝ) / 4) ^ (h - 1) * collisionWordUndampedPairRunFactor β α r u v) *
      wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ

/-- The normalization is exactly two microscopic time factors and two fused
spatial factors. This identity also holds at zero lattice scale. -/
theorem wordConsScaledSummand_eq {h : ℕ} (N : ℕ) (β : ℝ) (α : CollisionPair h)
    (w : List (CollisionPair h)) (n s r : ℕ) (x u v : LatticeConfiguration h)
    (Ψ : Configuration h → ℝ) :
    wordConsScaledSummand N β α w n s r x u v Ψ =
      (N : ℝ) ^ 2 * ((N : ℝ) / 4) ^ (2 * (h - 1)) *
        (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
          wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ) := by
  have hh : 1 ≤ h := by have ha := α.2; omega
  have hpow : ((N : ℝ) / 4) ^ h =
      ((N : ℝ) / 4) ^ (h - 1) * ((N : ℝ) / 4) := by
    have he : h = (h - 1) + 1 := by omega
    calc
      _ = ((N : ℝ) / 4) ^ ((h - 1) + 1) := congrArg (fun k : ℕ => ((N : ℝ) / 4) ^ k) he
      _ = _ := pow_succ _ _
  have hcoef : ((N : ℝ) / 4) ^ h *
      (4 * (N : ℝ) * ((N : ℝ) / 4) ^ (h - 1)) =
      (N : ℝ) ^ 2 * ((N : ℝ) / 4) ^ (2 * (h - 1)) := by
    rw [hpow, Nat.mul_comm 2 (h - 1), pow_mul]
    ring
  unfold wordConsScaledSummand
  calc
    _ = (((N : ℝ) / 4) ^ h * (4 * (N : ℝ) * ((N : ℝ) / 4) ^ (h - 1))) *
        (((∏ i, srwKernel s (u i - x i)) * collisionWordUndampedPairRunFactor β α r u v) *
          wordTerminalTest N (sigmaSq β) w (n - s - r) v Ψ) := by ring
    _ = _ := by rw [hcoef]

/-- At interior times and off the next-pair diagonal, shorter-word terminal convergence gives convergence of the normalized first-letter integrand. -/
theorem tendsto_wordConsScaledSummand_moving (ϑ : ℝ) {h : ℕ} (α : CollisionPair h)
    (w : List (CollisionPair h)) {s r q : ℝ} (hs : 0 < s) (hr : 0 < r)
    (nN sN rN : ℕ → ℕ)
    (hsN : Tendsto (fun N : ℕ => (sN N : ℝ) / N) atTop (𝓝 s))
    (hrN : Tendsto (fun N : ℕ => (rN N : ℝ) / N) atTop (𝓝 r))
    (xN uN vN : ℕ → LatticeConfiguration h) (x u v : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hu : ∀ i, Tendsto (fun N => latticeRepresentative N (uN N i)) atTop (𝓝 (u i)))
    (hv : ∀ i, Tendsto (fun N => latticeRepresentative N (vN N i)) atTop (𝓝 (v i)))
    (huPair : ∀ᶠ N : ℕ in atTop, uN N α.1.1 = uN N α.1.2)
    (hvPair : ∀ᶠ N : ℕ in atTop, vN N α.1.1 = vN N α.1.2)
    (hentryPhase : ∀ i, ∀ᶠ N : ℕ in atTop,
      Even ((uN N i - xN N i) 0 + (uN N i - xN N i) 1 + (sN N : ℤ)))
    (hrunPhase : ∀ i, ∀ᶠ N : ℕ in atTop,
      Even ((vN N i - uN N i) 0 + (vN N i - uN N i) 1 + (rN N : ℤ)))
    (Ψ : Configuration h → ℝ)
    (hTail : Tendsto (fun N => wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w
      (nN N - sN N - rN N) (vN N) Ψ) atTop
      (𝓝 (∫ y : Configuration h, Ψ y *
        (diagramKernel (ϑ - Real.eulerMascheroniConstant) w q v y).toReal))) :
    Tendsto (fun N => wordConsScaledSummand N (criticalBeta ϑ N) α w
      (nN N) (sN N) (rN N) (xN N) (uN N) (vN N) Ψ) atTop
      (𝓝 (freeKernel h s x u *
        collisionKernel α (ϑ - Real.eulerMascheroniConstant) r
          (u α.1.1, fun i : Spectator α => u i.1)
          (v α.1.1, fun i : Spectator α => v i.1) *
        (∫ y : Configuration h, Ψ y *
          (diagramKernel (ϑ - Real.eulerMascheroniConstant) w q v y).toReal))) := by
  exact ((tendsto_scaled_wordEntrance_moving hs sN hsN xN uN x u hx hu hentryPhase).mul
    (tendsto_scaled_wordPairRun_moving ϑ α hr rN hrN uN vN u v hu hv huPair hvPair hrunPhase)).mul hTail

end Critical2DKPZ.SHF.Moments
