/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSummand
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSampling
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitClocks
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitDiagonal
public import Critical2DKPZ.SHF.DeltaBose.PotentialFusedRows
import Mathlib.Tactic

/-! # The pointwise interior step in the moving-word induction -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped BigOperators CompactlySupported Topology
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- Under the shorter-word convergence hypothesis, separation of the next collision pair implies convergence of the interior first-letter integrand. -/
theorem tendsto_wordConsScaledSummand_sampled_of_tail_of_separated
    (ϑ : ℝ) {h : ℕ} (α : CollisionPair h) (w : List (CollisionPair h))
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
    {τ s r : ℝ} (hs : 0 < s) (hr : 0 < r) (hsr : s + r < τ)
    (nN : ℕ → ℕ) (hn : Tendsto (fun N : ℕ => (nN N : ℝ) / N) atTop (𝓝 τ))
    (xN : ℕ → Fin h → Site) (x : Configuration h)
    (hx : ∀ i, Tendsto (fun N => latticeRepresentative N (xN N i)) atTop (𝓝 (x i)))
    (hphase : ∀ i, ∀ᶠ N : ℕ in atTop, Even (xN N i 0 + xN N i 1 + (nN N : ℤ)))
    (u v : FusedConfiguration α)
    (hvsep : ∀ β ∈ w.head?, collisionEmbedding α v β.1.1 ≠ collisionEmbedding α v β.1.2) :
      Tendsto (fun N => wordConsScaledSummand N (criticalBeta ϑ N) α w (nN N)
        (wordEntranceClock N s) ⌊(N : ℝ) * r⌋₊ (xN N)
        (wordCollisionPhaseSample N (nN N - wordEntranceClock N s) α u)
        (wordCollisionPhaseSample N (wordRemainingClock N (nN N) s r) α v)
        (fun y => ∏ i, ψ i (y i))) atTop
        (𝓝 (incomingKernel α s u x * collisionKernel α (ϑ - Real.eulerMascheroniConstant) r u v *
          (∫ y : Configuration h, (∏ i, ψ i (y i)) *
            (diagramKernel (ϑ - Real.eulerMascheroniConstant) w (τ - s - r)
              (collisionEmbedding α v) y).toReal))) := by
  classical
  let aN := fun N => wordEntranceClock N s
  let bN := fun N : ℕ => ⌊(N : ℝ) * r⌋₊
  let mN := fun N => wordRemainingClock N (nN N) s r
  let uN := fun N => wordCollisionPhaseSample N (nN N - aN N) α u
  let vN := fun N => wordCollisionPhaseSample N (mN N) α v
  have hclocks := wordClocks_interior hs hr hsr nN hn
  have hfit : ∀ᶠ N : ℕ in atTop, aN N + bN N < nN N := hclocks.1
  have hu (i : Fin h) : Tendsto (fun N => latticeRepresentative N (uN N i)) atTop
      (𝓝 (collisionEmbedding α u i)) :=
    tendsto_wordCollisionPhaseSample (fun N => nN N - aN N) α u i
  have hv (i : Fin h) : Tendsto (fun N => latticeRepresentative N (vN N i)) atTop
      (𝓝 (collisionEmbedding α v i)) := tendsto_wordCollisionPhaseSample mN α v i
  have huPhase (N : ℕ) (i : Fin h) :
      Even (uN N i 0 + uN N i 1 + ((nN N - aN N : ℕ) : ℤ)) :=
    wordCollisionPhaseSample_phase N (nN N - aN N) α u i
  have hvPhase (N : ℕ) (i : Fin h) : Even (vN N i 0 + vN N i 1 + (mN N : ℤ)) :=
    wordCollisionPhaseSample_phase N (mN N) α v i
  have hentry (i : Fin h) : ∀ᶠ N : ℕ in atTop,
      Even ((uN N i - xN N i) 0 + (uN N i - xN N i) 1 + (aN N : ℤ)) := by
    filter_upwards [hphase i, hfit] with N hp hfitN
    have hup := huPhase N i
    rw [Int.even_iff] at hp hup ⊢
    simp only [Pi.sub_apply]
    omega
  have hrun (i : Fin h) : ∀ᶠ N : ℕ in atTop,
      Even ((vN N i - uN N i) 0 + (vN N i - uN N i) 1 + (bN N : ℤ)) := by
    filter_upwards [hfit] with N hfitN
    have hup := huPhase N i
    have hvp := hvPhase N i
    change Even (vN N i 0 + vN N i 1 + ((nN N - aN N - bN N : ℕ) : ℤ)) at hvp
    rw [Int.even_iff] at hup hvp ⊢
    simp only [Pi.sub_apply]
    omega
  have htailLimit := hTail (show 0 < τ - s - r by linarith only [hsr]) mN hclocks.2
    vN (collisionEmbedding α v) hv (fun i => Eventually.of_forall (fun N => hvPhase N i)) hvsep
  have hpoint := tendsto_wordConsScaledSummand_moving ϑ α w hs hr nN aN bN
    (tendsto_wordEntranceClock_scaled hs) (tendsto_wordRunClock_scaled hr)
    xN uN vN x (collisionEmbedding α u) (collisionEmbedding α v) hx hu hv
    (Eventually.of_forall (fun N => wordCollisionPhaseSample_pair N (nN N - aN N) α u))
    (Eventually.of_forall (fun N => wordCollisionPhaseSample_pair N (mN N) α v))
    hentry hrun (fun y => ∏ i, ψ i (y i)) htailLimit
  simpa only [collisionEmbedding_pair_left, collisionEmbedding_spectator_apply, Prod.mk.eta,
    incomingKernel, aN, bN, mN, uN, vN] using hpoint


end Critical2DKPZ.SHF.Moments
