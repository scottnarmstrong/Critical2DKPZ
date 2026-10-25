/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitLatticeFunctional
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitClocks
import Mathlib.Tactic

/-! Exact spatial and two-time cell representations combine into the terminal-word integral representation. -/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- At positive lattice scales, the finite lattice functional equals its two-time, fused-spatial cell integral with all normalization factors cancelled. Arbitrary spatial weights are allowed, including the constant one. -/
theorem wordFirstLetterLatticeFunctional_time_integral_of_timeCells {h N : ℕ} (hN : 0 < N)
    (n : ℕ)
    (hTimeCells : ∀ F : ℕ → ℕ → ℝ,
      Integrable (fun q : ℝ × ℝ =>
        if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
        then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) ∧
      (∫ q : ℝ × ℝ,
        if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n
        then F (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ else 0) =
        (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), F s r) / (N : ℝ)^2)
    (β : ℝ) (α : CollisionPair h) (w : List (CollisionPair h))
    (x : LatticeConfiguration h) (hx : ∀ i, Even (x i 0 + x i 1 + (n : ℤ)))
    (Ψ : Configuration h → ℝ) (κ : ℕ → ℕ → ℝ)
    (χ : (FusedConfiguration α × FusedConfiguration α) → ℝ) :
    Integrable (fun q : ℝ × ℝ =>
      if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n then
        κ (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ *
          ∫ p : FusedConfiguration α × FusedConfiguration α,
            wordFirstLetterSpatialIntegrand N β α w n (wordEntranceClock N q.1)
              ⌊(N : ℝ) * q.2⌋₊ x Ψ χ p
      else 0) ∧
    (∫ q : ℝ × ℝ,
      if 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ wordEntranceClock N q.1 + ⌊(N : ℝ) * q.2⌋₊ ≤ n then
        κ (wordEntranceClock N q.1) ⌊(N : ℝ) * q.2⌋₊ *
          ∫ p : FusedConfiguration α × FusedConfiguration α,
            wordFirstLetterSpatialIntegrand N β α w n (wordEntranceClock N q.1)
              ⌊(N : ℝ) * q.2⌋₊ x Ψ χ p
      else 0) = wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ := by
  let F := fun s r => κ s r * ∫ p : FusedConfiguration α × FusedConfiguration α,
    wordFirstLetterSpatialIntegrand N β α w n s r x Ψ χ p
  obtain ⟨hint, hi⟩ := hTimeCells F
  refine ⟨hint, hi.trans ?_⟩
  have hsum : (∑ s ∈ Finset.Icc 1 n, ∑ r ∈ Finset.range (n - s + 1), F s r) =
      (N : ℝ)^2 * wordFirstLetterLatticeFunctional N β α w n x Ψ κ χ := by
    rw [wordFirstLetterLatticeFunctional_eq_tsum]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    apply Finset.sum_congr rfl
    intro r hr
    have hfit : s + r ≤ n := by
      have hs' := Finset.mem_Icc.mp hs
      have hr' := Finset.mem_range.mp hr
      omega
    dsimp only [F]
    rw [integral_wordFirstLetterSpatialIntegrand_eq_lattice hN β α w n s r hfit x hx Ψ χ]
    simp only [wordFusedCoordinateRepresentative, wordFusedSiteProjection]
    ring
  rw [hsum]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hNr)

end Critical2DKPZ.SHF.Moments
