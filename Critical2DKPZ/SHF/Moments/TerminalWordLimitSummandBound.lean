/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.TerminalWordLimitRunBound
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSummand
public import Critical2DKPZ.SHF.Moments.TerminalWordLimitSeparatedScale
import Mathlib.Tactic

/-! # Bounded truncated first-letter integrands -/

@[expose] public noncomputable section

open Filter
open scoped BigOperators
open Critical2DKPZ.Polymer Critical2DKPZ.DeltaBose Critical2DKPZ.MomentBounds

namespace Critical2DKPZ.SHF.Moments

/-- The normalized entrance product is bounded on a positive entrance-time
slab, uniformly in every initial and collision configuration. -/
theorem exists_scaled_wordEntrance_interior_bound {h : ℕ} {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N s : ℕ), a * N ≤ (s : ℝ) →
      ∀ x u : LatticeConfiguration h,
        |((N : ℝ) / 4) ^ h * ∏ i, srwKernel s (u i - x i)| ≤ C := by
  obtain ⟨Q, hQ, hwalk⟩ := exists_scaled_srwKernel_interior_bound ha
  refine ⟨Q ^ h, pow_pos hQ _, fun N s hs x u => ?_⟩
  have heq : ((N : ℝ) / 4) ^ h * (∏ i, srwKernel s (u i - x i)) =
      ∏ i : Fin h, ((N : ℝ) / 4) * srwKernel s (u i - x i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [heq, Finset.abs_prod]
  calc
    _ ≤ ∏ _i : Fin h, Q := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact abs_nonneg _
      · intro i hi
        rw [abs_of_nonneg (mul_nonneg (by positivity) (srwKernel_nonneg _ _))]
        exact hwalk N s hs _
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- A tail with separated first pair has a uniform row bound. The empty tail word
has row mass one and therefore requires no separation. -/
theorem eventually_abs_wordTerminalTest_le_uniform_of_separated_head
    (ϑ : ℝ) {h : ℕ} (hD : WordPotentialDomination ϑ h)
    (T δ : ℝ) (hT : 0 < T) (hδ : 0 < δ)
    (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, (n : ℝ) ≤ T * N →
      ∀ x : LatticeConfiguration h,
      (∀ β ∈ w.head?, δ ≤ ‖latticeRepresentative N (x β.1.2 - x β.1.1)‖) →
      ∀ (Ψ : Configuration h → ℝ) (M : ℝ), 0 ≤ M → (∀ y, |Ψ y| ≤ M) →
        |wordTerminalTest N (sigmaSq (criticalBeta ϑ N)) w n x Ψ| ≤ M * C := by
  cases w with
  | nil =>
      refine ⟨1, zero_lt_one, Eventually.of_forall fun N n hn x hx Ψ M hM hΨ => ?_⟩
      have hb := abs_wordTerminalTest_le_mass N (sigmaSq_nonneg (criticalBeta ϑ N)) [] n x Ψ hΨ
      simpa only [wordTerminalTest_nil_one, mul_one] using hb
  | cons β w =>
      obtain ⟨C, hC, hbound⟩ := eventually_wordTerminalTest_mass_le_uniform_of_potentialDomination
        ϑ hD T δ hT hδ β w hw
      refine ⟨C, hC, hbound.mono fun N hb n hn x hx Ψ M hM hΨ => ?_⟩
      exact (abs_wordTerminalTest_le_mass N (sigmaSq_nonneg (criticalBeta ϑ N)) (β :: w) n x Ψ hΨ).trans
        (mul_le_mul_of_nonneg_left (hb n hn x (hx β (by simp))) hM)

/-- On positive entrance and run-time intervals, bounded terminal profiles and separation from the next collision diagonal give a uniform bound on the normalized first-letter integrand. The constant is independent of the lattice scale, clocks, locations and profiles satisfying these restrictions. -/
theorem eventually_abs_wordConsScaledSummand_interior_bound
    (ϑ a T R δ : ℝ) (ha : 0 < a) (haT : a ≤ T) (hδ : 0 < δ)
    {h : ℕ} (hD : WordPotentialDomination ϑ h) (α : CollisionPair h)
    (w : List (CollisionPair h)) (hw : w.IsChain (· ≠ ·)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ (n s r : ℕ),
      (n : ℝ) ≤ T * N → a * N ≤ (s : ℝ) → a * N ≤ (r : ℝ) → (r : ℝ) ≤ T * N →
      ∀ x u v : LatticeConfiguration h,
      u α.1.1 = u α.1.2 → v α.1.1 = v α.1.2 →
      Even ((r : ℤ) + (v α.1.1 - u α.1.1) 0 + (v α.1.1 - u α.1.1) 1) →
      ‖siteToPlane (v α.1.1 - u α.1.1)‖ ≤ R * Real.sqrt (N : ℝ) →
      (∀ β ∈ w.head?, δ ≤ ‖latticeRepresentative N (v β.1.2 - v β.1.1)‖) →
      ∀ (Ψ : Configuration h → ℝ) (M : ℝ), 0 ≤ M → (∀ y, |Ψ y| ≤ M) →
        |wordConsScaledSummand N (criticalBeta ϑ N) α w n s r x u v Ψ| ≤ C * M := by
  obtain ⟨A, hA, hentry⟩ := exists_scaled_wordEntrance_interior_bound (h := h) ha
  obtain ⟨B, hB, hrun⟩ := eventually_scaled_pairRun_interior_bound ϑ a T R ha haT α
  obtain ⟨D, hDpos, htail⟩ := eventually_abs_wordTerminalTest_le_uniform_of_separated_head
    ϑ hD T δ (ha.trans_le haT) hδ w hw
  refine ⟨A * B * D, by positivity, ?_⟩
  filter_upwards [hrun, htail] with N hr ht
  intro n s r hn hs hrl hrh x u v hu hv hp hz hsep Ψ M hM hΨ
  have hremain : ((n - s - r : ℕ) : ℝ) ≤ T * N :=
    (Nat.cast_le.mpr ((Nat.sub_le _ _).trans (Nat.sub_le _ _))).trans hn
  unfold wordConsScaledSummand
  rw [abs_mul, abs_mul]
  calc
    _ ≤ (A * B) * (M * D) :=
      mul_le_mul (mul_le_mul (hentry N s hs x u) (hr r hrl hrh u v hu hv hp hz)
        (abs_nonneg _) hA.le) (ht _ hremain v hsep Ψ M hM hΨ) (abs_nonneg _) (by positivity)
    _ = _ := by ring

end Critical2DKPZ.SHF.Moments
