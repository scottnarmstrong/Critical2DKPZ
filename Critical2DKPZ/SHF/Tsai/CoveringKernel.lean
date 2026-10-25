/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
import Mathlib.Tactic

/-! # Covering words in the four-particle moment expansion -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The labels touched by a collision word. -/
def wordSupport {n m : ℕ} (w : Fin m → CollisionPair n) : Finset (Fin n) :=
  Finset.univ.biUnion fun k => {(w k).1.1, (w k).1.2}

/-- The sum of diagram kernels whose collision words touch every label, indexed by Tsai's `𝒟_*[n]` in equation (2.20). -/
noncomputable def coveringKernel (n : ℕ) (θ t : ℝ) (x y : Configuration n) : ℝ≥0∞ :=
  ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
    if wordSupport w.1 = Finset.univ then diagramKernel θ (List.ofFn w.1) t x y else 0

/-- The diagram kernels of words with at least two letters. -/
noncomputable def longWordKernel (n : ℕ) (θ t : ℝ) (x y : Configuration n) : ℝ≥0∞ :=
  ∑' m : ℕ, ∑ w : CollisionWord n (m + 2), diagramKernel θ (List.ofFn w.1) t x y

/-- Covering four labels needs at least two collision letters. -/
theorem coveringKernel_four_le_longWordKernel (θ t : ℝ) (x y : Configuration 4) :
    coveringKernel 4 θ t x y ≤ longWordKernel 4 θ t x y := by
  let C : ℕ → ℝ≥0∞ := fun m =>
    ∑ w : CollisionWord 4 (m + 1),
      if wordSupport w.1 = Finset.univ then diagramKernel θ (List.ofFn w.1) t x y else 0
  let D : ℕ → ℝ≥0∞ := fun m =>
    ∑ w : CollisionWord 4 (m + 2), diagramKernel θ (List.ofFn w.1) t x y
  have hsingle (w : CollisionWord 4 1) : wordSupport w.1 ≠ Finset.univ := by
    have hsupport : wordSupport w.1 = {((w.1 0).1).1, ((w.1 0).1).2} := by
      ext i
      simp [wordSupport]
    have hpair : ((w.1 0).1).1 ≠ ((w.1 0).1).2 := ne_of_lt (w.1 0).2
    have hcard : ({((w.1 0).1).1, ((w.1 0).1).2} : Finset (Fin 4)).card = 2 := by
      simp [hpair]
    intro h
    have hbad := congrArg Finset.card (hsupport.symm.trans h)
    simp [hcard] at hbad
  have hzero : C 0 = 0 := by
    dsimp [C]
    apply Finset.sum_eq_zero
    intro w hw
    simp [hsingle w]
  have hle (m : ℕ) : C (m + 1) ≤ D m := by
    dsimp [C, D]
    apply Finset.sum_le_sum
    intro w hw
    by_cases h : wordSupport w.1 = Finset.univ
    · simp [h]
    · simp [h]
  calc
    coveringKernel 4 θ t x y = C 0 + ∑' m : ℕ, C (m + 1) := by
      change (∑' m : ℕ, C m) = C 0 + ∑' m : ℕ, C (m + 1)
      rw [tsum_eq_zero_add' ENNReal.summable]
    _ = ∑' m : ℕ, C (m + 1) := by rw [hzero, zero_add]
    _ ≤ ∑' m : ℕ, D m := ENNReal.tsum_le_tsum hle
    _ = longWordKernel 4 θ t x y := rfl

end Critical2DKPZ.SHF.Tsai

end
