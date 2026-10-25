/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25BoundaryVectorBoundMain
import Mathlib.Tactic

/-! # CCR boundary norms for compact indicator profiles -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.MomentBounds

/-- The finite counting `ℓ²` norm of the unit profile is the square root of
the support cardinality. -/
theorem finiteLpNorm_one_two_eq_sqrt_card {α : Type*}
    (A : Finset α) :
    finiteLpNorm A 2 (fun _ : α => (1 : ℝ)) = Real.sqrt (A.card : ℝ) := by
  unfold finiteLpNorm
  simp [Real.sqrt_eq_rpow]

/-- Uniform `ℓ²` estimate for the time-summed CCR boundary vector generated
by the indicator of a finite site set. -/
theorem finiteLpNorm_hattedBoundary_indicator_le (h : ℕ) (hh : 2 ≤ h) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (L : ℕ) (A : Finset Site)
      (s : Finset (LatticeConfiguration h)) (I : ReplicaPartition h) (_hI : I ≠ ⊥),
      finiteLpNorm s 2
        (fun x => hattedReplicaBoundaryVector L I A
          (fun y => if y ∈ A then (1 : ℝ) else 0) x) ≤
        2 * C * (A.card : ℝ) * (Real.sqrt (A.card : ℝ)) ^ (h - 1) := by
  obtain ⟨C, hC, hbound⟩ := finiteLpNorm_hattedReplicaBoundaryVector_le h hh
  refine ⟨C, hC, ?_⟩
  intro L A s I hI
  let f : Site → ℝ := fun y => if y ∈ A then 1 else 0
  have hf : ∀ y, 0 ≤ f y := by
    intro y
    dsimp [f]
    split_ifs <;> norm_num
  have hboundResult := hbound 0 (by norm_num) L 2 (by norm_num) A f hf s I hI
  have hsum : (∑ y ∈ A, f y * Real.exp (0 * ‖siteToPlane y‖)) = (A.card : ℝ) := by
    simp [f]
  have hnorm : finiteLpNorm A 2
      (fun y => f y * Real.exp (0 * ‖siteToPlane y‖)) =
        Real.sqrt (A.card : ℝ) := by
    calc
      finiteLpNorm A 2
          (fun y => f y * Real.exp (0 * ‖siteToPlane y‖)) =
          finiteLpNorm A 2 (fun _ : Site => (1 : ℝ)) := by
            apply finiteLpNorm_abs_congr
            intro y hy
            simp [f, hy]
      _ = Real.sqrt (A.card : ℝ) := finiteLpNorm_one_two_eq_sqrt_card A
  have hnorm' : finiteLpNorm A 2 f = Real.sqrt (A.card : ℝ) := by
    calc
      finiteLpNorm A 2 f = finiteLpNorm A 2 (fun _ : Site => (1 : ℝ)) := by
        apply finiteLpNorm_abs_congr
        intro y hy
        simp [f, hy]
      _ = Real.sqrt (A.card : ℝ) := finiteLpNorm_one_two_eq_sqrt_card A
  rw [hsum, hnorm] at hboundResult
  norm_num at hboundResult
  have h' : finiteLpNorm s 2
      (fun x => hattedReplicaBoundaryVector L I A f x /
        replicaExponentialWeight 0 x) ≤
        2 * C * (A.card : ℝ) * (Real.sqrt (A.card : ℝ)) ^ (h - 1) := by
    calc
      _ ≤ C * 2 * (A.card : ℝ) * (Real.sqrt (A.card : ℝ)) ^ (h - 1) := by
        nlinarith only [hboundResult]
      _ = _ := by ring
  simpa [f, replicaExponentialWeight] using h'

end Critical2DKPZ.SHF.Moments

end
