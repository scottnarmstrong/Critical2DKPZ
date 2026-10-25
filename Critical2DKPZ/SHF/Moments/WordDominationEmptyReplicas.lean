/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.LowReplicaWordIdentities
import Mathlib.Tactic

/-! # The zero-replica collision-word contribution -/

@[expose] public section

noncomputable section

open scoped BigOperators CompactlySupported
open Filter

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose

private instance instUniqueCollisionWordZero : Unique (CollisionWord 0 0) where
  default := ⟨Fin.elim0, by intro i; exact Fin.elim0 i⟩
  uniq w := by
    apply Subtype.ext
    funext i
    exact Fin.elim0 i

private instance collisionWord_zero_succ_isEmpty (m : ℕ) :
    IsEmpty (CollisionWord 0 (m + 1)) := by
  refine ⟨fun w => ?_⟩
  exact (collisionPair_impossible (by omega) (w.1 0)).elim

/-- With zero replicas, the empty collision word contributes exactly one. -/
theorem testedBlockWord_empty_of_zero_replicas (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (φ : Fin 0 → C_c(Plane × Plane, ℝ)) :
    testedBlockWord ϑ N s t φ [] = 1 := by
  classical
  simp [testedBlockWord, blockWordKernel]

/-- The zero-replica word sum consists only of its empty word. -/
theorem sum_abs_testedBlockWord_zero_replicas (ϑ : ℝ) (N : ℕ) (s t : ℝ)
    (m : ℕ) (φ : Fin 0 → C_c(Plane × Plane, ℝ)) :
    (∑ w : CollisionWord 0 m,
      |testedBlockWord ϑ N s t φ (List.ofFn w.1)|) = if m = 0 then 1 else 0 := by
  classical
  cases m with
  | zero =>
      simp [testedBlockWord_empty_of_zero_replicas]
  | succ m =>
      simp

/-- With no replicas, the geometric word bound holds with constant one and ratio zero. -/
theorem testedBlockWord_geometric_le_zero_replicas (ϑ : ℝ) {τ T : ℝ}
    (_hτ : 0 < τ) (φ : Fin 0 → C_c(Plane × Plane, ℝ)) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        ∀ m : ℕ, ∑ w : CollisionWord 0 m,
          |testedBlockWord ϑ N s t φ (List.ofFn w.1)| ≤ C * ρ ^ m := by
  refine ⟨1, 0, by norm_num, by norm_num, by norm_num, ?_⟩
  filter_upwards [Filter.Eventually.of_forall (fun _ : ℕ => True.intro)] with N _
  intro s t hs hst ht m
  rw [sum_abs_testedBlockWord_zero_replicas]
  by_cases hm : m = 0 <;> simp [hm]

end Critical2DKPZ.SHF.Moments

end
