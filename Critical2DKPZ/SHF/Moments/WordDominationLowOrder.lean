/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordDominationEmptyReplicas
public import Critical2DKPZ.SHF.Moments.WordDominationOneReplica
public import Critical2DKPZ.SHF.Moments.LowReplicaWordIdentities
import Mathlib.Tactic

/-! # Geometric word bounds at low replica orders -/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators CompactlySupported

namespace Critical2DKPZ.SHF.Moments

open DeltaBose

/-- The geometric word bound holds with at most one replica. -/
theorem testedBlockWord_geometric_le_of_h_le_one (ϑ : ℝ) {h : ℕ} (hh : h ≤ 1)
    {τ T : ℝ} (hτ : 0 < τ) (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    ∃ C ρ : ℝ, 0 ≤ C ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        ∀ m : ℕ, ∑ w : CollisionWord h m,
          |testedBlockWord ϑ N s t φ (List.ofFn w.1)| ≤ C * ρ ^ m := by
  have hcases : h = 0 ∨ h = 1 := by omega
  rcases hcases with rfl | rfl
  · exact testedBlockWord_geometric_le_zero_replicas ϑ hτ φ
  · exact testedBlockWord_geometric_le_one_replica ϑ hτ φ

/-- At replica orders at most two, the non-pair remainder vanishes and satisfies the asymptotic smallness bound. -/
theorem testedNonpairRemainder_small_of_h_le_two (ϑ : ℝ) {h : ℕ} (hh : h ≤ 2)
    {τ T : ℝ} (_hτ : 0 < τ) (φ : Fin h → C_c(Plane × Plane, ℝ)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
      |testedNonpairRemainder ϑ N s t φ| ≤ ε := by
  intro ε hε
  filter_upwards [Filter.Eventually.of_forall (fun _ : ℕ => True.intro)] with N hN
  intro s t hs hst ht
  rw [testedNonpairRemainder_eq_zero_of_h_le_two ϑ N hh φ]
  simpa using hε.le

end Critical2DKPZ.SHF.Moments

end
