/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25TimedRunKernelComposition
public import Critical2DKPZ.Polymer.PathComposition
import Mathlib.Tactic

/-! # Endpoint support bounds for timed CCR25 interaction runs -/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

/-- A timed interaction run can only reach configurations whose individual
replicas have traveled for the total duration of its prescribed gaps. -/
theorem ccr25TimedRunTargetConfigurations_subset_endpoints {h : ℕ}
    (gaps : List ℕ) (z : LatticeConfiguration h) :
    ccr25TimedRunTargetConfigurations gaps z ⊆
      Fintype.piFinset fun i : Fin h =>
        Critical2DKPZ.Polymer.endpoints (z i) gaps.sum := by
  induction gaps generalizing z with
  | nil =>
      intro x hx
      have hx' : x = z := by simpa [ccr25TimedRunTargetConfigurations] using hx
      subst x
      apply Fintype.mem_piFinset.mpr
      intro i
      apply (Critical2DKPZ.Polymer.mem_endpoints_iff (z i) (z i) 0).2
      exact ⟨Fin.elim0, by simp [Critical2DKPZ.walkPosition]⟩
  | cons d ds ih =>
      intro x hx
      obtain ⟨y, hy, hxy⟩ := Finset.mem_biUnion.mp hx
      apply Fintype.mem_piFinset.mpr
      intro i
      have hyi : y i ∈ Critical2DKPZ.Polymer.endpoints (z i) ds.sum :=
        Fintype.mem_piFinset.mp (ih z hy) i
      have hxyi : x i ∈ Critical2DKPZ.Polymer.endpoints (y i) d :=
        Fintype.mem_piFinset.mp hxy i
      obtain ⟨s, hs⟩ :=
        (Critical2DKPZ.Polymer.mem_endpoints_iff (z i) (y i) ds.sum).mp hyi
      obtain ⟨t, ht⟩ :=
        (Critical2DKPZ.Polymer.mem_endpoints_iff (y i) (x i) d).mp hxyi
      have hs' : y i = z i + ∑ j : Fin ds.sum, Critical2DKPZ.srwStep (s j) := by
        rw [← hs, Critical2DKPZ.Polymer.walkPosition_end]
      have ht' : x i = y i + ∑ j : Fin d, Critical2DKPZ.srwStep (t j) := by
        rw [← ht, Critical2DKPZ.Polymer.walkPosition_end]
      apply (Critical2DKPZ.Polymer.mem_endpoints_iff
        (z i) (x i) ((d :: ds).sum)).2
      refine ⟨Fin.append t s, ?_⟩
      change Critical2DKPZ.walkPosition (z i) (Fin.append t s) (d + ds.sum) = x i
      have hfinal : z i + ∑ j : Fin d, Critical2DKPZ.srwStep (t j) +
          ∑ j : Fin ds.sum, Critical2DKPZ.srwStep (s j) = x i := by
        rw [ht', hs']
        abel
      rw [Critical2DKPZ.Polymer.walkPosition_end, Fin.sum_univ_add]
      simpa [add_assoc] using hfinal

end Critical2DKPZ.MomentBounds

end
