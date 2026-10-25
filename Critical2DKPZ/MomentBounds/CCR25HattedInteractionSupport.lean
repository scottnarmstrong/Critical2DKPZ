/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25GapCompositions
public import Critical2DKPZ.MomentBounds.CCR25RunBoxSupport
public import Critical2DKPZ.MomentBounds.CCR25SequenceMomentProduct
public import Critical2DKPZ.MomentBounds.CCR25RunKernelBound
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Finite spatial support of the hatted CCR25 interaction operator -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

/-- The finite set of coordinate sites of a replica configuration. -/
noncomputable def ccr25ConfigurationCenterSites {h : ℕ}
    (z : LatticeConfiguration h) : Finset Site :=
  Finset.univ.image z

/-- Every configuration lies in the zero-radius box centered at its own
coordinate sites. -/
theorem ccr25_mem_configBox_centerSites {h : ℕ}
    (z : LatticeConfiguration h) :
    z ∈ configBox h (ccr25ConfigurationCenterSites z) 0 := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_biUnion.mpr
  refine ⟨z i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
  apply Fintype.mem_piFinset.mpr
  intro j
  simp

/-- A hatted free kernel is supported within its cutoff radius from the
starting configuration box. -/
theorem hattedFreeReplicaKernel_zero_of_not_configBox {h : ℕ}
    {A : Finset Site} {r L : ℕ} {I J : ReplicaPartition h}
    {z x : LatticeConfiguration h} (hz : z ∈ configBox h A r)
    (hx : x ∉ configBox h A (r + L)) :
    hattedFreeReplicaKernel L I J z x = 0 := by
  unfold hattedFreeReplicaKernel
  apply Finset.sum_eq_zero
  intro n hn
  have hnL : n + 1 ≤ L := by
    have hn' := Finset.mem_range.mp hn
    omega
  have hx' : x ∉ configBox h A (r + (n + 1)) := by
    intro hbox
    exact hx (ccr25ConfigBox_mono (Nat.add_le_add_left hnL r) hbox)
  rw [freeReplicaKernel_zero_of_not_configBox hz hx' I J]


/-- A hatted free-kernel row multiplied by any function is summable by its
finite walk support. -/
theorem summable_mul_hattedFreeReplicaKernel_row_any {h : ℕ}
    (L : ℕ) (I J : ReplicaPartition h) (z : LatticeConfiguration h)
    (f : LatticeConfiguration h → ℝ) :
    Summable (fun x => hattedFreeReplicaKernel L I J z x * f x) := by
  let A := ccr25ConfigurationCenterSites z
  apply summable_of_ne_finset_zero (s := configBox h A L)
  intro x hx
  have hz := ccr25_mem_configBox_centerSites z
  rw [hattedFreeReplicaKernel_zero_of_not_configBox
    (A := A) (r := 0) hz (by simpa [A, Nat.zero_add] using hx)]
  simp


/-- An interacting kernel of duration n is supported within n walk steps
of its starting configuration box. The proof uses its exact positive-gap
composition expansion. -/
theorem interactingReplicaKernelAbs_zero_of_not_configBox {h : ℕ}
    {A : Finset Site} {r n : ℕ} (β : ℝ) (I : ReplicaPartition h)
    {z x : LatticeConfiguration h} (hz : z ∈ configBox h A r)
    (hx : x ∉ configBox h A (r + n)) :
    interactingReplicaKernelAbs β I n z x = 0 := by
  rw [← ccr25TimedInteractionRunAbs_sum_gapCompositions β I n z x]
  apply Finset.sum_eq_zero
  intro gaps hgaps
  obtain ⟨_, hsum⟩ := ccr25PositiveGapCompositionsRev_spec n gaps hgaps
  have hx' : x ∉ configBox h A (r + gaps.sum) := by
    simpa [hsum] using hx
  exact ccr25TimedInteractionRunAbs_zero_of_not_configBox β I gaps hz hx'

/-- The Laplace-summed interacting kernel is supported within the radius-L
enlargement of its starting configuration box. -/
theorem hattedInteractingReplicaKernelAbs_zero_of_not_configBox {h : ℕ}
    {A : Finset Site} {r L : ℕ} (lam β : ℝ) (I : ReplicaPartition h)
    {z x : LatticeConfiguration h} (hz : z ∈ configBox h A r)
    (hx : x ∉ configBox h A (r + L)) :
    hattedInteractingReplicaKernelAbs L lam β I z x = 0 := by
  unfold hattedInteractingReplicaKernelAbs
  by_cases hdiag : z = x ∧ IsCollisionConfiguration I x
  · have hbox : x ∈ configBox h A (r + L) := by
      simpa [hdiag.1] using
        ccr25ConfigBox_mono (Nat.le_add_right r L) hz
    exact (hx hbox).elim
  · simp only [hdiag, ite_false, zero_add]
    apply Finset.sum_eq_zero
    intro m hm
    have hmL : m + 1 ≤ L := by
      have hm' := Finset.mem_range.mp hm
      omega
    have hx' : x ∉ configBox h A (r + (m + 1)) := by
      intro hbox
      exact hx (ccr25ConfigBox_mono (Nat.add_le_add_left hmL r) hbox)
    rw [interactingReplicaKernelAbs_zero_of_not_configBox
      β I hz hx']
    simp




end Critical2DKPZ.MomentBounds

end
