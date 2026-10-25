/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25PartitionMoments
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! # Factoring finite sums on partition equality configurations -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The least-label representative of the block containing a replica label. -/
noncomputable def canonicalReplicaBlockRepresentative {h : ℕ}
    (I : ReplicaPartition h) (i : Fin h) : Fin h :=
  Classical.choose (exists_replicaBlockRepresentative I i)

/-- The canonical representative belongs to the set of partition-block representatives. -/
theorem canonicalReplicaBlockRepresentative_mem {h : ℕ}
    (I : ReplicaPartition h) (i : Fin h) :
    canonicalReplicaBlockRepresentative I i ∈ replicaBlockRepresentatives I :=
  (Classical.choose_spec (exists_replicaBlockRepresentative I i)).1

/-- A label and its canonical representative lie in the same partition block. -/
theorem canonicalReplicaBlockRepresentative_rel {h : ℕ}
    (I : ReplicaPartition h) (i : Fin h) :
    I.r (canonicalReplicaBlockRepresentative I i) i :=
  (Classical.choose_spec (exists_replicaBlockRepresentative I i)).2

private theorem canonicalReplicaBlockRepresentative_unique {h : ℕ}
    (I : ReplicaPartition h) {r s : Fin h}
    (hr : r ∈ replicaBlockRepresentatives I)
    (hs : s ∈ replicaBlockRepresentatives I) (hrs : I.r r s) : r = s := by
  have hrle := (Finset.mem_filter.mp hr).2 s hrs
  have hsle := (Finset.mem_filter.mp hs).2 r (I.symm' hrs)
  exact Fin.le_antisymm hrle hsle

/-- A canonical block representative represents itself. -/
theorem canonicalReplicaBlockRepresentative_eq_self {h : ℕ}
    (I : ReplicaPartition h) {r : Fin h}
    (hr : r ∈ replicaBlockRepresentatives I) :
    canonicalReplicaBlockRepresentative I r = r := by
  apply canonicalReplicaBlockRepresentative_unique I
    (canonicalReplicaBlockRepresentative_mem I r) hr
  exact canonicalReplicaBlockRepresentative_rel I r

/-- Labels in the same partition block have the same canonical representative. -/
theorem canonicalReplicaBlockRepresentative_eq_of_rel {h : ℕ}
    (I : ReplicaPartition h) {i j : Fin h} (hij : I.r i j) :
    canonicalReplicaBlockRepresentative I i = canonicalReplicaBlockRepresentative I j := by
  apply canonicalReplicaBlockRepresentative_unique I
    (canonicalReplicaBlockRepresentative_mem I i)
    (canonicalReplicaBlockRepresentative_mem I j)
  exact I.trans (canonicalReplicaBlockRepresentative_rel I i)
    (I.trans hij (I.symm' (canonicalReplicaBlockRepresentative_rel I j)))

/-- A finite sum of a product indexed by partition blocks factors into one sum
per block. The source and the configurations are both restricted to endpoint
sets, so every sum is finite. -/
theorem sum_equalityConfigurations_prod_blocks {h : ℕ}
    (I : ReplicaPartition h) (z : LatticeConfiguration h)
    (hz : IsEqualityConfiguration I z) (n : ℕ)
    (f : {r : Fin h // r ∈ replicaBlockRepresentatives I} → Site → ℝ) :
    let T : Fin h → Finset Site := fun i => Critical2DKPZ.Polymer.endpoints (z i) n
    (∑ x ∈ (Fintype.piFinset T).filter (fun x => IsEqualityConfiguration I x),
      ∏ r : {r : Fin h // r ∈ replicaBlockRepresentatives I}, f r (x r.1)) =
      ∏ r : {r : Fin h // r ∈ replicaBlockRepresentatives I},
        ∑ v ∈ T r.1, f r v := by
  classical
  dsimp only
  let E := {r : Fin h // r ∈ replicaBlockRepresentatives I}
  let T : Fin h → Finset Site := fun i => Critical2DKPZ.Polymer.endpoints (z i) n
  let D : Finset (E → Site) := Fintype.piFinset fun r : E => T r.1
  let S : Finset (Fin h → Site) :=
    (Fintype.piFinset T).filter (fun x => IsEqualityConfiguration I x)
  let drop : (Fin h → Site) → E → Site := fun x r => x r.1
  let fill : (E → Site) → Fin h → Site := fun u i =>
    u ⟨canonicalReplicaBlockRepresentative I i,
      canonicalReplicaBlockRepresentative_mem I i⟩
  have hdrop_mem (x : Fin h → Site) (hx : x ∈ S) : drop x ∈ D := by
    apply Fintype.mem_piFinset.mpr
    intro r
    exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp hx).1 r.1
  have hfill_mem (u : E → Site) (hu : u ∈ D) : fill u ∈ S := by
    apply Finset.mem_filter.mpr
    refine ⟨Fintype.mem_piFinset.mpr ?_, ?_⟩
    · intro i
      have hrep : I.r (canonicalReplicaBlockRepresentative I i) i :=
        canonicalReplicaBlockRepresentative_rel I i
      have hzi : z (canonicalReplicaBlockRepresentative I i) = z i := hz _ _ hrep
      have hu' : u ⟨canonicalReplicaBlockRepresentative I i,
          canonicalReplicaBlockRepresentative_mem I i⟩ ∈
          T (canonicalReplicaBlockRepresentative I i) := Fintype.mem_piFinset.mp hu _
      simpa [fill, T, hzi] using hu'
    · intro i j hij
      have hrep := canonicalReplicaBlockRepresentative_eq_of_rel I hij
      have hsub : (⟨canonicalReplicaBlockRepresentative I i,
          canonicalReplicaBlockRepresentative_mem I i⟩ : E) =
          ⟨canonicalReplicaBlockRepresentative I j,
            canonicalReplicaBlockRepresentative_mem I j⟩ := Subtype.ext hrep
      change u ⟨canonicalReplicaBlockRepresentative I i,
          canonicalReplicaBlockRepresentative_mem I i⟩ =
        u ⟨canonicalReplicaBlockRepresentative I j,
          canonicalReplicaBlockRepresentative_mem I j⟩
      rw [hsub]
  have hfill_drop (x : Fin h → Site) (hx : x ∈ S) : fill (drop x) = x := by
    funext i
    have hxi : x (canonicalReplicaBlockRepresentative I i) = x i := by
      exact (Finset.mem_filter.mp hx).2 _ _
        (canonicalReplicaBlockRepresentative_rel I i)
    exact hxi
  have hdrop_fill (u : E → Site) : drop (fill u) = u := by
    funext r
    have hsub : (⟨canonicalReplicaBlockRepresentative I r.1,
        canonicalReplicaBlockRepresentative_mem I r.1⟩ : E) = r :=
      Subtype.ext (canonicalReplicaBlockRepresentative_eq_self I r.2)
    change u ⟨canonicalReplicaBlockRepresentative I r.1,
      canonicalReplicaBlockRepresentative_mem I r.1⟩ = u r
    rw [hsub]
  have hsum_image :
      (∑ x ∈ S, ∏ r : E, f r (drop x r)) =
        ∑ u ∈ D, ∏ r : E, f r (u r) := by
    apply Finset.sum_bij (fun x _ => drop x)
    · intro x hx
      exact hdrop_mem x hx
    · intro x hx y hy heq
      have hfill := congrArg fill heq
      rw [hfill_drop x hx, hfill_drop y hy] at hfill
      exact hfill
    · intro u hu
      refine ⟨fill u, hfill_mem u hu, ?_⟩
      exact hdrop_fill u
    · intro x hx
      rfl
  rw [show (∑ x ∈ (Fintype.piFinset T).filter
        (fun x => IsEqualityConfiguration I x),
      ∏ r : E, f r (x r.1)) = ∑ x ∈ S, ∏ r : E, f r (drop x r) by rfl,
    hsum_image]
  simpa [D, E] using
    (Finset.prod_univ_sum (fun r : E => T r.1) (fun r v => f r v)).symm

end

end Critical2DKPZ.MomentBounds

end
