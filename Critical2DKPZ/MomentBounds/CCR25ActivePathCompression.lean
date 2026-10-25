/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25RunExpansionBase
public import Critical2DKPZ.MomentBounds.CCR25FreeKernelSemigroup
public import Critical2DKPZ.MomentBounds.CCR25SequenceMomentProduct
import Mathlib.Tactic

/-! # Removing inactive times from CCR25 replica paths -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

/-- Encode active collision labels by the number of steps since the previous
active label. Inactive bottom labels increase the pending gap. -/
noncomputable def ccr25ActiveGapEncodeFrom {h : ℕ} (gap : ℕ) :
    List (ReplicaPartition h) → List (ℕ × ReplicaPartition h)
  | [] => []
  | I :: Is =>
      if I = ⊥ then ccr25ActiveGapEncodeFrom (gap + 1) Is
      else (gap + 1, I) :: ccr25ActiveGapEncodeFrom 0 Is

/-- Every retained event gap is positive. -/
theorem ccr25ActiveGapEncodeFrom_gap_pos {h : ℕ} :
    ∀ (gap : ℕ) (Is : List (ReplicaPartition h))
      {e : ℕ × ReplicaPartition h},
      e ∈ ccr25ActiveGapEncodeFrom gap Is → 1 ≤ e.1 := by
  intro gap Is
  induction Is generalizing gap with
  | nil => simp [ccr25ActiveGapEncodeFrom]
  | cons I Is ih =>
      intro e he
      by_cases hbot : I = ⊥
      · subst I
        exact ih (gap + 1) (by simpa [ccr25ActiveGapEncodeFrom] using he)
      · have hencode :
            ccr25ActiveGapEncodeFrom gap (I :: Is) =
              (gap + 1, I) :: ccr25ActiveGapEncodeFrom 0 Is := by
          simp [ccr25ActiveGapEncodeFrom, hbot]
        rw [hencode, List.mem_cons] at he
        rcases he with he | he
        · cases he
          omega
        · exact ih 0 he

/-- The total active gap is at most the length of the consumed sequence plus
the pending gap before it. In particular, at initial gap zero it is bounded
by the original time horizon. -/
theorem ccr25ActiveGapEncodeFrom_sum_le {h : ℕ} :
    ∀ gap : ℕ, ∀ Is : List (ReplicaPartition h),
      ((ccr25ActiveGapEncodeFrom gap Is).map Prod.fst).sum ≤ gap + Is.length := by
  intro gap Is
  induction Is generalizing gap with
  | nil => simp [ccr25ActiveGapEncodeFrom]
  | cons I Is ih =>
      by_cases hbot : I = ⊥
      · subst I
        have hencode :
            ccr25ActiveGapEncodeFrom gap ((⊥ : ReplicaPartition h) :: Is) =
              ccr25ActiveGapEncodeFrom (gap + 1) Is := by
          simp [ccr25ActiveGapEncodeFrom]
        rw [hencode]
        simp only [List.length_cons]
        have hi := ih (gap + 1)
        omega
      · have hencode :
            ccr25ActiveGapEncodeFrom gap (I :: Is) =
              (gap + 1, I) :: ccr25ActiveGapEncodeFrom 0 Is := by
          simp [ccr25ActiveGapEncodeFrom, hbot]
        rw [hencode]
        simp only [List.map_cons, List.sum_cons, List.length_cons]
        have hi := ih 0
        omega



/-- The label projection of the active-gap encoding is precisely the list
obtained by deleting bottom partitions. -/
theorem ccr25ActiveGapEncodeFrom_labels {h : ℕ} :
    ∀ gap : ℕ, ∀ Is : List (ReplicaPartition h),
      (ccr25ActiveGapEncodeFrom gap Is).map Prod.snd = Is.filter (· ≠ ⊥) := by
  intro gap Is
  induction Is generalizing gap with
  | nil => simp [ccr25ActiveGapEncodeFrom]
  | cons I Is ih =>
      by_cases hbot : I = ⊥
      · subst I
        simpa [ccr25ActiveGapEncodeFrom] using ih (gap + 1)
      · have hencode :
            ccr25ActiveGapEncodeFrom gap (I :: Is) =
              (gap + 1, I) :: ccr25ActiveGapEncodeFrom 0 Is := by
          simp [ccr25ActiveGapEncodeFrom, hbot]
        rw [hencode]
        simp [hbot, ih 0]

/-- The free-kernel path weight of a finite list of active events with their
successive time gaps, starting from the specified collision stratum. -/
noncomputable def ccr25ActiveKernelPathWeight {h : ℕ} :
    ReplicaPartition h → List (ℕ × ReplicaPartition h) →
      LatticeConfiguration h → ℝ
  | _, [], _ => 1
  | I, (d, J) :: events, z =>
      ∑' x : LatticeConfiguration h,
        freeReplicaKernel d I J z x * ccr25ActiveKernelPathWeight J events x

/-- The absolute disorder moments are inserted at each retained active event,
with the intervening free replica transitions left explicit. -/
noncomputable def ccr25ActiveMomentKernelPathWeight {h : ℕ} (β : ℝ) :
    ReplicaPartition h → List (ℕ × ReplicaPartition h) →
      LatticeConfiguration h → ℝ
  | _, [], _ => 1
  | I, (d, J) :: events, z =>
      |replicaPartitionDisorderMoment β J| *
        ∑' x : LatticeConfiguration h,
          freeReplicaKernel d I J z x *
            ccr25ActiveMomentKernelPathWeight β J events x

/-- Pulling the run-compressed product of collision moments into the active
path recursion is exact. -/
theorem ccr25ActiveMomentKernelPathWeight_eq_prod_mul_kernel {h : ℕ}
    (β : ℝ) :
    ∀ (I : ReplicaPartition h) (events : List (ℕ × ReplicaPartition h))
      (z : LatticeConfiguration h),
      ccr25ActiveMomentKernelPathWeight β I events z =
        (events.map fun e => |replicaPartitionDisorderMoment β e.2|).prod *
          ccr25ActiveKernelPathWeight I events z := by
  intro I events
  induction events generalizing I with
  | nil => intro z; simp [ccr25ActiveMomentKernelPathWeight, ccr25ActiveKernelPathWeight]
  | cons event events ih =>
      rcases event with ⟨d, J⟩
      intro z
      rw [ccr25ActiveMomentKernelPathWeight, ccr25ActiveKernelPathWeight]
      let P : ℝ := (events.map fun e => |replicaPartitionDisorderMoment β e.2|).prod
      have hfactor :
          (∑' x : LatticeConfiguration h,
            freeReplicaKernel d I J z x * ccr25ActiveMomentKernelPathWeight β J events x) =
            P * ∑' x : LatticeConfiguration h,
              freeReplicaKernel d I J z x * ccr25ActiveKernelPathWeight J events x := by
        calc
          _ = ∑' x : LatticeConfiguration h,
              freeReplicaKernel d I J z x *
                (P * ccr25ActiveKernelPathWeight J events x) := by
                  apply tsum_congr
                  intro x
                  rw [ih J x]
          _ = P * ∑' x : LatticeConfiguration h,
                freeReplicaKernel d I J z x * ccr25ActiveKernelPathWeight J events x := by
                  rw [← tsum_mul_left]
                  congr 1
                  funext x
                  ring
      rw [hfactor]
      simp only [List.map_cons, List.prod_cons]
      ring



private theorem freeReplicaKernel_zero_of_not_terminalCollision {h : ℕ} (n : ℕ)
    (I J : ReplicaPartition h) (z x : LatticeConfiguration h)
    (hx : ¬ IsCollisionConfiguration J x) :
    freeReplicaKernel n I J z x = 0 := by
  classical
  unfold freeReplicaKernel
  apply ite_eq_right
  rintro ⟨_, hJ⟩
  exact hx hJ

/-- For every list, removing bottom labels and replacing each resulting gap by
one free replica kernel preserves the replica path weight. If a previous
active collision label is supplied, the initial configuration must lie in
that collision stratum. -/
theorem replicaPathWeight_eq_activeKernelPathWeight {h : ℕ} :
    ∀ (Is : List (ReplicaPartition h)) (gap : ℕ)
      (I : ReplicaPartition h) (z : LatticeConfiguration h),
      (I = ⊥ ∨ IsCollisionConfiguration I z) →
      replicaPathWeight (List.replicate gap ⊥ ++ Is) z =
        ccr25ActiveKernelPathWeight I (ccr25ActiveGapEncodeFrom gap Is) z := by
  intro Is
  induction Is with
  | nil =>
      intro gap I z hI
      calc
        replicaPathWeight (List.replicate gap ⊥ ++ []) z =
            replicaPathWeight (List.replicate gap ⊥) z := by rw [List.append_nil]
        _ = 1 := replicaPathWeight_replicate_bot_eq_one gap z
        _ = ccr25ActiveKernelPathWeight I (ccr25ActiveGapEncodeFrom gap []) z := by
          simp [ccr25ActiveGapEncodeFrom, ccr25ActiveKernelPathWeight]
  | cons J Is ih =>
      intro gap I z hI
      by_cases hbot : J = ⊥
      · subst J
        have hlist :
            List.replicate gap (⊥ : ReplicaPartition h) ++ ⊥ :: Is =
              List.replicate (gap + 1) ⊥ ++ Is := by
          induction gap with
          | zero => rfl
          | succ n ih =>
              simp only [List.replicate_succ]
              change (⊥ : ReplicaPartition h) ::
                  (List.replicate n ⊥ ++ ⊥ :: Is) =
                (⊥ : ReplicaPartition h) ::
                  (List.replicate (n + 1) ⊥ ++ Is)
              congr 1
        have hencode :
            ccr25ActiveGapEncodeFrom gap ((⊥ : ReplicaPartition h) :: Is) =
              ccr25ActiveGapEncodeFrom (gap + 1) Is := by
          simp [ccr25ActiveGapEncodeFrom]
        rw [hlist, hencode]
        exact ih (gap + 1) I z hI
      · have hencode :
            ccr25ActiveGapEncodeFrom gap (J :: Is) =
              (gap + 1, J) :: ccr25ActiveGapEncodeFrom 0 Is := by
          simp [ccr25ActiveGapEncodeFrom, hbot]
        rw [hencode, ccr25ActiveKernelPathWeight]
        rw [replicaPathWeight_inactive_prefix gap J Is z]
        apply tsum_congr
        intro x
        by_cases hx : IsCollisionConfiguration J x
        · have hkernel : freeReplicaKernel (gap + 1) ⊥ J z x =
              freeReplicaKernel (gap + 1) I J z x := by
            rcases hI with hIbot | hIz
            · subst I
              rfl
            · exact freeReplicaKernel_bot_start_eq_of_collision
                (gap + 1) I J z x hIz
          have htail := ih 0 J x (Or.inr hx)
          have htail' : replicaPathWeight Is x =
              ccr25ActiveKernelPathWeight J
                (ccr25ActiveGapEncodeFrom 0 Is) x := by
            simpa using htail
          calc
            _ = freeReplicaKernel (gap + 1) I J z x * replicaPathWeight Is x := by
              rw [hkernel]
            _ = freeReplicaKernel (gap + 1) I J z x *
                ccr25ActiveKernelPathWeight J
                  (ccr25ActiveGapEncodeFrom 0 Is) x := by rw [htail']
        · have hleft := freeReplicaKernel_zero_of_not_terminalCollision
              (gap + 1) ⊥ J z x hx
          have hright := freeReplicaKernel_zero_of_not_terminalCollision
              (gap + 1) I J z x hx
          rw [hleft, hright]
          simp

/-- The absolute moment-weighted path contribution of a full finite partition
sequence is exactly the product of its positioned run moments times the
path weight with inactive times compressed to free gaps. -/
theorem absMoment_mul_replicaPathWeight_eq_positionedRunProduct
    {h L : ℕ} (β : ℝ) (I : Fin L → ReplicaPartition h)
    (z : LatticeConfiguration h) :
    (∏ k : Fin L, |replicaPartitionDisorderMoment β (I k)|) *
        replicaPathWeight (List.ofFn I) z =
      ((ccr25PositionedCollisionRuns I).map
        (fun run => |replicaPartitionDisorderMoment β run.1| ^ run.2.length)).prod *
        ccr25ActiveKernelPathWeight ⊥
          (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)) z := by
  have hmoment := ccr25_partitionSequence_absMomentProduct_eq_runProduct β I
  have hpath : replicaPathWeight (List.ofFn I) z =
      ccr25ActiveKernelPathWeight ⊥
        (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)) z := by
    simpa only [List.replicate_zero, List.nil_append] using
      (replicaPathWeight_eq_activeKernelPathWeight
        (List.ofFn I) 0 ⊥ z (Or.inl rfl))
  rw [hmoment, hpath]

/-- The collision moments and path transitions can be combined into one
recursive active-event weight. The gaps are the exact durations between
successive active times, with the initial gap measured from time zero. -/
theorem absMoment_mul_replicaPathWeight_eq_activeMomentKernelPathWeight
    {h L : ℕ} (β : ℝ) (I : Fin L → ReplicaPartition h)
    (z : LatticeConfiguration h) :
    (∏ k : Fin L, |replicaPartitionDisorderMoment β (I k)|) *
        replicaPathWeight (List.ofFn I) z =
      ccr25ActiveMomentKernelPathWeight β ⊥
        (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)) z := by
  have hgaplabels :
      (ccr25ActiveGapEncodeFrom 0 (List.ofFn I)).map Prod.snd =
        (List.ofFn I).filter ccr25IsActivePartition :=
    ccr25ActiveGapEncodeFrom_labels 0 (List.ofFn I)
  have hindexLabels :
      (ccr25ActiveIndexedPartitionSequence I).map Prod.snd =
        (List.ofFn I).filter ccr25IsActivePartition := by
    unfold ccr25ActiveIndexedPartitionSequence
    have hmap :
        (ccr25IndexedPartitionSequence I).map Prod.snd = List.ofFn I := by
      rw [ccr25IndexedPartitionSequence, List.map_ofFn]
      rfl
    calc
      _ = ((ccr25IndexedPartitionSequence I).map Prod.snd).filter
            ccr25IsActivePartition := by
              simpa [Function.comp_def] using
                (List.filter_map (p := ccr25IsActivePartition)
                  (f := Prod.snd) (l := ccr25IndexedPartitionSequence I)).symm
      _ = _ := by rw [hmap]
  have hgapMoment :
      ((ccr25ActiveGapEncodeFrom 0 (List.ofFn I)).map
          fun e => |replicaPartitionDisorderMoment β e.2|).prod =
        ((ccr25PositionedCollisionRuns I).map
          fun run => |replicaPartitionDisorderMoment β run.1| ^ run.2.length).prod := by
    calc
      _ = (((ccr25ActiveGapEncodeFrom 0 (List.ofFn I)).map Prod.snd).map
            (fun J => |replicaPartitionDisorderMoment β J|)).prod := by
              rw [List.map_map]
              rfl
      _ = ((((List.ofFn I).filter ccr25IsActivePartition).map
            (fun J => |replicaPartitionDisorderMoment β J|))).prod := by
              rw [hgaplabels]
      _ = (((ccr25ActiveIndexedPartitionSequence I).map Prod.snd).map
            (fun J => |replicaPartitionDisorderMoment β J|)).prod := by
              rw [← hindexLabels]
      _ = ((ccr25PositionedCollisionRuns I).map
            fun run => |replicaPartitionDisorderMoment β run.1| ^ run.2.length).prod := by
              simpa [ccr25PositionedCollisionRuns] using
                ccr25EncodeTimedRuns_prod_eq
                  (fun J => |replicaPartitionDisorderMoment β J|)
                  (ccr25ActiveIndexedPartitionSequence I)
  rw [absMoment_mul_replicaPathWeight_eq_positionedRunProduct]
  rw [← hgapMoment, ccr25ActiveMomentKernelPathWeight_eq_prod_mul_kernel]

end Critical2DKPZ.MomentBounds
