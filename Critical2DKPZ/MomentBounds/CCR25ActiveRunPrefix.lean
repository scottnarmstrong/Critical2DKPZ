/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25TimedRunKernelComposition
public import Critical2DKPZ.MomentBounds.CCR25ActivePathCompression
public import Critical2DKPZ.MomentBounds.CCR25StartBoundaryIdentity
public import Critical2DKPZ.MomentBounds.CCR25SequenceMomentProduct
public import Critical2DKPZ.MomentBounds.CCR25RunKernelBound
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Exact factorization of one active collision run -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

private theorem ccr25TimedInteractionRunAbs_nil_pairing {h : ℕ}
    (β : ℝ) (I : ReplicaPartition h) (z : LatticeConfiguration h)
    (f : LatticeConfiguration h → ℝ) :
    (∑' y : LatticeConfiguration h,
      ccr25TimedInteractionRunAbs β I [] z y * f y) =
        if IsCollisionConfiguration I z then f z else 0 := by
  classical
  have hsingle : ∀ y ≠ z,
      ccr25TimedInteractionRunAbs β I [] z y * f y = 0 := by
    intro y hy
    have hzy : z ≠ y := Ne.symm hy
    simp [ccr25TimedInteractionRunAbs, hzy]
  rw [tsum_eq_single z hsingle]
  simp [ccr25TimedInteractionRunAbs]

/-- An initial sequence of active collisions with the same label factors into one timed interaction run paired with the remaining continuation. -/
theorem ccr25ActiveMomentKernelPathWeight_eq_runPrefix {h : ℕ}
    (β : ℝ) (I : ReplicaPartition h) :
    ∀ (d : ℕ) (runPrefix tail : List (ℕ × ReplicaPartition h)),
      (∀ e ∈ runPrefix, e.2 = I) →
      ∀ (previous : ReplicaPartition h) (z : LatticeConfiguration h),
        ccr25ActiveMomentKernelPathWeight β previous
            (((d, I) :: runPrefix) ++ tail) z =
          |replicaPartitionDisorderMoment β I| *
            ∑' x : LatticeConfiguration h,
              freeReplicaKernel d previous I z x *
                ∑' y : LatticeConfiguration h,
                  ccr25TimedInteractionRunAbs β I
                    ((runPrefix.map Prod.fst).reverse) x y *
                    ccr25ActiveMomentKernelPathWeight β I tail y := by
  intro d runPrefix
  induction runPrefix generalizing d with
  | nil =>
      intro tail _ previous z
      change |replicaPartitionDisorderMoment β I| *
          ∑' x : LatticeConfiguration h,
            freeReplicaKernel d previous I z x *
              ccr25ActiveMomentKernelPathWeight β I tail x =
        |replicaPartitionDisorderMoment β I| *
          ∑' x : LatticeConfiguration h,
            freeReplicaKernel d previous I z x *
              ∑' y : LatticeConfiguration h,
                ccr25TimedInteractionRunAbs β I [] x y *
                  ccr25ActiveMomentKernelPathWeight β I tail y
      apply congrArg (fun v : ℝ =>
        |replicaPartitionDisorderMoment β I| * v)
      apply tsum_congr
      intro x
      have hid := ccr25TimedInteractionRunAbs_nil_pairing β I x
        (ccr25ActiveMomentKernelPathWeight β I tail)
      by_cases hx : IsCollisionConfiguration I x
      · rw [hid]
        simp [hx]
      · have hQ : freeReplicaKernel d previous I z x = 0 := by
          simp [freeReplicaKernel, hx]
        rw [hid]
        simp [hx, hQ]
  | cons event runPrefix ih =>
      rcases event with ⟨e, J⟩
      intro tail hevents previous z
      have hJ : J = I := hevents (e, J) (by simp)
      subst J
      have hprefix : ∀ event ∈ runPrefix, event.2 = I := by
        intro event he
        exact hevents event (List.mem_cons_of_mem _ he)
      let later := (runPrefix.map Prod.fst).reverse
      have hinner (x : LatticeConfiguration h) :
          (∑' y : LatticeConfiguration h,
            ccr25TimedInteractionRunAbs β I (later ++ [e]) x y *
              ccr25ActiveMomentKernelPathWeight β I tail y) =
            |replicaPartitionDisorderMoment β I| *
              ∑' y : LatticeConfiguration h,
                freeReplicaKernel e I I x y *
                  ∑' u : LatticeConfiguration h,
                    ccr25TimedInteractionRunAbs β I later y u *
                      ccr25ActiveMomentKernelPathWeight β I tail u := by
        have hcomp := ccr25TimedInteractionRunAbs_append_pairing β I
          later [e] x (ccr25ActiveMomentKernelPathWeight β I tail)
        calc
          _ = ∑' y : LatticeConfiguration h,
                ccr25TimedInteractionRunAbs β I [e] x y *
                  ∑' u : LatticeConfiguration h,
                    ccr25TimedInteractionRunAbs β I later y u *
                      ccr25ActiveMomentKernelPathWeight β I tail u := by
                  simpa [later, List.map_cons, List.reverse_cons] using hcomp
          _ = _ := by
                  rw [← tsum_mul_left]
                  apply tsum_congr
                  intro y
                  rw [ccr25TimedInteractionRunAbs_singleton β I e x y]
                  ring
      have hrev :
          (((e, I) :: runPrefix).map Prod.fst).reverse = later ++ [e] := by
        simp [later, List.map_cons, List.reverse_cons]
      change |replicaPartitionDisorderMoment β I| *
          ∑' x : LatticeConfiguration h,
            freeReplicaKernel d previous I z x *
              ccr25ActiveMomentKernelPathWeight β I
                (((e, I) :: runPrefix) ++ tail) x =
        |replicaPartitionDisorderMoment β I| *
          ∑' x : LatticeConfiguration h,
            freeReplicaKernel d previous I z x *
              ∑' y : LatticeConfiguration h,
                ccr25TimedInteractionRunAbs β I
                  (((e, I) :: runPrefix).map Prod.fst).reverse x y *
                  ccr25ActiveMomentKernelPathWeight β I tail y
      rw [hrev]
      apply congrArg (fun v : ℝ =>
        |replicaPartitionDisorderMoment β I| * v)
      apply tsum_congr
      intro x
      rw [ih e tail hprefix I x, ← hinner x]

/-- The longest initial segment whose event labels equal `I`. -/
noncomputable def ccr25ActiveLabelPrefix {h : ℕ} (I : ReplicaPartition h) :
    List (ℕ × ReplicaPartition h) → List (ℕ × ReplicaPartition h)
  | [] => []
  | event :: events =>
      if event.2 = I then event :: ccr25ActiveLabelPrefix I events else []

/-- Remove the longest initial segment whose event labels equal `I`. -/
noncomputable def ccr25ActiveLabelDrop {h : ℕ} (I : ReplicaPartition h) :
    List (ℕ × ReplicaPartition h) → List (ℕ × ReplicaPartition h)
  | [] => []
  | event :: events =>
      if event.2 = I then ccr25ActiveLabelDrop I events else event :: events

/-- The label-`I` prefix followed by the remainder gives back the event list. -/
theorem ccr25ActiveLabelPrefix_append_drop {h : ℕ}
    (I : ReplicaPartition h) (events : List (ℕ × ReplicaPartition h)) :
    ccr25ActiveLabelPrefix I events ++ ccr25ActiveLabelDrop I events = events := by
  induction events with
  | nil => rfl
  | cons event events ih =>
      by_cases he : event.2 = I <;>
        simp [ccr25ActiveLabelPrefix, ccr25ActiveLabelDrop, he, ih]

/-- Every event of the label-`I` prefix has label `I`. -/
theorem ccr25ActiveLabelPrefix_labels {h : ℕ}
    (I : ReplicaPartition h) (events : List (ℕ × ReplicaPartition h)) :
    ∀ e ∈ ccr25ActiveLabelPrefix I events, e.2 = I := by
  induction events with
  | nil => simp [ccr25ActiveLabelPrefix]
  | cons event events ih =>
      by_cases he : event.2 = I
      · simp only [ccr25ActiveLabelPrefix, he, ite_true, List.mem_cons]
        intro e hee
        rcases hee with rfl | hee
        · exact he
        · exact ih e hee
      · simp [ccr25ActiveLabelPrefix, he]



/-- Dropping the label-`I` prefix does not increase the length of the event list. -/
theorem ccr25ActiveLabelDrop_length_le {h : ℕ}
    (I : ReplicaPartition h) (events : List (ℕ × ReplicaPartition h)) :
    (ccr25ActiveLabelDrop I events).length ≤ events.length := by
  induction events with
  | nil => simp [ccr25ActiveLabelDrop]
  | cons event events ih =>
      by_cases he : event.2 = I
      · simpa [ccr25ActiveLabelDrop, he] using
          Nat.le_trans ih (Nat.le_succ events.length)
      · simp [ccr25ActiveLabelDrop, he]

/-- After dropping the label-`I` prefix, the list is empty or begins with a label other than `I`. -/
theorem ccr25ActiveLabelDrop_empty_or_head_ne {h : ℕ}
    (I : ReplicaPartition h) (events : List (ℕ × ReplicaPartition h)) :
    ccr25ActiveLabelDrop I events = [] ∨
      ∃ event rest, ccr25ActiveLabelDrop I events = event :: rest ∧ event.2 ≠ I := by
  induction events with
  | nil => exact Or.inl rfl
  | cons event events ih =>
      by_cases he : event.2 = I
      · simpa [ccr25ActiveLabelDrop, he] using ih
      · exact Or.inr ⟨event, events, by simp [ccr25ActiveLabelDrop, he], he⟩

/-- The label-`I` prefix of a run of `I`-events followed by a suitable tail is the run. -/
theorem ccr25ActiveLabelPrefix_append_of_labels {h : ℕ}
    (I : ReplicaPartition h) :
    ∀ (runPrefix tail : List (ℕ × ReplicaPartition h)),
      (∀ e ∈ runPrefix, e.2 = I) →
      (tail = [] ∨ ∃ event rest, tail = event :: rest ∧ event.2 ≠ I) →
      ccr25ActiveLabelPrefix I (runPrefix ++ tail) = runPrefix := by
  intro runPrefix
  induction runPrefix with
  | nil =>
      intro tail _ htail
      rcases htail with rfl | ⟨event, rest, rfl, he⟩
      · rfl
      · simp [ccr25ActiveLabelPrefix, he]
  | cons event runPrefix ih =>
      intro tail hlabels htail
      have he : event.2 = I := hlabels event (by simp)
      have hrest : ∀ e ∈ runPrefix, e.2 = I := by
        intro e he'
        exact hlabels e (List.mem_cons_of_mem _ he')
      simp only [List.cons_append, ccr25ActiveLabelPrefix, he, ite_true]
      rw [ih tail hrest htail]

/-- Dropping the label-`I` prefix of such a run followed by `tail` leaves `tail`. -/
theorem ccr25ActiveLabelDrop_append_of_labels {h : ℕ}
    (I : ReplicaPartition h) :
    ∀ (runPrefix tail : List (ℕ × ReplicaPartition h)),
      (∀ e ∈ runPrefix, e.2 = I) →
      (tail = [] ∨ ∃ event rest, tail = event :: rest ∧ event.2 ≠ I) →
      ccr25ActiveLabelDrop I (runPrefix ++ tail) = tail := by
  intro runPrefix
  induction runPrefix with
  | nil =>
      intro tail _ htail
      rcases htail with rfl | ⟨event, rest, rfl, he⟩
      · rfl
      · simp [ccr25ActiveLabelDrop, he]
  | cons event runPrefix ih =>
      intro tail hlabels htail
      have he : event.2 = I := hlabels event (by simp)
      have hrest : ∀ e ∈ runPrefix, e.2 = I := by
        intro e he'
        exact hlabels e (List.mem_cons_of_mem _ he')
      simp only [List.cons_append, ccr25ActiveLabelDrop, he, ite_true]
      exact ih tail hrest htail

/-- The active event path with each maximal same-label segment collapsed to a
single timed interaction run. -/
noncomputable def ccr25ActiveRunFactoredPathWeight {h : ℕ} (β : ℝ)
    (previous : ReplicaPartition h) :
    List (ℕ × ReplicaPartition h) → LatticeConfiguration h → ℝ
  | [], _ => 1
  | (d, I) :: events, z =>
      |replicaPartitionDisorderMoment β I| *
        ∑' x : LatticeConfiguration h,
          freeReplicaKernel d previous I z x *
            ∑' y : LatticeConfiguration h,
              ccr25TimedInteractionRunAbs β I
                ((ccr25ActiveLabelPrefix I events).map Prod.fst).reverse x y *
              ccr25ActiveRunFactoredPathWeight β I
                (ccr25ActiveLabelDrop I events) y
termination_by events => events.length
decreasing_by
  have hdrop := ccr25ActiveLabelDrop_length_le I events
  simp only [List.length_cons]
  omega

/-- The gap-run recursion is an exact regrouping of the active-event path;
it neither drops paths nor replaces timed gaps by summed kernels. -/
theorem ccr25ActiveMomentKernelPathWeight_eq_runFactored {h : ℕ}
    (β : ℝ) :
    ∀ (previous : ReplicaPartition h) (events : List (ℕ × ReplicaPartition h))
      (z : LatticeConfiguration h),
      ccr25ActiveMomentKernelPathWeight β previous events z =
        ccr25ActiveRunFactoredPathWeight β previous events z := by
  intro previous events
  have hmain :
      ∀ n, ∀ (previous : ReplicaPartition h)
        (events : List (ℕ × ReplicaPartition h)) (z : LatticeConfiguration h),
        events.length = n →
          ccr25ActiveMomentKernelPathWeight β previous events z =
            ccr25ActiveRunFactoredPathWeight β previous events z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro previous events z hlen
        cases events with
        | nil =>
            simp [ccr25ActiveMomentKernelPathWeight,
              ccr25ActiveRunFactoredPathWeight]
        | cons event events =>
            rcases event with ⟨d, I⟩
            have htailLt :
                (ccr25ActiveLabelDrop I events).length < n := by
              have hdrop := ccr25ActiveLabelDrop_length_le I events
              simp only [List.length_cons] at hlen
              omega
            let runPrefix := ccr25ActiveLabelPrefix I events
            let tail := ccr25ActiveLabelDrop I events
            have hsplit : runPrefix ++ tail = events := by
              simpa [runPrefix, tail] using
                ccr25ActiveLabelPrefix_append_drop I events
            have hlabels : ∀ e ∈ runPrefix, e.2 = I := by
              simpa [runPrefix] using ccr25ActiveLabelPrefix_labels I events
            have htailShape := ccr25ActiveLabelDrop_empty_or_head_ne I events
            have hrun := ccr25ActiveMomentKernelPathWeight_eq_runPrefix β I d
              runPrefix tail hlabels previous z
            have hrun' :
                ccr25ActiveMomentKernelPathWeight β previous
                    ((d, I) :: (runPrefix ++ tail)) z =
                  |replicaPartitionDisorderMoment β I| *
                    ∑' x : LatticeConfiguration h,
                      freeReplicaKernel d previous I z x *
                        ∑' y : LatticeConfiguration h,
                          ccr25TimedInteractionRunAbs β I
                            ((runPrefix.map Prod.fst).reverse) x y *
                          ccr25ActiveMomentKernelPathWeight β I tail y := by
              simpa only [List.cons_append] using hrun
            rw [← hsplit, hrun']
            rw [ccr25ActiveRunFactoredPathWeight]
            rw [ccr25ActiveLabelPrefix_append_of_labels I runPrefix tail hlabels htailShape,
              ccr25ActiveLabelDrop_append_of_labels I runPrefix tail hlabels htailShape]
            apply congrArg (fun v : ℝ => |replicaPartitionDisorderMoment β I| * v)
            apply tsum_congr
            intro x
            congr 1
            apply tsum_congr
            intro y
            rw [ih tail.length htailLt I tail y rfl]
  intro z
  exact hmain events.length previous events z rfl



end Critical2DKPZ.MomentBounds

end
