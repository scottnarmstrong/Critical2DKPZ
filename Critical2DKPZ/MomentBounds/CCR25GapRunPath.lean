/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25ActiveRunPrefix
public import Critical2DKPZ.MomentBounds.CCR25GapRunEncoding
import Mathlib.Tactic

/-! # Exact active-path factorization by maximal gap runs -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

/-- The recursive path weight indexed by maximal equal-label gap runs. -/
noncomputable def ccr25GapRunPathWeight {h : ℕ} (β : ℝ)
    (previous : ReplicaPartition h) :
    List (CCR25GapRun h) → LatticeConfiguration h → ℝ
  | [], _ => 1
  | run :: runs, z =>
      |replicaPartitionDisorderMoment β run.label| *
        ∑' x : LatticeConfiguration h,
          freeReplicaKernel run.firstGap previous run.label z x *
            ∑' y : LatticeConfiguration h,
              ccr25TimedInteractionRunAbs β run.label run.internalGapsRev x y *
                ccr25GapRunPathWeight β run.label runs y

/-- Encoding an event stream isolates its initial maximal label run, with
the internal gaps stored in the reverse order required by the interaction
kernel recursion. -/
theorem ccr25GapRunEncodeFrom_eq_prefix_drop {h : ℕ}
    (label : ReplicaPartition h) (firstGap : ℕ)
    (internalGapsRev : List ℕ)
    (events : List (ℕ × ReplicaPartition h)) :
    ccr25GapRunEncodeFrom label firstGap internalGapsRev events =
      [⟨label, firstGap,
        ((ccr25ActiveLabelPrefix label events).map Prod.fst).reverse ++
          internalGapsRev⟩] ++
        ccr25GapRunEncode (ccr25ActiveLabelDrop label events) := by
  induction events generalizing internalGapsRev with
  | nil => simp [ccr25GapRunEncodeFrom, ccr25ActiveLabelPrefix,
      ccr25ActiveLabelDrop, ccr25GapRunEncode]
  | cons event events ih =>
      rcases event with ⟨gap, nextLabel⟩
      by_cases hsame : nextLabel = label
      · subst nextLabel
        simpa [ccr25GapRunEncodeFrom, ccr25ActiveLabelPrefix,
          ccr25ActiveLabelDrop, List.map_cons, List.reverse_cons,
          List.append_assoc] using ih (gap :: internalGapsRev)
      · simp [ccr25GapRunEncodeFrom, ccr25ActiveLabelPrefix,
          ccr25ActiveLabelDrop, ccr25GapRunEncode, hsame]

/-- The active run-factorization recursion is exactly the path recursion on
the maximal gap-run encoding. -/
theorem ccr25ActiveRunFactoredPathWeight_eq_gapRunPathWeight {h : ℕ}
    (β : ℝ) :
    ∀ (previous : ReplicaPartition h)
      (events : List (ℕ × ReplicaPartition h)) (z : LatticeConfiguration h),
      ccr25ActiveRunFactoredPathWeight β previous events z =
        ccr25GapRunPathWeight β previous (ccr25GapRunEncode events) z := by
  intro previous events
  have hmain :
      ∀ n, ∀ (previous : ReplicaPartition h)
        (events : List (ℕ × ReplicaPartition h)) (z : LatticeConfiguration h),
        events.length = n →
        ccr25ActiveRunFactoredPathWeight β previous events z =
          ccr25GapRunPathWeight β previous (ccr25GapRunEncode events) z := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro previous events z hlen
        cases events with
        | nil => simp [ccr25ActiveRunFactoredPathWeight,
            ccr25GapRunPathWeight, ccr25GapRunEncode]
        | cons event events =>
            rcases event with ⟨d, I⟩
            let runPrefix := ccr25ActiveLabelPrefix I events
            let rest := ccr25ActiveLabelDrop I events
            have htailLt : rest.length < n := by
              have hdrop := ccr25ActiveLabelDrop_length_le I events
              simp only [List.length_cons] at hlen
              change (ccr25ActiveLabelDrop I events).length < n
              omega
            have hsplit : runPrefix ++ rest = events := by
              simpa [runPrefix, rest] using
                ccr25ActiveLabelPrefix_append_drop I events
            have hlabels : ∀ e ∈ runPrefix, e.2 = I := by
              simpa [runPrefix] using ccr25ActiveLabelPrefix_labels I events
            have htailShape := ccr25ActiveLabelDrop_empty_or_head_ne I events
            have hencode := ccr25GapRunEncodeFrom_eq_prefix_drop I d [] events
            have hencode' :
                ccr25GapRunEncode ((d, I) :: events) =
                  ⟨I, d, ((runPrefix.map Prod.fst).reverse)⟩ ::
                    ccr25GapRunEncode rest := by
              simpa [ccr25GapRunEncode, runPrefix, rest] using hencode
            rw [hencode']
            rw [← hsplit]
            rw [ccr25ActiveRunFactoredPathWeight,
              ccr25ActiveLabelPrefix_append_of_labels I runPrefix rest hlabels htailShape,
              ccr25ActiveLabelDrop_append_of_labels I runPrefix rest hlabels htailShape]
            simp only [ccr25GapRunPathWeight]
            apply congrArg (fun v : ℝ =>
              |replicaPartitionDisorderMoment β I| * v)
            apply tsum_congr
            intro x
            apply congrArg (fun v : ℝ =>
              freeReplicaKernel d previous I z x * v)
            apply tsum_congr
            intro y
            rw [ih rest.length htailLt I rest y rfl]
  intro z
  exact hmain events.length previous events z rfl

end Critical2DKPZ.MomentBounds

end
