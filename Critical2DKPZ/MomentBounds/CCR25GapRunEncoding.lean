/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25ActiveGapTimes
public import Critical2DKPZ.MomentBounds.CCR25SequenceMomentProduct
public import Critical2DKPZ.MomentBounds.CCR25RunKernelBound
public import Critical2DKPZ.MomentBounds.CCR25AbsolutePositivity
public import Mathlib.Tactic
import Mathlib.Tactic

/-! # Run encoding for active collision gaps -/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

/-- One maximal consecutive run in an active gap stream. The internal gaps
are stored in reverse chronological order, matching the interacting-kernel
recursion. -/
structure CCR25GapRun (h : ℕ) where
  label : ReplicaPartition h
  firstGap : ℕ
  internalGapsRev : List ℕ

/-- Encode the remaining active events, continuing the current label run. -/
noncomputable def ccr25GapRunEncodeFrom {h : ℕ} (label : ReplicaPartition h)
    (firstGap : ℕ) (internalGapsRev : List ℕ) :
    List (ℕ × ReplicaPartition h) → List (CCR25GapRun h)
  | [] => [⟨label, firstGap, internalGapsRev⟩]
  | (gap, nextLabel) :: events =>
      if nextLabel = label then
        ccr25GapRunEncodeFrom label firstGap (gap :: internalGapsRev) events
      else
        ⟨label, firstGap, internalGapsRev⟩ ::
          ccr25GapRunEncodeFrom nextLabel gap [] events
termination_by events => events.length

decreasing_by all_goals simp_wf

/-- Group active events into maximal consecutive equal-label runs. -/
noncomputable def ccr25GapRunEncode {h : ℕ} :
    List (ℕ × ReplicaPartition h) → List (CCR25GapRun h)
  | [] => []
  | (gap, label) :: events =>
      ccr25GapRunEncodeFrom label gap [] events

/-- Expand one run to its first event and its internal events. -/
def ccr25GapRunExpandOne {h : ℕ} (run : CCR25GapRun h) :
    List (ℕ × ReplicaPartition h) :=
  (run.firstGap, run.label) ::
    run.internalGapsRev.reverse.map (fun gap => (gap, run.label))

/-- Expand a list of maximal gap runs back to its active event stream. -/
def ccr25GapRunExpand {h : ℕ} : List (CCR25GapRun h) →
    List (ℕ × ReplicaPartition h)
  | [] => []
  | run :: runs => ccr25GapRunExpandOne run ++ ccr25GapRunExpand runs

/-- The run continuation retains exactly the original events, including the
gaps accumulated while the current label was being extended. -/
theorem ccr25GapRunExpand_encodeFrom {h : ℕ} :
    ∀ (label : ReplicaPartition h) (firstGap : ℕ)
      (internalGapsRev : List ℕ) (events : List (ℕ × ReplicaPartition h)),
      ccr25GapRunExpand (ccr25GapRunEncodeFrom label firstGap
        internalGapsRev events) =
        (firstGap, label) ::
          internalGapsRev.reverse.map (fun gap => (gap, label)) ++ events := by
  intro label firstGap internalGapsRev events
  induction events generalizing label firstGap internalGapsRev with
  | nil => simp [ccr25GapRunEncodeFrom, ccr25GapRunExpand,
      ccr25GapRunExpandOne]
  | cons event events ih =>
      rcases event with ⟨gap, nextLabel⟩
      by_cases hsame : nextLabel = label
      · subst nextLabel
        simpa [ccr25GapRunEncodeFrom, ccr25GapRunExpand,
          ccr25GapRunExpandOne, List.reverse_cons, List.map_append,
          List.append_assoc] using
          ih label firstGap (gap :: internalGapsRev)
      · simp only [ccr25GapRunEncodeFrom, hsame, ite_false,
          ccr25GapRunExpand]
        rw [ih nextLabel gap []]
        simp [ccr25GapRunExpandOne]



/-- Encoding and then expanding any active event stream is the
identity. -/
theorem ccr25GapRunExpand_encode {h : ℕ}
    (events : List (ℕ × ReplicaPartition h)) :
    ccr25GapRunExpand (ccr25GapRunEncode events) = events := by
  cases events with
  | nil => rfl
  | cons event events =>
      rcases event with ⟨gap, label⟩
      simpa [ccr25GapRunEncode] using
        ccr25GapRunExpand_encodeFrom label gap [] events

/-- The labels of a continued gap-run encoding agree with ordinary
run-length encoding of its label stream. -/
theorem ccr25GapRunEncodeFrom_labels {h : ℕ} :
    ∀ (label : ReplicaPartition h) (firstGap duration : ℕ)
      (internalGapsRev : List ℕ)
      (events : List (ℕ × ReplicaPartition h)),
      (ccr25GapRunEncodeFrom label firstGap internalGapsRev events).map
          CCR25GapRun.label =
        (ccr25EncodeRunsFrom label duration (events.map Prod.snd)).map Prod.fst := by
  intro label firstGap duration internalGapsRev events
  induction events generalizing label firstGap duration internalGapsRev with
  | nil => simp [ccr25GapRunEncodeFrom, ccr25EncodeRunsFrom]
  | cons event events ih =>
      rcases event with ⟨gap, nextLabel⟩
      by_cases hsame : nextLabel = label
      · subst nextLabel
        simpa [ccr25GapRunEncodeFrom, ccr25EncodeRunsFrom] using
          ih label firstGap (duration + 1) (gap :: internalGapsRev)
      · simpa [ccr25GapRunEncodeFrom, ccr25EncodeRunsFrom, hsame] using
          congrArg (List.cons label) (ih nextLabel gap 1 [])

/-- The labels of encoded runs are exactly the maximal-run compression of
the active event labels. -/
theorem ccr25GapRunEncode_labels {h : ℕ}
    (events : List (ℕ × ReplicaPartition h)) :
    (ccr25GapRunEncode events).map CCR25GapRun.label =
      (ccr25EncodeRuns (events.map Prod.snd)).map Prod.fst := by
  cases events with
  | nil => rfl
  | cons event events =>
      rcases event with ⟨gap, label⟩
      simpa [ccr25GapRunEncode, ccr25EncodeRuns] using
        ccr25GapRunEncodeFrom_labels label gap 1 [] events

/-- Encoding the active gap stream gives the same maximal-run labels as grouping collision events by their occurrence times. -/
theorem ccr25ActiveGapRun_labels_eq_positioned {h n : ℕ}
    (I : Fin n → ReplicaPartition h) :
    (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).map
        CCR25GapRun.label =
      (ccr25PositionedCollisionRuns I).map Prod.fst := by
  rw [ccr25GapRunEncode_labels,
    ccr25ActiveGapEncodeFrom_labels 0 (List.ofFn I)]
  have hfilter : (List.ofFn I).filter (fun J : ReplicaPartition h => J ≠ ⊥) =
      (List.ofFn I).filter ccr25IsActivePartition := by
    have hpred (J : ReplicaPartition h) :
        decide (J ≠ ⊥) = ccr25IsActivePartition J := by
      by_cases hJ : J = ⊥ <;> simp [ccr25IsActivePartition, hJ]
    induction List.ofFn I with
    | nil => rfl
    | cons J Js ih =>
        simp only [List.filter_cons]
        rw [hpred J, ih]
  calc
    (ccr25EncodeRuns ((List.ofFn I).filter (fun J => J ≠ ⊥))).map Prod.fst =
        (ccr25EncodeRuns ((List.ofFn I).filter ccr25IsActivePartition)).map
          Prod.fst := by rw [hfilter]
    _ = (ccr25PositionedCollisionRuns I).map Prod.fst := by
      simpa [ccr25CollisionRunWord] using
        (ccr25PositionedCollisionRuns_labels_eq_collisionRunWord I).symm

/-- A full-support partition sequence gives an admissible CCR25 word directly
from its active gap-run encoding. -/
theorem ccr25ActiveGapRun_admissibleWord {h L : ℕ}
    (hh : 0 < h) {I : Fin L → ReplicaPartition h}
    (hI : I ∈ fullSupportSequences h L) :
    ∃ r, ∃ J : Fin (r + 1) → ReplicaPartition h,
      ccr25AdmissibleWord J ∧
        List.ofFn J =
          (ccr25GapRunEncode (ccr25ActiveGapEncodeFrom 0 (List.ofFn I))).map
            CCR25GapRun.label := by
  obtain ⟨r, J, hJ, hruns⟩ :=
    ccr25PositionedCollisionRuns_admissibleWord hh hI
  refine ⟨r, J, hJ, ?_⟩
  rw [ccr25ActiveGapRun_labels_eq_positioned]
  exact hruns

end Critical2DKPZ.MomentBounds

end
