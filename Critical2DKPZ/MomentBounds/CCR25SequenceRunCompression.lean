/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25RunExpansionBase
import Mathlib.Tactic

/-! # Run-length encoding for finite CCR25 collision sequences -/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

variable {α : Type*}

/-- Continue a run-length encoding with a current value and its accumulated
positive duration. -/
def ccr25EncodeRunsFrom [DecidableEq α] (a : α) (duration : ℕ) :
    List α → List (α × ℕ)
  | [] => [(a, duration)]
  | b :: bs =>
      if b = a then ccr25EncodeRunsFrom a (duration + 1) bs
      else (a, duration) :: ccr25EncodeRunsFrom b 1 bs

/-- Run-length encode a finite sequence, retaining each run's value and
duration. -/
def ccr25EncodeRuns [DecidableEq α] : List α → List (α × ℕ)
  | [] => []
  | a :: xs => ccr25EncodeRunsFrom a 1 xs

/-- Consecutive labels in a run sequence are distinct. -/
def ccr25RunAdjacentDistinct : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: runs => x ≠ y ∧ ccr25RunAdjacentDistinct (y :: runs)

/-- The run-label condition is the usual adjacent relation-chain property. -/
theorem ccr25RunAdjacentDistinct_iff_isChain (xs : List α) :
    ccr25RunAdjacentDistinct xs ↔ xs.IsChain (· ≠ ·) := by
  induction xs with
  | nil => simp [ccr25RunAdjacentDistinct]
  | cons a xs ih =>
      cases xs with
      | nil => simp [ccr25RunAdjacentDistinct]
      | cons b xs =>
          simp only [ccr25RunAdjacentDistinct, List.isChain_cons_cons]
          constructor
          · rintro ⟨hab, htail⟩
            exact ⟨hab, (ih).1 htail⟩
          · rintro ⟨hab, htail⟩
            exact ⟨hab, (ih).2 htail⟩

/-- Expand a run-length encoding back to the represented sequence. -/
def ccr25ExpandRuns : List (α × ℕ) → List α
  | [] => []
  | (a, duration) :: runs =>
      List.replicate duration a ++ ccr25ExpandRuns runs

/-- The first run in a continuation always carries its current value. -/
theorem ccr25EncodeRunsFrom_head [DecidableEq α] (a : α) (duration : ℕ)
    (xs : List α) :
    ∃ d rest, ccr25EncodeRunsFrom a duration xs = (a, d) :: rest := by
  induction xs generalizing a duration with
  | nil => exact ⟨duration, [], rfl⟩
  | cons b bs ih =>
      by_cases hb : b = a
      · simpa [ccr25EncodeRunsFrom, hb] using ih a (duration + 1)
      · exact ⟨duration, ccr25EncodeRunsFrom b 1 bs, by
          simp [ccr25EncodeRunsFrom, hb]⟩

private theorem cons_replicate_append (a : α) (duration : ℕ) (xs : List α) :
    a :: (List.replicate duration a ++ xs) =
      List.replicate duration a ++ a :: xs := by
  induction duration with
  | zero => rfl
  | succ n ih =>
      change a :: (a :: (List.replicate n a ++ xs)) =
        a :: (List.replicate n a ++ a :: xs)
      congr 1

/-- The run-length continuation expands to the original tail, prefixed by the
already accumulated part of the current run. -/
theorem ccr25ExpandRuns_encodeFrom [DecidableEq α] (a : α) (duration : ℕ)
    (xs : List α) :
    ccr25ExpandRuns (ccr25EncodeRunsFrom a duration xs) =
      List.replicate duration a ++ xs := by
  induction xs generalizing a duration with
  | nil => simp [ccr25EncodeRunsFrom, ccr25ExpandRuns]
  | cons b bs ih =>
      by_cases hb : b = a
      · subst b
        simp [ccr25EncodeRunsFrom, ih,
          List.replicate_succ, cons_replicate_append]
      · simp [ccr25EncodeRunsFrom, ccr25ExpandRuns, hb, ih,
          List.replicate_one]

/-- Run-length encoding leaves no equal labels next to each other. -/
theorem ccr25EncodeRunsFrom_adjacentDistinct [DecidableEq α] (a : α)
    (duration : ℕ) (xs : List α) :
    ccr25RunAdjacentDistinct ((ccr25EncodeRunsFrom a duration xs).map Prod.fst) := by
  induction xs generalizing a duration with
  | nil => simp [ccr25EncodeRunsFrom, ccr25RunAdjacentDistinct]
  | cons b bs ih =>
      by_cases hb : b = a
      · simpa [ccr25EncodeRunsFrom, hb] using ih a (duration + 1)
      · obtain ⟨d, rest, hhead⟩ := ccr25EncodeRunsFrom_head b 1 bs
        simp only [ccr25EncodeRunsFrom, hb, hhead]
        refine ⟨Ne.symm hb, ?_⟩
        simpa [hhead] using ih b 1

/-- The run-length encoding of any sequence has pairwise-distinct adjacent
run values. -/
theorem ccr25EncodeRuns_adjacentDistinct [DecidableEq α] (xs : List α) :
    ccr25RunAdjacentDistinct ((ccr25EncodeRuns xs).map Prod.fst) := by
  cases xs with
  | nil => simp [ccr25EncodeRuns, ccr25RunAdjacentDistinct]
  | cons a xs =>
      exact ccr25EncodeRunsFrom_adjacentDistinct a 1 xs

/-- Expanding the run-length encoding recovers the original sequence. -/
theorem ccr25ExpandRuns_encode [DecidableEq α] (xs : List α) :
    ccr25ExpandRuns (ccr25EncodeRuns xs) = xs := by
  cases xs with
  | nil => rfl
  | cons a xs =>
      simpa [ccr25EncodeRuns] using
        (ccr25ExpandRuns_encodeFrom a 1 xs)

/-- Every encoded run has positive duration. -/
theorem ccr25EncodeRunsFrom_duration_pos [DecidableEq α] (a : α)
    (duration : ℕ) (xs : List α) (hduration : 0 < duration)
    {run : α × ℕ} (hrun : run ∈ ccr25EncodeRunsFrom a duration xs) :
    0 < run.2 := by
  induction xs generalizing a duration with
  | nil =>
      have heq : run = (a, duration) := by
        simpa [ccr25EncodeRunsFrom] using hrun
      simpa [heq] using hduration
  | cons b bs ih =>
      by_cases hb : b = a
      · have hrun' : run ∈ ccr25EncodeRunsFrom a (duration + 1) bs := by
          simpa [ccr25EncodeRunsFrom, hb] using hrun
        exact ih a (duration + 1) (by omega) hrun'
      · have hcase : run = (a, duration) ∨
            run ∈ ccr25EncodeRunsFrom b 1 bs := by
          simpa [ccr25EncodeRunsFrom, hb] using hrun
        rcases hcase with heq | hrun'
        · simpa [heq] using hduration
        · exact ih b 1 (by omega) hrun'

/-- Every run in a nonempty sequence's encoding has positive duration. -/
theorem ccr25EncodeRuns_duration_pos [DecidableEq α] {xs : List α}
    {run : α × ℕ} (hrun : run ∈ ccr25EncodeRuns xs) : 0 < run.2 := by
  cases xs with
  | nil => simp [ccr25EncodeRuns] at hrun
  | cons a xs =>
      exact ccr25EncodeRunsFrom_duration_pos a 1 xs (by norm_num) hrun

/-- A run's value occurs in the expanded encoding. -/
theorem ccr25RunValue_mem_expandRuns {run : α × ℕ}
    {runs : List (α × ℕ)} (hrun : run ∈ runs) (hpos : 0 < run.2) :
    run.1 ∈ ccr25ExpandRuns runs := by
  induction runs with
  | nil => simp at hrun
  | cons head runs ih =>
      rcases List.mem_cons.mp hrun with heq | hrun'
      · subst run
        apply List.mem_append.mpr
        left
        exact List.mem_replicate.mpr ⟨Nat.ne_of_gt hpos, rfl⟩
      · apply List.mem_append.mpr
        right
        exact ih hrun'

/-- The value of every run in an encoding appears in the encoded sequence. -/
theorem ccr25EncodeRuns_value_mem [DecidableEq α] {xs : List α}
    {run : α × ℕ} (hrun : run ∈ ccr25EncodeRuns xs) : run.1 ∈ xs := by
  have hx := ccr25RunValue_mem_expandRuns hrun
    (ccr25EncodeRuns_duration_pos hrun)
  rw [ccr25ExpandRuns_encode] at hx
  exact hx

/-- Every value in an expanded run list is the value of one of its runs. -/
theorem ccr25Value_mem_expandRuns (x : α) (runs : List (α × ℕ))
    (hx : x ∈ ccr25ExpandRuns runs) :
    ∃ run ∈ runs, run.1 = x := by
  induction runs with
  | nil => simp [ccr25ExpandRuns] at hx
  | cons run runs ih =>
      rcases run with ⟨a, duration⟩
      simp only [ccr25ExpandRuns, List.mem_append] at hx
      rcases hx with hx | hx
      · have hxa : x = a := (List.mem_replicate.mp hx).2
        exact ⟨(a, duration), List.mem_cons_self, hxa.symm⟩
      · obtain ⟨run, hruns, hrun⟩ := ih hx
        exact ⟨run, List.mem_cons_of_mem _ hruns, hrun⟩

/-- Every value in a sequence belongs to a run in its run-length encoding. -/
theorem ccr25EncodeRuns_mem_value [DecidableEq α] {x : α} {xs : List α}
    (hx : x ∈ xs) :
    ∃ run ∈ ccr25EncodeRuns xs, run.1 = x := by
  have hx' : x ∈ ccr25ExpandRuns (ccr25EncodeRuns xs) := by
    rw [ccr25ExpandRuns_encode]
    exact hx
  exact ccr25Value_mem_expandRuns x (ccr25EncodeRuns xs) hx'

/-- The indicator of a nontrivial partition, used to remove times without a
collision. -/
noncomputable def ccr25IsActivePartition {h : ℕ}
    (I : ReplicaPartition h) : Bool := by
  classical
  exact decide (I ≠ ⊥)

/-- The compressed sequence of collision runs, with its full durations. -/
noncomputable def ccr25CollisionRunWord {h : ℕ}
    (xs : List (ReplicaPartition h)) : List (ReplicaPartition h × ℕ) := by
  classical
  exact ccr25EncodeRuns (xs.filter ccr25IsActivePartition)

private theorem not_inCollisionBlock_bot {h : ℕ} (a : Fin h) :
    ¬ InCollisionBlock (⊥ : ReplicaPartition h) a := by
  rintro ⟨b, hba, hab⟩
  have heq : a = b := by simpa [Setoid.bot_def] using hab
  exact hba heq.symm


/-- Collision-run labels are all nontrivial and adjacent labels are distinct,
as required by CCR25's admissible words. -/
theorem ccr25CollisionRunWord_admissibleShape {h : ℕ}
    (xs : List (ReplicaPartition h)) :
    (∀ run ∈ ccr25CollisionRunWord xs, run.1 ≠ ⊥) ∧
      ccr25RunAdjacentDistinct ((ccr25CollisionRunWord xs).map Prod.fst) := by
  classical
  constructor
  · intro run hrun
    change run ∈ ccr25EncodeRuns (xs.filter ccr25IsActivePartition) at hrun
    have hvalue : run.1 ∈ xs.filter ccr25IsActivePartition :=
      ccr25EncodeRuns_value_mem hrun
    simpa [ccr25IsActivePartition] using (List.mem_filter.mp hvalue).2
  · simpa [ccr25CollisionRunWord] using
      ccr25EncodeRuns_adjacentDistinct
        (xs.filter ccr25IsActivePartition)


/-- Encode events with both a time stamp and a partition label, retaining the
time stamps in each constant-label run. -/
def ccr25EncodeTimedRunsFrom [DecidableEq α] (a : α) (times : List ℕ) :
    List (ℕ × α) → List (α × List ℕ)
  | [] => [(a, times)]
  | (n, b) :: events =>
      if b = a then ccr25EncodeTimedRunsFrom a (times ++ [n]) events
      else (a, times) :: ccr25EncodeTimedRunsFrom b [n] events

/-- Run-length encode a time-stamped sequence while retaining every event
time in the corresponding run. -/
def ccr25EncodeTimedRuns [DecidableEq α] : List (ℕ × α) → List (α × List ℕ)
  | [] => []
  | (n, a) :: events => ccr25EncodeTimedRunsFrom a [n] events

/-- Expand time-stamped runs to their event sequence. -/
def ccr25ExpandTimedRuns : List (α × List ℕ) → List (ℕ × α)
  | [] => []
  | (a, times) :: runs =>
      times.map (fun n => (n, a)) ++ ccr25ExpandTimedRuns runs

/-- The event-time projection of expanded timed runs is the concatenation of
their occurrence-time lists. -/
theorem ccr25ExpandTimedRuns_timeProjection
    (runs : List (α × List ℕ)) :
    (ccr25ExpandTimedRuns runs).map Prod.fst =
      (runs.map Prod.snd).flatten := by
  induction runs with
  | nil => rfl
  | cons run runs ih =>
      rcases run with ⟨a, times⟩
      simp [ccr25ExpandTimedRuns, ih, Function.comp_def]

/-- Expanding a timed-run continuation recovers the input events. -/
theorem ccr25ExpandTimedRuns_encodeFrom [DecidableEq α] (a : α)
    (times : List ℕ) (events : List (ℕ × α)) :
    ccr25ExpandTimedRuns (ccr25EncodeTimedRunsFrom a times events) =
      times.map (fun n => (n, a)) ++ events := by
  induction events generalizing a times with
  | nil => simp [ccr25EncodeTimedRunsFrom, ccr25ExpandTimedRuns]
  | cons event events ih =>
      rcases event with ⟨n, b⟩
      by_cases hb : b = a
      · subst b
        simp [ccr25EncodeTimedRunsFrom, ih, List.map_append, List.append_assoc]
      · simp [ccr25EncodeTimedRunsFrom, ccr25ExpandTimedRuns, hb, ih]

/-- Every run retains at least one time when the initial time list is
nonempty. -/
theorem ccr25EncodeTimedRunsFrom_times_nonempty [DecidableEq α] (a : α)
    (times : List ℕ) (events : List (ℕ × α)) (htimes : times ≠ []) :
    ∀ run ∈ ccr25EncodeTimedRunsFrom a times events, run.2 ≠ [] := by
  induction events generalizing a times with
  | nil =>
      intro run hrun
      have heq : run = (a, times) := by
        simpa [ccr25EncodeTimedRunsFrom] using hrun
      simpa [heq] using htimes
  | cons event events ih =>
      rcases event with ⟨n, b⟩
      by_cases hb : b = a
      · intro run hrun
        have hrun' : run ∈ ccr25EncodeTimedRunsFrom a (times ++ [n]) events := by
          simpa [ccr25EncodeTimedRunsFrom, hb] using hrun
        exact ih a (times ++ [n]) (by simp) run hrun'
      · intro run hrun
        have hcase : run = (a, times) ∨
            run ∈ ccr25EncodeTimedRunsFrom b [n] events := by
          simpa [ccr25EncodeTimedRunsFrom, hb] using hrun
        rcases hcase with heq | hrun'
        · simpa [heq] using htimes
        · exact ih b [n] (by simp) run hrun'

/-- Every run in a timed-run encoding has a nonempty list of occurrence
times. -/
theorem ccr25EncodeTimedRuns_times_nonempty [DecidableEq α]
    {events : List (ℕ × α)} {run : α × List ℕ}
    (hrun : run ∈ ccr25EncodeTimedRuns events) : run.2 ≠ [] := by
  cases events with
  | nil => simp [ccr25EncodeTimedRuns] at hrun
  | cons event events =>
      rcases event with ⟨n, a⟩
      exact ccr25EncodeTimedRunsFrom_times_nonempty a [n] events (by simp)
        run (by simpa [ccr25EncodeTimedRuns] using hrun)

/-- If the event stream is strictly time ordered, each run's occurrence-time
list is strictly time ordered as well. -/
theorem ccr25EncodeTimedRunsFrom_times_pairwise [DecidableEq α] (a : α)
    (times : List ℕ) (events : List (ℕ × α))
    (htimes : times.Pairwise (· < ·))
    (hevents : (events.map Prod.fst).Pairwise (· < ·))
    (hbefore : ∀ t ∈ times, ∀ event ∈ events, t < event.1) :
    ∀ run ∈ ccr25EncodeTimedRunsFrom a times events,
      run.2.Pairwise (· < ·) := by
  induction events generalizing a times with
  | nil =>
      intro run hrun
      have heq : run = (a, times) := by
        simpa [ccr25EncodeTimedRunsFrom] using hrun
      simpa [heq] using htimes
  | cons event events ih =>
      rcases event with ⟨n, b⟩
      have hevents' : (n :: events.map Prod.fst).Pairwise (· < ·) := by
        simpa using hevents
      rcases List.pairwise_cons.mp hevents' with ⟨hnEvents, htail⟩
      by_cases hb : b = a
      · intro run hrun
        have hrun' : run ∈ ccr25EncodeTimedRunsFrom a (times ++ [n]) events := by
          simpa [ccr25EncodeTimedRunsFrom, hb] using hrun
        have htimes' : (times ++ [n]).Pairwise (· < ·) := by
          rw [List.pairwise_append]
          refine ⟨htimes, by simp, ?_⟩
          intro t ht u hu
          have hu' : u = n := by simpa using hu
          subst u
          exact hbefore t ht (n, b) (by simp)
        have hbefore' : ∀ t ∈ times ++ [n], ∀ event ∈ events, t < event.1 := by
          intro t ht event hevent
          rcases List.mem_append.mp ht with ht | ht
          · exact hbefore t ht event (List.mem_cons_of_mem _ hevent)
          · have htn : t = n := by simpa using ht
            subst t
            exact hnEvents event.1 (List.mem_map.mpr ⟨event, hevent, rfl⟩)
        exact ih a (times ++ [n]) htimes' htail hbefore' run hrun'
      · intro run hrun
        have hcase : run = (a, times) ∨
            run ∈ ccr25EncodeTimedRunsFrom b [n] events := by
          simpa [ccr25EncodeTimedRunsFrom, hb] using hrun
        rcases hcase with heq | hrun'
        · simpa [heq] using htimes
        · have hbefore' : ∀ t ∈ [n], ∀ event ∈ events, t < event.1 := by
            intro t ht event hevent
            have htn : t = n := by simpa using ht
            subst t
            exact hnEvents event.1 (List.mem_map.mpr ⟨event, hevent, rfl⟩)
          exact ih b [n] (by simp) htail hbefore' run hrun'

/-- If the input event times are strictly ordered, the occurrence times in
each encoded run remain strictly ordered. -/
theorem ccr25EncodeTimedRuns_times_pairwise [DecidableEq α]
    {events : List (ℕ × α)}
    (hevents : (events.map Prod.fst).Pairwise (· < ·)) :
    ∀ run ∈ ccr25EncodeTimedRuns events, run.2.Pairwise (· < ·) := by
  cases events with
  | nil => simp [ccr25EncodeTimedRuns] at *
  | cons event events =>
      rcases event with ⟨n, a⟩
      have hevents' : (n :: events.map Prod.fst).Pairwise (· < ·) := by
        simpa using hevents
      rcases List.pairwise_cons.mp hevents' with ⟨hnEvents, htail⟩
      have hbefore : ∀ t ∈ [n], ∀ event ∈ events, t < event.1 := by
        intro t ht event hevent
        have htn : t = n := by simpa using ht
        subst t
        exact hnEvents event.1 (List.mem_map.mpr ⟨event, hevent, rfl⟩)
      intro run hrun
      exact ccr25EncodeTimedRunsFrom_times_pairwise a [n] events
        (by simp) htail hbefore run
        (by simpa [ccr25EncodeTimedRuns] using hrun)

/-- Expanding the timed-run encoding recovers every time-stamped event. -/
theorem ccr25ExpandTimedRuns_encode [DecidableEq α]
    (events : List (ℕ × α)) :
    ccr25ExpandTimedRuns (ccr25EncodeTimedRuns events) = events := by
  cases events with
  | nil => rfl
  | cons event events =>
      rcases event with ⟨n, a⟩
      simpa [ccr25EncodeTimedRuns] using
        (ccr25ExpandTimedRuns_encodeFrom a [n] events)

/-- The label projection of a timed continuation agrees with ordinary
run-length encoding of the projected label sequence. -/
theorem ccr25EncodeTimedRuns_labelsFrom [DecidableEq α] (a : α)
    (times : List ℕ) (events : List (ℕ × α)) :
    (ccr25EncodeTimedRunsFrom a times events).map Prod.fst =
      (ccr25EncodeRunsFrom a times.length (events.map Prod.snd)).map Prod.fst := by
  induction events generalizing a times with
  | nil => simp [ccr25EncodeTimedRunsFrom, ccr25EncodeRunsFrom]
  | cons event events ih =>
      rcases event with ⟨n, b⟩
      by_cases hb : b = a
      · subst b
        simp [ccr25EncodeTimedRunsFrom, ccr25EncodeRunsFrom, ih]
      · simpa [ccr25EncodeTimedRunsFrom, ccr25EncodeRunsFrom, hb] using
          (ih b [n])

/-- The timed encoding and ordinary run encoding have the same label list. -/
theorem ccr25EncodeTimedRuns_labels [DecidableEq α]
    (events : List (ℕ × α)) :
    (ccr25EncodeTimedRuns events).map Prod.fst =
      (ccr25EncodeRuns (events.map Prod.snd)).map Prod.fst := by
  cases events with
  | nil => rfl
  | cons event events =>
      rcases event with ⟨n, a⟩
      simpa [ccr25EncodeTimedRuns, ccr25EncodeRuns] using
        (ccr25EncodeTimedRuns_labelsFrom a [n] events)

/-- Label lists of timed runs are adjacent-distinct. -/
theorem ccr25EncodeTimedRuns_adjacentDistinct [DecidableEq α]
    (events : List (ℕ × α)) :
    ccr25RunAdjacentDistinct ((ccr25EncodeTimedRuns events).map Prod.fst) := by
  rw [ccr25EncodeTimedRuns_labels]
  exact ccr25EncodeRuns_adjacentDistinct (events.map Prod.snd)

/-- Every label in a time-stamped sequence is present in its timed-run
encoding. -/
theorem ccr25EncodeTimedRuns_mem_label [DecidableEq α] {a : α}
    {events : List (ℕ × α)}
    (ha : a ∈ events.map Prod.snd) :
    ∃ run ∈ ccr25EncodeTimedRuns events, run.1 = a := by
  obtain ⟨run, hrun, hvalue⟩ := ccr25EncodeRuns_mem_value ha
  have hlabel : a ∈ (ccr25EncodeTimedRuns events).map Prod.fst := by
    rw [ccr25EncodeTimedRuns_labels]
    exact List.mem_map.mpr ⟨run, hrun, hvalue⟩
  obtain ⟨run, hrun, hvalue⟩ := List.mem_map.mp hlabel
  exact ⟨run, hrun, hvalue⟩

/-- Every label carried by an encoded timed run appeared in the original event
sequence. -/
theorem ccr25EncodeTimedRuns_label_memSource [DecidableEq α]
    {run : α × List ℕ} {events : List (ℕ × α)}
    (hrun : run ∈ ccr25EncodeTimedRuns events) :
    run.1 ∈ events.map Prod.snd := by
  have hlabel : run.1 ∈
      (ccr25EncodeRuns (events.map Prod.snd)).map Prod.fst := by
    rw [← ccr25EncodeTimedRuns_labels]
    exact List.mem_map.mpr ⟨run, hrun, rfl⟩
  obtain ⟨encodedRun, hencodedRun, hvalue⟩ := List.mem_map.mp hlabel
  have hsource : encodedRun.1 ∈ events.map Prod.snd :=
    ccr25EncodeRuns_value_mem hencodedRun
  simpa [hvalue] using hsource

/-- The time-indexed partition sequence, with the source's one-based collision
time convention. -/
def ccr25IndexedPartitionSequence {h n : ℕ}
    (I : Fin n → ReplicaPartition h) : List (ℕ × ReplicaPartition h) :=
  List.ofFn fun k : Fin n => (k.val + 1, I k)

/-- Collision time stamps in the indexed sequence are strictly increasing. -/
theorem ccr25IndexedPartitionSequence_times_pairwise {h n : ℕ}
    (I : Fin n → ReplicaPartition h) :
    (ccr25IndexedPartitionSequence I).map Prod.fst |>.Pairwise (· < ·) := by
  rw [List.pairwise_map, ccr25IndexedPartitionSequence, List.pairwise_ofFn]
  intro i j hij
  simp
  omega

/-- Time-indexed collision events after removing times with no collision. -/
noncomputable def ccr25ActiveIndexedPartitionSequence {h n : ℕ}
    (I : Fin n → ReplicaPartition h) : List (ℕ × ReplicaPartition h) := by
  exact (ccr25IndexedPartitionSequence I).filter
    (fun event => ccr25IsActivePartition event.2)

/-- Removing noncollision times preserves the strict ordering of the remaining
collision times. -/
theorem ccr25ActiveIndexedPartitionSequence_times_pairwise {h n : ℕ}
    (I : Fin n → ReplicaPartition h) :
    (ccr25ActiveIndexedPartitionSequence I).map Prod.fst |>.Pairwise (· < ·) := by
  rw [List.pairwise_map]
  unfold ccr25ActiveIndexedPartitionSequence
  apply List.Pairwise.filter
  have hindexed := ccr25IndexedPartitionSequence_times_pairwise I
  rw [List.pairwise_map] at hindexed
  exact hindexed

/-- The partition labels with their collision-time lists, grouped into maximal
consecutive runs in the active time sequence. -/
noncomputable def ccr25PositionedCollisionRuns {h n : ℕ}
    (I : Fin n → ReplicaPartition h) : List (ReplicaPartition h × List ℕ) := by
  classical
  exact ccr25EncodeTimedRuns (ccr25ActiveIndexedPartitionSequence I)

/-- List form of CCR25 admissibility: the word is nonempty, uses only
nontrivial partitions, has distinct neighbors, and covers every replica. -/
def ccr25AdmissiblePartitionList {h : ℕ}
    (word : List (ReplicaPartition h)) : Prop :=
  word ≠ [] ∧
    (∀ I ∈ word, I ≠ ⊥) ∧
    ccr25RunAdjacentDistinct word ∧
    ∀ a : Fin h, ∃ I ∈ word, InCollisionBlock I a

/-- Convert an admissible partition list to the finite-function word convention
used by CCR25's operator bounds. -/
theorem ccr25AdmissiblePartitionList_to_word {h : ℕ}
    (word : List (ReplicaPartition h))
    (hword : ccr25AdmissiblePartitionList word) :
    ∃ n, ∃ J : Fin (n + 1) → ReplicaPartition h,
      ccr25AdmissibleWord J ∧ List.ofFn J = word := by
  classical
  rcases hword with ⟨hne, hnontrivial, hadjacent, hfull⟩
  have hlenpos : 0 < word.length := List.length_pos_iff.mpr hne
  let n := word.length - 1
  have hlen : n + 1 = word.length := Nat.sub_add_cancel (by omega)
  let J : Fin (n + 1) → ReplicaPartition h := fun j =>
    word.get ⟨j.val, by rw [← hlen]; exact j.isLt⟩
  have hJlist : List.ofFn J = word := by
    calc
      List.ofFn J = List.ofFn (fun j : Fin word.length => word.get j) := by
        rw [List.ofFn_congr hlen J]
        congr 1
      _ = word := List.ofFn_get word
  have hJnontrivial : ∀ j, J j ≠ ⊥ := by
    intro j
    apply hnontrivial
    have hjmem : J j ∈ List.ofFn J := List.mem_ofFn.mpr ⟨j, rfl⟩
    rw [hJlist] at hjmem
    exact hjmem
  have hJadjacent : ∀ j : Fin n, J j.castSucc ≠ J j.succ := by
    intro j
    have hchain : word.IsChain (· ≠ ·) :=
      (ccr25RunAdjacentDistinct_iff_isChain word).mp hadjacent
    have hlt : j.val + 1 < word.length := by
      calc
        j.val + 1 < n + 1 := Nat.succ_lt_succ j.isLt
        _ = word.length := hlen
    have hget := hchain.getElem j.val hlt
    simpa [J, List.get] using hget
  have hJfull : ∀ a : Fin h, ∃ j : Fin (n + 1), InCollisionBlock (J j) a := by
    intro a
    obtain ⟨I, hI, hcollision⟩ := hfull a
    have hImem : I ∈ List.ofFn J := by rw [hJlist]; exact hI
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hImem
    exact ⟨j, by rw [hj]; exact hcollision⟩
  refine ⟨n, J, ?_, hJlist⟩
  exact ⟨hJnontrivial, hJadjacent, hJfull⟩

/-- Forgetting the occurrence times in the positioned runs gives exactly the
ordinary compressed word of active partition labels. -/
theorem ccr25PositionedCollisionRuns_labels_eq_collisionRunWord {h n : ℕ}
    (I : Fin n → ReplicaPartition h) :
    (ccr25PositionedCollisionRuns I).map Prod.fst =
      (ccr25CollisionRunWord (List.ofFn I)).map Prod.fst := by
  classical
  rw [ccr25PositionedCollisionRuns, ccr25CollisionRunWord,
    ccr25EncodeTimedRuns_labels]
  have hmap : (ccr25IndexedPartitionSequence I).map Prod.snd = List.ofFn I := by
    rw [ccr25IndexedPartitionSequence, List.map_ofFn]
    change List.ofFn (fun k : Fin n => I k) = List.ofFn I
    rfl
  congr 1
  change ccr25EncodeRuns (((ccr25IndexedPartitionSequence I).filter
      (fun event => ccr25IsActivePartition event.2)).map Prod.snd) =
    ccr25EncodeRuns ((List.ofFn I).filter ccr25IsActivePartition)
  congr 1
  calc
    _ = ((ccr25IndexedPartitionSequence I).map Prod.snd).filter
        ccr25IsActivePartition := by
          simpa [Function.comp_def] using
            (List.filter_map (p := ccr25IsActivePartition) (f := Prod.snd)
              (l := ccr25IndexedPartitionSequence I)).symm
    _ = (List.ofFn I).filter ccr25IsActivePartition := by rw [hmap]

/-- Expanding the positioned collision runs recovers all active collision
times and labels. -/
theorem ccr25PositionedCollisionRuns_expand {h n : ℕ}
    (I : Fin n → ReplicaPartition h) :
    ccr25ExpandTimedRuns (ccr25PositionedCollisionRuns I) =
      ccr25ActiveIndexedPartitionSequence I := by
  classical
  exact ccr25ExpandTimedRuns_encode _

/-- The active time-stamped sequence determines the original partition
sequence: at every omitted time the partition is the discrete one. -/
theorem ccr25ActiveIndexedPartitionSequence_injective {h n : ℕ}
    {I J : Fin n → ReplicaPartition h}
    (heq : ccr25ActiveIndexedPartitionSequence I =
      ccr25ActiveIndexedPartitionSequence J) : I = J := by
  funext k
  by_cases hI : I k = ⊥
  · by_cases hJ : J k = ⊥
    · exact hI.trans hJ.symm
    · have hmemJ : (k.val + 1, J k) ∈ ccr25ActiveIndexedPartitionSequence J := by
        apply List.mem_filter.mpr
        constructor
        · change (k.val + 1, J k) ∈
            List.ofFn (fun i : Fin n => (i.val + 1, J i))
          exact List.mem_ofFn.mpr ⟨k, rfl⟩
        · simp [ccr25IsActivePartition, hJ]
      rw [← heq] at hmemJ
      have hfiltered := List.mem_filter.mp hmemJ
      have hidx := hfiltered.1
      change (k.val + 1, J k) ∈
        List.ofFn (fun i : Fin n => (i.val + 1, I i)) at hidx
      obtain ⟨j, hjeq⟩ := List.mem_ofFn.mp hidx
      have hfirst : j.val + 1 = k.val + 1 := by
        have := congrArg Prod.fst hjeq
        simpa using this
      have hjk : j = k := Fin.ext (by omega)
      subst j
      have hpart := congrArg Prod.snd hjeq
      exact False.elim (hJ (hpart.symm.trans hI))
  · have hmemI : (k.val + 1, I k) ∈ ccr25ActiveIndexedPartitionSequence I := by
      apply List.mem_filter.mpr
      constructor
      · change (k.val + 1, I k) ∈
          List.ofFn (fun i : Fin n => (i.val + 1, I i))
        exact List.mem_ofFn.mpr ⟨k, rfl⟩
      · simp [ccr25IsActivePartition, hI]
    rw [heq] at hmemI
    have hfiltered := List.mem_filter.mp hmemI
    have hidx := hfiltered.1
    change (k.val + 1, I k) ∈
      List.ofFn (fun i : Fin n => (i.val + 1, J i)) at hidx
    obtain ⟨j, hjeq⟩ := List.mem_ofFn.mp hidx
    have hfirst : j.val + 1 = k.val + 1 := by
      have := congrArg Prod.fst hjeq
      simpa using this
    have hjk : j = k := Fin.ext (by omega)
    subst j
    exact (congrArg Prod.snd hjeq).symm



/-- The positioned collision-run word has adjacent distinct labels. -/
theorem ccr25PositionedCollisionRuns_adjacentDistinct {h n : ℕ}
    (I : Fin n → ReplicaPartition h) :
    ccr25RunAdjacentDistinct ((ccr25PositionedCollisionRuns I).map Prod.fst) := by
  classical
  exact ccr25EncodeTimedRuns_adjacentDistinct _

/-- Each positioned collision run contains at least one active time. -/
theorem ccr25PositionedCollisionRuns_times_nonempty {h n : ℕ}
    {I : Fin n → ReplicaPartition h} {run : ReplicaPartition h × List ℕ}
    (hrun : run ∈ ccr25PositionedCollisionRuns I) : run.2 ≠ [] := by
  classical
  change run ∈ ccr25EncodeTimedRuns (ccr25ActiveIndexedPartitionSequence I) at hrun
  exact ccr25EncodeTimedRuns_times_nonempty hrun






/-- Every positioned collision-run label is nontrivial. -/
theorem ccr25PositionedCollisionRuns_labels_nontrivial {h n : ℕ}
    {I : Fin n → ReplicaPartition h}
    {run : ReplicaPartition h × List ℕ}
    (hrun : run ∈ ccr25PositionedCollisionRuns I) : run.1 ≠ ⊥ := by
  classical
  change run ∈ ccr25EncodeTimedRuns (ccr25ActiveIndexedPartitionSequence I) at hrun
  have hsource := ccr25EncodeTimedRuns_label_memSource hrun
  obtain ⟨event, hevent, hvalue⟩ := List.mem_map.mp hsource
  have hactive := (List.mem_filter.mp hevent).2
  simpa [ccr25ActiveIndexedPartitionSequence, ccr25IsActivePartition, hvalue] using
    hactive

/-- A full-support partition sequence yields a positioned collision word in
which every replica is represented. -/
theorem ccr25PositionedCollisionRuns_fullSupport {h n : ℕ}
    {I : Fin n → ReplicaPartition h}
    (hI : I ∈ fullSupportSequences h n) :
    ∀ a : Fin h, ∃ run ∈ ccr25PositionedCollisionRuns I,
      InCollisionBlock run.1 a := by
  classical
  intro a
  obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hI).2 a
  have hnontrivial : I k ≠ ⊥ := by
    intro hbot
    have hbot' : InCollisionBlock (⊥ : ReplicaPartition h) a := by
      simpa [hbot] using hk
    exact not_inCollisionBlock_bot a hbot'
  have hindexed : (k.val + 1, I k) ∈ ccr25IndexedPartitionSequence I := by
    simp [ccr25IndexedPartitionSequence]
    exact ⟨k, by simp, rfl⟩
  have hactive : (k.val + 1, I k) ∈ ccr25ActiveIndexedPartitionSequence I := by
    apply List.mem_filter.mpr
    exact ⟨hindexed, by simpa [ccr25IsActivePartition] using hnontrivial⟩
  have hlabel : I k ∈
      (ccr25ActiveIndexedPartitionSequence I).map Prod.snd :=
    List.mem_map.mpr ⟨(k.val + 1, I k), hactive, rfl⟩
  obtain ⟨run, hrun, hvalue⟩ := ccr25EncodeTimedRuns_mem_label hlabel
  exact ⟨run, hrun, by rw [hvalue]; exact hk⟩

/-- The positioned collision-run labels form an admissible partition list for
every full-support sequence when at least one replica is present. -/
theorem ccr25PositionedCollisionRuns_admissibleList {h n : ℕ}
    (hh : 0 < h) {I : Fin n → ReplicaPartition h}
    (hI : I ∈ fullSupportSequences h n) :
    ccr25AdmissiblePartitionList
      ((ccr25PositionedCollisionRuns I).map Prod.fst) := by
  classical
  let word := (ccr25PositionedCollisionRuns I).map Prod.fst
  have hlabels : ∀ a : Fin h, ∃ run ∈ ccr25PositionedCollisionRuns I,
      InCollisionBlock run.1 a := ccr25PositionedCollisionRuns_fullSupport hI
  have hnonempty : word ≠ [] := by
    obtain ⟨run, hrun, hblock⟩ := hlabels ⟨0, hh⟩
    have hmem : run.1 ∈ word := List.mem_map.mpr ⟨run, hrun, rfl⟩
    exact List.ne_nil_of_mem hmem
  have hnontrivial : ∀ J ∈ word, J ≠ ⊥ := by
    intro J hJ
    obtain ⟨run, hrun, hvalue⟩ := List.mem_map.mp hJ
    have hrun' := ccr25PositionedCollisionRuns_labels_nontrivial hrun
    simpa [hvalue] using hrun'
  have hadjacent : ccr25RunAdjacentDistinct word := by
    simpa [word] using ccr25PositionedCollisionRuns_adjacentDistinct I
  have hfull : ∀ a : Fin h, ∃ J ∈ word, InCollisionBlock J a := by
    intro a
    obtain ⟨run, hrun, hblock⟩ := hlabels a
    exact ⟨run.1, List.mem_map.mpr ⟨run, hrun, rfl⟩, hblock⟩
  exact ⟨hnonempty, hnontrivial, hadjacent, hfull⟩

/-- Every full-support collision sequence determines a finite CCR25 admissible
word of its maximal active runs. -/
theorem ccr25PositionedCollisionRuns_admissibleWord {h n : ℕ}
    (hh : 0 < h) {I : Fin n → ReplicaPartition h}
    (hI : I ∈ fullSupportSequences h n) :
    ∃ r, ∃ J : Fin (r + 1) → ReplicaPartition h,
      ccr25AdmissibleWord J ∧
        List.ofFn J = (ccr25PositionedCollisionRuns I).map Prod.fst := by
  have hlist := ccr25PositionedCollisionRuns_admissibleList hh hI
  exact ccr25AdmissiblePartitionList_to_word
    ((ccr25PositionedCollisionRuns I).map Prod.fst) hlist

/-- A finite list of nonempty time lists has no more runs than total
occurrences. -/
theorem ccr25_length_le_flatten_length_of_nonempty_snd {α β : Type*}
    (runs : List (α × List β))
    (hne : ∀ run ∈ runs, run.2 ≠ []) :
    runs.length ≤ (runs.map Prod.snd).flatten.length := by
  induction runs with
  | nil => simp
  | cons run runs ih =>
      have hhead : run.2 ≠ [] := hne run (by simp)
      have htail : ∀ r ∈ runs, r.2 ≠ [] := by
        intro r hr
        exact hne r (by simp [hr])
      have hlen : 1 ≤ run.2.length := List.length_pos_iff.mpr hhead
      have hrest := ih htail
      simp only [List.length_cons, List.map_cons, List.flatten_cons,
        List.length_append]
      omega

/-- The number of positioned collision runs is at most the number of
microscopic steps in the sequence. -/
theorem ccr25PositionedCollisionRuns_length_le {h n : ℕ}
    (I : Fin n → ReplicaPartition h) :
    (ccr25PositionedCollisionRuns I).length ≤ n := by
  have hnonempty : ∀ run ∈ ccr25PositionedCollisionRuns I, run.2 ≠ [] := by
    intro run hrun
    exact ccr25PositionedCollisionRuns_times_nonempty hrun
  have hcompress := ccr25_length_le_flatten_length_of_nonempty_snd
    (ccr25PositionedCollisionRuns I) hnonempty
  have hflatten : ((ccr25PositionedCollisionRuns I).map Prod.snd).flatten =
      (((ccr25IndexedPartitionSequence I).filter
        (fun event : ℕ × ReplicaPartition h =>
          ccr25IsActivePartition event.2)).map Prod.fst) := by
    rw [← ccr25ExpandTimedRuns_timeProjection,
      ccr25PositionedCollisionRuns_expand]
    rfl
  have hactive :
      ((ccr25IndexedPartitionSequence I).filter
        (fun event : ℕ × ReplicaPartition h =>
          ccr25IsActivePartition event.2)).length ≤ n := by
    calc
      _ ≤ (ccr25IndexedPartitionSequence I).length := List.length_filter_le _ _
      _ = n := by simp [ccr25IndexedPartitionSequence]
  have hactive' :
      (((ccr25IndexedPartitionSequence I).filter
        (fun event : ℕ × ReplicaPartition h =>
          ccr25IsActivePartition event.2)).map Prod.fst).length ≤ n := by
    simpa only [List.length_map] using hactive
  rw [hflatten] at hcompress
  exact hcompress.trans hactive'

/-- A full-support sequence of length `L` produces an admissible CCR25 word
with `r + 1 ≤ L` operators. -/
theorem ccr25PositionedCollisionRuns_admissibleWord_length_le {h L : ℕ}
    (hh : 0 < h) {I : Fin L → ReplicaPartition h}
    (hI : I ∈ fullSupportSequences h L) :
    ∃ r, ∃ J : Fin (r + 1) → ReplicaPartition h,
      r + 1 ≤ L ∧ ccr25AdmissibleWord J ∧
        List.ofFn J = (ccr25PositionedCollisionRuns I).map Prod.fst := by
  obtain ⟨r, J, hJ, hword⟩ := ccr25PositionedCollisionRuns_admissibleWord hh hI
  have hlength := ccr25PositionedCollisionRuns_length_le I
  have hwordlen : (List.ofFn J).length = r + 1 := by simp
  have hmaplen : ((ccr25PositionedCollisionRuns I).map Prod.fst).length =
      (ccr25PositionedCollisionRuns I).length := by
    simp
  refine ⟨r, J, ?_, hJ, hword⟩
  calc
    r + 1 = (List.ofFn J).length := hwordlen.symm
    _ = ((ccr25PositionedCollisionRuns I).map Prod.fst).length := by rw [hword]
    _ = (ccr25PositionedCollisionRuns I).length := hmaplen
    _ ≤ L := hlength

end Critical2DKPZ.MomentBounds

end
