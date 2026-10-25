/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25ActivePathCompression
public import Critical2DKPZ.MomentBounds.CCR25SequenceRunCompression
import Mathlib.Tactic

/-! # Active gap encoding agrees with the timed collision stream -/

@[expose] public section

namespace Critical2DKPZ.MomentBounds

attribute [local instance] Classical.propDecidable

/-- Active labels in a list, annotated by their one-based occurrence times. -/
noncomputable def ccr25ActiveTimedFrom {h : ℕ} (time : ℕ) :
    List (ReplicaPartition h) → List (ℕ × ReplicaPartition h)
  | [] => []
  | I :: Is =>
      if I = ⊥ then ccr25ActiveTimedFrom (time + 1) Is
      else (time + 1, I) :: ccr25ActiveTimedFrom (time + 1) Is

/-- Replace increasing absolute event times by the gaps since the preceding
event time, starting from the supplied previous time. -/
def ccr25TimedGapProjectionFrom {α : Type*} (previous : ℕ) :
    List (ℕ × α) → List (ℕ × α)
  | [] => []
  | (time, a) :: events =>
      (time - previous, a) :: ccr25TimedGapProjectionFrom time events

/-- The active gap encoder records exactly the time differences in the
one-based active event stream. -/
theorem ccr25ActiveGapEncodeFrom_eq_timedGapProjectionFrom {h : ℕ} :
    ∀ (gap previous time : ℕ) (Is : List (ReplicaPartition h)),
      previous ≤ time → time - previous = gap →
        ccr25ActiveGapEncodeFrom gap Is =
          ccr25TimedGapProjectionFrom previous
            (ccr25ActiveTimedFrom time Is) := by
  intro gap previous time Is
  induction Is generalizing gap previous time with
  | nil => intro _ _; simp [ccr25ActiveGapEncodeFrom, ccr25ActiveTimedFrom,
      ccr25TimedGapProjectionFrom]
  | cons I Is ih =>
      intro hprev hgap
      by_cases hbot : I = ⊥
      · subst I
        have hgap' : time + 1 - previous = gap + 1 := by omega
        simpa [ccr25ActiveGapEncodeFrom, ccr25ActiveTimedFrom,
          ccr25TimedGapProjectionFrom, hgap'] using
          ih (gap + 1) previous (time + 1) (by omega) (by omega)
      · have hgap' : time + 1 - previous = gap + 1 := by omega
        simp only [ccr25ActiveGapEncodeFrom, ccr25ActiveTimedFrom,
          ccr25TimedGapProjectionFrom, hbot, ite_false, hgap']
        congr 1
        exact ih 0 (time + 1) (time + 1) (by omega) (by omega)

/-- Annotate every entry of a list by its one-based time, starting after the
given number of entries. -/
def ccr25TimedIndexFrom {α : Type*} (time : ℕ) : List α → List (ℕ × α)
  | [] => []
  | a :: as => (time + 1, a) :: ccr25TimedIndexFrom (time + 1) as

/-- Filtering the full timed stream to active labels gives the active timed
stream. -/
theorem ccr25ActiveTimedFrom_eq_filter_timedIndexFrom {h : ℕ} (time : ℕ)
    (Is : List (ReplicaPartition h)) :
    ccr25ActiveTimedFrom time Is =
      (ccr25TimedIndexFrom time Is).filter
        (fun event => ccr25IsActivePartition event.2) := by
  induction Is generalizing time with
  | nil => simp [ccr25ActiveTimedFrom, ccr25TimedIndexFrom]
  | cons I Is ih =>
      by_cases hbot : I = ⊥
      · subst I
        simpa [ccr25ActiveTimedFrom, ccr25TimedIndexFrom,
          ccr25IsActivePartition] using ih (time + 1)
      · simpa [ccr25ActiveTimedFrom, ccr25TimedIndexFrom,
          ccr25IsActivePartition, hbot] using ih (time + 1)

/-- The recursively annotated list agrees with the one-based finite-index
annotation, including after an arbitrary time offset. -/
theorem ccr25TimedIndexFrom_ofFn {h n : ℕ} (time : ℕ)
    (I : Fin n → ReplicaPartition h) :
    ccr25TimedIndexFrom time (List.ofFn I) =
      List.ofFn (fun k : Fin n => (k.val + (time + 1), I k)) := by
  induction n generalizing time with
  | zero => simp [ccr25TimedIndexFrom]
  | succ n ih =>
      let tail : Fin n → ReplicaPartition h := fun j => I j.succ
      have hcons : I = Fin.cons (I 0) tail := by
        funext j
        refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · rfl
      have hfun :
          (fun k : Fin (n + 1) => (k.val + (time + 1), I k)) =
            Fin.cons (time + 1, I 0)
              (fun j : Fin n => (j.val + (time + 2), tail j)) := by
        funext k
        refine Fin.cases ?_ (fun j => ?_) k
        · simp [Fin.cons_zero]
        · simp only [Fin.cons_succ, Fin.val_succ]
          congr 1
          · omega
      rw [show List.ofFn I = I 0 :: List.ofFn tail by
        rw [hcons, List.ofFn_cons]
        simp [Fin.cons_zero]]
      simp only [ccr25TimedIndexFrom]
      rw [ih (time + 1) tail, hfun, List.ofFn_cons]

/-- Zero offset gives the partition sequence indexed from one. -/
theorem ccr25TimedIndexFrom_zero_ofFn {h n : ℕ}
    (I : Fin n → ReplicaPartition h) :
    ccr25TimedIndexFrom 0 (List.ofFn I) = ccr25IndexedPartitionSequence I := by
  simpa [ccr25IndexedPartitionSequence] using ccr25TimedIndexFrom_ofFn 0 I

/-- The recursive stream equals the indexed active collision stream with its occurrence times. -/
theorem ccr25ActiveTimedFrom_zero_ofFn {h n : ℕ}
    (I : Fin n → ReplicaPartition h) :
    ccr25ActiveTimedFrom 0 (List.ofFn I) =
      ccr25ActiveIndexedPartitionSequence I := by
  rw [ccr25ActiveTimedFrom_eq_filter_timedIndexFrom,
    ccr25TimedIndexFrom_zero_ofFn]
  rfl

/-- The existing active-gap encoding can be read directly from the timed
active stream, with each entry storing its positive inter-event duration. -/
theorem ccr25ActiveGapEncodeFrom_zero_eq_timedGapProjection {h n : ℕ}
    (I : Fin n → ReplicaPartition h) :
    ccr25ActiveGapEncodeFrom 0 (List.ofFn I) =
      ccr25TimedGapProjectionFrom 0
        (ccr25ActiveIndexedPartitionSequence I) := by
  rw [← ccr25ActiveTimedFrom_zero_ofFn]
  exact ccr25ActiveGapEncodeFrom_eq_timedGapProjectionFrom
    0 0 0 (List.ofFn I) (by omega) (by omega)

/-- Ordered event streams are determined by their successive positive gaps.
The lower-bound hypothesis rules out translating the whole stream while
keeping all gaps fixed. -/
theorem ccr25TimedGapProjectionFrom_injective {α : Type*} :
    ∀ (previous : ℕ) (events₁ : List (ℕ × α)),
      (∀ e ∈ events₁, previous ≤ e.1) →
      (events₁.map Prod.fst).Pairwise (· < ·) →
      ∀ events₂ : List (ℕ × α),
        (∀ e ∈ events₂, previous ≤ e.1) →
        (events₂.map Prod.fst).Pairwise (· < ·) →
        ccr25TimedGapProjectionFrom previous events₁ =
          ccr25TimedGapProjectionFrom previous events₂ →
        events₁ = events₂ := by
  intro previous events₁
  induction events₁ generalizing previous with
  | nil =>
      intro h₁ _ events₂ _ _ heq
      cases events₂ with
      | nil => rfl
      | cons e es => simp [ccr25TimedGapProjectionFrom] at heq
  | cons e₁ es₁ ih =>
      rcases e₁ with ⟨t₁, a₁⟩
      intro h₁ hp₁ events₂ h₂ hp₂ heq
      cases events₂ with
      | nil => simp [ccr25TimedGapProjectionFrom] at heq
      | cons e₂ es₂ =>
          rcases e₂ with ⟨t₂, a₂⟩
          have heq' := List.cons.inj heq
          have hhead : t₁ = t₂ ∧ a₁ = a₂ := by
            have htime : t₁ - previous = t₂ - previous := congrArg Prod.fst heq'.1
            have hlabel : a₁ = a₂ := congrArg Prod.snd heq'.1
            constructor
            · have h₁head := h₁ (t₁, a₁) (by simp)
              have h₂head := h₂ (t₂, a₂) (by simp)
              omega
            · exact hlabel
          rcases hhead with ⟨rfl, rfl⟩
          have htail₁ : ∀ e ∈ es₁, t₁ ≤ e.1 := by
            intro e he
            have hp := List.pairwise_map.mp hp₁
            exact le_of_lt (hp.rel_head_tail he)
          have htail₂ : ∀ e ∈ es₂, t₁ ≤ e.1 := by
            intro e he
            have hp := List.pairwise_map.mp hp₂
            exact le_of_lt (hp.rel_head_tail he)
          have htailEq : ccr25TimedGapProjectionFrom t₁ es₁ =
              ccr25TimedGapProjectionFrom t₁ es₂ := heq'.2
          have hpTail₁ : (es₁.map Prod.fst).Pairwise (· < ·) :=
            List.pairwise_map.mpr (List.Pairwise.tail (List.pairwise_map.mp hp₁))
          have hpTail₂ : (es₂.map Prod.fst).Pairwise (· < ·) :=
            List.pairwise_map.mpr (List.Pairwise.tail (List.pairwise_map.mp hp₂))
          have htail := ih t₁ htail₁ hpTail₁
            es₂ htail₂ hpTail₂ htailEq
          simp [htail]

/-- The active-gap encoding is injective on finite time-indexed partition
sequences: the encoding records the non-bottom entries with their times, and the
remaining entries are bottom, so `I` is recovered. -/
theorem ccr25ActiveGapEncodeFrom_zero_ofFn_injective {h n : ℕ}
    {I J : Fin n → ReplicaPartition h}
    (heq : ccr25ActiveGapEncodeFrom 0 (List.ofFn I) =
      ccr25ActiveGapEncodeFrom 0 (List.ofFn J)) :
    I = J := by
  apply ccr25ActiveIndexedPartitionSequence_injective
  apply ccr25TimedGapProjectionFrom_injective 0
    (ccr25ActiveIndexedPartitionSequence I)
  · intro e he
    have hmem : e ∈ ccr25ActiveIndexedPartitionSequence I := he
    change e ∈ (ccr25IndexedPartitionSequence I).filter
      (fun event => ccr25IsActivePartition event.2) at hmem
    obtain ⟨hmem', _⟩ := List.mem_filter.mp hmem
    have hmem'' : e ∈ List.ofFn (fun k : Fin n => (k.val + 1, I k)) := by
      simpa [ccr25IndexedPartitionSequence] using hmem'
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hmem''
    have ht := congrArg Prod.fst hk
    simp at ht
    omega
  · exact ccr25ActiveIndexedPartitionSequence_times_pairwise I
  · intro e he
    have hmem : e ∈ ccr25ActiveIndexedPartitionSequence J := he
    change e ∈ (ccr25IndexedPartitionSequence J).filter
      (fun event => ccr25IsActivePartition event.2) at hmem
    obtain ⟨hmem', _⟩ := List.mem_filter.mp hmem
    have hmem'' : e ∈ List.ofFn (fun k : Fin n => (k.val + 1, J k)) := by
      simpa [ccr25IndexedPartitionSequence] using hmem'
    obtain ⟨k, hk⟩ := List.mem_ofFn.mp hmem''
    have ht := congrArg Prod.fst hk
    simp at ht
    omega
  · exact ccr25ActiveIndexedPartitionSequence_times_pairwise J
  · rw [ccr25ActiveGapEncodeFrom_zero_eq_timedGapProjection I,
      ccr25ActiveGapEncodeFrom_zero_eq_timedGapProjection J] at heq
    exact heq

end Critical2DKPZ.MomentBounds

end
