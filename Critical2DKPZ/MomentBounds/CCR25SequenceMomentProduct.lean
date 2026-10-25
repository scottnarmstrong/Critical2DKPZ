/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.CCR25SequenceRunCompression
public import Critical2DKPZ.MomentBounds.CCR25PartitionMoments
import Mathlib.Tactic

/-! # Moment weights under CCR25 collision-run compression -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Run compression groups the product of event weights into powers of the
weight of each run label. -/
theorem ccr25EncodeTimedRuns_prod_eq {α : Type*} [DecidableEq α]
    (g : α → ℝ) (events : List (ℕ × α)) :
    ((events.map Prod.snd).map g).prod =
      ((ccr25EncodeTimedRuns events).map
        (fun run => g run.1 ^ run.2.length)).prod := by
  induction events with
  | nil => simp [ccr25EncodeTimedRuns]
  | cons event events ih =>
      rcases event with ⟨t, a⟩
      have hfrom (b : α) (times : List ℕ) (events : List (ℕ × α)) :
          ((events.map Prod.snd).map g).prod * g b ^ times.length =
            ((ccr25EncodeTimedRunsFrom b times events).map
              (fun run => g run.1 ^ run.2.length)).prod := by
        induction events generalizing b times with
        | nil => simp [ccr25EncodeTimedRunsFrom]
        | cons event events ihFrom =>
            rcases event with ⟨s, c⟩
            by_cases hbc : b = c
            · subst c
              rw [ccr25EncodeTimedRunsFrom, ite_eq_left rfl]
              have hlen : (times ++ [s]).length = times.length + 1 := by simp
              calc
                ((List.cons (s, b) events).map Prod.snd |>.map g).prod *
                    g b ^ times.length =
                    ((events.map Prod.snd).map g).prod *
                      g b ^ (times.length + 1) := by
                        simp only [List.map_cons, List.prod_cons]
                        rw [pow_succ]
                        ring
                _ = ((events.map Prod.snd).map g).prod *
                      g b ^ (times ++ [s]).length := by rw [hlen]
                _ = ((ccr25EncodeTimedRunsFrom b (times ++ [s]) events).map
                      (fun run => g run.1 ^ run.2.length)).prod := ihFrom b (times ++ [s])
            · have henc : ccr25EncodeTimedRunsFrom b times ((s, c) :: events) =
                  (b, times) :: ccr25EncodeTimedRunsFrom c [s] events := by
                rw [ccr25EncodeTimedRunsFrom, ite_eq_right (Ne.symm hbc)]
              have hsingle : ([s] : List ℕ).length = 1 := by simp
              calc
                ((List.cons (s, c) events).map Prod.snd |>.map g).prod *
                    g b ^ times.length =
                    g b ^ times.length *
                      (((events.map Prod.snd).map g).prod * g c ^ [s].length) := by
                        simp only [List.map_cons, List.prod_cons]
                        rw [hsingle, pow_one]
                        ring
                _ = g b ^ times.length *
                      ((ccr25EncodeTimedRunsFrom c [s] events).map
                        (fun run => g run.1 ^ run.2.length)).prod := by
                          rw [ihFrom c [s]]
                _ = ((ccr25EncodeTimedRunsFrom b times
                      ((s, c) :: events)).map
                      (fun run => g run.1 ^ run.2.length)).prod := by
                        rw [henc]
                        simp only [List.map_cons, List.prod_cons]
      cases events with
      | nil =>
          simp [ccr25EncodeTimedRuns, ccr25EncodeTimedRunsFrom]
      | cons next rest =>
          have htop := hfrom a [t] (next :: rest)
          have htop' : g a * (((next :: rest).map Prod.snd).map g).prod =
              ((ccr25EncodeTimedRunsFrom a [t] (next :: rest)).map
                (fun run => g run.1 ^ run.2.length)).prod := by
            simpa [List.map_cons, List.prod_cons, pow_one, mul_comm] using htop
          simpa [ccr25EncodeTimedRuns] using htop'

/-- Filtering the discrete partition does not change a product when its
weight is one. -/
theorem ccr25_prod_map_filter_eq_of_inactive_one {α : Type*}
    (active : α → Bool) (g : α → ℝ)
    (hone : ∀ x, active x = false → g x = 1) (xs : List α) :
    ((xs.filter active).map g).prod = (xs.map g).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      by_cases hx : active x = true
      · simp [hx, ih]
      · have hx' : active x = false := Bool.eq_false_of_not_eq_true hx
        simp [hx', hone x hx', ih]

/-- The partition moment of the discrete replica partition is one. -/
theorem replicaPartitionDisorderMoment_bot_eq_one {h : ℕ} (β : ℝ) :
    replicaPartitionDisorderMoment β (⊥ : ReplicaPartition h) = 1 := by
  simp [replicaPartitionDisorderMoment, replicaBlockRepresentatives,
    replicaBlockSize, Finset.filter_eq]

/-- The absolute disorder-moment product along a finite partition sequence is
exactly the product of run-label moments, each raised to its number of
collision times. -/
theorem ccr25_partitionSequence_absMomentProduct_eq_runProduct {h L : ℕ}
    (β : ℝ) (I : Fin L → ReplicaPartition h) :
    (∏ k : Fin L, |replicaPartitionDisorderMoment β (I k)|) =
      ((ccr25PositionedCollisionRuns I).map
        (fun run => |replicaPartitionDisorderMoment β run.1| ^ run.2.length)).prod := by
  let g : ReplicaPartition h → ℝ :=
    fun J => |replicaPartitionDisorderMoment β J|
  have hactive := ccr25_prod_map_filter_eq_of_inactive_one
    ccr25IsActivePartition g
    (fun J hJ => by
      have hne : J = ⊥ := by simpa [ccr25IsActivePartition] using hJ
      simp [g, hne, replicaPartitionDisorderMoment_bot_eq_one])
    (List.ofFn I)
  have hindex : (ccr25IndexedPartitionSequence I).map Prod.snd = List.ofFn I := by
    rw [ccr25IndexedPartitionSequence, List.map_ofFn]
    rfl
  have hfilterMap (events : List (ℕ × ReplicaPartition h)) :
      ((events.filter (fun event => ccr25IsActivePartition event.2)).map Prod.snd) =
        ((events.map Prod.snd).filter ccr25IsActivePartition) := by
    induction events with
    | nil => simp
    | cons event events ih =>
        by_cases he : ccr25IsActivePartition event.2 = true <;>
          simp [he, ih]
  have hfilter :
      ((ccr25ActiveIndexedPartitionSequence I).map Prod.snd).map g =
        ((List.ofFn I).filter ccr25IsActivePartition).map g := by
    unfold ccr25ActiveIndexedPartitionSequence
    rw [hfilterMap, hindex]
  have hruns := ccr25EncodeTimedRuns_prod_eq g
    (ccr25ActiveIndexedPartitionSequence I)
  have hfin : (∏ k : Fin L, g (I k)) = ((List.ofFn I).map g).prod := by
    rw [← List.prod_ofFn]
    rw [List.map_ofFn]
    rfl
  calc
    (∏ k : Fin L, |replicaPartitionDisorderMoment β (I k)|) =
        ((List.ofFn I).map g).prod := by simpa [g] using hfin
    _ = (((List.ofFn I).filter ccr25IsActivePartition).map g).prod := by
      rw [← hactive]
    _ = (((ccr25ActiveIndexedPartitionSequence I).map Prod.snd).map g).prod := by
      rw [hfilter]
    _ = ((ccr25PositionedCollisionRuns I).map
          (fun run => g run.1 ^ run.2.length)).prod := by
        simpa [ccr25PositionedCollisionRuns] using hruns
    _ = _ := by simp [g]


end

end Critical2DKPZ.MomentBounds
