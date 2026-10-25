/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CollisionRunExpansionRuns
public import Critical2DKPZ.SHF.Moments.CollisionRunExpansionSupport
import Mathlib.Tactic

/-! Combinatorial identities describe the first run of a collision-word expansion. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose
attribute [local instance] Classical.propDecidable

private abbrev FirstRunDatumType {h : ℕ} :=
  Σ _α : CollisionPair h, Σ _s : ℕ, Σ _r : ℕ, Σ _S : Finset ℕ,
    Finset (ℕ × CollisionPair h)

private def firstRunDataSet {h : ℕ} (L : Finset (CollisionPair h)) (n : ℕ) :
    Finset (@FirstRunDatumType h) :=
  L.sigma fun α => (Finset.Icc 1 n).sigma fun s =>
    (Finset.range (n - s + 1)).sigma fun r => runTimeSets r |>.sigma fun _S =>
      (collisionEdges (n - s - r) h).powerset.filter
        (fun A' => IsPairSimple A' ∧ FirstPairIn (Finset.univ.erase α) A')

private def firstRunDatumEdges {h : ℕ} (d : @FirstRunDatumType h) :
    Finset (ℕ × CollisionPair h) :=
  runEdges d.1 d.2.1 d.2.2.2.1 ∪
    shiftEdges (d.2.1 + d.2.2.1) d.2.2.2.2

private theorem firstRunDatum_sum {h : ℕ} (L : Finset (CollisionPair h)) (n : ℕ)
    (F : Finset (ℕ × CollisionPair h) → ℝ) :
    (∑ α ∈ L, ∑ s ∈ Finset.Icc 1 n,
      ∑ r ∈ Finset.range (n - s + 1), ∑ S ∈ runTimeSets r,
        ∑ A' ∈ (collisionEdges (n - s - r) h).powerset.filter
            (fun A' => IsPairSimple A' ∧ FirstPairIn (Finset.univ.erase α) A'),
          F (runEdges α s S ∪ shiftEdges (s + r) A')) =
      ∑ d ∈ firstRunDataSet L n, F (firstRunDatumEdges d) := by
  simp [firstRunDataSet, firstRunDatumEdges, Finset.sum_sigma]

private theorem list_mem_le_getLast_of_pairwise {l : List ℕ} (hl : l ≠ [])
    (hp : l.Pairwise (· < ·)) {t : ℕ} (ht : t ∈ l) : t ≤ l.getLast hl := by
  induction l generalizing t with
  | nil => exact (hl rfl).elim
  | cons a l ih =>
      cases l with
      | nil =>
          have hta : t = a := by simpa using ht
          subst t
          simp
      | cons b l =>
          have hp' := List.pairwise_cons.mp hp
          have hlast : (a :: b :: l).getLast (by simp) = (b :: l).getLast (by simp) := by
            simp
          rcases List.mem_cons.mp ht with hta | ht'
          · subst t
            have hab := hp'.1 b (by simp)
            have hb := ih (by simp) hp'.2 (by simp : b ∈ b :: l)
            exact hab.le.trans (by simpa [hlast] using hb)
          · have htLast := ih (by simp) hp'.2 ht'
            simpa [hlast] using htLast

/-- A timed-run continuation always begins with the current label. -/
theorem timedRunContinuation_head {α : Type*} [DecidableEq α]
    (a : α) (times : List ℕ) (events : List (ℕ × α)) :
    ∃ runTimes rest,
      MomentBounds.ccr25EncodeTimedRunsFrom a times events = (a, runTimes) :: rest := by
  induction events generalizing a times with
  | nil => exact ⟨times, [], rfl⟩
  | cons event events ih =>
      rcases event with ⟨n, b⟩
      by_cases hb : b = a
      · simpa [MomentBounds.ccr25EncodeTimedRunsFrom, hb] using ih a (times ++ [n])
      · exact ⟨times, MomentBounds.ccr25EncodeTimedRunsFrom b [n] events, by
          simp [MomentBounds.ccr25EncodeTimedRunsFrom, hb]⟩

/-- The timed run encoding of a nonempty event stream has a first run whose
time list is nonempty. -/
theorem ccr25EncodeTimedRuns_head {α : Type*} [DecidableEq α]
    {events : List (ℕ × α)} (hevents : events ≠ []) :
    ∃ a times rest, MomentBounds.ccr25EncodeTimedRuns events = (a, times) :: rest ∧
      times ≠ [] := by
  cases events with
  | nil => exact (hevents rfl).elim
  | cons event events =>
      rcases event with ⟨n, a⟩
      obtain ⟨times, rest, hhead⟩ := timedRunContinuation_head a [n] events
      refine ⟨a, times, rest, ?_, ?_⟩
      · simpa [MomentBounds.ccr25EncodeTimedRuns] using hhead
      · exact MomentBounds.ccr25EncodeTimedRunsFrom_times_nonempty a [n] events (by simp)
          (run := (a, times)) (by rw [hhead]; exact List.mem_cons_self)

/-- A nonempty pair-simple edge set has a first maximal run in its timed
encoding. -/
theorem pairSimpleRunEncoding_head {h : ℕ} {A : Finset (ℕ × CollisionPair h)}
    (hA : A ≠ ∅) :
    ∃ α times rest, pairSimpleRunEncoding A = (α, times) :: rest ∧ times ≠ [] := by
  have hlen : (collisionEdgeChronologicalList A).length = A.card := by
    simp [collisionEdgeChronologicalList, Finset.length_sort]
  have hEvents : collisionEdgeChronologicalList A ≠ [] := by
    intro hnil
    apply hA
    apply Finset.card_eq_zero.mp
    rw [← hlen, hnil]
    rfl
  obtain ⟨α, times, rest, hhead, htimes⟩ :=
    ccr25EncodeTimedRuns_head hEvents
  exact ⟨α, times, rest, by simpa [pairSimpleRunEncoding] using hhead, htimes⟩

/-- The first run precedes its encoded tail, and the tail retains strict time
order. -/
theorem pairSimpleRunEncoding_head_tail_order_facts {h : ℕ}
    {A : Finset (ℕ × CollisionPair h)} (hA : IsPairSimple A)
    (α : CollisionPair h) (times : List ℕ) (rest : List (CollisionPair h × List ℕ))
    (hhead : pairSimpleRunEncoding A = (α, times) :: rest) :
    (∀ t ∈ times, ∀ e ∈ MomentBounds.ccr25ExpandTimedRuns rest, t < e.1) ∧
      List.Pairwise (· < ·) ((MomentBounds.ccr25ExpandTimedRuns rest).map Prod.fst) := by
  have hExpand := pairSimpleRunEncoding_expand A
  rw [hhead, MomentBounds.ccr25ExpandTimedRuns] at hExpand
  have hpair := pairSimpleEventList_times_pairwise A hA
  have hpairTimes : List.Pairwise (· < ·) (collisionEdgeChronologicalList A |>.map Prod.fst) := by
    simpa only [List.pairwise_map] using hpair
  have hpair' : List.Pairwise (· < ·)
      (times ++ (MomentBounds.ccr25ExpandTimedRuns rest).map Prod.fst) := by
    rw [← hExpand] at hpairTimes
    simpa [List.map_append, List.map_map, Function.comp_def] using hpairTimes
  rcases List.pairwise_append.mp hpair' with ⟨_, htail, hcross⟩
  refine ⟨?_, htail⟩
  intro t ht e he
  exact hcross t ht e.1 (List.mem_map.mpr ⟨e, he, rfl⟩)

/-- Every event after the first encoded run of a pair-simple edge set has a
strictly later time than every event in that run. -/
theorem pairSimpleRunEncoding_head_time_order {h : ℕ}
    {A : Finset (ℕ × CollisionPair h)} (hA : IsPairSimple A)
    (α : CollisionPair h) (times : List ℕ) (rest : List (CollisionPair h × List ℕ))
    (hhead : pairSimpleRunEncoding A = (α, times) :: rest) :
    ∀ t ∈ times, ∀ e ∈ MomentBounds.ccr25ExpandTimedRuns rest, t < e.1 :=
  (pairSimpleRunEncoding_head_tail_order_facts hA α times rest hhead).1


/-- The first run's noninitial times, translated to offsets from its first
event, form an element of `runTimeSets`. -/
theorem pairSimpleRunEncoding_firstRun_times {h : ℕ}
    {A : Finset (ℕ × CollisionPair h)} (hA : IsPairSimple A) (hne : A ≠ ∅) :
    ∃ α times rest s r S,
      pairSimpleRunEncoding A = (α, times) :: rest ∧ times ≠ [] ∧
      times.head! = s ∧ s + r = times.getLast! ∧
      S = (times.tail.map (fun t => t - s)).toFinset ∧ S ∈ runTimeSets r := by
  obtain ⟨α, times, rest, hhead, htimes⟩ := pairSimpleRunEncoding_head hne
  have hrunMem : (α, times) ∈ pairSimpleRunEncoding A := by
    rw [hhead]
    exact List.mem_cons_self
  have hsorted := pairSimpleRunEncoding_times_pairwise A hA (α, times) hrunMem
  cases times with
  | nil => exact (htimes rfl).elim
  | cons s tail =>
      let hneTimes : s :: tail ≠ [] := by simp
      have hfirst {t : ℕ} (ht : t ∈ tail) : s < t := by
        have hpair := List.pairwise_cons.mp hsorted
        exact hpair.1 t ht
      have hleLast {t : ℕ} (ht : t ∈ s :: tail) :
          t ≤ (s :: tail).getLast hneTimes :=
        list_mem_le_getLast_of_pairwise hneTimes hsorted ht
      let r := (s :: tail).getLast hneTimes - s
      let S := (tail.map fun t => t - s).toFinset
      have hsle : s ≤ (s :: tail).getLast hneTimes := hleLast (by simp)
      have hSsub : S ⊆ Finset.Icc 1 r := by
        intro d hd
        have hdList := List.mem_toFinset.mp hd
        obtain ⟨u, hu, hut⟩ := List.mem_map.mp hdList
        rw [← hut]
        have hlo := hfirst hu
        have hhi := hleLast (List.mem_cons_of_mem s hu)
        apply Finset.mem_Icc.mpr
        constructor
        · omega
        · dsimp [r]
          omega
      have hlastMem : r = 0 ∨ r ∈ S := by
        cases tail with
        | nil => left; simp [r]
        | cons t ts =>
            right
            have hneTail : t :: ts ≠ [] := by simp
            apply List.mem_toFinset.mpr
            apply List.mem_map.mpr
            refine ⟨(t :: ts).getLast hneTail, List.getLast_mem hneTail, ?_⟩
            dsimp [S, r]
      have hgetLast : (s :: tail).getLast! = (s :: tail).getLast hneTimes := by
        unfold List.getLast!
        exact List.getLast_congr (by simp) hneTimes rfl
      refine ⟨α, s :: tail, rest, s, r, S, hhead, by simp, by simp, ?_, rfl, ?_⟩
      · dsimp [r]
        rw [hgetLast]
        exact Nat.add_sub_of_le hsle
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_powerset.mpr hSsub, hlastMem⟩

/-- The `runEdges` constructor reconstructs the timed list of the first run. -/
theorem runEdges_eq_toFinset_of_times {h : ℕ} (α : CollisionPair h) (s : ℕ)
    (tail : List ℕ) (hfirst : ∀ t ∈ tail, s < t) :
    runEdges α s ((tail.map fun t => t - s).toFinset) =
      ((s :: tail).map fun t => (t, α)).toFinset := by
  ext e
  simp only [runEdges, Finset.mem_insert, Finset.mem_image]
  constructor
  · intro heLeft
    rcases heLeft with he | hImage
    · apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      exact ⟨s, by simp, he.symm⟩
    · obtain ⟨d, hd, he⟩ := hImage
      obtain ⟨t, ht, hdt⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨t, List.mem_cons_of_mem s ht, ?_⟩
      have hst := hfirst t ht
      have htime : s + (t - s) = t := Nat.add_sub_of_le hst.le
      rw [← hdt, htime] at he
      exact he
  · intro he
    obtain ⟨t, ht, he⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    rcases List.mem_cons.mp ht with hts | ht
    · subst t
      exact Or.inl he.symm
    · right
      refine ⟨t - s, List.mem_toFinset.mpr (List.mem_map.mpr ⟨t, ht, rfl⟩), ?_⟩
      have hst := hfirst t ht
      have htime : s + (t - s) = t := Nat.add_sub_of_le hst.le
      rw [htime]
      exact he

/-- Shifting a finite event list back by `k` and then forward recovers its
edge set when every event lies strictly after `k`. -/
theorem shiftEdges_sub_toFinset {h : ℕ} (k : ℕ)
    (events : List (ℕ × CollisionPair h))
    (hafter : ∀ e ∈ events, k < e.1) :
    shiftEdges k ((events.map fun e => (e.1 - k, e.2)).toFinset) = events.toFinset := by
  ext e
  simp only [shiftEdges, Finset.mem_image]
  constructor
  · rintro ⟨e', he', hshift⟩
    obtain ⟨e₁, he₁, hmap₁⟩ := List.mem_map.mp (List.mem_toFinset.mp he')
    have he'val : e' = (e₁.1 - k, e₁.2) := hmap₁.symm
    subst e'
    have hshift' : ((e₁.1 - k) + k, e₁.2) = e := by
      simpa [shiftEdges] using hshift
    have htime : (e₁.1 - k) + k = e₁.1 := Nat.sub_add_cancel (le_of_lt (hafter e₁ he₁))
    have heq : e₁ = e := by
      simpa only [htime] using hshift'
    rw [← heq]
    exact List.mem_toFinset.mpr he₁
  · intro he
    have heList := List.mem_toFinset.mp he
    refine ⟨(e.1 - k, e.2), ?_, ?_⟩
    · exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e, heList, rfl⟩)
    · have htime : (e.1 - k) + k = e.1 := Nat.sub_add_cancel (le_of_lt (hafter e heList))
      change ((e.1 - k) + k, e.2) = e
      rw [htime]

/-- Every nonempty pair-simple edge set is the union of its first run and a
time-shifted residual edge set. -/
theorem pairSimpleRunEncoding_reconstruct_edges {h : ℕ}
    {A : Finset (ℕ × CollisionPair h)} (hA : IsPairSimple A) (hne : A ≠ ∅) :
    ∃ α times rest s r S A',
      pairSimpleRunEncoding A = (α, times) :: rest ∧ times ≠ [] ∧
      times.head! = s ∧ s + r = times.getLast! ∧
      S = (times.tail.map fun t => t - s).toFinset ∧ S ∈ runTimeSets r ∧
      A' = (MomentBounds.ccr25ExpandTimedRuns rest |>.map
        fun e => (e.1 - (s + r), e.2)).toFinset ∧
      A = runEdges α s S ∪ shiftEdges (s + r) A' := by
  obtain ⟨α, times, rest, s, r, S, hhead, htimes, hs, hsr, hS, hrun⟩ :=
    pairSimpleRunEncoding_firstRun_times hA hne
  cases times with
  | nil => exact (htimes rfl).elim
  | cons s' tail =>
      have hs' : s' = s := by simpa using hs
      subst s'
      let hneTimes : s :: tail ≠ [] := by simp
      have hrunMem : (α, s :: tail) ∈ pairSimpleRunEncoding A := by
        rw [hhead]
        exact List.mem_cons_self
      have hsorted := pairSimpleRunEncoding_times_pairwise A hA (α, s :: tail) hrunMem
      have hfirst {t : ℕ} (ht : t ∈ tail) : s < t := by
        exact (List.pairwise_cons.mp hsorted).1 t ht
      have hRunEq := runEdges_eq_toFinset_of_times α s tail (fun t ht => hfirst ht)
      have hRunEq' : runEdges α s S = ((s :: tail).map fun t => (t, α)).toFinset := by
        rw [hS]
        exact hRunEq
      have hgetLast : (s :: tail).getLast! = (s :: tail).getLast hneTimes := by
        unfold List.getLast!
        exact List.getLast_congr (by simp) hneTimes rfl
      have hlastMem : (s :: tail).getLast hneTimes ∈ s :: tail :=
        List.getLast_mem hneTimes
      have hcross := pairSimpleRunEncoding_head_time_order hA α (s :: tail) rest hhead
      have hafter : ∀ e ∈ MomentBounds.ccr25ExpandTimedRuns rest, s + r < e.1 := by
        intro e he
        have hlt := hcross ((s :: tail).getLast hneTimes) hlastMem e he
        have hend : s + r = (s :: tail).getLast hneTimes := by
          rw [← hgetLast]
          exact hsr
        omega
      let A' := (MomentBounds.ccr25ExpandTimedRuns rest |>.map
        fun e => (e.1 - (s + r), e.2)).toFinset
      have hshift := shiftEdges_sub_toFinset (s + r)
        (MomentBounds.ccr25ExpandTimedRuns rest) hafter
      have hAexpand := pairSimpleRunEncoding_reconstruct A
      rw [hhead, MomentBounds.ccr25ExpandTimedRuns] at hAexpand
      have hAunion : A = ((s :: tail).map fun t => (t, α)).toFinset ∪
          (MomentBounds.ccr25ExpandTimedRuns rest).toFinset := by
        rw [← hAexpand]
        simp
      refine ⟨α, s :: tail, rest, s, r, S, A', hhead, by simp, by simp, ?_, hS, hrun, rfl, ?_⟩
      · rw [hgetLast]
        exact hsr
      · calc
        A = ((s :: tail).map fun t => (t, α)).toFinset ∪
            (MomentBounds.ccr25ExpandTimedRuns rest).toFinset := hAunion
        _ = runEdges α s S ∪ shiftEdges (s + r) A' := by
          rw [← hRunEq', ← hshift]

/-- The shifted residual inherits pair simplicity and fits in the remaining
time window. -/
theorem pairSimpleRunEncoding_remainder_pairSimple_support {n h : ℕ}
    {A : Finset (ℕ × CollisionPair h)} (hA : IsPairSimple A)
    (hAsub : A ⊆ collisionEdges n h) (hne : A ≠ ∅) :
    ∃ α times rest s r S A',
      pairSimpleRunEncoding A = (α, times) :: rest ∧ times ≠ [] ∧
      times.head! = s ∧ s + r = times.getLast! ∧
      S = (times.tail.map fun t => t - s).toFinset ∧ S ∈ runTimeSets r ∧
      A' = (MomentBounds.ccr25ExpandTimedRuns rest |>.map
        fun e => (e.1 - (s + r), e.2)).toFinset ∧
      A' ⊆ collisionEdges (n - s - r) h ∧ IsPairSimple A' ∧
      A = runEdges α s S ∪ shiftEdges (s + r) A' := by
  obtain ⟨α, times, rest, s, r, S, A', hhead, htimes, hs, hsr, hS, hrun,
      hAdef, hAeq⟩ := pairSimpleRunEncoding_reconstruct_edges hA hne
  have hAexpand := pairSimpleRunEncoding_reconstruct A
  rw [hhead, MomentBounds.ccr25ExpandTimedRuns] at hAexpand
  have htailSub : (MomentBounds.ccr25ExpandTimedRuns rest).toFinset ⊆ A := by
    rw [← hAexpand]
    simp
  have hcross := pairSimpleRunEncoding_head_time_order hA α times rest hhead
  cases times with
  | nil => exact (htimes rfl).elim
  | cons s' tail =>
      have hs' : s' = s := by simpa using hs
      subst s'
      have hneTimes : s :: tail ≠ [] := by simp
      have hgetLast : (s :: tail).getLast! = (s :: tail).getLast hneTimes := by
        unfold List.getLast!
        exact List.getLast_congr (by simp) hneTimes rfl
      have hlastMem : (s :: tail).getLast hneTimes ∈ s :: tail :=
        List.getLast_mem hneTimes
      have hafter : ∀ e ∈ MomentBounds.ccr25ExpandTimedRuns rest, s + r < e.1 := by
        intro e he
        have hlt := hcross ((s :: tail).getLast hneTimes) hlastMem e he
        have hend : s + r = (s :: tail).getLast hneTimes := by
          rw [← hgetLast]
          exact hsr
        omega
      have hA'bound : A' ⊆ collisionEdges (n - s - r) h := by
        intro e he
        rw [hAdef] at he
        obtain ⟨e₀, he₀, hmap⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
        have hsourceA : e₀ ∈ A := htailSub (List.mem_toFinset.mpr he₀)
        have hsourceRange : e₀ ∈ (Finset.Icc 1 n).product Finset.univ := hAsub hsourceA
        have hsourceTime := Finset.mem_Icc.mp (Finset.mem_product.mp hsourceRange).1
        have hafter₀ := hafter e₀ he₀
        have hmapTime := congrArg Prod.fst hmap
        change e ∈ (Finset.Icc 1 (n - s - r)).product Finset.univ
        apply Finset.mem_product.mpr
        refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, Finset.mem_univ _⟩
        · rw [← hmapTime]
          omega
        · rw [← hmapTime]
          omega
      have hA'simple : IsPairSimple A' := by
        rw [hAdef]
        intro e he e' he' heq
        obtain ⟨e₀, he₀, hmap₀⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
        obtain ⟨e₁, he₁, hmap₁⟩ := List.mem_map.mp (List.mem_toFinset.mp he')
        have hsourceA₀ : e₀ ∈ A := htailSub (List.mem_toFinset.mpr he₀)
        have hsourceA₁ : e₁ ∈ A := htailSub (List.mem_toFinset.mpr he₁)
        have hmapTime₀ := congrArg Prod.fst hmap₀
        have hmapTime₁ := congrArg Prod.fst hmap₁
        have hafter₀ := hafter e₀ he₀
        have hafter₁ := hafter e₁ he₁
        have htime₀₁ : e₀.1 = e₁.1 := by
          have hsubeq : e₀.1 - (s + r) = e₁.1 - (s + r) := by
            calc
              e₀.1 - (s + r) = e.1 := hmapTime₀
              _ = e'.1 := heq
              _ = e₁.1 - (s + r) := hmapTime₁.symm
          omega
        have hsourceEq := hA e₀ hsourceA₀ e₁ hsourceA₁ htime₀₁
        calc
          e = (e₀.1 - (s + r), e₀.2) := hmap₀.symm
          _ = (e₁.1 - (s + r), e₁.2) := by rw [hsourceEq]
          _ = e' := hmap₁
      exact ⟨α, s :: tail, rest, s, r, S, A', hhead, by simp, by simp,
        by simpa using hsr, by simpa using hS, hrun, hAdef, hA'bound, hA'simple, hAeq⟩

/-- The first selected time in a pair-simple run encoding is the least time
in the original edge set. -/
theorem pairSimpleRunEncoding_firstRun_time_minimal {h : ℕ}
    {A : Finset (ℕ × CollisionPair h)} (hA : IsPairSimple A)
    {α : CollisionPair h} {times : List ℕ} {rest : List (CollisionPair h × List ℕ)}
    (hhead : pairSimpleRunEncoding A = (α, times) :: rest) (htimes : times ≠ [])
    {s : ℕ} (hs : times.head! = s) :
    ∀ e ∈ A, s ≤ e.1 := by
  cases times with
  | nil => exact (htimes rfl).elim
  | cons s' tail =>
      have hs' : s' = s := by simpa using hs
      subst s'
      have hEvents := pairSimpleRunEncoding_expand A
      rw [hhead, MomentBounds.ccr25ExpandTimedRuns] at hEvents
      have hchrono : collisionEdgeChronologicalList A =
          (s, α) :: ((tail.map fun t => (t, α)) ++
            MomentBounds.ccr25ExpandTimedRuns rest) := by
        simpa [List.map_cons] using hEvents.symm
      have hpair := pairSimpleEventList_times_pairwise A hA
      rw [hchrono] at hpair
      have hheadLe := (List.pairwise_cons.mp hpair).1
      intro e he
      have heChrono : e ∈ collisionEdgeChronologicalList A := by
        have heExpand : e ∈
            (MomentBounds.ccr25ExpandTimedRuns (pairSimpleRunEncoding A)) := by
          apply List.mem_toFinset.mp
          rw [pairSimpleRunEncoding_reconstruct A]
          exact he
        exact (pairSimpleRunEncoding_expand A).symm ▸ heExpand
      rw [hchrono] at heChrono
      rcases List.mem_cons.mp heChrono with heq | hetail
      · have : e.1 = s := by simpa using congrArg Prod.fst heq
        omega
      · exact (hheadLe e hetail).le

/-- The residual after a maximal first run has a different earliest pair. -/
theorem pairSimpleRunEncoding_remainder_firstPairIn {n h : ℕ}
    {A : Finset (ℕ × CollisionPair h)} (hA : IsPairSimple A)
    (hAsub : A ⊆ collisionEdges n h) (hne : A ≠ ∅) :
    ∃ α times rest s r S A',
      pairSimpleRunEncoding A = (α, times) :: rest ∧ times ≠ [] ∧
      times.head! = s ∧ s + r = times.getLast! ∧
      S = (times.tail.map fun t => t - s).toFinset ∧ S ∈ runTimeSets r ∧
      A' = (MomentBounds.ccr25ExpandTimedRuns rest |>.map
        fun e => (e.1 - (s + r), e.2)).toFinset ∧
      A' ⊆ collisionEdges (n - s - r) h ∧ IsPairSimple A' ∧
      FirstPairIn (Finset.univ.erase α) A' ∧
      A = runEdges α s S ∪ shiftEdges (s + r) A' := by
  obtain ⟨α, times, rest, s, r, S, A', hhead, htimes, hs, hsr, hS, hrun,
      hAdef, hA'bound, hA'simple, hAeq⟩ :=
    pairSimpleRunEncoding_remainder_pairSimple_support hA hAsub hne
  cases times with
  | nil => exact (htimes rfl).elim
  | cons s' tail =>
    have hs' : s' = s := by simpa using hs
    subst s'
    have hneTimes : s :: tail ≠ [] := by simp
    have hcross := pairSimpleRunEncoding_head_time_order hA α (s :: tail) rest hhead
    have hgetLast : (s :: tail).getLast! = (s :: tail).getLast hneTimes := by
      unfold List.getLast!
      exact List.getLast_congr hneTimes hneTimes rfl
    have hlastMem : (s :: tail).getLast hneTimes ∈ s :: tail :=
      List.getLast_mem hneTimes
    have hafter : ∀ e ∈ MomentBounds.ccr25ExpandTimedRuns rest,
      s + r < e.1 := by
      intro e he
      have hlt := hcross ((s :: tail).getLast hneTimes) hlastMem e he
      have hend : s + r = (s :: tail).getLast hneTimes := by
        rw [← hgetLast]
        exact hsr
      omega
    have hadj := pairSimpleRunEncoding_labels_adjacentDistinct A
    rw [hhead, List.map_cons] at hadj
    cases rest with
    | nil =>
        have hA'empty : A' = ∅ := by
          rw [hAdef]
          simp [MomentBounds.ccr25ExpandTimedRuns]
        refine ⟨α, s :: tail, [], s, r, S, A', hhead, by simp, by simp, hsr, hS, hrun,
          hAdef, hA'bound, hA'simple, ?_, hAeq⟩
        intro e he
        rw [hA'empty] at he
        simp at he
    | cons run rest' =>
        rcases run with ⟨β, runTimes⟩
        have hneq : α ≠ β := by
          exact hadj.1
        have hrunTimes : runTimes ≠ [] := by
          have hmem : (β, runTimes) ∈ pairSimpleRunEncoding A := by
            rw [hhead]
            simp
          exact MomentBounds.ccr25EncodeTimedRuns_times_nonempty hmem
        cases runTimes with
        | nil => exact (hrunTimes rfl).elim
        | cons t₀ tail₂ =>
            let k := s + r
            let q : ℕ × CollisionPair h := (t₀, β)
            have hqmem : q ∈ MomentBounds.ccr25ExpandTimedRuns ((β, t₀ :: tail₂) :: rest') := by
              simp [q, MomentBounds.ccr25ExpandTimedRuns]
            have hqafter : k < q.1 := hafter q hqmem
            have hqA' : (q.1 - k, q.2) ∈ A' := by
              rw [hAdef]
              apply List.mem_toFinset.mpr
              apply List.mem_map.mpr
              exact ⟨q, hqmem, rfl⟩
            have htailPairwise :
                List.Pairwise (· < ·)
                  ((MomentBounds.ccr25ExpandTimedRuns ((β, t₀ :: tail₂) :: rest')).map Prod.fst) := by
              exact (pairSimpleRunEncoding_head_tail_order_facts hA α (s :: tail)
                ((β, t₀ :: tail₂) :: rest') hhead).2
            have htailNorm : MomentBounds.ccr25ExpandTimedRuns
                ((β, t₀ :: tail₂) :: rest') =
                  q :: ((tail₂.map fun t => (t, β)) ++ MomentBounds.ccr25ExpandTimedRuns rest') := by
              simp [q, MomentBounds.ccr25ExpandTimedRuns]
            have htailPairwise' : List.Pairwise (· < ·)
                (q.1 :: ((tail₂.map fun t => (t, β)).map Prod.fst ++
                  (MomentBounds.ccr25ExpandTimedRuns rest').map Prod.fst)) := by
              simpa [htailNorm, List.map_append] using htailPairwise
            have hqLeast (p : ℕ × CollisionPair h)
                (hp : p ∈ MomentBounds.ccr25ExpandTimedRuns ((β, t₀ :: tail₂) :: rest')) :
                q.1 ≤ p.1 := by
              have hp' : p ∈ q ::
                  ((tail₂.map fun t => (t, β)) ++ MomentBounds.ccr25ExpandTimedRuns rest') := by
                rw [← htailNorm]
                exact hp
              rcases List.mem_cons.mp hp' with hpq | hptail
              · exact le_of_eq (congrArg Prod.fst hpq).symm
              · have hfirst := (List.pairwise_cons.mp htailPairwise').1
                have hmemTimes : p.1 ∈
                    ((tail₂.map fun t => (t, β)).map Prod.fst ++
                      (MomentBounds.ccr25ExpandTimedRuns rest').map Prod.fst) := by
                  rcases List.mem_append.mp hptail with htail | hrest
                  · obtain ⟨t, ht, hp⟩ := List.mem_map.mp htail
                    have hpt : p = (t, β) := by simpa using hp.symm
                    subst p
                    exact List.mem_append.mpr (Or.inl
                      (List.mem_map.mpr ⟨(t, β),
                        List.mem_map.mpr ⟨t, ht, rfl⟩, rfl⟩))
                  · exact List.mem_append.mpr (Or.inr
                      (List.mem_map.mpr ⟨p, hrest, rfl⟩))
                exact le_of_lt (hfirst p.1 hmemTimes)
            have hfirstPair : FirstPairIn (Finset.univ.erase α) A' := by
              intro e he hmin
              rw [hAdef] at he
              obtain ⟨p, hp, hmap⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
              have hpA' : (p.1 - k, p.2) ∈ A' := by
                rw [hAdef]
                exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)
              have hqshift : q.1 - k ≤ p.1 - k :=
                Nat.sub_le_sub_right (hqLeast p hp) k
              have heTime : e.1 = q.1 - k := by
                have hmaptime := congrArg Prod.fst hmap
                have hminq := hmin (q.1 - k, q.2) hqA'
                have hminSource : p.1 - k ≤ q.1 - k := by
                  calc
                    p.1 - k = e.1 := hmaptime
                    _ ≤ q.1 - k := hminq
                calc
                  e.1 = p.1 - k := hmaptime.symm
                  _ = q.1 - k := le_antisymm hminSource hqshift
              have hsameTime : (p.1 - k) = (q.1 - k) := by
                have hmaptime := congrArg Prod.fst hmap
                exact hmaptime.trans heTime
              have hsameSourceTime : p.1 = q.1 := by
                dsimp [q, k] at *
                omega
              have hsameEdge : p = q := by
                have heq := hA'simple (p.1 - k, p.2) hpA'
                  (q.1 - k, q.2) hqA' hsameTime
                have hpair : p.2 = q.2 := by simpa using congrArg Prod.snd heq
                exact Prod.ext hsameSourceTime hpair
              have hpair : e.2 = β := by
                calc
                  e.2 = p.2 := (congrArg Prod.snd hmap).symm
                  _ = q.2 := congrArg Prod.snd hsameEdge
                  _ = β := by simp [q]
              rw [hpair]
              exact Finset.mem_erase.mpr ⟨hneq.symm, Finset.mem_univ _⟩
            refine ⟨α, s :: tail, (β, t₀ :: tail₂) :: rest', s, r, S, A', hhead,
              htimes, hs, hsr, hS, hrun, hAdef, hA'bound, hA'simple, hfirstPair, hAeq⟩

/-- The canonical first-run data of a nonempty pair-simple set satisfy the
finite ranges in the first-run sum. -/
theorem pairSimpleRunEncoding_firstRun_data_mem {n h : ℕ}
    (L : Finset (CollisionPair h)) {A : Finset (ℕ × CollisionPair h)}
    (hA : IsPairSimple A) (hAsub : A ⊆ collisionEdges n h)
    (hFirst : FirstPairIn L A) (hne : A ≠ ∅) :
    ∃ α, α ∈ L ∧ ∃ s, s ∈ Finset.Icc 1 n ∧
    ∃ r, r ∈ Finset.range (n - s + 1) ∧
    ∃ S, S ∈ runTimeSets r ∧
    ∃ A', A' ∈ (collisionEdges (n - s - r) h).powerset.filter
      (fun A' => IsPairSimple A' ∧ FirstPairIn (Finset.univ.erase α) A') ∧
      A = runEdges α s S ∪ shiftEdges (s + r) A' := by
  obtain ⟨α, times, rest, s, r, S, A', hhead, htimes, hs, hsr, hS, hrun,
      hAdef, hA'bound, hA'simple, hA'first, hAeq⟩ :=
    pairSimpleRunEncoding_remainder_firstPairIn hA hAsub hne
  have hleast := pairSimpleRunEncoding_firstRun_time_minimal hA hhead htimes hs
  have hstart : (s, α) ∈ runEdges α s S := Finset.mem_insert_self ..
  have hstartA : (s, α) ∈ A := by
    rw [hAeq]
    exact Finset.mem_union.mpr (Or.inl hstart)
  have hαL : α ∈ L := hFirst (s, α) hstartA (fun e he => hleast e he)
  have hsIcc : s ∈ Finset.Icc 1 n := by
    have htime := Finset.mem_product.mp (hAsub hstartA)
    simpa using htime.1
  have hSsub : S ⊆ Finset.Icc 1 r :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hrun).1
  have hEnd : r = 0 ∨ r ∈ S := (Finset.mem_filter.mp hrun).2
  have hterminal : (s + r, α) ∈ runEdges α s S := by
    change (s + r, α) ∈ insert (s, α) (S.image fun t => (s + t, α))
    rcases hEnd with hr | hr
    · subst r
      simp
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
  have hterminalA : (s + r, α) ∈ A := by
    rw [hAeq]
    exact Finset.mem_union.mpr (Or.inl hterminal)
  have hterminalTime : s + r ≤ n := by
    have ht := Finset.mem_product.mp (hAsub hterminalA)
    exact (Finset.mem_Icc.mp ht.1).2
  have hrRange : r ∈ Finset.range (n - s + 1) := by
    simp only [Finset.mem_range]
    omega
  have hA'mem : A' ∈ (collisionEdges (n - s - r) h).powerset.filter
      (fun B => IsPairSimple B ∧ FirstPairIn (Finset.univ.erase α) B) := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_powerset.mpr hA'bound, hA'simple, hA'first⟩
  exact ⟨α, hαL, s, hsIcc, r, hrRange, S, hrun, A', hA'mem, hAeq⟩

private theorem firstRunDatum_exists_of_decomposition {h : ℕ}
    (L : Finset (CollisionPair h)) (n : ℕ)
    {A : Finset (ℕ × CollisionPair h)} (hA : IsPairSimple A)
    (hAsub : A ⊆ collisionEdges n h) (hFirst : FirstPairIn L A) (hne : A ≠ ∅) :
    ∃ d : @FirstRunDatumType h, d ∈ firstRunDataSet L n ∧
      A = firstRunDatumEdges d := by
  obtain ⟨α, hα, s, hs, r, hr, S, hS, A', hA', hEq⟩ :=
    pairSimpleRunEncoding_firstRun_data_mem L hA hAsub hFirst hne
  refine ⟨⟨α, s, r, S, A'⟩, ?_, hEq⟩
  simp only [firstRunDataSet, Finset.mem_sigma]
  exact ⟨hα, hs, hr, hS, hA'⟩


/-- Every edge in a run lies between its first and last selected times. -/
theorem runEdges_time_mem_Icc {h : ℕ} (α : CollisionPair h) {s r : ℕ}
    {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 r)
    {e : ℕ × CollisionPair h} (he : e ∈ runEdges α s S) :
    e ∈ (Finset.Icc s (s + r)).product Finset.univ := by
  change e ∈ insert (s, α) (S.image fun t => (s + t, α)) at he
  rcases Finset.mem_insert.mp he with he | he
  · subst e
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨le_rfl, Nat.le_add_right s r⟩, Finset.mem_univ _⟩
  · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
    have ht' := Finset.mem_Icc.mp (hS ht)
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_univ _⟩

private theorem runEdges_terminal_mem {h : ℕ} (α : CollisionPair h) {s r : ℕ}
    {S : Finset ℕ} (hS : S ∈ runTimeSets r) :
    (s + r, α) ∈ runEdges α s S := by
  have hEnd : r = 0 ∨ r ∈ S := (Finset.mem_filter.mp hS).2
  change (s + r, α) ∈ insert (s, α) (S.image fun t => (s + t, α))
  rcases hEnd with hr | hr
  · subst r
    simp
  · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r, hr, rfl⟩)

/-- Shifting an available edge past the end of a run puts it strictly after the run. -/
theorem shiftEdges_time_gt_runEnd {h : ℕ} (s r m : ℕ)
    {A' : Finset (ℕ × CollisionPair h)} (hA' : A' ⊆ collisionEdges m h)
    {e : ℕ × CollisionPair h} (he : e ∈ shiftEdges (s + r) A') :
    s + r < e.1 := by
  obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
  have ht := Finset.mem_product.mp (hA' he')
  have ht' := Finset.mem_Icc.mp ht.1
  change s + r < e'.1 + (s + r)
  omega

/-- A first run and its shifted rest fit in the combined available time interval. -/
theorem runEdges_union_shiftEdges_subset_collisionEdges {h : ℕ}
    (α : CollisionPair h) {s r m n : ℕ} (hs : 1 ≤ s)
    (hn : s + r + m ≤ n) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 r)
    {A' : Finset (ℕ × CollisionPair h)} (hA' : A' ⊆ collisionEdges m h) :
    runEdges α s S ∪ shiftEdges (s + r) A' ⊆ collisionEdges n h := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · have ht := Finset.mem_product.mp (runEdges_time_mem_Icc α hS he)
    have ht' := Finset.mem_Icc.mp ht.1
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_univ _⟩
  · obtain ⟨e', he', rfl⟩ := Finset.mem_image.mp he
    have ht := Finset.mem_product.mp (hA' he')
    have ht' := Finset.mem_Icc.mp ht.1
    apply Finset.mem_product.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, Finset.mem_univ _⟩

/-- The first-run reconstruction is pair-simple when its shifted rest is pair-simple. -/
theorem runEdges_union_shiftEdges_pairSimple {h : ℕ} (α : CollisionPair h)
    {s r m : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 r)
    {A' : Finset (ℕ × CollisionPair h)} (hA' : A' ⊆ collisionEdges m h)
    (hAsimple : IsPairSimple A') :
    IsPairSimple (runEdges α s S ∪ shiftEdges (s + r) A') := by
  have hrunPair {e : ℕ × CollisionPair h} (he : e ∈ runEdges α s S) : e.2 = α := by
    change e ∈ insert (s, α) (S.image fun t => (s + t, α)) at he
    rcases Finset.mem_insert.mp he with he | he
    · exact congrArg Prod.snd he
    · obtain ⟨t, ht, he⟩ := Finset.mem_image.mp he
      exact (congrArg Prod.snd he).symm
  intro e he e' he' htime
  rcases Finset.mem_union.mp he with heRun | heRest
  · have htRun := Finset.mem_product.mp (runEdges_time_mem_Icc α hS heRun)
    rcases Finset.mem_union.mp he' with heRun' | heRest'
    · exact Prod.ext htime ((hrunPair heRun).trans (hrunPair heRun').symm)
    · have htRest := shiftEdges_time_gt_runEnd s r m hA' heRest'
      have htRun' := Finset.mem_Icc.mp htRun.1
      omega
  · rcases Finset.mem_union.mp he' with heRun' | heRest'
    · have htRest := shiftEdges_time_gt_runEnd s r m hA' heRest
      have htRun := Finset.mem_product.mp (runEdges_time_mem_Icc α hS heRun')
      have htRun' := Finset.mem_Icc.mp htRun.1
      omega
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp heRest
      obtain ⟨q', hq', rfl⟩ := Finset.mem_image.mp heRest'
      have hqq : q.1 = q'.1 := by
        have := htime
        exact Nat.add_right_cancel this
      have hqq' := hAsimple q hq q' hq' hqq
      exact Prod.ext (by simpa using congrArg Prod.fst hqq') (by simpa using congrArg Prod.snd hqq')

/-- The reconstructed set's first pair is the run letter, independently of the later rest. -/
theorem runEdges_union_shiftEdges_firstPairIn {h : ℕ} (L : Finset (CollisionPair h))
    (α : CollisionPair h) (hα : α ∈ L) {s r m : ℕ}
    {S : Finset ℕ} (_hS : S ⊆ Finset.Icc 1 r)
    {A' : Finset (ℕ × CollisionPair h)} (hA' : A' ⊆ collisionEdges m h) :
    FirstPairIn L (runEdges α s S ∪ shiftEdges (s + r) A') := by
  intro e he hmin
  rcases Finset.mem_union.mp he with heRun | heRest
  · change e ∈ insert (s, α) (S.image fun t => (s + t, α)) at heRun
    rcases Finset.mem_insert.mp heRun with heRun | heRun
    · subst e
      exact hα
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp heRun
      exact hα
  · have hstart : (s, α) ∈ runEdges α s S := Finset.mem_insert_self ..
    have hle := hmin (s, α) (Finset.mem_union.mpr (Or.inl hstart))
    have hgt := shiftEdges_time_gt_runEnd s r m hA' heRest
    omega

private theorem firstRunDatum_edges_mem_source {h : ℕ} (L : Finset (CollisionPair h))
    (n : ℕ) (d : @FirstRunDatumType h) (hd : d ∈ firstRunDataSet L n) :
    firstRunDatumEdges d ∈ (collisionEdges n h).powerset.filter
      (fun A => IsPairSimple A ∧ FirstPairIn L A) ∧ firstRunDatumEdges d ≠ ∅ := by
  rcases d with ⟨α, s, r, S, A'⟩
  simp only [firstRunDataSet, Finset.mem_sigma] at hd
  rcases hd with ⟨hα, hs, hr, hS, hA'⟩
  have hsIcc := Finset.mem_Icc.mp hs
  have hrRange := Finset.mem_range.mp hr
  have hSsub : S ⊆ Finset.Icc 1 r :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hA'sub : A' ⊆ collisionEdges (n - s - r) h :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hA').1
  have hA'simple := (Finset.mem_filter.mp hA').2.1
  have hA'first := (Finset.mem_filter.mp hA').2.2
  have hrs : s + r ≤ n := by omega
  have htime : s + r + (n - s - r) ≤ n := by omega
  have hsub : firstRunDatumEdges ⟨α, s, r, S, A'⟩ ⊆ collisionEdges n h := by
    exact runEdges_union_shiftEdges_subset_collisionEdges α (s := s) (r := r)
      (m := n - s - r) (n := n) (by omega) htime hSsub hA'sub
  have hsimple : IsPairSimple (firstRunDatumEdges ⟨α, s, r, S, A'⟩) := by
    exact runEdges_union_shiftEdges_pairSimple α hSsub hA'sub hA'simple
  have hfirst : FirstPairIn L (firstRunDatumEdges ⟨α, s, r, S, A'⟩) := by
    exact runEdges_union_shiftEdges_firstPairIn L α hα hSsub hA'sub
  have hstart : (s, α) ∈ firstRunDatumEdges ⟨α, s, r, S, A'⟩ :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self ..))
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hsimple, hfirst⟩, ?_⟩
  intro hempty
  rw [hempty] at hstart
  simp at hstart

private theorem exists_minimal_edge_pair_ne {h : ℕ} {α : CollisionPair h}
    {A : Finset (ℕ × CollisionPair h)} (hne : A ≠ ∅)
    (hFirst : FirstPairIn (Finset.univ.erase α) A) :
    ∃ e ∈ A, (∀ e' ∈ A, e.1 ≤ e'.1) ∧ e.2 ≠ α := by
  classical
  let T := A.image Prod.fst
  have hTne : T.Nonempty := by
    rcases Finset.nonempty_iff_ne_empty.mpr hne with ⟨e, he⟩
    exact ⟨e.1, Finset.mem_image.mpr ⟨e, he, rfl⟩⟩
  let t := T.min' hTne
  have htT : t ∈ T := Finset.min'_mem T hTne
  obtain ⟨e, he, het⟩ := Finset.mem_image.mp htT
  have hmin : ∀ e' ∈ A, e.1 ≤ e'.1 := by
    intro e' he'
    have hle := Finset.min'_le T e'.1 (Finset.mem_image.mpr ⟨e', he', rfl⟩)
    simpa [t, het] using hle
  have heL : e.2 ∈ Finset.univ.erase α := hFirst e he hmin
  exact ⟨e, he, hmin, (Finset.mem_erase.mp heL).1⟩

private def pairSimpleFirstPairInSet {h : ℕ} (L : Finset (CollisionPair h)) (n : ℕ) :=
  (collisionEdges n h).powerset.filter
    (fun A => IsPairSimple A ∧ FirstPairIn L A)

private noncomputable def firstRunDatumOfSource {h : ℕ} (L : Finset (CollisionPair h))
    (n : ℕ) {A : Finset (ℕ × CollisionPair h)}
    (hA : A ∈ (pairSimpleFirstPairInSet L n).filter (fun A => A ≠ ∅)) :
    @FirstRunDatumType h := by
  classical
  have houter := Finset.mem_filter.mp hA
  have hinner := Finset.mem_filter.mp houter.1
  have hsub : A ⊆ collisionEdges n h := Finset.mem_powerset.mp hinner.1
  exact Classical.choose
    (firstRunDatum_exists_of_decomposition L n hinner.2.1 hsub hinner.2.2 houter.2)

private theorem firstRunDatumOfSource_spec {h : ℕ} (L : Finset (CollisionPair h))
    (n : ℕ) {A : Finset (ℕ × CollisionPair h)}
    (hA : A ∈ (pairSimpleFirstPairInSet L n).filter (fun A => A ≠ ∅)) :
    firstRunDatumOfSource L n hA ∈ firstRunDataSet L n ∧
      A = firstRunDatumEdges (firstRunDatumOfSource L n hA) := by
  classical
  exact Classical.choose_spec (firstRunDatum_exists_of_decomposition L n
    (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).2.1
    (Finset.mem_powerset.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).1)
    (Finset.mem_filter.mp (Finset.mem_filter.mp hA).1).2.2
    (Finset.mem_filter.mp hA).2)

private theorem firstRunEnd_unique {h : ℕ} (α : CollisionPair h)
    (s r q mA mB : ℕ) {S T : Finset ℕ}
    (hS : S ∈ runTimeSets r) (hT : T ∈ runTimeSets q)
    {A' B' : Finset (ℕ × CollisionPair h)}
    (hA'sub : A' ⊆ collisionEdges mA h) (hB'sub : B' ⊆ collisionEdges mB h)
    (hA'first : FirstPairIn (Finset.univ.erase α) A')
    (hB'first : FirstPairIn (Finset.univ.erase α) B')
    (hEq : runEdges α s S ∪ shiftEdges (s + r) A' =
      runEdges α s T ∪ shiftEdges (s + q) B') : r = q := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hrq | hqr
  · have hterminal : (s + q, α) ∈ runEdges α s T := runEdges_terminal_mem α hT
    have hterminalA : (s + q, α) ∈ runEdges α s S ∪ shiftEdges (s + r) A' := by
      rw [hEq]
      exact Finset.mem_union.mpr (Or.inl hterminal)
    have hnotrun : (s + q, α) ∉ runEdges α s S := by
      intro he
      have ht := Finset.mem_Icc.mp
        (Finset.mem_product.mp (runEdges_time_mem_Icc α
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1) he)).1
      omega
    obtain ⟨e₀, he₀, he₀eq⟩ := Finset.mem_image.mp
      ((Finset.mem_union.mp hterminalA).resolve_left hnotrun)
    have he₀pair : e₀.2 = α := by
      have := congrArg Prod.snd he₀eq
      simpa [shiftEdges] using this
    have he₀time : e₀.1 + (s + r) = s + q := by
      have := congrArg Prod.fst he₀eq
      simpa [shiftEdges] using this
    have hA'ne : A' ≠ ∅ := by
      intro hzero
      rw [hzero] at he₀
      simp at he₀
    obtain ⟨e, he, hmin, hpair⟩ := exists_minimal_edge_pair_ne hA'ne hA'first
    have hshiftE : (e.1 + (s + r), e.2) ∈ shiftEdges (s + r) A' :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    have hshiftEB : (e.1 + (s + r), e.2) ∈
        runEdges α s T ∪ shiftEdges (s + q) B' := by
      rw [← hEq]
      exact Finset.mem_union.mpr (Or.inr hshiftE)
    have htimeLe : e.1 + (s + r) ≤ s + q := by
      have hle := hmin e₀ he₀
      omega
    rcases Finset.mem_union.mp hshiftEB with hrun | hrest
    · have hepair : e.2 = α := by
        change (e.1 + (s + r), e.2) ∈ insert (s, α) (T.image fun t => (s + t, α)) at hrun
        rcases Finset.mem_insert.mp hrun with h | h
        · exact congrArg Prod.snd h
        · obtain ⟨t, ht, h⟩ := Finset.mem_image.mp h
          exact (congrArg Prod.snd h).symm
      exact hpair hepair
    · have hlate := shiftEdges_time_gt_runEnd s q mB hB'sub hrest
      omega
  · have hterminal : (s + r, α) ∈ runEdges α s S := runEdges_terminal_mem α hS
    have hterminalB : (s + r, α) ∈ runEdges α s T ∪ shiftEdges (s + q) B' := by
      rw [← hEq]
      exact Finset.mem_union.mpr (Or.inl hterminal)
    have hnotrun : (s + r, α) ∉ runEdges α s T := by
      intro he
      have ht := Finset.mem_Icc.mp
        (Finset.mem_product.mp (runEdges_time_mem_Icc α
          (Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1) he)).1
      omega
    obtain ⟨e₀, he₀, he₀eq⟩ := Finset.mem_image.mp
      ((Finset.mem_union.mp hterminalB).resolve_left hnotrun)
    have he₀pair : e₀.2 = α := by
      have := congrArg Prod.snd he₀eq
      simpa [shiftEdges] using this
    have he₀time : e₀.1 + (s + q) = s + r := by
      have := congrArg Prod.fst he₀eq
      simpa [shiftEdges] using this
    have hB'ne : B' ≠ ∅ := by
      intro hzero
      rw [hzero] at he₀
      simp at he₀
    obtain ⟨e, he, hmin, hpair⟩ := exists_minimal_edge_pair_ne hB'ne hB'first
    have hshiftE : (e.1 + (s + q), e.2) ∈ shiftEdges (s + q) B' :=
      Finset.mem_image.mpr ⟨e, he, rfl⟩
    have hshiftEA : (e.1 + (s + q), e.2) ∈
        runEdges α s S ∪ shiftEdges (s + r) A' := by
      rw [hEq]
      exact Finset.mem_union.mpr (Or.inr hshiftE)
    have htimeLe : e.1 + (s + q) ≤ s + r := by
      have hle := hmin e₀ he₀
      omega
    rcases Finset.mem_union.mp hshiftEA with hrun | hrest
    · have hepair : e.2 = α := by
        change (e.1 + (s + q), e.2) ∈ insert (s, α) (S.image fun t => (s + t, α)) at hrun
        rcases Finset.mem_insert.mp hrun with h | h
        · exact congrArg Prod.snd h
        · obtain ⟨t, ht, h⟩ := Finset.mem_image.mp h
          exact (congrArg Prod.snd h).symm
      exact hpair hepair
    · have hlate := shiftEdges_time_gt_runEnd s r mA hA'sub hrest
      omega

private theorem firstRunDatum_injective {h : ℕ} (L : Finset (CollisionPair h)) (n : ℕ)
    {d e : @FirstRunDatumType h} (hd : d ∈ firstRunDataSet L n)
    (he : e ∈ firstRunDataSet L n)
    (hEq : firstRunDatumEdges d = firstRunDatumEdges e) : d = e := by
  classical
  rcases d with ⟨α, s, r, S, A'⟩
  rcases e with ⟨β, t, q, T, B'⟩
  simp only [firstRunDataSet, Finset.mem_sigma] at hd he
  rcases hd with ⟨hα, hs, hr, hS, hA'⟩
  rcases he with ⟨hβ, ht, hq, hT, hB'⟩
  have hSsub : S ⊆ Finset.Icc 1 r :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  have hTsub : T ⊆ Finset.Icc 1 q :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
  have hA'sub : A' ⊆ collisionEdges (n - s - r) h :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hA').1
  have hB'sub : B' ⊆ collisionEdges (n - t - q) h :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hB').1
  have hA'first := (Finset.mem_filter.mp hA').2.2
  have hB'first := (Finset.mem_filter.mp hB').2.2
  change runEdges α s S ∪ shiftEdges (s + r) A' =
    runEdges β t T ∪ shiftEdges (t + q) B' at hEq
  have hleft_start : (s, α) ∈ runEdges α s S ∪ shiftEdges (s + r) A' :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self ..))
  have hright_start : (t, β) ∈ runEdges β t T ∪ shiftEdges (t + q) B' :=
    Finset.mem_union.mpr (Or.inl (Finset.mem_insert_self ..))
  have hright_time_ge : ∀ z ∈ runEdges β t T ∪ shiftEdges (t + q) B', t ≤ z.1 := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzrun | hzrest
    · have htIcc := Finset.mem_Icc.mp
        (Finset.mem_product.mp (runEdges_time_mem_Icc β hTsub hzrun)).1
      exact htIcc.1
    · have hlate := shiftEdges_time_gt_runEnd t q (n - t - q) hB'sub hzrest
      omega
  have hleft_time_ge : ∀ z ∈ runEdges α s S ∪ shiftEdges (s + r) A', s ≤ z.1 := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzrun | hzrest
    · have hsIcc := Finset.mem_Icc.mp
        (Finset.mem_product.mp (runEdges_time_mem_Icc α hSsub hzrun)).1
      exact hsIcc.1
    · have hlate := shiftEdges_time_gt_runEnd s r (n - s - r) hA'sub hzrest
      omega
  have hstart_in_right : (s, α) ∈ runEdges β t T ∪ shiftEdges (t + q) B' := by
    rw [← hEq]
    exact hleft_start
  have hstart_in_left : (t, β) ∈ runEdges α s S ∪ shiftEdges (s + r) A' := by
    rw [hEq]
    exact hright_start
  have hts : t ≤ s := hright_time_ge (s, α) hstart_in_right
  have hst : s ≤ t := hleft_time_ge (t, β) hstart_in_left
  have hstime : s = t := Nat.le_antisymm hst hts
  subst t
  have hαβ : α = β := by
    rcases Finset.mem_union.mp hstart_in_right with hrun | hrest
    · change (s, α) ∈ insert (s, β) (T.image fun u => (s + u, β)) at hrun
      rcases Finset.mem_insert.mp hrun with hEqPair | hImage
      · exact congrArg Prod.snd hEqPair
      · obtain ⟨u, hu, hPair⟩ := Finset.mem_image.mp hImage
        exact (congrArg Prod.snd hPair).symm
    · have hlate := shiftEdges_time_gt_runEnd s q (n - s - q) hB'sub hrest
      simp at hlate
  subst β
  have hrq : r = q := firstRunEnd_unique α s r q (n - s - r) (n - s - q)
    hS hT hA'sub hB'sub hA'first hB'first hEq
  subst q
  have hST : S = T := by
    apply Finset.ext
    intro u
    constructor
    · intro hu
      have huIcc := Finset.mem_Icc.mp (hSsub hu)
      have hmem : (s + u, α) ∈ runEdges α s S ∪ shiftEdges (s + r) A' :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨u, hu, rfl⟩)))
      have hmem' : (s + u, α) ∈ runEdges α s T ∪ shiftEdges (s + r) B' := by
        rw [← hEq]
        exact hmem
      rcases Finset.mem_union.mp hmem' with hrun | hrest
      · have hrun' : (s + u, α) ∈ insert (s, α) (T.image fun v => (s + v, α)) := by
          change (s + u, α) ∈ runEdges α s T at hrun
          exact hrun
        rcases Finset.mem_insert.mp hrun' with hstart | himage
        · have := congrArg Prod.fst hstart
          simp at this
          omega
        · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp himage
          have htime := congrArg Prod.fst heq
          simp at htime
          have hvu : v = u := by omega
          simpa [hvu] using hv
      · have hlate := shiftEdges_time_gt_runEnd s r (n - s - r) hB'sub hrest
        have huUpper := huIcc.2
        omega
    · intro hu
      have huIcc := Finset.mem_Icc.mp (hTsub hu)
      have hmem : (s + u, α) ∈ runEdges α s T ∪ shiftEdges (s + r) B' :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨u, hu, rfl⟩)))
      have hmem' : (s + u, α) ∈ runEdges α s S ∪ shiftEdges (s + r) A' := by
        rw [hEq]
        exact hmem
      rcases Finset.mem_union.mp hmem' with hrun | hrest
      · have hrun' : (s + u, α) ∈ insert (s, α) (S.image fun v => (s + v, α)) := by
          change (s + u, α) ∈ runEdges α s S at hrun
          exact hrun
        rcases Finset.mem_insert.mp hrun' with hstart | himage
        · have := congrArg Prod.fst hstart
          simp at this
          omega
        · obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp himage
          have htime := congrArg Prod.fst heq
          simp at htime
          have hvu : v = u := by omega
          simpa [hvu] using hv
      · have hlate := shiftEdges_time_gt_runEnd s r (n - s - r) hA'sub hrest
        have huUpper := huIcc.2
        omega
  have hAB : A' = B' := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      have hmem : (z.1 + (s + r), z.2) ∈ runEdges α s S ∪ shiftEdges (s + r) A' :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
      have hmem' : (z.1 + (s + r), z.2) ∈ runEdges α s T ∪ shiftEdges (s + r) B' := by
        rw [← hEq]
        exact hmem
      rcases Finset.mem_union.mp hmem' with hrun | hrest
      · have htime := Finset.mem_Icc.mp
          (Finset.mem_product.mp (runEdges_time_mem_Icc α hTsub hrun)).1
        have hlate := shiftEdges_time_gt_runEnd s r (n - s - r) hA'sub
          (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
        omega
      · obtain ⟨z', hz', heq⟩ := Finset.mem_image.mp hrest
        have hfst := congrArg Prod.fst heq
        have hsnd := congrArg Prod.snd heq
        have htime : z'.1 = z.1 := by omega
        have hpair : z'.2 = z.2 := hsnd
        have hzEq : z' = z := Prod.ext htime hpair
        rw [← hzEq]
        exact hz'
    · intro hz
      have hmem : (z.1 + (s + r), z.2) ∈ runEdges α s T ∪ shiftEdges (s + r) B' :=
        Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨z, hz, rfl⟩))
      have hmem' : (z.1 + (s + r), z.2) ∈ runEdges α s S ∪ shiftEdges (s + r) A' := by
        rw [hEq]
        exact hmem
      rcases Finset.mem_union.mp hmem' with hrun | hrest
      · have htime := Finset.mem_Icc.mp
          (Finset.mem_product.mp (runEdges_time_mem_Icc α hSsub hrun)).1
        have hlate := shiftEdges_time_gt_runEnd s r (n - s - r) hB'sub
          (Finset.mem_image.mpr ⟨z, hz, rfl⟩)
        omega
      · obtain ⟨z', hz', heq⟩ := Finset.mem_image.mp hrest
        have hfst := congrArg Prod.fst heq
        have hsnd := congrArg Prod.snd heq
        have htime : z'.1 = z.1 := by omega
        have hpair : z'.2 = z.2 := hsnd
        have hzEq : z' = z := Prod.ext htime hpair
        rw [← hzEq]
        exact hz'
  subst T
  subst B'
  rfl

/-- Reindex the nonempty pair-simple edge sets by their unique maximal first
run and shifted remainder. -/
theorem sum_pairSimple_firstRun {h : ℕ} (L : Finset (CollisionPair h)) (n : ℕ)
    (F : Finset (ℕ × CollisionPair h) → ℝ) :
    ∑ A ∈ (collisionEdges n h).powerset.filter
        (fun A => IsPairSimple A ∧ FirstPairIn L A), F A =
      F ∅ + ∑ α ∈ L, ∑ s ∈ Finset.Icc 1 n,
        ∑ r ∈ Finset.range (n - s + 1), ∑ S ∈ runTimeSets r,
          ∑ A' ∈ (collisionEdges (n - s - r) h).powerset.filter
              (fun A' => IsPairSimple A' ∧ FirstPairIn (Finset.univ.erase α) A'),
            F (runEdges α s S ∪ shiftEdges (s + r) A') := by
  classical
  let P := pairSimpleFirstPairInSet L n
  let Q := P.filter (fun A => A ≠ ∅)
  have hempty : (∅ : Finset (ℕ × CollisionPair h)) ∈ P := by
    simp [P, pairSimpleFirstPairInSet, IsPairSimple, FirstPairIn]
  have hsplit : (∑ A ∈ P, F A) = F ∅ + ∑ A ∈ Q, F A := by
    rw [← Finset.sum_filter_add_sum_filter_not P (fun A => A ≠ ∅)]
    have hnonempty : P.filter (fun A => ¬ A ≠ ∅) = {∅} := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨hA, hne⟩
        simpa using hne
      · rintro rfl
        exact ⟨hempty, by simp⟩
    rw [hnonempty]
    simp only [Finset.sum_singleton]
    simp only [Q]
    ring
  have hbij : (∑ A ∈ Q, F A) =
      ∑ d ∈ firstRunDataSet L n, F (firstRunDatumEdges d) := by
    refine Finset.sum_bij' (s := Q) (t := firstRunDataSet L n)
      (i := fun A hA => firstRunDatumOfSource L n hA)
      (j := fun d _ => firstRunDatumEdges d) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      exact (firstRunDatumOfSource_spec L n hA).1
    · intro d hd
      exact Finset.mem_filter.mpr
        ⟨(firstRunDatum_edges_mem_source L n d hd).1,
          (firstRunDatum_edges_mem_source L n d hd).2⟩
    · intro A hA
      exact (firstRunDatumOfSource_spec L n hA).2.symm
    · intro d hd
      have hsrc : firstRunDatumEdges d ∈ Q := by
        exact Finset.mem_filter.mpr
          ⟨(firstRunDatum_edges_mem_source L n d hd).1,
            (firstRunDatum_edges_mem_source L n d hd).2⟩
      have hs := firstRunDatumOfSource_spec L n hsrc
      exact firstRunDatum_injective L n hs.1 hd hs.2.symm
    · intro A hA
      exact congrArg F (firstRunDatumOfSource_spec L n hA).2
  calc
    _ = F ∅ + ∑ A ∈ Q, F A := hsplit
    _ = F ∅ + ∑ d ∈ firstRunDataSet L n, F (firstRunDatumEdges d) := by rw [hbij]
    _ = _ := by rw [firstRunDatum_sum]


end Critical2DKPZ.SHF.Moments

end
