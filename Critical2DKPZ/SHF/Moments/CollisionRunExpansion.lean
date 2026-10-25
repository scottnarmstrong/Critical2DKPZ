/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WordExpansion
import Critical2DKPZ.Blocks.StringSumPropagation
public import Critical2DKPZ.MomentBounds.CCR25SequenceRunCompression
import Critical2DKPZ.SHF.Tsai.WordFactorization
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic

/-! # Exact resummations for the collision-word expansion -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer DeltaBose
attribute [local instance] Classical.propDecidable

/-- Shift every selected edge `k` steps later. -/
def shiftEdges {h : ℕ} (k : ℕ) (A : Finset (ℕ × CollisionPair h)) :
    Finset (ℕ × CollisionPair h) :=
  A.image fun e => (e.1 + k, e.2)

/-- The edges of one run of the pair `α`: its first edge at time `s`, then the further edges at the
times `s + t`, `t ∈ S`. -/
def runEdges {h : ℕ} (α : CollisionPair h) (s : ℕ) (S : Finset ℕ) :
    Finset (ℕ × CollisionPair h) :=
  insert (s, α) (S.image fun t => (s + t, α))

/-- The relative times of the further edges of a run of length `r`: subsets of `[1, r]` containing
`r` (only `∅` when `r = 0`). The last edge of the run is at its end. -/
def runTimeSets (r : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 r).powerset.filter fun S => r = 0 ∨ r ∈ S

/-- The earliest selected edge of `A`, if any, has its pair in `L`. -/
def FirstPairIn {h : ℕ} (L : Finset (CollisionPair h))
    (A : Finset (ℕ × CollisionPair h)) : Prop :=
  ∀ e ∈ A, (∀ e' ∈ A, e.1 ≤ e'.1) → e.2 ∈ L

/-- The word kernels summed over all words whose first letter, if any, lies in `L`. -/
def wordSumFrom {h : ℕ} (σ2 : ℝ) (L : Finset (CollisionPair h)) (n : ℕ)
    (x y : Fin h → Site) : ℝ :=
  ∑' m : ℕ, ∑ w : CollisionWord h m,
    if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ∈ L then
      blockWordKernel σ2 (List.ofFn w.1) n x y else 0

private def replicaPathsAppendEquiv (h t m : ℕ) :
    (Fin h → Fin (t + m) → Fin 4) ≃
      ((Fin h → Fin t → Fin 4) × (Fin h → Fin m → Fin 4)) where
  toFun p := ((fun i => ((Fin.appendEquiv t m).symm (p i)).1),
    (fun i => ((Fin.appendEquiv t m).symm (p i)).2))
  invFun p := fun i => (Fin.appendEquiv t m) (p.1 i, p.2 i)
  left_inv p := by
    funext i
    exact (Fin.appendEquiv t m).right_inv (p i)
  right_inv p := by
    apply Prod.ext
    · funext i j
      exact congrFun
        (congrArg Prod.fst ((Fin.appendEquiv t m).left_inv (p.1 i, p.2 i))) j
    · funext i j
      exact congrFun
        (congrArg Prod.snd ((Fin.appendEquiv t m).left_inv (p.1 i, p.2 i))) j

private theorem edgeIndicator_append_first {h t m : ℕ}
    (x : Fin h → Site) (p : Fin h → Fin t → Fin 4) (q : Fin h → Fin m → Fin 4)
    (e : ℕ × CollisionPair h) (he : e.1 ≤ t) :
    edgeIndicator x (fun i => Fin.append (p i) (q i)) e = edgeIndicator x p e := by
  simp only [edgeIndicator]
  rw [Polymer.walkPosition_append_le (x e.2.val.1) (p e.2.val.1) (q e.2.val.1) e.1 he,
    Polymer.walkPosition_append_le (x e.2.val.2) (p e.2.val.2) (q e.2.val.2) e.1 he]

private theorem edgeIndicator_append_shift {h t m : ℕ}
    (x : Fin h → Site) (p : Fin h → Fin t → Fin 4) (q : Fin h → Fin m → Fin 4)
    (e : ℕ × CollisionPair h) :
    edgeIndicator x (fun i => Fin.append (p i) (q i)) (e.1 + t, e.2) =
      edgeIndicator (fun i => walkPosition (x i) (p i) t) q e := by
  simp only [edgeIndicator]
  have ht : e.1 + t = t + e.1 := Nat.add_comm e.1 t
  rw [ht,
    Polymer.walkPosition_append_add (x e.2.val.1) (p e.2.val.1) (q e.2.val.1) e.1,
    Polymer.walkPosition_append_add (x e.2.val.2) (p e.2.val.2) (q e.2.val.2) e.1]

private theorem collisionEdgeProduct_append {h t m : ℕ}
    (A₁ : Finset (ℕ × CollisionPair h)) (A₂ : Finset (ℕ × CollisionPair h))
    (h₁ : A₁ ⊆ collisionEdges t h) (h₂ : A₂ ⊆ collisionEdges m h)
    (x : Fin h → Site) (p : Fin h → Fin t → Fin 4) (q : Fin h → Fin m → Fin 4) :
    (∏ e ∈ A₁ ∪ shiftEdges t A₂,
      edgeIndicator x (fun i => Fin.append (p i) (q i)) e) =
      (∏ e ∈ A₁, edgeIndicator x p e) *
        (∏ e ∈ A₂, edgeIndicator (fun i => walkPosition (x i) (p i) t) q e) := by
  classical
  have hdisj : Disjoint A₁ (shiftEdges t A₂) := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    obtain ⟨e₂, he₂', heeq⟩ := Finset.mem_image.mp he₂
    have htime₁ : e.1 ≤ t := by
      have hm := Finset.mem_product.mp (h₁ he₁)
      exact (Finset.mem_Icc.mp hm.1).2
    have htime₂ : 1 ≤ e₂.1 := by
      have hm := Finset.mem_product.mp (h₂ he₂')
      exact (Finset.mem_Icc.mp hm.1).1
    have heqtime : e.1 = e₂.1 + t := by
      have := congrArg Prod.fst heeq
      simpa [shiftEdges] using this.symm
    omega
  rw [Finset.prod_union hdisj, shiftEdges, Finset.prod_image]
  · congr 1
    · apply Finset.prod_congr rfl
      intro e he
      exact edgeIndicator_append_first x p q e (by
        have hm := Finset.mem_product.mp (h₁ he)
        exact (Finset.mem_Icc.mp hm.1).2)
    · apply Finset.prod_congr rfl
      intro e he
      exact edgeIndicator_append_shift x p q e
  · intro e he e' he' heeq
    change (e.1 + t, e.2) = (e'.1 + t, e'.2) at heeq
    rcases Prod.mk.inj heeq with ⟨htime, hpair⟩
    exact Prod.ext (Nat.add_right_cancel htime) hpair

private theorem endpointIndicator_eq_ite {h : ℕ} (z u : Fin h → Site) :
    (∏ i, if z i = u i then (1 : ℝ) else 0) = if z = u then 1 else 0 := by
  classical
  by_cases hzu : z = u
  · subst u
    simp
  · have hex : ∃ i, z i ≠ u i := by
      by_contra hn
      push Not at hn
      exact hzu (funext hn)
    obtain ⟨i, hi⟩ := hex
    have hzero : (∏ j, if z j = u j then (1 : ℝ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    simp [hzu, hzero]

/-- Markov property of the collision coefficients at time `t`: edges up to `t`, then edges after
`t` shifted back, joined at the configuration `u` at time `t`. -/
theorem collisionSubsetCoefficient_union_shiftEdges {h : ℕ} (t m : ℕ)
    {A₁ A₂ : Finset (ℕ × CollisionPair h)}
    (h₁ : A₁ ⊆ collisionEdges t h) (h₂ : A₂ ⊆ collisionEdges m h)
    (x y : Fin h → Site) :
    collisionSubsetCoefficient (t + m) h (A₁ ∪ shiftEdges t A₂) x y =
      ∑' u : Fin h → Site,
        collisionSubsetCoefficient t h A₁ x u *
          collisionSubsetCoefficient m h A₂ u y := by
  classical
  let P := (Fin h → Fin t → Fin 4)
  let Q := (Fin h → Fin m → Fin 4)
  let mid : P → (Fin h → Site) := fun p i => walkPosition (x i) (p i) t
  let c₁ : ℝ := ((4 : ℝ)⁻¹ ^ t) ^ h
  let c₂ : ℝ := ((4 : ℝ)⁻¹ ^ m) ^ h
  let pre : P → (Fin h → Site) → ℝ := fun p u =>
    c₁ * (∏ e ∈ A₁, edgeIndicator x p e) *
      ∏ i, if mid p i = u i then 1 else 0
  let post : Q → (Fin h → Site) → ℝ := fun q u =>
    c₂ * (∏ e ∈ A₂, edgeIndicator u q e) *
      ∏ i, if walkPosition (u i) (q i) m = y i then 1 else 0
  let R : Finset (Fin h → Site) := Finset.univ.image mid
  have hpre (u : Fin h → Site) :
      collisionSubsetCoefficient t h A₁ x u = ∑ p : P, pre p u := by
    simp [collisionSubsetCoefficient, pre, c₁, P, mid]
  have hpost (u : Fin h → Site) :
      collisionSubsetCoefficient m h A₂ u y = ∑ q : Q, post q u := by
    simp [collisionSubsetCoefficient, post, c₂, Q]
  have hc : ((4 : ℝ)⁻¹ ^ (t + m)) ^ h = c₁ * c₂ := by
    dsimp [c₁, c₂]
    rw [pow_add, mul_pow]
  have hsymm (p : P) (q : Q) :
      (replicaPathsAppendEquiv h t m).symm (p, q) =
        (fun i => Fin.append (p i) (q i)) := by
    rfl
  have hleft :
      collisionSubsetCoefficient (t + m) h (A₁ ∪ shiftEdges t A₂) x y =
        ∑ p : P, ∑ q : Q, pre p (mid p) * post q (mid p) := by
    let fullTerm (r : Fin h → Fin (t + m) → Fin 4) : ℝ :=
      ((4 : ℝ)⁻¹ ^ (t + m)) ^ h *
        (∏ e ∈ A₁ ∪ shiftEdges t A₂, edgeIndicator x r e) *
        ∏ i, if walkPosition (x i) (r i) (t + m) = y i then 1 else 0
    rw [collisionSubsetCoefficient]
    change (∑ r : Fin h → Fin (t + m) → Fin 4, fullTerm r) = _
    rw [← (replicaPathsAppendEquiv h t m).symm.sum_comp fullTerm,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hsymm p q]
    have hprod := collisionEdgeProduct_append A₁ A₂ h₁ h₂ x p q
    have hend (i : Fin h) :
        walkPosition (x i) (Fin.append (p i) (q i)) (t + m) =
          walkPosition (mid p i) (q i) m := by
      simpa [mid] using Polymer.walkPosition_append_end (x i) (p i) (q i)
    dsimp only [fullTerm]
    rw [hc, hprod]
    simp_rw [hend]
    simp [pre, post, mid, endpointIndicator_eq_ite]
    ring_nf
  have hsupport : ∀ u ∉ R, collisionSubsetCoefficient t h A₁ x u = 0 := by
    intro u hu
    rw [collisionSubsetCoefficient]
    apply Finset.sum_eq_zero
    intro p hp
    have hne : mid p ≠ u := by
      intro heq
      apply hu
      exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, heq⟩
    rw [endpointIndicator_eq_ite]
    simp [mid, hne]
  have hright :
      (∑' u : Fin h → Site,
        collisionSubsetCoefficient t h A₁ x u *
          collisionSubsetCoefficient m h A₂ u y) =
        ∑ p : P, ∑ q : Q, pre p (mid p) * post q (mid p) := by
    rw [tsum_eq_sum (s := R)]
    · simp_rw [hpre, hpost]
      calc
        _ = ∑ u ∈ R, ∑ p : P, ∑ q : Q, pre p u * post q u := by
          apply Finset.sum_congr rfl
          intro u hu
          calc
            _ = ∑ p : P, pre p u * (∑ q : Q, post q u) := by
              rw [← Finset.sum_mul]
            _ = _ := by
              apply Fintype.sum_congr
              intro p
              rw [← Finset.mul_sum]
        _ = ∑ p : P, ∑ q : Q, ∑ u ∈ R, pre p u * post q u := by
          calc
            _ = ∑ u ∈ R, ∑ z : P × Q, pre z.1 u * post z.2 u := by
              apply Finset.sum_congr rfl
              intro u hu
              exact (Fintype.sum_prod_type' (fun p q => pre p u * post q u)).symm
            _ = ∑ z : P × Q, ∑ u ∈ R, pre z.1 u * post z.2 u := by
              rw [Finset.sum_comm]
            _ = ∑ p : P, ∑ q : Q, ∑ u ∈ R, pre p u * post q u := by
              rw [Fintype.sum_prod_type]
        _ = ∑ p : P, ∑ q : Q, pre p (mid p) * post q (mid p) := by
          apply Fintype.sum_congr
          intro p
          apply Fintype.sum_congr
          intro q
          have hmid : mid p ∈ R := Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
          rw [Finset.sum_eq_single (mid p) (by
            intro u hu hune
            simp [pre, endpointIndicator_eq_ite, Ne.symm hune]) (by
              intro hnot
              exact False.elim (hnot hmid))]
    · intro u hu
      simp [hsupport u hu]
  exact hleft.trans hright.symm

/-- The equivalence labelling selected collision edges `(k, c)` by `(k, index of c)`. -/
noncomputable def collisionEdgeKeyEquiv {h : ℕ} :
    (ℕ × CollisionPair h) ≃ (ℕ × Fin (Fintype.card (CollisionPair h))) :=
  Equiv.prodCongr (Equiv.refl ℕ) (Fintype.equivFin (CollisionPair h))

/-- A total chronological order on selected collision edges, with a finite-label tie break. -/
noncomputable def collisionEdgeOrderKey {h : ℕ} (e : ℕ × CollisionPair h) :
    ℕ ×ₗ Fin (Fintype.card (CollisionPair h)) :=
  toLex (collisionEdgeKeyEquiv e)

/-- The relation `e ≤ e'` of the lexicographic order keys of two selected collision edges. -/
def collisionEdgeChronologicalRel {h : ℕ} (e e' : ℕ × CollisionPair h) : Prop :=
  collisionEdgeOrderKey e ≤ collisionEdgeOrderKey e'

/-- Distinct selected collision edges have distinct order keys. -/
theorem collisionEdgeOrderKey_injective {h : ℕ} :
    Function.Injective (collisionEdgeOrderKey (h := h)) := by
  intro a b hab
  apply collisionEdgeKeyEquiv.injective
  exact toLex_inj.mp hab

local instance {h : ℕ} : DecidableRel (collisionEdgeChronologicalRel (h := h)) :=
  inferInstance

local instance {h : ℕ} : IsTrans (ℕ × CollisionPair h)
    (collisionEdgeChronologicalRel (h := h)) :=
  ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩

local instance {h : ℕ} : Std.Antisymm (collisionEdgeChronologicalRel (h := h)) := by
  constructor
  intro e e' hee' he'e
  apply collisionEdgeOrderKey_injective
  exact le_antisymm hee' he'e

local instance {h : ℕ} : Std.Total (collisionEdgeChronologicalRel (h := h)) :=
  ⟨fun e e' => le_total (collisionEdgeOrderKey e) (collisionEdgeOrderKey e')⟩

/-- The collision edges of a finite set in chronological order. -/
noncomputable def collisionEdgeChronologicalList {h : ℕ}
    (A : Finset (ℕ × CollisionPair h)) : List (ℕ × CollisionPair h) :=
  A.sort collisionEdgeChronologicalRel

/-- Encode selected edges as maximal same-pair runs, retaining all times in each run. -/
noncomputable def pairSimpleRunEncoding {h : ℕ} (A : Finset (ℕ × CollisionPair h)) :
    List (CollisionPair h × List ℕ) :=
  MomentBounds.ccr25EncodeTimedRuns (collisionEdgeChronologicalList A)

/-- Expanding the maximal-run encoding recovers the selected edges in chronological order. -/
theorem pairSimpleRunEncoding_expand {h : ℕ} (A : Finset (ℕ × CollisionPair h)) :
    MomentBounds.ccr25ExpandTimedRuns (pairSimpleRunEncoding A) =
      collisionEdgeChronologicalList A := by
  classical
  exact MomentBounds.ccr25ExpandTimedRuns_encode _

/-- The maximal-run encoding is injective on edge subsets: expanding and erasing the order
recovers the original finite set. -/
theorem pairSimpleRunEncoding_reconstruct {h : ℕ} (A : Finset (ℕ × CollisionPair h)) :
    (MomentBounds.ccr25ExpandTimedRuns (pairSimpleRunEncoding A)).toFinset = A := by
  classical
  rw [pairSimpleRunEncoding_expand]
  change (A.sort collisionEdgeChronologicalRel).toFinset = A
  exact Finset.sort_toFinset (s := A) (r := collisionEdgeChronologicalRel)



/-- Consecutive run labels are distinct, so they form a collision word. -/
theorem pairSimpleRunEncoding_labels_adjacentDistinct {h : ℕ}
    (A : Finset (ℕ × CollisionPair h)) :
    MomentBounds.ccr25RunAdjacentDistinct ((pairSimpleRunEncoding A).map Prod.fst) :=
  MomentBounds.ccr25EncodeTimedRuns_adjacentDistinct _


/-- Pair simplicity makes the times in the chronological event list strictly increasing. -/
theorem pairSimpleEventList_times_pairwise {h : ℕ}
    (A : Finset (ℕ × CollisionPair h)) (hA : IsPairSimple A) :
    List.Pairwise (fun e e' : ℕ × CollisionPair h => e.1 < e'.1)
      (collisionEdgeChronologicalList A) := by
  classical
  have hsort : List.Pairwise collisionEdgeChronologicalRel
      (collisionEdgeChronologicalList A) := by
    change List.Pairwise collisionEdgeChronologicalRel (A.sort collisionEdgeChronologicalRel)
    exact Finset.pairwise_sort A collisionEdgeChronologicalRel
  have hnodup : List.Nodup (collisionEdgeChronologicalList A) := by
    change List.Nodup (A.sort collisionEdgeChronologicalRel)
    exact Finset.sort_nodup A collisionEdgeChronologicalRel
  have hmem : ∀ e ∈ collisionEdgeChronologicalList A, e ∈ A := by
    intro e he
    change e ∈ A.sort collisionEdgeChronologicalRel at he
    exact (Finset.mem_sort (s := A) (r := collisionEdgeChronologicalRel)).mp he
  have aux : ∀ xs : List (ℕ × CollisionPair h),
      List.Pairwise collisionEdgeChronologicalRel xs → xs.Nodup →
        (∀ e ∈ xs, e ∈ A) →
        List.Pairwise (fun e e' : ℕ × CollisionPair h => e.1 < e'.1) xs := by
    intro xs
    induction xs with
    | nil => intro hp hn hm; simp
    | cons e es ih =>
        intro hp hn hm
        rw [List.pairwise_cons] at hp ⊢
        rcases hp with ⟨hpHead, hpTail⟩
        rcases List.nodup_cons.mp hn with ⟨hne, hnTail⟩
        refine ⟨?_, ih hpTail hnTail ?_⟩
        · intro e' he'
          have heA : e ∈ A := hm e (by simp)
          have he'A : e' ∈ A := hm e' (by simp [he'])
          have hrel : collisionEdgeOrderKey e ≤ collisionEdgeOrderKey e' := hpHead e' he'
          have hkey : (collisionEdgeKeyEquiv e).1 ≤ (collisionEdgeKeyEquiv e').1 := by
            have hkey' := (Prod.Lex.toLex_le_toLex'
              (x := collisionEdgeKeyEquiv e) (y := collisionEdgeKeyEquiv e')).mp hrel
            exact hkey'.1
          have htime : e.1 ≤ e'.1 := by simpa [collisionEdgeKeyEquiv] using hkey
          have htimeNe : e.1 ≠ e'.1 := by
            intro htimeEq
            have heq : e = e' := hA e heA e' he'A htimeEq
            subst e'
            exact hne he'
          exact lt_of_le_of_ne htime htimeNe
        · intro z hz
          exact hm z (by simp [hz])
  exact aux _ hsort hnodup hmem

/-- The selected times within every maximal same-pair run are strictly
increasing. -/
theorem pairSimpleRunEncoding_times_pairwise {h : ℕ}
    (A : Finset (ℕ × CollisionPair h)) (hA : IsPairSimple A) :
    ∀ run ∈ pairSimpleRunEncoding A, run.2.Pairwise (· < ·) := by
  change ∀ run ∈ MomentBounds.ccr25EncodeTimedRuns
      (collisionEdgeChronologicalList A), run.2.Pairwise (· < ·)
  apply MomentBounds.ccr25EncodeTimedRuns_times_pairwise
  have htimes := pairSimpleEventList_times_pairwise A hA
  simpa only [List.pairwise_map] using htimes

/-- The number of edges of a run followed by a shifted rest. -/
theorem card_runEdges_union_shiftEdges {h : ℕ} (α : CollisionPair h) {s r m : ℕ}
    (_hs : 1 ≤ s) {S : Finset ℕ} (hS : S ⊆ Finset.Icc 1 r)
    {A' : Finset (ℕ × CollisionPair h)} (hA' : A' ⊆ collisionEdges m h) :
    (runEdges α s S ∪ shiftEdges (s + r) A').card = S.card + A'.card + 1 := by
  classical
  have hfirst_not : (s, α) ∉ S.image (fun t => (s + t, α)) := by
    intro he
    obtain ⟨t, ht, hte⟩ := Finset.mem_image.mp he
    have htpos := (Finset.mem_Icc.mp (hS ht)).1
    have htime := congrArg Prod.fst hte
    omega
  have hinjS : Set.InjOn (fun t : ℕ => (s + t, α)) S := by
    intro t ht t' ht' heq
    have htime := congrArg Prod.fst heq
    exact Nat.add_left_cancel htime
  have hrun_card : (runEdges α s S).card = S.card + 1 := by
    rw [runEdges, Finset.card_insert_of_notMem hfirst_not,
      Finset.card_image_of_injOn hinjS]
  have hshift_inj :
      Set.InjOn (fun e : ℕ × CollisionPair h => (e.1 + (s + r), e.2)) A' := by
    intro e he e' he' heq
    have htime := congrArg Prod.fst heq
    have hpair : e.2 = e'.2 := by simpa using congrArg Prod.snd heq
    exact Prod.ext (Nat.add_right_cancel htime) hpair
  have hshift_card : (shiftEdges (s + r) A').card = A'.card := by
    rw [shiftEdges, Finset.card_image_of_injOn hshift_inj]
  have hdisj : Disjoint (runEdges α s S) (shiftEdges (s + r) A') := by
    rw [Finset.disjoint_left]
    intro e he hf
    have hrun_time : e.1 ≤ s + r := by
      change e ∈ insert (s, α) (S.image fun t => (s + t, α)) at he
      rcases Finset.mem_insert.mp he with he | he
      · subst e
        change s ≤ s + r
        exact Nat.le_add_right s r
      · obtain ⟨t, ht, hte⟩ := Finset.mem_image.mp he
        have htle := (Finset.mem_Icc.mp (hS ht)).2
        have htime := congrArg Prod.fst hte
        rw [← htime]
        omega
    obtain ⟨e', he', heq⟩ := Finset.mem_image.mp hf
    have hpositive : 1 ≤ e'.1 := by
      have hmem := Finset.mem_product.mp (hA' he')
      exact (Finset.mem_Icc.mp hmem.1).1
    have htime : e.1 = e'.1 + (s + r) := by
      have := congrArg Prod.fst heq
      exact this.symm
    omega
  rw [Finset.card_union_of_disjoint hdisj, hrun_card, hshift_card]
  omega

private noncomputable def collisionWordFirstLetterEquiv (h m : ℕ) :
    CollisionWord h (m + 1) ≃
      Σ α : CollisionPair h,
        {w : CollisionWord h m // ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α} where
  toFun w := by
    refine ⟨w.1 ⟨0, by omega⟩,
      ⟨Critical2DKPZ.SHF.Tsai.collisionWord_dropHead w, ?_⟩⟩
    intro hm
    have hadj := w.2 ⟨0, by omega⟩ (Fin.succ ⟨0, hm⟩) (by simp)
    change w.1 (Fin.succ ⟨0, hm⟩) ≠ w.1 ⟨0, by omega⟩
    exact hadj.symm
  invFun p :=
    Critical2DKPZ.SHF.Tsai.collisionWord_cons p.1 p.2.1 p.2.2
  left_inv w := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases with
    | zero => rfl
    | succ i => rfl
  right_inv p := by
    cases p
    rfl

/-- Words with a first letter: a letter `α ∈ L`, then a word that does not start with `α`. -/
theorem sum_collisionWord_succ_firstIn {h : ℕ} (L : Finset (CollisionPair h)) (m : ℕ)
    (G : List (CollisionPair h) → ℝ) :
    (∑ w : CollisionWord h (m + 1), if w.1 0 ∈ L then G (List.ofFn w.1) else 0) =
      ∑ α ∈ L, ∑ w : CollisionWord h m,
        if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then G (α :: List.ofFn w.1) else 0 := by
  classical
  let e := collisionWordFirstLetterEquiv h m
  have hinner (α : CollisionPair h) :
      (∑ w : {w : CollisionWord h m //
          ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α},
        if α ∈ L then G (α :: List.ofFn w.1.1) else 0) =
        if α ∈ L then
          ∑ w : CollisionWord h m,
            if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
              G (α :: List.ofFn w.1) else 0 else 0 := by
    by_cases hα : α ∈ L
    · simp only [hα, ite_true]
      exact Critical2DKPZ.SHF.Tsai.fintype_sum_subtype_eq_sum_ite
        (p := fun w : CollisionWord h m =>
          ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α)
        (f := fun w => G (α :: List.ofFn w.1.1))
    · simp [hα]
  let f : (Σ α : CollisionPair h,
      {w : CollisionWord h m // ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α}) → ℝ := fun p =>
    if p.1 ∈ L then G (p.1 :: List.ofFn p.2.1.1) else 0
  calc
    _ = ∑ w : CollisionWord h (m + 1), f (e w) := by
      apply Fintype.sum_congr
      intro w
      simp [f, e, collisionWordFirstLetterEquiv,
        Critical2DKPZ.SHF.Tsai.collisionWord_dropHead, List.ofFn_succ]
    _ = ∑ p : Σ α : CollisionPair h,
          {w : CollisionWord h m // ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α}, f p := e.sum_comp f
    _ = ∑ α : CollisionPair h,
          (if α ∈ L then
            ∑ w : CollisionWord h m,
              if ∀ hm : 0 < m, w.1 ⟨0, hm⟩ ≠ α then
                G (α :: List.ofFn w.1) else 0 else 0) := by
      simp only [f]
      rw [Fintype.sum_sigma]
      apply Fintype.sum_congr
      intro α
      exact hinner α
    _ = _ := by simp [Finset.sum_ite_mem]

/-- Every fixed collision word kernel is nonnegative at nonnegative coupling. -/
theorem blockWordKernel_nonneg {h : ℕ} (σ2 : ℝ) (hσ : 0 ≤ σ2) :
    ∀ (w : List (CollisionPair h)) (n : ℕ) (x y : Fin h → Site),
      0 ≤ blockWordKernel σ2 w n x y := by
  intro w
  induction w with
  | nil =>
      intro n x y
      simp only [blockWordKernel]
      exact Finset.prod_nonneg fun i _ => Critical2DKPZ.srwKernel_nonneg n (y i - x i)
  | cons α w ih =>
      intro n x y
      simp only [blockWordKernel]
      apply Finset.sum_nonneg
      intro s hs
      apply Finset.sum_nonneg
      intro r hr
      apply tsum_nonneg
      intro u
      apply tsum_nonneg
      intro v
      have hfirst : 0 ≤ if u α.1.1 = u α.1.2 ∧ v α.1.1 = v α.1.2 then (1 : ℝ) else 0 := by
        split_ifs <;> norm_num
      have hfree : 0 ≤ ∏ i, Critical2DKPZ.srwKernel s (u i - x i) :=
        Finset.prod_nonneg fun i _ => Critical2DKPZ.srwKernel_nonneg s (u i - x i)
      have hrenewal : 0 ≤ Collision.spatialRenewal σ2 r (v α.1.1 - u α.1.1) :=
        Critical2DKPZ.Blocks.spatialRenewal_nonneg hσ r (v α.1.1 - u α.1.1)
      have hspectator : 0 ≤ ∏ i, if i = α.1.1 ∨ i = α.1.2 then (1 : ℝ) else
          Critical2DKPZ.srwKernel r (v i - u i) :=
        Finset.prod_nonneg fun i _ => by
          split_ifs
          · norm_num
          · exact Critical2DKPZ.srwKernel_nonneg r (v i - u i)
      have htail : 0 ≤ blockWordKernel σ2 w (n - s - r) v y := ih _ _ _
      positivity

/-- Split the exact collision expansion into pair-simple and non-pair edge sets. -/
theorem pointToPoint_collision_expansion_split (β : ℝ) (a n h : ℕ) (x y : Fin h → Site) :
    (∫ ω, ∏ i, pointToPoint β a n (x i) (y i) ω ∂disorderLaw) =
      (∑ A ∈ (collisionEdges n h).powerset.filter IsPairSimple,
        sigmaSq β ^ A.card * collisionSubsetCoefficient n h A x y) +
        nonpairCollisionRemainder β n h x y := by
  rw [pointToPoint_collision_expansion, nonpairCollisionRemainder]
  rw [← Finset.sum_filter_add_sum_filter_not ((collisionEdges n h).powerset) IsPairSimple]

/-- The non-pair remainder has nonnegative endpoint coefficients. -/
theorem nonpairCollisionRemainder_nonneg (β : ℝ) (n h : ℕ) (x y : Fin h → Site) :
    0 ≤ nonpairCollisionRemainder β n h x y := by
  classical
  unfold nonpairCollisionRemainder
  apply Finset.sum_nonneg
  intro A hA
  exact collision_term_nonneg β n h A x y


/-- A word with more letters than available time steps has zero kernel. -/
theorem blockWordKernel_eq_zero_of_length_gt {h : ℕ} (σ2 : ℝ) :
    ∀ (w : List (CollisionPair h)) (n : ℕ) (x y : Fin h → Site),
      n < w.length → blockWordKernel σ2 w n x y = 0 := by
  intro w
  induction w with
  | nil => intro n x y hn; simp at hn
  | cons α w ih =>
      intro n x y hn
      simp only [List.length_cons] at hn
      simp only [blockWordKernel]
      apply Finset.sum_eq_zero
      intro s hs
      apply Finset.sum_eq_zero
      intro r hr
      have hs' : 1 ≤ s ∧ s ≤ n := Finset.mem_Icc.mp hs
      have hr' : r < n - s + 1 := Finset.mem_range.mp hr
      have htail : n - s - r < w.length := by omega
      have hzero (v : Fin h → Site) :
          blockWordKernel σ2 w (n - s - r) v y = 0 := ih (n - s - r) v y htail
      simp_rw [hzero]
      simp


/-- The empty collision set contributes the product of the free walk kernels. -/
theorem collisionSubsetCoefficient_empty_eq_prod_srwKernel (n h : ℕ)
    (x y : Fin h → Site) :
    collisionSubsetCoefficient n h ∅ x y = ∏ i, srwKernel n (y i - x i) := by
  classical
  let c : ℝ := (4 : ℝ)⁻¹ ^ n
  rw [collisionSubsetCoefficient]
  simp only [Finset.prod_empty, mul_one]
  calc
    (∑ s : Fin h → Fin n → Fin 4,
        ((4 : ℝ)⁻¹ ^ n) ^ h *
          ∏ i, if walkPosition (x i) (s i) n = y i then 1 else 0) =
        c ^ h * ∑ s : Fin h → Fin n → Fin 4,
          ∏ i, if walkPosition (x i) (s i) n = y i then 1 else 0 := by
      dsimp [c]
      rw [Finset.mul_sum]
    _ = ∏ i : Fin h, ∑ r : Fin n → Fin 4,
          c * if walkPosition (x i) r n = y i then 1 else 0 := by
      rw [Fintype.prod_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.prod_mul_distrib, Finset.prod_const]
      simp [Fintype.card_fin]
    _ = ∏ i, srwKernel n (y i - x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [srwKernel]
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      have hcond : walkPosition (x i) r n = y i ↔
          walkPosition 0 r n = y i - x i := by
        rw [Polymer.walkPosition_eq_start_add]
        constructor
        · intro hxy
          calc
            walkPosition 0 r n = x i + walkPosition 0 r n - x i := by abel
            _ = y i - x i := by rw [hxy]
        · intro hxy
          calc
            x i + walkPosition 0 r n = x i + (y i - x i) := by rw [hxy]
            _ = y i := by abel
      simp only [hcond]


/-- A single selected edge at the final time is the endpoint collision of the selected pair. -/
theorem collisionSubsetCoefficient_singleton_end {h : ℕ} {s : ℕ} (_hs : 1 ≤ s)
    (α : CollisionPair h) (x u : Fin h → Site) :
    collisionSubsetCoefficient s h {(s, α)} x u =
      (if u α.1.1 = u α.1.2 then (1 : ℝ) else 0) *
        ∏ i, srwKernel s (u i - x i) := by
  classical
  let I : ℝ := if u α.1.1 = u α.1.2 then 1 else 0
  have hempty : collisionSubsetCoefficient s h ∅ x u =
      ∑ p : Fin h → Fin s → Fin 4,
        ((4 : ℝ)⁻¹ ^ s) ^ h *
          ∏ i, if walkPosition (x i) (p i) s = u i then 1 else 0 := by
    rw [collisionSubsetCoefficient]
    simp only [Finset.prod_empty, mul_one]
  have hedge (p : Fin h → Fin s → Fin 4) :
      edgeIndicator x p (s, α) *
        (∏ i, if walkPosition (x i) (p i) s = u i then (1 : ℝ) else 0) =
      I *
        (∏ i, if walkPosition (x i) (p i) s = u i then (1 : ℝ) else 0) := by
    by_cases h₁ : walkPosition (x α.1.1) (p α.1.1) s = u α.1.1
    · by_cases h₂ : walkPosition (x α.1.2) (p α.1.2) s = u α.1.2
      · simp [edgeIndicator, h₁, h₂, I]
      · have hp :
            (∏ i, if walkPosition (x i) (p i) s = u i then (1 : ℝ) else 0) = 0 :=
          Finset.prod_eq_zero (Finset.mem_univ α.1.2) (by simp [h₂])
        rw [hp]
        simp [I, edgeIndicator]
    · have hp :
          (∏ i, if walkPosition (x i) (p i) s = u i then (1 : ℝ) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ α.1.1) (by simp [h₁])
      rw [hp]
      simp [I]
  have hsum :
      (∑ p : Fin h → Fin s → Fin 4,
        ((4 : ℝ)⁻¹ ^ s) ^ h * edgeIndicator x p (s, α) *
          ∏ i, if walkPosition (x i) (p i) s = u i then 1 else 0) =
        I * ∑ p : Fin h → Fin s → Fin 4,
          ((4 : ℝ)⁻¹ ^ s) ^ h *
            ∏ i, if walkPosition (x i) (p i) s = u i then 1 else 0 := by
    calc
      _ = ∑ p : Fin h → Fin s → Fin 4,
          I * (((4 : ℝ)⁻¹ ^ s) ^ h *
            ∏ i, if walkPosition (x i) (p i) s = u i then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro p hp
        calc
          _ = ((4 : ℝ)⁻¹ ^ s) ^ h *
              (edgeIndicator x p (s, α) *
                ∏ i, if walkPosition (x i) (p i) s = u i then 1 else 0) := by ring
          _ = ((4 : ℝ)⁻¹ ^ s) ^ h *
              (I * ∏ i, if walkPosition (x i) (p i) s = u i then 1 else 0) := by
                rw [hedge p]
          _ = _ := by ring
      _ = _ := by rw [Finset.mul_sum]
  have hsingleton : collisionSubsetCoefficient s h {(s, α)} x u =
      (∑ p : Fin h → Fin s → Fin 4,
        ((4 : ℝ)⁻¹ ^ s) ^ h * edgeIndicator x p (s, α) *
          ∏ i, if walkPosition (x i) (p i) s = u i then 1 else 0) := by
    rw [collisionSubsetCoefficient]
    simp only [Finset.prod_singleton]
  have hcoef : collisionSubsetCoefficient s h {(s, α)} x u =
      I * collisionSubsetCoefficient s h ∅ x u := by
    calc
      _ = _ := hsingleton
      _ = I * collisionSubsetCoefficient s h ∅ x u := by
        rw [hsum, ← hempty]
  calc
    _ = I * collisionSubsetCoefficient s h ∅ x u := hcoef
    _ = I * ∏ i, srwKernel s (u i - x i) := by
      rw [collisionSubsetCoefficient_empty_eq_prod_srwKernel]
    _ = _ := by rfl







end Critical2DKPZ.SHF.Moments

end
