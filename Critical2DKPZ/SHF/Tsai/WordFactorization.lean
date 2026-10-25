/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeadTail
import Mathlib.Tactic

/-! # Factor a prescribed long collision word into head and tail -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Prepending a pair preserves admissibility when it differs from the old first pair. -/
def collisionWord_cons {n m : ℕ} (α : CollisionPair n) (w : CollisionWord n m)
    (hfirst : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ α) :
    CollisionWord n (m + 1) := by
  refine ⟨Fin.cons α w.1, ?_⟩
  intro i j hij
  cases i using Fin.cases with
  | zero =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j =>
          have hjval : j.val = 0 := by simpa [Fin.val_succ] using hij
          have hm : 0 < m := by have := j.isLt; omega
          have hj0 : j = (⟨0, hm⟩ : Fin m) := Fin.ext (by simpa using hjval)
          subst j
          change α ≠ w.1 (⟨0, hm⟩ : Fin m)
          exact (hfirst hm).symm
  | succ i =>
      cases j using Fin.cases with
      | zero => simp at hij
      | succ j =>
          have hij' : i.val + 1 = j.val := by
            simpa [Fin.val_succ] using hij
          exact w.2 i j hij'

/-- Removing the first letter of an admissible word leaves an admissible word. -/
def collisionWord_dropHead {n m : ℕ} (w : CollisionWord n (m + 1)) : CollisionWord n m :=
  ⟨fun i => w.1 i.succ, by
    intro i j hij
    apply w.2 i.succ j.succ
    simpa [Fin.val_succ] using hij⟩

/-- Split a collision word into its first two letters and its continuation. -/
noncomputable def collisionWordSplit₂ (n m : ℕ) :
    CollisionWord n (m + 2) ≃
      Σ α : CollisionPair n, Σ β : CollisionPair n,
        {w : CollisionWord n m // α ≠ β ∧ ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β} := by
  classical
  refine
    { toFun := ?_
      invFun := ?_
      left_inv := ?_
      right_inv := ?_ }
  · intro w
    let v := collisionWord_dropHead w
    let r := collisionWord_dropHead v
    refine ⟨w.1 ⟨0, by omega⟩, v.1 ⟨0, by omega⟩, r, ?_, ?_⟩
    · have h := w.2 ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
      exact h
    · intro h
      have hadj := v.2 ⟨0, by omega⟩ (Fin.succ ⟨0, h⟩) (by simp)
      change v.1 (Fin.succ ⟨0, h⟩) ≠ v.1 ⟨0, by omega⟩
      exact hadj.symm
  · rintro ⟨α, β, ⟨w, hαβ, hfirst⟩⟩
    have htail : ∀ h : 0 < m + 1,
        (collisionWord_cons β w hfirst).1 ⟨0, h⟩ ≠ α := by
      intro h
      change β ≠ α
      exact hαβ.symm
    exact collisionWord_cons α (collisionWord_cons β w hfirst) htail
  · intro w
    apply Subtype.ext
    funext i
    cases i using Fin.cases with
    | zero =>
        simp only [collisionWord_cons, collisionWord_dropHead, Fin.cons_zero]
        congr 1
    | succ i =>
      cases i using Fin.cases with
      | zero =>
          simp only [collisionWord_cons, collisionWord_dropHead, Fin.cons_succ, Fin.cons_zero]
          congr 1
      | succ i => simp only [collisionWord_cons, collisionWord_dropHead, Fin.cons_succ]
  · rintro ⟨α, β, ⟨w, hαβ, hfirst⟩⟩
    apply Sigma.ext
    · rfl
    · rfl

/-- Reindex a fixed long-word sum by its first two collision letters. -/
theorem diagramWordSum_eq_split {n : ℕ} (θ t : ℝ) (x y : Configuration n) (m : ℕ) :
    (∑ w : CollisionWord n (m + 2), diagramKernel θ (List.ofFn w.1) t x y) =
      ∑ α : CollisionPair n, ∑ β : CollisionPair n,
        ∑ w : {w : CollisionWord n m //
            α ≠ β ∧ ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β},
          diagramKernel θ (α :: β :: List.ofFn w.1.1) t x y := by
  classical
  rw [← (collisionWordSplit₂ n m).symm.sum_comp]
  simp_rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro α hα
  apply Finset.sum_congr rfl
  intro β hβ
  apply Finset.sum_congr rfl
  intro w hw
  simp only [collisionWordSplit₂, Equiv.symm, Equiv.coe_fn_mk, collisionWord_cons,
    collisionWord_dropHead, Fin.cons_zero, Fin.cons_succ, List.ofFn_succ]

/-- A finite sum over a subtype is the sum over the carrier with a membership indicator. -/
theorem fintype_sum_subtype_eq_sum_ite {ι M : Type*} [Fintype ι] [AddCommMonoid M]
    (p : ι → Prop) [DecidablePred p] (f : {i // p i} → M) :
    (∑ i : {i // p i}, f i) = ∑ i, if h : p i then f ⟨i, h⟩ else 0 := by
  classical
  let g : ι → M := fun i => if h : p i then f ⟨i, h⟩ else 0
  have hfalse : (∑ i : {i // ¬ p i}, g i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    simp [g, i.property]
  calc
    (∑ i : {i // p i}, f i) = ∑ i : {i // p i}, g i := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [g, i.property]
    _ = (∑ i : {i // p i}, g i) + ∑ i : {i // ¬ p i}, g i := by rw [hfalse, add_zero]
    _ = ∑ i, g i := Fintype.sum_subtype_add_sum_subtype p g
    _ = _ := rfl

/-- The same reindexing as a sum over all continuations with an explicit admissibility indicator. -/
theorem diagramWordSum_eq_filtered {n : ℕ} (θ t : ℝ) (x y : Configuration n) (m : ℕ) :
    (∑ w : CollisionWord n (m + 2), diagramKernel θ (List.ofFn w.1) t x y) =
      ∑ α : CollisionPair n, ∑ β : CollisionPair n, ∑ w : CollisionWord n m,
        if α ≠ β ∧ (∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β) then
          diagramKernel θ (α :: β :: List.ofFn w.1) t x y else 0 := by
  classical
  rw [diagramWordSum_eq_split]
  simp_rw [fintype_sum_subtype_eq_sum_ite]
  rfl

/-- A word beginning with two collisions splits at the merge of its second pair. -/
theorem diagramKernel_cons_cons_eq_head_tail {n : ℕ} (θ : ℝ) (α β : CollisionPair n)
    (w : List (CollisionPair n)) (t : ℝ) (ht : 0 < t)
    (x y : Configuration n) :
    diagramKernel θ (α :: β :: w) t x y =
      ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
        headKernel θ α β s x z * tailWordKernel θ β w (t - s) z y := by
  let P : TimeKernel (Configuration n) (FusedConfiguration α) :=
    causalKernel (freeTimeKernel id (collisionEmbedding α))
  let J : TimeKernel (FusedConfiguration α) (FusedConfiguration α) :=
    causalKernel (collisionTimeKernel α θ)
  let S : TimeKernel (FusedConfiguration α) (FusedConfiguration β) :=
    causalKernel (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β))
  let Jβ : TimeKernel (FusedConfiguration β) (FusedConfiguration β) :=
    causalKernel (collisionTimeKernel β θ)
  let R : TimeKernel (FusedConfiguration β) (Configuration n) :=
    causalKernel (pathTimeKernel θ w (collisionEmbedding β) id)
  let T : TimeKernel (FusedConfiguration β) (Configuration n) :=
    timeKernelComp volume Jβ R
  have hP : Measurable P := by
    dsimp [P]
    exact measurable_causalKernel
      (measurable_freeTimeKernel measurable_id (measurable_collisionEmbedding α))
  have hJ : Measurable J := by
    dsimp [J]
    exact measurable_causalKernel (measurable_collisionTimeKernel α θ)
  have hS : Measurable S := by
    dsimp [S]
    exact measurable_causalKernel
      (measurable_freeTimeKernel (measurable_collisionEmbedding α) (measurable_collisionEmbedding β))
  have hJβ : Measurable Jβ := by
    dsimp [Jβ]
    exact measurable_causalKernel (measurable_collisionTimeKernel β θ)
  have hR : Measurable R := by
    dsimp [R]
    exact measurable_causalKernel
      (measurable_pathTimeKernel θ w (measurable_collisionEmbedding β) measurable_id)
  have hT : Measurable T := by
    dsimp [T]
    exact measurable_timeKernelComp volume hJβ hR
  have hJS : Measurable (timeKernelComp volume J S) :=
    measurable_timeKernelComp volume hJ hS
  have hHeadTime : Measurable (headTimeKernel θ α β) := by
    change Measurable (timeKernelComp volume P (timeKernelComp volume J S))
    exact measurable_timeKernelComp volume hP hJS
  have hTailTime : Measurable (tailWordTimeKernel θ β w) := by
    change Measurable T
    exact hT
  have hAssoc₁ :
      timeKernelComp volume (timeKernelComp volume J S) T =
        timeKernelComp volume J (timeKernelComp volume S T) :=
    timeKernelComp_assoc volume volume hJ hS hT
  have hAssoc₂ :
      timeKernelComp volume
          (timeKernelComp volume P (timeKernelComp volume J S)) T =
        timeKernelComp volume P (timeKernelComp volume (timeKernelComp volume J S) T) :=
    timeKernelComp_assoc volume volume hP hJS hT
  have hPath :
      pathTimeKernel θ (α :: β :: w) id id =
        timeKernelComp volume (headTimeKernel θ α β) (tailWordTimeKernel θ β w) := by
    have hRpath : pathTimeKernel θ w (collisionEmbedding β) id = R := by
      dsimp [R]
      exact (pathTimeKernel_causal θ w (collisionEmbedding β) id).symm
    change timeKernelComp volume P
        (timeKernelComp volume J
          (timeKernelComp volume S
            (timeKernelComp volume Jβ (pathTimeKernel θ w (collisionEmbedding β) id)))) = _
    rw [hRpath]
    rw [← hAssoc₁, ← hAssoc₂]
    rfl
  have hHeadC : causalKernel (headTimeKernel θ α β) = headTimeKernel θ α β := by
    have hPC : causalKernel P = P := by
      dsimp [P]
      exact causalKernel_idem _
    have hJSC : causalKernel (timeKernelComp volume J S) = timeKernelComp volume J S := by
      dsimp [J, S]
      exact timeKernelComp_causal volume (collisionTimeKernel α θ)
        (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β))
    have h := timeKernelComp_causal volume P (timeKernelComp volume J S)
    simpa only [headTimeKernel, P, J, S, hPC, hJSC] using h
  have hRC : causalKernel R = R := by
    dsimp [R]
    exact causalKernel_idem _
  have hTC : causalKernel T = T := by
    have hJβC : causalKernel Jβ = Jβ := by
      dsimp [Jβ]
      exact causalKernel_idem _
    have h := timeKernelComp_causal volume Jβ R
    simpa only [T, Jβ, R, hJβC, hRC] using h
  have hTailC : causalKernel (tailWordTimeKernel θ β w) = tailWordTimeKernel θ β w := by
    simpa only [tailWordTimeKernel, T, Jβ, R] using hTC
  have hPathDiagram := pathTimeKernel_eq_diagram θ (α :: β :: w)
    (measurable_id : Measurable (fun x : Configuration n => x))
    (measurable_id : Measurable (fun y : Configuration n => y))
  have hDiagram :
      diagramKernel θ (α :: β :: w) t x y =
        timeKernelComp volume (causalKernel (headTimeKernel θ α β))
          (causalKernel (tailWordTimeKernel θ β w)) (t, x, y) := by
    have hEval := congrFun hPathDiagram (t, x, y)
    rw [causalKernel_of_pos _ ht] at hEval
    rw [hPath] at hEval
    rw [← hHeadC, ← hTailC] at hEval
    exact hEval.symm
  rw [hDiagram, timeKernelComp_causal_eq volume hHeadTime hTailTime t x y]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
  apply lintegral_congr_ae
  filter_upwards [] with z
  rw [← headKernel_eq_headTimeKernel θ α β s x z,
    ← tailWordKernel_eq_tailWordTimeKernel θ β w (t - s) z y]

/-- Measurability of a head factor in its cut time and fused endpoint. -/
theorem measurable_headKernel_apply {n : ℕ} (θ : ℝ) (α β : CollisionPair n) (x : Configuration n) :
    Measurable (fun p : ℝ × FusedConfiguration β => headKernel θ α β p.1 x p.2) := by
  let P : TimeKernel (Configuration n) (FusedConfiguration α) :=
    causalKernel (freeTimeKernel id (collisionEmbedding α))
  let J : TimeKernel (FusedConfiguration α) (FusedConfiguration α) :=
    causalKernel (collisionTimeKernel α θ)
  let S : TimeKernel (FusedConfiguration α) (FusedConfiguration β) :=
    causalKernel (freeTimeKernel (collisionEmbedding α) (collisionEmbedding β))
  have hP : Measurable P := by
    dsimp [P]
    exact measurable_causalKernel
      (measurable_freeTimeKernel measurable_id (measurable_collisionEmbedding α))
  have hJ : Measurable J := by
    dsimp [J]
    exact measurable_causalKernel (measurable_collisionTimeKernel α θ)
  have hS : Measurable S := by
    dsimp [S]
    exact measurable_causalKernel
      (measurable_freeTimeKernel (measurable_collisionEmbedding α) (measurable_collisionEmbedding β))
  have hJS : Measurable (timeKernelComp volume J S) := measurable_timeKernelComp volume hJ hS
  have hHead : Measurable (headTimeKernel θ α β) := by
    change Measurable (timeKernelComp volume P (timeKernelComp volume J S))
    exact measurable_timeKernelComp volume hP hJS
  have hmap : Measurable (fun p : ℝ × FusedConfiguration β => (p.1, x, p.2)) := by fun_prop
  have hcomp := hHead.comp hmap
  intro s hs
  have hpre :
      (fun p : ℝ × FusedConfiguration β => headKernel θ α β p.1 x p.2) ⁻¹' s =
        (headTimeKernel θ α β ∘ fun p : ℝ × FusedConfiguration β => (p.1, x, p.2)) ⁻¹' s := by
    ext p
    exact Iff.of_eq
      (congrArg (fun v => v ∈ s) (headKernel_eq_headTimeKernel θ α β p.1 x p.2))
  rw [hpre]
  exact hcomp hs

/-- Measurability of one tail word in its remaining time and fused endpoint. -/
theorem measurable_tailWordKernel_apply {n : ℕ} (θ : ℝ) (β : CollisionPair n)
    (w : List (CollisionPair n)) (t : ℝ) (y : Configuration n) :
    Measurable (fun p : ℝ × FusedConfiguration β =>
      tailWordKernel θ β w (t - p.1) p.2 y) := by
  have hJ : Measurable (collisionTimeKernel β θ) := measurable_collisionTimeKernel β θ
  have hPath : Measurable (pathTimeKernel θ w (collisionEmbedding β) id) :=
    measurable_pathTimeKernel θ w (measurable_collisionEmbedding β) measurable_id
  have hTail : Measurable (tailWordTimeKernel θ β w) := by
    exact measurable_timeKernelComp volume (measurable_causalKernel hJ)
      (measurable_causalKernel hPath)
  have hmap : Measurable (fun p : ℝ × FusedConfiguration β => (t - p.1, p.2, y)) := by
    fun_prop
  have hcomp := hTail.comp hmap
  intro s hs
  have hpre :
      (fun p : ℝ × FusedConfiguration β => tailWordKernel θ β w (t - p.1) p.2 y) ⁻¹' s =
        (tailWordTimeKernel θ β w ∘ fun p : ℝ × FusedConfiguration β => (t - p.1, p.2, y)) ⁻¹' s := by
    ext p
    exact Iff.of_eq (congrArg (fun v => v ∈ s)
      (tailWordKernel_eq_tailWordTimeKernel θ β w (t - p.1) p.2 y))
  rw [hpre]
  exact hcomp hs

/-- Measurability of the resummed tail in its remaining time and fused endpoint. -/
theorem measurable_tailKernel_apply {n : ℕ} (θ : ℝ) (β : CollisionPair n)
    (t : ℝ) (y : Configuration n) :
    Measurable (fun p : ℝ × FusedConfiguration β => tailKernel θ β (t - p.1) p.2 y) := by
  change Measurable (fun p : ℝ × FusedConfiguration β =>
    ∑' m : ℕ, ∑ w : CollisionWord n m,
      if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
        tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y else 0)
  apply Measurable.tsum
  intro m
  apply Finset.measurable_sum
  intro w hw
  by_cases h : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β
  · have heq : (fun p : ℝ × FusedConfiguration β =>
        if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
          tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y else 0) =
      fun p => tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y := by
        funext p
        exact ite_eq_left h
    rw [heq]
    exact measurable_tailWordKernel_apply θ β (List.ofFn w.1) t y
  · have heq : (fun p : ℝ × FusedConfiguration β =>
        if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
          tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y else 0) =
      fun _ => 0 := by
        funext p
        exact ite_eq_right h
    rw [heq]
    exact measurable_const

/-- Tonelli expands the resummed tail under the head cut integral, word by word. -/
theorem headKernel_mul_tailKernel_eq_tsum {n : ℕ} (θ : ℝ) (α β : CollisionPair n)
    (t : ℝ) (x y : Configuration n) :
    (∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
      headKernel θ α β s x z * tailKernel θ β (t - s) z y) =
      ∑' m : ℕ, ∑ w : CollisionWord n m,
        if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
          ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
            headKernel θ α β s x z * tailWordKernel θ β (List.ofFn w.1) (t - s) z y
        else 0 := by
  let μ : Measure ℝ := volume.restrict (Ioo 0 t)
  let ν : Measure (FusedConfiguration β) := volume
  let H : ℝ × FusedConfiguration β → ℝ≥0∞ := fun p =>
    headKernel θ α β p.1 x p.2 * tailKernel θ β (t - p.1) p.2 y
  let term (m : ℕ) (w : CollisionWord n m) :
      ℝ × FusedConfiguration β → ℝ≥0∞ := fun p =>
    if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
      headKernel θ α β p.1 x p.2 *
        tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y else 0
  let block (m : ℕ) : ℝ × FusedConfiguration β → ℝ≥0∞ := fun p =>
    ∑ w : CollisionWord n m, term m w p
  have hhead : Measurable (fun p : ℝ × FusedConfiguration β =>
      headKernel θ α β p.1 x p.2) := measurable_headKernel_apply θ α β x
  have htail : Measurable (fun p : ℝ × FusedConfiguration β =>
      tailKernel θ β (t - p.1) p.2 y) := measurable_tailKernel_apply θ β t y
  have hH : Measurable H := hhead.mul htail
  have hterm (m : ℕ) (w : CollisionWord n m) : Measurable (term m w) := by
    dsimp [term]
    by_cases hg : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β
    · have heq : (fun p : ℝ × FusedConfiguration β =>
          if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
            headKernel θ α β p.1 x p.2 *
              tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y else 0) =
        fun p => headKernel θ α β p.1 x p.2 *
          tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y := by
          funext p
          exact ite_eq_left hg
      rw [heq]
      exact hhead.mul (measurable_tailWordKernel_apply θ β (List.ofFn w.1) t y)
    · have heq : (fun p : ℝ × FusedConfiguration β =>
          if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
            headKernel θ α β p.1 x p.2 *
              tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y else 0) =
        fun _ => 0 := by
          funext p
          exact ite_eq_right hg
      rw [heq]
      exact measurable_const
  have hblock (m : ℕ) : Measurable (block m) := by
    apply Finset.measurable_sum
    intro w hw
    exact hterm m w
  have hpoint (p : ℝ × FusedConfiguration β) :
      H p = ∑' m : ℕ, block m p := by
    simp only [H, block, term]
    change headKernel θ α β p.1 x p.2 *
        (∑' m : ℕ, ∑ w : CollisionWord n m,
          if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
            tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y else 0) = _
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro m
    calc
      headKernel θ α β p.1 x p.2 *
          (∑ w : CollisionWord n m,
            if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
              tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y else 0) =
        ∑ w : CollisionWord n m, headKernel θ α β p.1 x p.2 *
          (if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
            tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y else 0) := by
              rw [Finset.mul_sum]
      _ = ∑ w : CollisionWord n m,
          if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
            headKernel θ α β p.1 x p.2 *
              tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y else 0 := by
            apply Finset.sum_congr rfl
            intro w hw
            by_cases hg : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β <;> simp [hg]
  have hprodH :
      (∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β, H (s, z)) =
        ∫⁻ p, H p ∂(μ.prod ν) := by
    change (∫⁻ s, ∫⁻ z, H (s, z) ∂ν ∂μ) = _
    exact (lintegral_prod H hH.aemeasurable).symm
  have htermProd (m : ℕ) (w : CollisionWord n m) :
      (∫⁻ p, term m w p ∂(μ.prod ν)) =
        if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
          ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
            headKernel θ α β s x z *
              tailWordKernel θ β (List.ofFn w.1) (t - s) z y
        else 0 := by
    by_cases hg : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β
    · have heq : term m w = (fun p : ℝ × FusedConfiguration β =>
          headKernel θ α β p.1 x p.2 *
            tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y) := by
        funext p
        simp [term, hg]
      rw [heq]
      calc
        (∫⁻ p, (fun p : ℝ × FusedConfiguration β =>
            headKernel θ α β p.1 x p.2 *
              tailWordKernel θ β (List.ofFn w.1) (t - p.1) p.2 y) p ∂(μ.prod ν)) =
            ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
              headKernel θ α β s x z *
                tailWordKernel θ β (List.ofFn w.1) (t - s) z y :=
          lintegral_prod _
            (hhead.mul (measurable_tailWordKernel_apply θ β (List.ofFn w.1) t y)).aemeasurable
        _ = if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
              ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
                headKernel θ α β s x z *
                  tailWordKernel θ β (List.ofFn w.1) (t - s) z y
            else 0 := (ite_eq_left hg).symm
    · have heq : term m w = (fun _ : ℝ × FusedConfiguration β => 0) := by
        funext p
        simp [term, hg]
      rw [heq]
      simp [hg]
  calc
    (∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
        headKernel θ α β s x z * tailKernel θ β (t - s) z y) =
        ∫⁻ p, H p ∂(μ.prod ν) := by
          simpa only [H] using hprodH
    _ = ∫⁻ p, ∑' m : ℕ, block m p ∂(μ.prod ν) := by
          apply lintegral_congr_ae
          filter_upwards [] with p
          exact hpoint p
    _ = ∑' m : ℕ, ∫⁻ p, block m p ∂(μ.prod ν) :=
          lintegral_tsum (fun m => (hblock m).aemeasurable)
    _ = ∑' m : ℕ, ∑ w : CollisionWord n m,
          if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
            ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
              headKernel θ α β s x z *
                tailWordKernel θ β (List.ofFn w.1) (t - s) z y
          else 0 := by
            apply tsum_congr
            intro m
            calc
              (∫⁻ p, block m p ∂(μ.prod ν)) =
                  ∑ w : CollisionWord n m, ∫⁻ p, term m w p ∂(μ.prod ν) := by
                    rw [show block m = fun p => ∑ w : CollisionWord n m, term m w p by rfl]
                    exact lintegral_finsetSum Finset.univ
                      (fun w hw => hterm m w)
              _ = ∑ w : CollisionWord n m,
                    if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
                      ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
                        headKernel θ α β s x z *
                          tailWordKernel θ β (List.ofFn w.1) (t - s) z y
                    else 0 := by
                      apply Finset.sum_congr rfl
                      intro w hw
                      exact htermProd m w

/-- The complete series of words with at least two letters factors at the merge
of its second letter. -/
theorem longWordKernel_eq_sum_head_tail {n : ℕ} (θ : ℝ) {t : ℝ} (ht : 0 < t)
    (x y : Configuration n) :
    longWordKernel n θ t x y =
      ∑ α : CollisionPair n, ∑ β : CollisionPair n, if α = β then 0 else
        ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
          headKernel θ α β s x z * tailKernel θ β (t - s) z y := by
  classical
  let D : ℕ → CollisionPair n → CollisionPair n → ℝ≥0∞ := fun m α β =>
    ∑ w : CollisionWord n m,
      if α ≠ β ∧ (∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β) then
        diagramKernel θ (α :: β :: List.ofFn w.1) t x y else 0
  have hReorder :
      (∑' m : ℕ, ∑ α : CollisionPair n, ∑ β : CollisionPair n, D m α β) =
        ∑ α : CollisionPair n, ∑ β : CollisionPair n, ∑' m : ℕ, D m α β := by
    calc
      _ = ∑' m : ℕ, ∑'[SummationFilter.unconditional (CollisionPair n)] α,
            ∑ β : CollisionPair n, D m α β := by
              apply tsum_congr
              intro m
              exact (tsum_fintype
                (L := SummationFilter.unconditional (CollisionPair n))
                (fun α => ∑ β : CollisionPair n, D m α β)).symm
      _ = ∑'[SummationFilter.unconditional (CollisionPair n)] α, ∑' m : ℕ,
            ∑ β : CollisionPair n, D m α β := ENNReal.tsum_comm
      _ = ∑'[SummationFilter.unconditional (CollisionPair n)] α, ∑' m : ℕ,
            ∑'[SummationFilter.unconditional (CollisionPair n)] β, D m α β := by
              apply tsum_congr
              intro α
              apply tsum_congr
              intro m
              exact (tsum_fintype
                (L := SummationFilter.unconditional (CollisionPair n))
                (fun β => D m α β)).symm
      _ = ∑'[SummationFilter.unconditional (CollisionPair n)] α,
            ∑'[SummationFilter.unconditional (CollisionPair n)] β, ∑' m : ℕ,
              D m α β := by
              apply tsum_congr
              intro α
              exact ENNReal.tsum_comm (f := fun m β => D m α β)
      _ = ∑'[SummationFilter.unconditional (CollisionPair n)] α,
            ∑ β : CollisionPair n, ∑' m : ℕ, D m α β := by
              apply tsum_congr
              intro α
              exact tsum_fintype
                (L := SummationFilter.unconditional (CollisionPair n))
                (fun β => ∑' m : ℕ, D m α β)
      _ = ∑ α : CollisionPair n, ∑ β : CollisionPair n, ∑' m : ℕ, D m α β :=
            tsum_fintype
              (L := SummationFilter.unconditional (CollisionPair n))
              (fun α => ∑ β : CollisionPair n, ∑' m : ℕ, D m α β)
  have hword (α β : CollisionPair n) (hαβ : α ≠ β) (m : ℕ) :
      (∑ w : CollisionWord n m,
        if α ≠ β ∧ (∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β) then
          diagramKernel θ (α :: β :: List.ofFn w.1) t x y else 0) =
      ∑ w : CollisionWord n m,
        if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
          ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
            headKernel θ α β s x z *
              tailWordKernel θ β (List.ofFn w.1) (t - s) z y
        else 0 := by
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hg : ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β
    · calc
        (if α ≠ β ∧ (∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β) then
            diagramKernel θ (α :: β :: List.ofFn w.1) t x y else 0) =
          diagramKernel θ (α :: β :: List.ofFn w.1) t x y :=
            ite_eq_left (And.intro hαβ hg)
        _ = ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
              headKernel θ α β s x z *
                tailWordKernel θ β (List.ofFn w.1) (t - s) z y :=
            diagramKernel_cons_cons_eq_head_tail θ α β (List.ofFn w.1) t ht x y
        _ = if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
              ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
                headKernel θ α β s x z *
                  tailWordKernel θ β (List.ofFn w.1) (t - s) z y
            else 0 := (ite_eq_left hg).symm
    · simp [hαβ, hg]
  have hseries (α β : CollisionPair n) :
      (∑' m : ℕ, D m α β) = if α = β then 0 else
        ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
          headKernel θ α β s x z * tailKernel θ β (t - s) z y := by
    by_cases hαβ : α = β
    · subst β
      simp [D]
    · calc
        (∑' m : ℕ, D m α β) =
            ∑' m : ℕ, ∑ w : CollisionWord n m,
              if ∀ h : 0 < m, w.1 ⟨0, h⟩ ≠ β then
                ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
                  headKernel θ α β s x z *
                    tailWordKernel θ β (List.ofFn w.1) (t - s) z y
              else 0 := by
                apply tsum_congr
                intro m
                exact hword α β hαβ m
          _ = ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
                headKernel θ α β s x z * tailKernel θ β (t - s) z y :=
              (headKernel_mul_tailKernel_eq_tsum θ α β t x y).symm
          _ = if α = β then 0 else
                ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
                  headKernel θ α β s x z * tailKernel θ β (t - s) z y := by
                simp [hαβ]
  calc
    longWordKernel n θ t x y =
        ∑' m : ℕ, ∑ α : CollisionPair n, ∑ β : CollisionPair n, D m α β := by
          change ∑' m : ℕ, ∑ w : CollisionWord n (m + 2),
            diagramKernel θ (List.ofFn w.1) t x y = _
          apply tsum_congr
          intro m
          simpa only [D] using diagramWordSum_eq_filtered θ t x y m
    _ = ∑ α : CollisionPair n, ∑ β : CollisionPair n, ∑' m : ℕ, D m α β :=
          hReorder
    _ = ∑ α : CollisionPair n, ∑ β : CollisionPair n,
          if α = β then 0 else
            ∫⁻ s in Ioo 0 t, ∫⁻ z : FusedConfiguration β,
              headKernel θ α β s x z * tailKernel θ β (t - s) z y := by
          apply Finset.sum_congr rfl
          intro α hα
          apply Finset.sum_congr rfl
          intro β hβ
          exact hseries α β

end Critical2DKPZ.SHF.Tsai

end
