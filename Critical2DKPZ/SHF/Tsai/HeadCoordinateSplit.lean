/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PiCoordinateSplit
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Reindexing a four-particle configuration after deleting one label -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The three labels other than a chosen label of a four-particle configuration. -/
abbrev OmittedLabels (i : Fin 4) := {j : Fin 4 // j ≠ i}

/-- The equivalence `Fin 3 ≃ OmittedLabels i` sending `j` to `i.succAbove j`. The measure
statement is `measurePreserving_omittedConfigurationEquiv`. -/
noncomputable def omittedLabelsEquiv (i : Fin 4) : Fin 3 ≃ OmittedLabels i := by
  classical
  let f : Fin 3 → OmittedLabels i := fun j => ⟨i.succAbove j, Fin.succAbove_ne i j⟩
  have hf : Function.Bijective f := by
    constructor
    · intro j k h
      exact Fin.succAbove_right_injective (congrArg Subtype.val h)
    · intro j
      obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq j.2
      exact ⟨k, Subtype.ext hk⟩
  exact Equiv.ofBijective f hf

/-- The endpoint `β.1.2` if `i = β.1.1`, and `β.1.1` otherwise; it is the other endpoint of `β`
when `i` is an endpoint of `β`. -/
noncomputable def omittedBetaOtherLabel (i : Fin 4) (β : CollisionPair 4) : OmittedLabels i := by
  classical
  by_cases h : i = β.1.1
  · exact ⟨β.1.2, by
      intro heq
      exact (ne_of_lt β.2) (heq.trans h).symm⟩
  · exact ⟨β.1.1, fun heq => h heq.symm⟩

/-- The center coordinate of a `β`-fused configuration is indexed by the
other endpoint after deleting one endpoint of `β`; all other coordinates are
its spectators. -/
noncomputable def omittedBetaIndexEquiv (i : Fin 4) (β : CollisionPair 4)
    (hi : i = β.1.1 ∨ i = β.1.2) : Option (Spectator β) ≃ OmittedLabels i := by
  classical
  let f : Option (Spectator β) → OmittedLabels i := fun o => by
    cases o with
    | none => exact omittedBetaOtherLabel i β
    | some s =>
        have hsi : s.1 ≠ i := by
          intro h
          rcases hi with hi | hi
          · exact s.2.1 (h.trans hi)
          · exact s.2.2 (h.trans hi)
        exact ⟨s.1, hsi⟩
  have hf : Function.Bijective f := by
    constructor
    · intro o o' heq
      cases o with
      | none =>
          cases o' with
          | none => rfl
          | some s =>
              have hval := congrArg Subtype.val heq
              dsimp [f] at hval
              by_cases h : i = β.1.1
              · have hs : s.1 ≠ β.1.2 := s.2.2
                exact False.elim (hs (hval.symm.trans (by simp [omittedBetaOtherLabel, h])))
              · have hs : s.1 ≠ β.1.1 := s.2.1
                exact False.elim (hs (hval.symm.trans (by simp [omittedBetaOtherLabel, h])))
      | some s =>
          cases o' with
          | none =>
              have hval := congrArg Subtype.val heq
              dsimp [f] at hval
              by_cases h : i = β.1.1
              · exact False.elim (s.2.2 (hval.trans (by simp [omittedBetaOtherLabel, h])))
              · exact False.elim (s.2.1 (hval.trans (by simp [omittedBetaOtherLabel, h])))
          | some t =>
              have hval := congrArg Subtype.val heq
              exact congrArg some (Subtype.ext hval)
    · intro l
      by_cases h : l.1 = (omittedBetaOtherLabel i β).1
      · refine ⟨none, ?_⟩
        apply Subtype.ext
        exact h.symm
      · rcases hi with hi | hi
        · have h₁ : l.1 ≠ β.1.1 := fun heq => l.2 (heq.trans hi.symm)
          have h₂ : l.1 ≠ β.1.2 := by
            intro heq
            have hother : (omittedBetaOtherLabel i β).1 = β.1.2 := by
              simp [omittedBetaOtherLabel, hi]
            exact h (heq.trans hother.symm)
          let s : Spectator β := ⟨l.1, h₁, h₂⟩
          refine ⟨some s, ?_⟩
          apply Subtype.ext
          rfl
        · have h₂ : l.1 ≠ β.1.2 := fun heq => l.2 (heq.trans hi.symm)
          have h₁ : l.1 ≠ β.1.1 := by
            intro heq
            have hother : (omittedBetaOtherLabel i β).1 = β.1.1 := by
              simp [omittedBetaOtherLabel, hi, ne_of_gt β.2]
            exact h (heq.trans hother.symm)
          let s : Spectator β := ⟨l.1, h₁, h₂⟩
          refine ⟨some s, ?_⟩
          apply Subtype.ext
          rfl
  exact Equiv.ofBijective f hf


/-- A spectator index goes to the same label under `omittedBetaIndexEquiv`. -/
theorem omittedBetaIndexEquiv_apply_some_val (i : Fin 4) (β : CollisionPair 4)
    (hi : i = β.1.1 ∨ i = β.1.2) (s : Spectator β) :
    (omittedBetaIndexEquiv i β hi (some s)).1 = s.1 := by
  rfl

/-- Delete one endpoint of `β` and identify its fused configuration with
ordinary coordinates on the remaining three labels. -/
noncomputable def omittedBetaConfigurationEquiv (i : Fin 4) (β : CollisionPair 4)
    (hi : i = β.1.1 ∨ i = β.1.2) : FusedConfiguration β ≃ᵐ (OmittedLabels i → Plane) :=
  MeasurableEquiv.prodComm.trans
    ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Spectator β) => Plane)).symm.trans
      (MeasurableEquiv.piCongrLeft (fun _ : OmittedLabels i => Plane)
        (omittedBetaIndexEquiv i β hi)))

/-- `omittedBetaOtherLabel` is an endpoint of `β` when `i` is one. -/
theorem omittedBetaOtherLabel_endpoint (i : Fin 4) (β : CollisionPair 4)
    (_hi : i = β.1.1 ∨ i = β.1.2) :
    (omittedBetaOtherLabel i β).1 = β.1.1 ∨
      (omittedBetaOtherLabel i β).1 = β.1.2 := by
  by_cases h : i = β.1.1
  · right
    simp [omittedBetaOtherLabel, h]
  · left
    simp [omittedBetaOtherLabel, h]

/-- On each remaining label, the reindexed fused configuration agrees with
the original collision embedding. -/
theorem omittedBetaConfigurationEquiv_apply (i : Fin 4) (β : CollisionPair 4)
    (hi : i = β.1.1 ∨ i = β.1.2) (w : FusedConfiguration β) (j : OmittedLabels i) :
    omittedBetaConfigurationEquiv i β hi w j = collisionEmbedding β w j.1 := by
  classical
  let e := omittedBetaIndexEquiv i β hi
  by_cases h : j.1 = (omittedBetaOtherLabel i β).1
  · have hEq : j = e none := by
      apply Subtype.ext
      exact h
    have hsymm : e.symm j = none := by
      calc
        e.symm j = e.symm (e none) := congrArg e.symm hEq
        _ = none := Equiv.symm_apply_apply e none
    have hcenter : omittedBetaConfigurationEquiv i β hi w j = w.1 := by
      unfold omittedBetaConfigurationEquiv
      change (MeasurableEquiv.piCongrLeft (fun _ : OmittedLabels i => Plane) e
        ((MeasurableEquiv.piOptionEquivProd
          (fun _ : Option (Spectator β) => Plane)).symm (w.2, w.1))) j = w.1
      rw [← e.apply_symm_apply j]
      rw [MeasurableEquiv.piCongrLeft_apply_apply, hsymm]
      rfl
    have hend := omittedBetaOtherLabel_endpoint i β hi
    have hjend : j.1 = β.1.1 ∨ j.1 = β.1.2 := by
      rcases hend with h1 | h2
      · exact Or.inl (h.trans h1)
      · exact Or.inr (h.trans h2)
    rw [hcenter]
    simp [collisionEmbedding, hjend]
  · have hα : j.1 ≠ i := j.2
    have hsProp : j.1 ≠ β.1.1 ∧ j.1 ≠ β.1.2 := by
      rcases hi with hi | hi
      · constructor
        · intro hj
          exact hα (hj.trans hi.symm)
        · intro hj
          apply h
          have hother : (omittedBetaOtherLabel i β).1 = β.1.2 := by
            simp [omittedBetaOtherLabel, hi]
          exact hj.trans hother.symm
      · constructor
        · intro hj
          apply h
          have hother : (omittedBetaOtherLabel i β).1 = β.1.1 := by
            simp [omittedBetaOtherLabel, hi, ne_of_gt β.2]
          exact hj.trans hother.symm
        · intro hj
          exact hα (hj.trans hi.symm)
    let hs : Spectator β := ⟨j.1, hsProp.1, hsProp.2⟩
    have hEq : e (some hs) = j := by
      apply Subtype.ext
      simpa [hs] using (omittedBetaIndexEquiv_apply_some_val i β hi hs)
    have hsymm : e.symm j = some hs := by
      calc
        e.symm j = e.symm (e (some hs)) := congrArg e.symm hEq.symm
        _ = some hs := Equiv.symm_apply_apply e (some hs)
    have hspec : omittedBetaConfigurationEquiv i β hi w j = w.2 hs := by
      unfold omittedBetaConfigurationEquiv
      change (MeasurableEquiv.piCongrLeft (fun _ : OmittedLabels i => Plane) e
        ((MeasurableEquiv.piOptionEquivProd
          (fun _ : Option (Spectator β) => Plane)).symm (w.2, w.1))) j = w.2 hs
      rw [← e.apply_symm_apply j]
      rw [MeasurableEquiv.piCongrLeft_apply_apply, hsymm]
      rfl
    have hEmbedding : collisionEmbedding β w j.1 = w.2 hs := by
      unfold collisionEmbedding
      split
      · rename_i hEndpoint
        rcases hEndpoint with h1 | h2
        · exact (hsProp.1 h1).elim
        · exact (hsProp.2 h2).elim
      · exact congrArg w.2 (Subtype.ext rfl)
    exact hspec.trans hEmbedding.symm

/-- The coordinate reindexing of the fused `β` space preserves product
Lebesgue measure. -/
theorem measurePreserving_omittedBetaConfigurationEquiv (i : Fin 4)
    (β : CollisionPair 4) (hi : i = β.1.1 ∨ i = β.1.2) :
    MeasurePreserving (omittedBetaConfigurationEquiv i β hi) volume volume := by
  let e := omittedBetaIndexEquiv i β hi
  have hswap0 : MeasurePreserving
      (Prod.swap : Plane × (Spectator β → Plane) → (Spectator β → Plane) × Plane)
      (volume : Measure (Plane × (Spectator β → Plane)))
      (volume : Measure ((Spectator β → Plane) × Plane)) := by
    simpa only [Measure.volume_eq_prod] using
      (Measure.measurePreserving_swap (μ := (volume : Measure Plane))
        (ν := (volume : Measure (Spectator β → Plane))))
  have hswap : MeasurePreserving
      (MeasurableEquiv.prodComm (α := Plane) (β := Spectator β → Plane)) volume volume := by
    apply hswap0.congr MeasurableEquiv.prodComm.measurable
    filter_upwards with x
    rfl
  have hoption : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Spectator β) => Plane)).symm volume volume := by
    refine ⟨(MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Spectator β) => Plane)).symm.measurable, ?_⟩
    simpa only [Measure.volume_eq_prod, volume_pi] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option (Spectator β) => (volume : Measure Plane)))
  have hpi : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : OmittedLabels i => Plane) e) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : OmittedLabels i => Plane) e
  exact hpi.comp (hoption.comp hswap)

/-- The coordinate map from `Fin 3 → Plane` to the three coordinates in
`Fin 4` other than `i`. -/
noncomputable def omittedConfigurationEquiv (i : Fin 4) :
    Configuration 3 ≃ᵐ (OmittedLabels i → Plane) :=
  MeasurableEquiv.piCongrLeft (fun _ : OmittedLabels i => Plane) (omittedLabelsEquiv i)

/-- Deleting a coordinate and reindexing the remaining three coordinates
preserves product Lebesgue measure. -/
theorem measurePreserving_omittedConfigurationEquiv (i : Fin 4) :
    MeasurePreserving (omittedConfigurationEquiv i) volume volume := by
  exact volume_measurePreserving_piCongrLeft (fun _ : OmittedLabels i => Plane)
    (omittedLabelsEquiv i)

/-- Transport a collision pair that avoids `i` to the three-label
configuration obtained by deleting `i`. -/
noncomputable def omittedCollisionPair (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) : CollisionPair 3 := by
  classical
  let e := omittedLabelsEquiv i
  let a := e.symm ⟨α.1.1, hi₁⟩
  let b := e.symm ⟨α.1.2, hi₂⟩
  have hab : a ≠ b := by
    intro heq
    have hA : e a = ⟨α.1.1, hi₁⟩ := Equiv.apply_symm_apply _ _
    have hB : e b = ⟨α.1.2, hi₂⟩ := Equiv.apply_symm_apply _ _
    have hval := congrArg Subtype.val (hA.symm.trans ((congrArg e heq).trans hB))
    exact (ne_of_lt α.2) hval
  by_cases h : a < b
  · exact ⟨(a, b), h⟩
  · exact ⟨(b, a), lt_of_le_of_ne (le_of_not_gt h) hab.symm⟩

/-- Deleting a label outside `α` preserves its two collision endpoints as an
unordered pair. -/
theorem omittedCollisionPair_endpoint_set (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) :
    ({((omittedLabelsEquiv i) (omittedCollisionPair i α hi₁ hi₂).1.1).1,
      ((omittedLabelsEquiv i) (omittedCollisionPair i α hi₁ hi₂).1.2).1} : Finset (Fin 4)) =
      {α.1.1, α.1.2} := by
  classical
  let e := omittedLabelsEquiv i
  let a := e.symm ⟨α.1.1, hi₁⟩
  let b := e.symm ⟨α.1.2, hi₂⟩
  have hA : e a = ⟨α.1.1, hi₁⟩ := Equiv.apply_symm_apply _ _
  have hB : e b = ⟨α.1.2, hi₂⟩ := Equiv.apply_symm_apply _ _
  have hab : a ≠ b := by
    intro heq
    have hval := congrArg Subtype.val (hA.symm.trans ((congrArg e heq).trans hB))
    exact (ne_of_lt α.2) hval
  by_cases h : a < b
  · simp [omittedCollisionPair, e, a, b, h, Equiv.apply_symm_apply]
  · simp [omittedCollisionPair, e, a, b, h, Equiv.apply_symm_apply, Finset.pair_comm]

/-- Endpoint membership in the reduced pair is equivalent to endpoint
membership in the original pair. -/
theorem omittedCollisionPair_endpoint_mem_iff (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) (j : Fin 3) :
    j = (omittedCollisionPair i α hi₁ hi₂).1.1 ∨
        j = (omittedCollisionPair i α hi₁ hi₂).1.2 ↔
      ((omittedLabelsEquiv i j).1 = α.1.1 ∨ (omittedLabelsEquiv i j).1 = α.1.2) := by
  classical
  let e := omittedLabelsEquiv i
  let γ := omittedCollisionPair i α hi₁ hi₂
  have hs := omittedCollisionPair_endpoint_set i α hi₁ hi₂
  have hred :
      (j = γ.1.1 ∨ j = γ.1.2) ↔
        ((e j).1 = (e γ.1.1).1 ∨ (e j).1 = (e γ.1.2).1) := by
    constructor
    · rintro (hj | hj)
      · left
        exact congrArg Subtype.val (congrArg e hj)
      · right
        exact congrArg Subtype.val (congrArg e hj)
    · rintro (hj | hj)
      · left
        exact e.injective (Subtype.ext hj)
      · right
        exact e.injective (Subtype.ext hj)
  have hpair : ({(e γ.1.1).1, (e γ.1.2).1} : Finset (Fin 4)) =
      {α.1.1, α.1.2} := hs
  have horig :
      ((e j).1 = (e γ.1.1).1 ∨ (e j).1 = (e γ.1.2).1) ↔
        ((e j).1 = α.1.1 ∨ (e j).1 = α.1.2) := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      (show (e j).1 ∈ ({(e γ.1.1).1, (e γ.1.2).1} : Finset (Fin 4)) ↔
          (e j).1 ∈ ({α.1.1, α.1.2} : Finset (Fin 4)) by rw [hpair])
  exact hred.trans horig

/-- The spectator labels of the reduced collision space are exactly the
original spectator labels other than the deleted one. -/
abbrev OmittedSpectators (i : Fin 4) (α : CollisionPair 4) :=
  {j : OmittedLabels i // j.1 ≠ α.1.1 ∧ j.1 ≠ α.1.2}

/-- The spectators of the reduced pair correspond to the remaining labels outside `α`. -/
noncomputable def omittedSpectatorsEquiv (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) :
    Spectator (omittedCollisionPair i α hi₁ hi₂) ≃ OmittedSpectators i α := by
  classical
  let e := omittedLabelsEquiv i
  let γ := omittedCollisionPair i α hi₁ hi₂
  have hmem := omittedCollisionPair_endpoint_mem_iff i α hi₁ hi₂
  let f : Spectator γ → OmittedSpectators i α := fun j =>
    ⟨e j.1, by
      have hj : ¬ (j.1 = γ.1.1 ∨ j.1 = γ.1.2) := by
        simpa only [not_or] using j.2
      have hnot : ¬ ((e j.1).1 = α.1.1 ∨ (e j.1).1 = α.1.2) :=
        fun h => hj (hmem j.1 |>.2 h)
      exact not_or.mp hnot⟩
  have hf : Function.Bijective f := by
    constructor
    · intro j k h
      apply Subtype.ext
      apply e.injective
      exact congrArg Subtype.val h
    · intro j
      let k := e.symm j.1
      have hnot : ¬ (k = γ.1.1 ∨ k = γ.1.2) := by
        intro hk
        have hbad := (hmem k).mp hk
        have heval : (e k).1 = j.1.1 := by
          dsimp [k]
          exact congrArg Subtype.val (Equiv.apply_symm_apply e j.1)
        rcases hbad with hbad | hbad
        · exact j.2.1 (heval.symm.trans hbad)
        · exact j.2.2 (heval.symm.trans hbad)
      have hk : k ≠ γ.1.1 ∧ k ≠ γ.1.2 := by
        simpa only [not_or] using hnot
      refine ⟨⟨k, hk⟩, ?_⟩
      apply Subtype.ext
      exact Equiv.apply_symm_apply e j.1
  exact Equiv.ofBijective f hf

/-- Original spectators of `α` other than the deleted free label. -/
abbrev OmittedAlphaSpectators (i : Fin 4) (α : CollisionPair 4) :=
  {s : Spectator α // s.1 ≠ i}

/-- Reinterpret the remaining labels outside `α` as its original spectator
indices, retaining the condition that they avoid `i`. -/
noncomputable def omittedSpectatorsToAlpha (i : Fin 4) (α : CollisionPair 4) :
    OmittedSpectators i α ≃ OmittedAlphaSpectators i α where
  toFun q := ⟨⟨q.1.1, ⟨q.2.1, q.2.2⟩⟩, q.1.2⟩
  invFun s := ⟨⟨s.1.1, s.2⟩, ⟨s.1.2.1, s.1.2.2⟩⟩
  left_inv q := by cases q; rfl
  right_inv s := by cases s with | mk s hs => cases s; rfl

/-- Put the deleted free label back among the original spectator labels. -/
noncomputable def omittedAlphaSpectatorOptionEquiv (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) :
    Option (Spectator (omittedCollisionPair i α hi₁ hi₂)) ≃ Spectator α := by
  let e₁ := omittedSpectatorsEquiv i α hi₁ hi₂
  let e₂ := omittedSpectatorsToAlpha i α
  let e₃ : Option (OmittedAlphaSpectators i α) ≃ Spectator α :=
    { toFun := fun o => match o with
        | none => ⟨i, hi₁.symm, hi₂.symm⟩
        | some s => s.1
      invFun := fun s => if h : s.1 = i then none else some ⟨s, h⟩
      left_inv := by
        intro o
        cases o with
        | none => simp
        | some s => simp [s.2]
      right_inv := by
        intro s
        by_cases h : s.1 = i
        · apply Subtype.ext
          simp [h]
        · simp [h] }
  exact e₁.optionCongr.trans (e₂.optionCongr.trans e₃)

/-- Split the deleted free spectator coordinate off an `α`-fused space. -/
noncomputable def omittedAlphaFusedEquiv (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) :
    FusedConfiguration α ≃ᵐ
      (FusedConfiguration (omittedCollisionPair i α hi₁ hi₂) × Plane) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Plane)
    (MeasurableEquiv.piCongrLeft (fun _ : Spectator α => Plane)
      (omittedAlphaSpectatorOptionEquiv i α hi₁ hi₂)).symm).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl Plane)
      (MeasurableEquiv.piOptionEquivProd
        (fun _ : Option (Spectator (omittedCollisionPair i α hi₁ hi₂)) => Plane))).trans
      MeasurableEquiv.prodAssoc.symm)

/-- The center coordinate is unchanged by `omittedAlphaFusedEquiv`. -/
theorem omittedAlphaFusedEquiv_apply_center (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) (z : FusedConfiguration α) :
    (omittedAlphaFusedEquiv i α hi₁ hi₂ z).1.1 = z.1 := by
  rfl

/-- The deleted coordinate of `omittedAlphaFusedEquiv` is the value at the free label `i`. -/
theorem omittedAlphaFusedEquiv_apply_deleted (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) (z : FusedConfiguration α) :
    (omittedAlphaFusedEquiv i α hi₁ hi₂ z).2 =
      z.2 ⟨i, hi₁.symm, hi₂.symm⟩ := by
  rfl

/-- The remaining spectator coordinates of `omittedAlphaFusedEquiv` are the original ones. -/
theorem omittedAlphaFusedEquiv_apply_spectator (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i)
    (k : Spectator (omittedCollisionPair i α hi₁ hi₂)) (z : FusedConfiguration α) :
    (omittedAlphaFusedEquiv i α hi₁ hi₂ z).1.2 k =
      z.2 (omittedAlphaSpectatorOptionEquiv i α hi₁ hi₂ (some k)) := by
  rfl

/-- The split of the `α`-fused space preserves product Lebesgue measure. -/
theorem measurePreserving_omittedAlphaFusedEquiv (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) :
    MeasurePreserving (omittedAlphaFusedEquiv i α hi₁ hi₂) volume volume := by
  let γ := omittedCollisionPair i α hi₁ hi₂
  let e := omittedAlphaSpectatorOptionEquiv i α hi₁ hi₂
  have hpi : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : Spectator α => Plane) e) volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Spectator α => Plane) e
  have hoptionRev : MeasurePreserving
      (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Spectator γ) => Plane)).symm
        volume volume := by
    refine ⟨(MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Spectator γ) => Plane)).symm.measurable, ?_⟩
    simpa only [Measure.volume_eq_prod, volume_pi] using
      (Measure.pi_map_piOptionEquivProd
        (fun _ : Option (Spectator γ) => (volume : Measure Plane)))
  have hAssoc : MeasurePreserving
      (MeasurableEquiv.prodAssoc.symm :
        Plane × ((Spectator γ → Plane) × Plane) ≃ᵐ (Plane × (Spectator γ → Plane)) × Plane)
        volume volume := by
    exact (MeasureTheory.measurePreserving_prodAssoc
      (volume : Measure Plane) (volume : Measure (Spectator γ → Plane))
      (volume : Measure Plane)).symm
  have h1 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Plane)
        (MeasurableEquiv.piCongrLeft (fun _ : Spectator α => Plane) e).symm)
        volume volume := by
    exact (MeasurePreserving.id (volume : Measure Plane)).prod hpi.symm
  have h2 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Plane)
        (MeasurableEquiv.piOptionEquivProd
          (fun _ : Option (Spectator γ) => Plane))) volume volume := by
    exact (MeasurePreserving.id (volume : Measure Plane)).prod hoptionRev.symm
  have hfull := hAssoc.comp (h2.comp h1)
  exact hfull.congr (omittedAlphaFusedEquiv i α hi₁ hi₂).measurable
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Delete a coordinate from a full configuration, retaining it as a final
planar factor and reindexing the remaining three labels by `Fin 3`. -/
noncomputable def omittedFullConfigurationEquiv (i : Fin 4) :
    Configuration 4 ≃ᵐ (Configuration 3 × Plane) :=
  (Critical2DKPZ.DeltaBose.splitCoordinate i).trans
    (MeasurableEquiv.prodCongr (omittedConfigurationEquiv i).symm
      (MeasurableEquiv.refl Plane))

/-- The three retained coordinates of a full four-particle configuration. -/
noncomputable def omittedFullPart (i : Fin 4) (x : Configuration 4) : Configuration 3 :=
  (omittedFullConfigurationEquiv i x).1

/-- The `k`-th retained coordinate is the coordinate at label `omittedLabelsEquiv i k`. -/
theorem omittedFullPart_apply (i : Fin 4) (x : Configuration 4) (k : Fin 3) :
    omittedFullPart i x k = x ((omittedLabelsEquiv i k).1) := by
  rfl

/-- Removing a free spectator coordinate from an `α`-collision embedding
gives the reduced collision embedding. -/
theorem omittedFullPart_collisionEmbedding_alpha (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) (z : FusedConfiguration α) :
    omittedFullPart i (collisionEmbedding α z) =
      collisionEmbedding (omittedCollisionPair i α hi₁ hi₂)
        ((omittedAlphaFusedEquiv i α hi₁ hi₂ z).1) := by
  classical
  let γ := omittedCollisionPair i α hi₁ hi₂
  let zr := (omittedAlphaFusedEquiv i α hi₁ hi₂ z).1
  funext j
  rw [omittedFullPart_apply]
  have he := omittedCollisionPair_endpoint_mem_iff i α hi₁ hi₂ j
  by_cases hj : j = γ.1.1 ∨ j = γ.1.2
  · have hα : (omittedLabelsEquiv i j).1 = α.1.1 ∨
        (omittedLabelsEquiv i j).1 = α.1.2 := he.mp hj
    have hleft : collisionEmbedding α z (omittedLabelsEquiv i j).1 = z.1 := by
      simp [collisionEmbedding, hα]
    have hright : collisionEmbedding γ zr j = zr.1 := by
      simp [collisionEmbedding, hj]
    rw [hleft, hright, omittedAlphaFusedEquiv_apply_center]
  · have hj' : ¬ (j = γ.1.1 ∨ j = γ.1.2) := hj
    have hα : ¬ ((omittedLabelsEquiv i j).1 = α.1.1 ∨
        (omittedLabelsEquiv i j).1 = α.1.2) := by
      intro h
      exact hj (he.mpr h)
    let ks : Spectator γ := ⟨j, not_or.mp hj'⟩
    let ksα : Spectator α := ⟨(omittedLabelsEquiv i j).1, not_or.mp hα⟩
    have hidx : omittedAlphaSpectatorOptionEquiv i α hi₁ hi₂ (some ks) = ksα := by
      apply Subtype.ext
      rfl
    have hspec := omittedAlphaFusedEquiv_apply_spectator i α hi₁ hi₂ ks z
    rw [hidx] at hspec
    calc
      collisionEmbedding α z (omittedLabelsEquiv i j).1 = z.2 ksα := by
        simp [collisionEmbedding, hα, ksα]
      _ = zr.2 ks := hspec.symm
      _ = collisionEmbedding γ zr j := by
        simp [collisionEmbedding, hj', ks]

/-- The four-particle free kernel factors into the heat kernel in coordinate `i` and the
three-particle free kernel on the other coordinates. -/
theorem freeKernel_omittedPart_factor {t : ℝ} (i : Fin 4) (x y : Configuration 4) :
    freeKernel 4 t x y =
      heatKernel t (y i - x i) *
        freeKernel 3 t (omittedFullPart i x) (omittedFullPart i y) := by
  classical
  unfold freeKernel
  rw [Critical2DKPZ.DeltaBose.prod_splitCoordinate i]
  have hprod :
      (∏ k : Fin 3, heatKernel t
        (omittedFullPart i y k - omittedFullPart i x k)) =
      (∏ j : OmittedLabels i, heatKernel t (y j.1 - x j.1)) := by
    calc
      _ = ∏ k : Fin 3,
          heatKernel t (y ((omittedLabelsEquiv i k).1) - x ((omittedLabelsEquiv i k).1)) := by
            apply Finset.prod_congr rfl
            intro k hk
            simp only [omittedFullPart_apply]
      _ = _ := Equiv.prod_comp (omittedLabelsEquiv i)
        (fun j : OmittedLabels i => heatKernel t (y j.1 - x j.1))
  rw [hprod]

/-- The incoming kernel factors into the selected free heat coordinate and
the reduced incoming kernel. -/
theorem incomingKernel_omitted_factor (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) (t : ℝ)
    (z : FusedConfiguration α) (x : Configuration 4) :
    incomingKernel α t z x =
      heatKernel t (z.2 ⟨i, hi₁.symm, hi₂.symm⟩ - x i) *
        incomingKernel (omittedCollisionPair i α hi₁ hi₂) t
          ((omittedAlphaFusedEquiv i α hi₁ hi₂ z).1) (omittedFullPart i x) := by
  have hkernel := freeKernel_omittedPart_factor (t := t) i x (collisionEmbedding α z)
  rw [incomingKernel, hkernel, omittedFullPart_collisionEmbedding_alpha]
  have hi : collisionEmbedding α z i = z.2 ⟨i, hi₁.symm, hi₂.symm⟩ := by
    simp [collisionEmbedding, hi₁.symm, hi₂.symm]
  rw [hi]
  rfl

/-- The collision block separates its heat strand on the deleted spectator
coordinate from the reduced collision block. -/
theorem collisionKernel_omitted_factor (i : Fin 4) (α : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i) (θ t : ℝ)
    (z z' : FusedConfiguration α) :
    collisionKernel α θ t z z' =
      collisionKernel (omittedCollisionPair i α hi₁ hi₂) θ t
        ((omittedAlphaFusedEquiv i α hi₁ hi₂ z).1)
        ((omittedAlphaFusedEquiv i α hi₁ hi₂ z').1) *
        heatKernel t
          ((omittedAlphaFusedEquiv i α hi₁ hi₂ z').2 -
            (omittedAlphaFusedEquiv i α hi₁ hi₂ z).2) := by
  classical
  let γ := omittedCollisionPair i α hi₁ hi₂
  let zr := (omittedAlphaFusedEquiv i α hi₁ hi₂ z).1
  let zr' := (omittedAlphaFusedEquiv i α hi₁ hi₂ z').1
  let e := omittedAlphaSpectatorOptionEquiv i α hi₁ hi₂
  have hnone : e none = ⟨i, hi₁.symm, hi₂.symm⟩ := by
    apply Subtype.ext
    rfl
  have hprod :
      (∏ s : Spectator α, heatKernel t (z'.2 s - z.2 s)) =
        heatKernel t ((omittedAlphaFusedEquiv i α hi₁ hi₂ z').2 -
          (omittedAlphaFusedEquiv i α hi₁ hi₂ z).2) *
          ∏ k : Spectator γ, heatKernel t (zr'.2 k - zr.2 k) := by
    calc
      _ = ∏ o : Option (Spectator γ), heatKernel t (z'.2 (e o) - z.2 (e o)) :=
        (Equiv.prod_comp e (fun s : Spectator α => heatKernel t (z'.2 s - z.2 s))).symm
      _ = heatKernel t (z'.2 (e none) - z.2 (e none)) *
          ∏ k : Spectator γ, heatKernel t (z'.2 (e (some k)) - z.2 (e (some k))) :=
        Fintype.prod_option _
      _ = _ := by
        rw [hnone, omittedAlphaFusedEquiv_apply_deleted,
          omittedAlphaFusedEquiv_apply_deleted]
        congr 1
  unfold collisionKernel
  rw [omittedAlphaFusedEquiv_apply_center i α hi₁ hi₂ z,
    omittedAlphaFusedEquiv_apply_center i α hi₁ hi₂ z', hprod]
  dsimp [zr, zr', γ]
  ac_rfl

/-- A swap with the deleted label in `β` factors into its selected heat
coordinate and a reduced free strand. -/
theorem swappingKernel_omitted_factor (i : Fin 4) (α β : CollisionPair 4)
    (hi₁ : α.1.1 ≠ i) (hi₂ : α.1.2 ≠ i)
    (hβ : i = β.1.1 ∨ i = β.1.2) (t : ℝ)
    (z : FusedConfiguration α) (w : FusedConfiguration β) :
    swappingKernel α β t z w =
      heatKernel t (w.1 - z.2 ⟨i, hi₁.symm, hi₂.symm⟩) *
        freeKernel 3 t
          (collisionEmbedding (omittedCollisionPair i α hi₁ hi₂)
            ((omittedAlphaFusedEquiv i α hi₁ hi₂ z).1))
          (omittedFullPart i (collisionEmbedding β w)) := by
  have hiβ : collisionEmbedding β w i = w.1 := by
    rcases hβ with hβ | hβ
    · simp [collisionEmbedding, hβ]
    · simp [collisionEmbedding, hβ]
  have hiα : collisionEmbedding α z i = z.2 ⟨i, hi₁.symm, hi₂.symm⟩ := by
    simp [collisionEmbedding, hi₁.symm, hi₂.symm]
  have hred := omittedFullPart_collisionEmbedding_alpha i α hi₁ hi₂ z
  rw [swappingKernel, freeKernel_omittedPart_factor,
    hred, hiβ, hiα]

/-- Deleting a coordinate from a full configuration preserves product
Lebesgue measure. -/
theorem measurePreserving_omittedFullConfigurationEquiv (i : Fin 4) :
    MeasurePreserving (omittedFullConfigurationEquiv i) volume volume := by
  have hSplit : MeasurePreserving (Critical2DKPZ.DeltaBose.splitCoordinate i) volume volume :=
    Critical2DKPZ.DeltaBose.measurePreserving_splitCoordinate i
  have hProd : MeasurePreserving
      (MeasurableEquiv.prodCongr (omittedConfigurationEquiv i).symm
        (MeasurableEquiv.refl Plane)) volume volume := by
    exact (measurePreserving_omittedConfigurationEquiv i).symm.prod
      (MeasurePreserving.id (volume : Measure Plane))
  have hfull := hProd.comp hSplit
  exact hfull.congr (omittedFullConfigurationEquiv i).measurable
    (Filter.Eventually.of_forall fun _ => rfl)

/-- Distinct four-particle collision pairs have a β-endpoint outside α. -/
theorem exists_beta_endpoint_outside_alpha (α β : CollisionPair 4) (hαβ : α ≠ β) :
    ∃ i : Fin 4, (i = β.1.1 ∨ i = β.1.2) ∧
      i ≠ α.1.1 ∧ i ≠ α.1.2 := by
  classical
  by_contra hnot
  have hβ₁ : β.1.1 = α.1.1 ∨ β.1.1 = α.1.2 := by
    by_contra h
    have hne := not_or.mp h
    exact hnot ⟨β.1.1, Or.inl rfl, hne.1, hne.2⟩
  have hβ₂ : β.1.2 = α.1.1 ∨ β.1.2 = α.1.2 := by
    by_contra h
    have hne := not_or.mp h
    exact hnot ⟨β.1.2, Or.inr rfl, hne.1, hne.2⟩
  rcases hβ₁ with h₁ | h₁
  · rcases hβ₂ with h₂ | h₂
    · exact (ne_of_lt β.2) (h₁.trans h₂.symm)
    · apply hαβ
      apply Subtype.ext
      exact Prod.ext h₁.symm h₂.symm
  · rcases hβ₂ with h₂ | h₂
    · have hlt : α.1.2 < α.1.1 := by simpa [h₁, h₂] using β.2
      exact (not_lt_of_ge α.2.le) hlt
    · exact (ne_of_lt β.2) (h₁.trans h₂.symm)

end Critical2DKPZ.SHF.Tsai

end
