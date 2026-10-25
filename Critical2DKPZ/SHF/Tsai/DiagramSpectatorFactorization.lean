/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.SubsetProductIntegrals
public import Critical2DKPZ.SHF.Tsai.CoveringKernel
public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
import Critical2DKPZ.SHF.DeltaBose.IncomingMass
import Critical2DKPZ.SHF.DeltaBose.PotentialFusedRows
import Critical2DKPZ.SHF.Tsai.HeadGaussian
import Critical2DKPZ.Collision.RenewalStringCells

/-! # Spectator factorization for collision diagrams

When a word only collides labels in a subset, the other coordinates retain a
free heat strand. The free-strand case is the base of that factorization.
-/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- A free configuration strand splits into the selected coordinates and the
free heat strands on their complement. -/
theorem freeKernel_eq_subset_mul_compl {n : ℕ} (S : Finset (Fin n)) (t : ℝ)
    (x y : Configuration n) :
    freeKernel n t x y =
      freeKernel S.card t (fun i => x (S.orderEmbOfFin rfl i))
          (fun i => y (S.orderEmbOfFin rfl i)) *
        ∏ i : Fin Sᶜ.card,
          heatKernel t (y (Sᶜ.orderEmbOfFin rfl i) - x (Sᶜ.orderEmbOfFin rfl i)) := by
  simpa only [freeKernel] using
    prod_subset_mul_compl S (fun i => heatKernel t (y i - x i))

/-- Pull a collision pair contained in a finite label set back to its
increasing enumeration. -/
noncomputable def collisionPairWithin {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    CollisionPair S.card := by
  let e := S.orderIsoOfFin rfl
  have hlt : (⟨α.1.1, h₁⟩ : S) < ⟨α.1.2, h₂⟩ := α.2
  exact ⟨(e.symm ⟨α.1.1, h₁⟩, e.symm ⟨α.1.2, h₂⟩), e.symm.strictMono hlt⟩

/-- Embed a collision pair in the increasing enumeration of a selected set
back into the original labels. -/
noncomputable def collisionPairInto {n : ℕ} (S : Finset (Fin n))
    (γ : CollisionPair S.card) : CollisionPair n := by
  let e := S.orderIsoOfFin rfl
  refine ⟨((e γ.1.1).1, (e γ.1.2).1), ?_⟩
  change (e γ.1.1).1 < (e γ.1.2).1
  exact e.strictMono γ.2

/-- Embedding a reduced collision and pulling it back recovers the reduced
pair. -/
theorem collisionPairWithin_collisionPairInto {n : ℕ} (S : Finset (Fin n))
    (γ : CollisionPair S.card) :
    collisionPairWithin S (collisionPairInto S γ)
      ((S.orderIsoOfFin rfl γ.1.1).2)
      ((S.orderIsoOfFin rfl γ.1.2).2) = γ := by
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    change ((S.orderIsoOfFin rfl).symm
      (S.orderIsoOfFin rfl γ.1.1)).1 = γ.1.1
    simp
  · apply Fin.ext
    change ((S.orderIsoOfFin rfl).symm
      (S.orderIsoOfFin rfl γ.1.2)).1 = γ.1.2
    simp

/-- Re-enumerating a collision pair in its active subset and embedding it back
recovers the original first label. -/
theorem orderEmb_collisionPairWithin_fst {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    S.orderEmbOfFin rfl (collisionPairWithin S α h₁ h₂).1.1 = α.1.1 := by
  change ((S.orderIsoOfFin rfl)
    ((S.orderIsoOfFin rfl).symm ⟨α.1.1, h₁⟩)).val = α.1.1
  simp

/-- Re-enumerating a collision pair in its active subset and embedding it back
recovers the original second label. -/
theorem orderEmb_collisionPairWithin_snd {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    S.orderEmbOfFin rfl (collisionPairWithin S α h₁ h₂).1.2 = α.1.2 := by
  change ((S.orderIsoOfFin rfl)
    ((S.orderIsoOfFin rfl).symm ⟨α.1.2, h₂⟩)).val = α.1.2
  simp

/-- Pulling back a collision whose two endpoints lie in `S`, then embedding
it again, recovers the original pair. -/
theorem collisionPairInto_collisionPairWithin {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    collisionPairInto S (collisionPairWithin S α h₁ h₂) = α := by
  apply Subtype.ext
  change (S.orderEmbOfFin rfl (collisionPairWithin S α h₁ h₂).1.1,
      S.orderEmbOfFin rfl (collisionPairWithin S α h₁ h₂).1.2) = α.1
  exact Prod.ext (orderEmb_collisionPairWithin_fst S α h₁ h₂)
    (orderEmb_collisionPairWithin_snd S α h₁ h₂)

/-- Reduced pairs are equivalent to full pairs with both endpoints in the
selected set. -/
noncomputable def collisionPairSubsetEquiv {n : ℕ} (S : Finset (Fin n)) :
    CollisionPair S.card ≃ {α : CollisionPair n // α.1.1 ∈ S ∧ α.1.2 ∈ S} where
  toFun γ := ⟨collisionPairInto S γ,
    (S.orderIsoOfFin rfl γ.1.1).2, (S.orderIsoOfFin rfl γ.1.2).2⟩
  invFun α := collisionPairWithin S α.1 α.2.1 α.2.2
  left_inv γ := by
    simpa using collisionPairWithin_collisionPairInto S γ
  right_inv α := by
    apply Subtype.ext
    exact collisionPairInto_collisionPairWithin S α.1 α.2.1 α.2.2

/-- A word touches only labels in `S` exactly when every pair in it has both
endpoints in `S`. -/
theorem wordSupport_subset_iff {n m : ℕ} (S : Finset (Fin n))
    (w : CollisionWord n m) :
    wordSupport w.1 ⊆ S ↔ ∀ i : Fin m, (w.1 i).1.1 ∈ S ∧ (w.1 i).1.2 ∈ S := by
  constructor
  · intro h i
    constructor
    · apply h
      change (w.1 i).1.1 ∈
        Finset.univ.biUnion (fun k => {((w.1 k).1.1), ((w.1 k).1.2)})
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ _, by simp⟩
    · apply h
      change (w.1 i).1.2 ∈
        Finset.univ.biUnion (fun k => {((w.1 k).1.1), ((w.1 k).1.2)})
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ _, by simp⟩
  · intro h j hj
    rcases Finset.mem_biUnion.mp hj with ⟨i, hi, hmem⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hfst | hsnd
    · subst j
      exact (h i).1
    · subst j
      exact (h i).2

/-- Embed each letter of a reduced collision word into the original labels. -/
noncomputable def collisionWordInto {n m : ℕ} (S : Finset (Fin n))
    (w : CollisionWord S.card m) : CollisionWord n m := by
  refine ⟨fun i => collisionPairInto S (w.1 i), ?_⟩
  intro i j hij heq
  apply w.2 i j hij
  apply (collisionPairSubsetEquiv S).injective
  apply Subtype.ext
  exact heq

/-- The word formed by embedding reduced collision letters is supported in the
selected labels. -/
theorem collisionWordInto_support_subset {n m : ℕ} (S : Finset (Fin n))
    (w : CollisionWord S.card m) :
    wordSupport (collisionWordInto S w).1 ⊆ S := by
  apply (wordSupport_subset_iff S (collisionWordInto S w)).2
  intro i
  exact (collisionPairSubsetEquiv S (w.1 i)).2

/-- Restrict a full collision word supported in `S` to its increasing
enumeration. -/
noncomputable def collisionWordWithin {n m : ℕ} (S : Finset (Fin n))
    (w : CollisionWord n m) (hs : wordSupport w.1 ⊆ S) : CollisionWord S.card m := by
  have hletters := (wordSupport_subset_iff S w).mp hs
  refine ⟨fun i => collisionPairWithin S (w.1 i) (hletters i).1 (hletters i).2, ?_⟩
  intro i j hij heq
  apply w.2 i j hij
  have hp := congrArg (collisionPairInto S) heq
  rw [collisionPairInto_collisionPairWithin S (w.1 i) (hletters i).1 (hletters i).2,
    collisionPairInto_collisionPairWithin S (w.1 j) (hletters j).1 (hletters j).2] at hp
  exact hp

/-- Reduced collision words correspond exactly to full words supported in the
selected labels. -/
noncomputable def collisionWordSubsetEquiv {n m : ℕ} (S : Finset (Fin n)) :
    CollisionWord S.card m ≃ {w : CollisionWord n m // wordSupport w.1 ⊆ S} where
  toFun w := ⟨collisionWordInto S w, collisionWordInto_support_subset S w⟩
  invFun w := collisionWordWithin S w.1 w.2
  left_inv w := by
    apply Subtype.ext
    funext i
    exact collisionPairWithin_collisionPairInto S (w.1 i)
  right_inv w := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact collisionPairInto_collisionPairWithin S (w.1.1 i)
      ((wordSupport_subset_iff S w.1).mp w.2 i).1
      ((wordSupport_subset_iff S w.1).mp w.2 i).2

/-- The active spectators of a collision are exactly the spectators of its
relabelled pair in the selected coordinates. -/
noncomputable def spectatorWithinEquiv {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    Spectator (collisionPairWithin S α h₁ h₂) ≃
      {i : Spectator α // i.1 ∈ S} := by
  classical
  let e := S.orderIsoOfFin rfl
  refine
    { toFun := fun i =>
        ⟨⟨(e i.1).1, ⟨?_, ?_⟩⟩, (e i.1).2⟩,
        invFun := fun i =>
        ⟨e.symm ⟨i.1.1, i.2⟩, ⟨?_, ?_⟩⟩,
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    apply i.2.1
    apply e.injective
    apply Subtype.ext
    calc
      (e i.1).1 = α.1.1 := h
      _ = (e (collisionPairWithin S α h₁ h₂).1.1).1 :=
        (orderEmb_collisionPairWithin_fst S α h₁ h₂).symm
  · intro h
    apply i.2.2
    apply e.injective
    apply Subtype.ext
    calc
      (e i.1).1 = α.1.2 := h
      _ = (e (collisionPairWithin S α h₁ h₂).1.2).1 :=
        (orderEmb_collisionPairWithin_snd S α h₁ h₂).symm
  · intro h
    apply i.1.2.1
    calc
      i.1.1 = (e (e.symm ⟨i.1.1, i.2⟩)).1 := by simp
      _ = (e (collisionPairWithin S α h₁ h₂).1.1).1 := by rw [h]
      _ = α.1.1 := orderEmb_collisionPairWithin_fst S α h₁ h₂
  · intro h
    apply i.1.2.2
    calc
      i.1.1 = (e (e.symm ⟨i.1.1, i.2⟩)).1 := by simp
      _ = (e (collisionPairWithin S α h₁ h₂).1.2).1 := by rw [h]
      _ = α.1.2 := orderEmb_collisionPairWithin_snd S α h₁ h₂
  · intro i
    apply Subtype.ext
    exact e.symm_apply_apply i.1
  · intro i
    apply Subtype.ext
    apply Subtype.ext
    simp [e]

/-- Spectator labels outside the selected set are exactly its complement
coordinates. -/
noncomputable def spectatorOutsideEquiv {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    {i : Spectator α // i.1 ∉ S} ≃ Fin Sᶜ.card where
  toFun i := (Sᶜ.orderIsoOfFin rfl).symm ⟨i.1.1, Finset.mem_compl.mpr i.2⟩
  invFun j :=
    ⟨⟨(Sᶜ.orderIsoOfFin rfl j).1,
        ⟨fun h => (Finset.mem_compl.mp (Sᶜ.orderIsoOfFin rfl j).2) (h.symm ▸ h₁),
          fun h => (Finset.mem_compl.mp (Sᶜ.orderIsoOfFin rfl j).2) (h.symm ▸ h₂)⟩⟩,
      Finset.mem_compl.mp (Sᶜ.orderIsoOfFin rfl j).2⟩
  left_inv i := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  right_inv j := by
    apply (Sᶜ.orderIsoOfFin rfl).injective
    apply Subtype.ext
    simp [Finset.coe_orderIsoOfFin_apply]

/-- The active spectator relabelling preserves the selected label value. -/
theorem spectatorWithinEquiv_val {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (j : Spectator (collisionPairWithin S α h₁ h₂)) :
    (spectatorWithinEquiv S α h₁ h₂ j).1.1 = S.orderEmbOfFin rfl j.1 := by
  rfl

/-- The external spectator relabelling preserves the complement label value. -/
theorem spectatorOutsideEquiv_val {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (j : Fin Sᶜ.card) :
    ((spectatorOutsideEquiv S α h₁ h₂).symm j).1.1 = Sᶜ.orderEmbOfFin rfl j := by
  rfl

/-- Partition the spectator index type into active and external labels. -/
noncomputable def spectatorPartitionEquiv {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    Spectator α ≃ Spectator (collisionPairWithin S α h₁ h₂) ⊕ Fin Sᶜ.card := by
  classical
  exact (Equiv.sumCompl (fun i : Spectator α => i.1 ∈ S)).symm.trans
    (Equiv.sumCongr (spectatorWithinEquiv S α h₁ h₂).symm
      (spectatorOutsideEquiv S α h₁ h₂))

/-- The inverse active correspondence sends a reduced spectator to its
original selected label. -/
theorem spectatorPartitionEquiv_symm_inl {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (j : Spectator (collisionPairWithin S α h₁ h₂)) :
    (spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inl j) =
      (spectatorWithinEquiv S α h₁ h₂ j).1 := by
  apply (spectatorPartitionEquiv S α h₁ h₂).injective
  rw [(spectatorPartitionEquiv S α h₁ h₂).apply_symm_apply]
  have hm : ((spectatorWithinEquiv S α h₁ h₂ j).1).1 ∈ S :=
    (spectatorWithinEquiv S α h₁ h₂ j).2
  simp [spectatorPartitionEquiv, Equiv.sumCompl, hm]

/-- The inverse complement correspondence sends an external index to its
original spectator label. -/
theorem spectatorPartitionEquiv_symm_inr {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (j : Fin Sᶜ.card) :
    (spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inr j) =
      ((spectatorOutsideEquiv S α h₁ h₂).symm j).1 := by
  apply (spectatorPartitionEquiv S α h₁ h₂).injective
  rw [(spectatorPartitionEquiv S α h₁ h₂).apply_symm_apply]
  have hm : (((spectatorOutsideEquiv S α h₁ h₂).symm j).1).1 ∉ S :=
    ((spectatorOutsideEquiv S α h₁ h₂).symm j).2
  simp [spectatorPartitionEquiv, Equiv.sumCompl, hm]

/-- Products over all spectators split into active and external products. -/
theorem prod_spectatorPartition {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    {M : Type*} [CommMonoid M] (f : Spectator α → M) :
    (∏ i : Spectator α, f i) =
      (∏ j : Spectator (collisionPairWithin S α h₁ h₂),
        f ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inl j))) *
      ∏ k : Fin Sᶜ.card,
        f ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inr k)) := by
  rw [← Equiv.prod_comp (spectatorPartitionEquiv S α h₁ h₂).symm f,
    Fintype.prod_sum_type]

/-- Split the fused spectator coordinates into the selected collision's
spectators and the labels outside the selected set. -/
noncomputable def spectatorCoordinateSplit {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    (Spectator α → Plane) ≃ᵐ
      (Spectator (collisionPairWithin S α h₁ h₂) → Plane) ×
        (Fin Sᶜ.card → Plane) :=
  (MeasurableEquiv.piCongrLeft (fun _ :
      Spectator (collisionPairWithin S α h₁ h₂) ⊕ Fin Sᶜ.card => Plane)
      (spectatorPartitionEquiv S α h₁ h₂)).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ :
      Spectator (collisionPairWithin S α h₁ h₂) ⊕ Fin Sᶜ.card => Plane))

/-- The selected spectator coordinates are evaluated at the inverse active
index correspondence. -/
theorem spectatorCoordinateSplit_fst_apply {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (z : Spectator α → Plane) (j : Spectator (collisionPairWithin S α h₁ h₂)) :
    (spectatorCoordinateSplit S α h₁ h₂ z).1 j =
      z ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inl j)) := by
  change (Equiv.sumPiEquivProdPi
      (fun _ : Spectator (collisionPairWithin S α h₁ h₂) ⊕ Fin Sᶜ.card => Plane)
      (Equiv.piCongrLeft
        (fun _ : Spectator (collisionPairWithin S α h₁ h₂) ⊕ Fin Sᶜ.card => Plane)
        (spectatorPartitionEquiv S α h₁ h₂) z)).1 j = _
  simp [Equiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply]

/-- The external spectator coordinates are evaluated at the inverse
complement-index correspondence. -/
theorem spectatorCoordinateSplit_snd_apply {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (z : Spectator α → Plane) (j : Fin Sᶜ.card) :
    (spectatorCoordinateSplit S α h₁ h₂ z).2 j =
      z ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inr j)) := by
  change (Equiv.sumPiEquivProdPi
      (fun _ : Spectator (collisionPairWithin S α h₁ h₂) ⊕ Fin Sᶜ.card => Plane)
      (Equiv.piCongrLeft
        (fun _ : Spectator (collisionPairWithin S α h₁ h₂) ⊕ Fin Sᶜ.card => Plane)
        (spectatorPartitionEquiv S α h₁ h₂) z)).2 j = _
  simp [Equiv.sumPiEquivProdPi, Equiv.piCongrLeft_apply]

/-- The spectator coordinate split preserves the product Lebesgue measure. -/
theorem measurePreserving_spectatorCoordinateSplit {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    MeasurePreserving (spectatorCoordinateSplit S α h₁ h₂)
      (volume : Measure (Spectator α → Plane))
      ((volume : Measure (Spectator (collisionPairWithin S α h₁ h₂) → Plane)).prod
        (volume : Measure (Fin Sᶜ.card → Plane))) := by
  classical
  change MeasurePreserving (spectatorCoordinateSplit S α h₁ h₂)
    (Measure.pi fun _ : Spectator α => (volume : Measure Plane))
    ((Measure.pi fun _ : Spectator (collisionPairWithin S α h₁ h₂) =>
        (volume : Measure Plane)).prod
      (Measure.pi fun _ : Fin Sᶜ.card => (volume : Measure Plane)))
  exact (measurePreserving_sumPiEquivProdPi (fun _ => (volume : Measure Plane))).comp
    (measurePreserving_piCongrLeft
      (fun _ : Spectator (collisionPairWithin S α h₁ h₂) ⊕ Fin Sᶜ.card =>
        (volume : Measure Plane))
      (spectatorPartitionEquiv S α h₁ h₂))

/-- Split a fused collision configuration into the reduced fused coordinates
and the coordinates outside the selected set. -/
noncomputable def fusedCoordinateSplit {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    FusedConfiguration α ≃ᵐ
      FusedConfiguration (collisionPairWithin S α h₁ h₂) ×
        (Fin Sᶜ.card → Plane) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl Plane)
      (spectatorCoordinateSplit S α h₁ h₂)).trans
    MeasurableEquiv.prodAssoc.symm

/-- The active part of the fused split leaves its center coordinate unchanged. -/
theorem fusedCoordinateSplit_center {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (z : FusedConfiguration α) :
    (fusedCoordinateSplit S α h₁ h₂ z).1.1 = z.1 := rfl

/-- The active fused spectator coordinates are the values at their original
selected labels. -/
theorem fusedCoordinateSplit_active_apply {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (z : FusedConfiguration α) (j : Spectator (collisionPairWithin S α h₁ h₂)) :
    (fusedCoordinateSplit S α h₁ h₂ z).1.2 j =
      z.2 (spectatorWithinEquiv S α h₁ h₂ j).1 := by
  change ((z.1, (spectatorCoordinateSplit S α h₁ h₂ z.2).1),
    (spectatorCoordinateSplit S α h₁ h₂ z.2).2).1.2 j = _
  exact spectatorCoordinateSplit_fst_apply S α h₁ h₂ z.2 j

/-- The external fused coordinates are the values at their original
complement labels. -/
theorem fusedCoordinateSplit_external_apply {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (z : FusedConfiguration α) (j : Fin Sᶜ.card) :
    (fusedCoordinateSplit S α h₁ h₂ z).2 j =
      z.2 ((spectatorOutsideEquiv S α h₁ h₂).symm j).1 := by
  change ((z.1, (spectatorCoordinateSplit S α h₁ h₂ z.2).1),
    (spectatorCoordinateSplit S α h₁ h₂ z.2).2).2 j = _
  exact spectatorCoordinateSplit_snd_apply S α h₁ h₂ z.2 j

/-- The fused coordinate split preserves product Lebesgue measure. -/
theorem measurePreserving_fusedCoordinateSplit {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S) :
    MeasurePreserving (fusedCoordinateSplit S α h₁ h₂)
      (volume : Measure (FusedConfiguration α))
      ((volume : Measure (FusedConfiguration (collisionPairWithin S α h₁ h₂))).prod
        (volume : Measure (Fin Sᶜ.card → Plane))) := by
  classical
  change MeasurePreserving (fusedCoordinateSplit S α h₁ h₂)
    ((volume : Measure Plane).prod
      (volume : Measure (Spectator α → Plane)))
    (((volume : Measure Plane).prod
        (volume : Measure (Spectator (collisionPairWithin S α h₁ h₂) → Plane))).prod
      (volume : Measure (Fin Sᶜ.card → Plane)))
  exact (measurePreserving_prodAssoc volume volume volume).symm.comp
    ((MeasurePreserving.prod (MeasurePreserving.id volume)
      (measurePreserving_spectatorCoordinateSplit S α h₁ h₂)))

/-- On selected labels, a full collision embedding agrees with the reduced
collision embedding. -/
theorem collisionEmbedding_subset_active {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (z : FusedConfiguration α) (i : Fin S.card) :
    collisionEmbedding α z (S.orderEmbOfFin rfl i) =
      collisionEmbedding (collisionPairWithin S α h₁ h₂)
        (fusedCoordinateSplit S α h₁ h₂ z).1 i := by
  let γ := collisionPairWithin S α h₁ h₂
  let zS := (fusedCoordinateSplit S α h₁ h₂ z).1
  by_cases hi₁ : i = γ.1.1
  · subst i
    change collisionEmbedding α z
        (S.orderEmbOfFin rfl (collisionPairWithin S α h₁ h₂).1.1) =
      collisionEmbedding (collisionPairWithin S α h₁ h₂)
        (fusedCoordinateSplit S α h₁ h₂ z).1
        (collisionPairWithin S α h₁ h₂).1.1
    rw [orderEmb_collisionPairWithin_fst]
    simp only [collisionEmbedding_pair_left]
    exact (fusedCoordinateSplit_center S α h₁ h₂ z).symm
  · by_cases hi₂ : i = γ.1.2
    · subst i
      change collisionEmbedding α z
          (S.orderEmbOfFin rfl (collisionPairWithin S α h₁ h₂).1.2) =
        collisionEmbedding (collisionPairWithin S α h₁ h₂)
          (fusedCoordinateSplit S α h₁ h₂ z).1
          (collisionPairWithin S α h₁ h₂).1.2
      rw [orderEmb_collisionPairWithin_snd]
      simp only [collisionEmbedding_pair_right]
      exact (fusedCoordinateSplit_center S α h₁ h₂ z).symm
    · let j : Spectator γ := ⟨i, ⟨hi₁, hi₂⟩⟩
      calc
        collisionEmbedding α z (S.orderEmbOfFin rfl i) =
            collisionEmbedding α z (spectatorWithinEquiv S α h₁ h₂ j).1.1 := by
          rw [spectatorWithinEquiv_val]
        _ = z.2 (spectatorWithinEquiv S α h₁ h₂ j).1 :=
          collisionEmbedding_spectator_apply α z _
        _ = zS.2 j := (fusedCoordinateSplit_active_apply S α h₁ h₂ z j).symm
        _ = collisionEmbedding γ zS j.1 :=
          (collisionEmbedding_spectator_apply γ zS j).symm

/-- On labels outside the selected set, a full collision embedding is exactly
the corresponding external spectator coordinate. -/
theorem collisionEmbedding_subset_external {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (z : FusedConfiguration α) (i : Fin Sᶜ.card) :
    collisionEmbedding α z (Sᶜ.orderEmbOfFin rfl i) =
      (fusedCoordinateSplit S α h₁ h₂ z).2 i := by
  let j := (spectatorOutsideEquiv S α h₁ h₂).symm i
  calc
    collisionEmbedding α z (Sᶜ.orderEmbOfFin rfl i) =
        collisionEmbedding α z j.1.1 := by
      rw [spectatorOutsideEquiv_val]
    _ = z.2 j.1 := collisionEmbedding_spectator_apply α z j.1
    _ = (fusedCoordinateSplit S α h₁ h₂ z).2 i :=
      (fusedCoordinateSplit_external_apply S α h₁ h₂ z i).symm

/-- The incoming trace kernel factors into the reduced active collision and
the independent external heat strands. -/
theorem ofReal_incomingKernel_subset_factor {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    {r : ℝ} (hr : 0 < r) (z : FusedConfiguration α) (x : Configuration n) :
    ENNReal.ofReal (incomingKernel α r z x) =
      ENNReal.ofReal (incomingKernel (collisionPairWithin S α h₁ h₂) r
        (fusedCoordinateSplit S α h₁ h₂ z).1
        (fun j => x (S.orderEmbOfFin rfl j))) *
      ∏ j : Fin Sᶜ.card,
        ENNReal.ofReal (heatKernel r
          ((fusedCoordinateSplit S α h₁ h₂ z).2 j -
            x (Sᶜ.orderEmbOfFin rfl j))) := by
  let γ := collisionPairWithin S α h₁ h₂
  let zS := (fusedCoordinateSplit S α h₁ h₂ z).1
  let zC := (fusedCoordinateSplit S α h₁ h₂ z).2
  let xS : Configuration S.card := fun j => x (S.orderEmbOfFin rfl j)
  have hcenter :
      (ENNReal.ofReal (heatKernel r (z.1 - x α.1.1)) *
        ENNReal.ofReal (heatKernel r (z.1 - x α.1.2))) =
      (ENNReal.ofReal (heatKernel r (zS.1 - xS γ.1.1)) *
        ENNReal.ofReal (heatKernel r (zS.1 - xS γ.1.2))) := by
    simp [γ, zS, xS, fusedCoordinateSplit_center,
      orderEmb_collisionPairWithin_fst, orderEmb_collisionPairWithin_snd]
  have hactive :
      (∏ j : Spectator γ,
        ENNReal.ofReal (heatKernel r (zS.2 j - xS j.1))) =
      ∏ j : Spectator γ,
        ENNReal.ofReal (heatKernel r
          (z.2 ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inl j)) -
            x ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inl j)).1)) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [γ, zS, xS, fusedCoordinateSplit_active_apply,
      spectatorPartitionEquiv_symm_inl, spectatorWithinEquiv_val]
  have hexternal :
      (∏ j : Fin Sᶜ.card,
        ENNReal.ofReal (heatKernel r (zC j - x (Sᶜ.orderEmbOfFin rfl j)))) =
      ∏ j : Fin Sᶜ.card,
        ENNReal.ofReal (heatKernel r
          (z.2 ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inr j)) -
            x ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inr j)).1)) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [zC, fusedCoordinateSplit_external_apply,
      spectatorPartitionEquiv_symm_inr, spectatorOutsideEquiv_val]
  rw [Critical2DKPZ.DeltaBose.ofReal_incomingKernel_eq_prod α hr z x,
    Critical2DKPZ.DeltaBose.ofReal_incomingKernel_eq_prod γ hr zS xS,
    prod_spectatorPartition S α h₁ h₂
      (fun i : Spectator α => ENNReal.ofReal (heatKernel r (z.2 i - x i.1))),
    hcenter, hactive, hexternal]
  ac_rfl

/-- A collision block factors into its reduced active block and the external
heat transition. -/
theorem collisionKernel_subset_factor {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    (θ s : ℝ) (z z' : FusedConfiguration α) :
    collisionKernel α θ s z z' =
      collisionKernel (collisionPairWithin S α h₁ h₂) θ s
        (fusedCoordinateSplit S α h₁ h₂ z).1
        (fusedCoordinateSplit S α h₁ h₂ z').1 *
      ∏ j : Fin Sᶜ.card,
        heatKernel s
          ((fusedCoordinateSplit S α h₁ h₂ z').2 j -
            (fusedCoordinateSplit S α h₁ h₂ z).2 j) := by
  let γ := collisionPairWithin S α h₁ h₂
  let zS := (fusedCoordinateSplit S α h₁ h₂ z).1
  let zC := (fusedCoordinateSplit S α h₁ h₂ z).2
  let z'S := (fusedCoordinateSplit S α h₁ h₂ z').1
  let z'C := (fusedCoordinateSplit S α h₁ h₂ z').2
  have hactive :
      (∏ j : Spectator γ, heatKernel s (z'S.2 j - zS.2 j)) =
      ∏ j : Spectator γ,
        heatKernel s
          (z'.2 ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inl j)) -
            z.2 ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inl j))) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [γ, zS, z'S, fusedCoordinateSplit_active_apply,
      spectatorPartitionEquiv_symm_inl]
  have hexternal :
      (∏ j : Fin Sᶜ.card, heatKernel s (z'C j - zC j)) =
      ∏ j : Fin Sᶜ.card,
        heatKernel s
          (z'.2 ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inr j)) -
            z.2 ((spectatorPartitionEquiv S α h₁ h₂).symm (Sum.inr j))) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [zC, z'C, fusedCoordinateSplit_external_apply,
      spectatorPartitionEquiv_symm_inr]
  unfold collisionKernel
  rw [prod_spectatorPartition S α h₁ h₂
    (fun i : Spectator α => heatKernel s (z'.2 i - z.2 i)), hactive, hexternal]
  simp only [γ, fusedCoordinateSplit_center]
  ac_rfl

/-- The `ENNReal` collision factor splits into its active block and external
heat transitions. -/
theorem ofReal_collisionKernel_subset_factor {n : ℕ} (S : Finset (Fin n))
    (α : CollisionPair n) (h₁ : α.1.1 ∈ S) (h₂ : α.1.2 ∈ S)
    {θ s : ℝ} (hs : 0 < s) (z z' : FusedConfiguration α) :
    ENNReal.ofReal (collisionKernel α θ s z z') =
      ENNReal.ofReal (collisionKernel (collisionPairWithin S α h₁ h₂) θ s
        (fusedCoordinateSplit S α h₁ h₂ z).1
        (fusedCoordinateSplit S α h₁ h₂ z').1) *
      ∏ j : Fin Sᶜ.card,
        ENNReal.ofReal (heatKernel s
          ((fusedCoordinateSplit S α h₁ h₂ z').2 j -
            (fusedCoordinateSplit S α h₁ h₂ z).2 j)) := by
  rw [collisionKernel_subset_factor]
  rw [ENNReal.ofReal_mul
    (collisionKernel_pos (collisionPairWithin S α h₁ h₂) θ hs _ _).le]
  rw [ENNReal.ofReal_prod_of_nonneg (fun j _ => (heatKernel_pos hs _).le)]

/-- The empty collision word splits into the active free kernel and the free
heat strands on the complement. -/
theorem diagramKernel_nil_subset_factor {n : ℕ} (S : Finset (Fin n)) (θ : ℝ)
    {t : ℝ} (ht : 0 < t) (x y : Configuration n) :
    diagramKernel θ [] t x y =
      diagramKernel θ [] t
        (fun i => x (S.orderEmbOfFin rfl i))
        (fun i => y (S.orderEmbOfFin rfl i)) *
      ∏ i : Fin Sᶜ.card,
        ENNReal.ofReal (heatKernel t
          (y (Sᶜ.orderEmbOfFin rfl i) - x (Sᶜ.orderEmbOfFin rfl i))) := by
  rw [diagramKernel, diagramKernel, freeKernel_eq_subset_mul_compl]
  rw [ENNReal.ofReal_mul (freeKernel_pos S.card ht _ _).le]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => (heatKernel_pos ht _).le)]

private theorem lintegral_iterated_mul {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    (f : X → ℝ≥0∞) (g : Y → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ x, ∫⁻ y, f x * g y ∂ν ∂μ) =
      (∫⁻ x, f x ∂μ) * ∫⁻ y, g y ∂ν := by
  have hm : Measurable (fun p : X × Y => f p.1 * g p.2) :=
    (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  calc
    _ = ∫⁻ p : X × Y, f p.1 * g p.2 ∂(μ.prod ν) :=
      lintegral_lintegral hm.aemeasurable
    _ = _ := lintegral_prod_mul hf.aemeasurable hg.aemeasurable

private theorem lintegral_rect_pair_assoc {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {f : (X × Y) → (X × Y) → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) :
    (∫⁻ p : X × Y, ∫⁻ p' : X × Y, f p p' ∂(μ.prod ν) ∂(μ.prod ν)) =
      ∫⁻ x : X, ∫⁻ y : Y, ∫⁻ x' : X, ∫⁻ y' : Y,
        f (x, y) (x', y') ∂ν ∂μ ∂ν ∂μ := by
  have hOuter : Measurable (fun p : X × Y => ∫⁻ p' : X × Y, f p p' ∂(μ.prod ν)) :=
    hf.lintegral_prod_right'
  have hOuter' : Measurable (fun p : X × Y =>
      ∫⁻ x' : X, ∫⁻ y' : Y, f p (x', y') ∂ν ∂μ) := by
    have heq : (fun p : X × Y => ∫⁻ p' : X × Y, f p p' ∂(μ.prod ν)) =
        fun p => ∫⁻ x' : X, ∫⁻ y' : Y, f p (x', y') ∂ν ∂μ := by
      funext p
      exact lintegral_prod (fun p' : X × Y => f p p')
        ((hf.comp (measurable_const.prodMk measurable_id)).aemeasurable)
    rw [← heq]
    exact hOuter
  calc
    _ = ∫⁻ p : X × Y, ∫⁻ x' : X, ∫⁻ y' : Y, f p (x', y') ∂ν ∂μ
          ∂(μ.prod ν) := by
      apply lintegral_congr
      intro p
      exact lintegral_prod (fun p' : X × Y => f p p')
        ((hf.comp (measurable_const.prodMk measurable_id)).aemeasurable)
    _ = ∫⁻ x : X, ∫⁻ y : Y, ∫⁻ x' : X, ∫⁻ y' : Y,
          f (x, y) (x', y') ∂ν ∂μ ∂ν ∂μ := by
      rw [lintegral_prod _ hOuter'.aemeasurable]

private theorem lintegral_rect_product {X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]
    {R : X → X → ℝ≥0∞} {H : Y → Y → ℝ≥0∞}
    (hR : Measurable (Function.uncurry R)) (hH : Measurable (Function.uncurry H)) :
    (∫⁻ x : X, ∫⁻ y : Y, ∫⁻ x' : X, ∫⁻ y' : Y,
      R x x' * H y y' ∂ν ∂μ ∂ν ∂μ) =
      (∫⁻ x : X, ∫⁻ x' : X, R x x' ∂μ ∂μ) *
        ∫⁻ y : Y, ∫⁻ y' : Y, H y y' ∂ν ∂ν := by
  calc
    _ = ∫⁻ x : X, ∫⁻ y : Y,
        (∫⁻ x' : X, R x x' ∂μ) * ∫⁻ y' : Y, H y y' ∂ν ∂ν ∂μ := by
      apply lintegral_congr
      intro x
      apply lintegral_congr
      intro y
      exact lintegral_iterated_mul (R x) (H y)
        (hR.comp (measurable_const.prodMk measurable_id))
        (hH.comp (measurable_const.prodMk measurable_id))
    _ = _ := lintegral_iterated_mul
      (fun x => ∫⁻ x' : X, R x x' ∂μ)
      (fun y => ∫⁻ y' : Y, H y y' ∂ν)
      hR.lintegral_prod_right' hH.lintegral_prod_right'

private theorem lintegral_pair_product {F X Y : Type*} [MeasurableSpace F]
    [MeasurableSpace X] [MeasurableSpace Y] {μF : Measure F} {μX : Measure X}
    {μY : Measure Y} [SFinite μF] [SFinite μX] [SFinite μY]
    (e : F ≃ᵐ X × Y) (hMP : MeasurePreserving e μF (μX.prod μY))
    {R : X → X → ℝ≥0∞} {H : Y → Y → ℝ≥0∞}
    (hR : Measurable (Function.uncurry R)) (hH : Measurable (Function.uncurry H)) :
    (∫⁻ z : F, ∫⁻ z' : F,
      R (e z).1 (e z').1 * H (e z).2 (e z').2 ∂μF ∂μF) =
      (∫⁻ x : X, ∫⁻ x' : X, R x x' ∂μX ∂μX) *
        ∫⁻ y : Y, ∫⁻ y' : Y, H y y' ∂μY ∂μY := by
  let f : (X × Y) → (X × Y) → ℝ≥0∞ := fun p p' => R p.1 p'.1 * H p.2 p'.2
  have hf : Measurable (Function.uncurry f) := by
    have hRmap : Measurable (fun p : (X × Y) × (X × Y) => (p.1.1, p.2.1)) :=
      measurable_fst.fst.prodMk measurable_snd.fst
    have hHmap : Measurable (fun p : (X × Y) × (X × Y) => (p.1.2, p.2.2)) :=
      measurable_fst.snd.prodMk measurable_snd.snd
    exact (hR.comp hRmap).mul (hH.comp hHmap)
  have hMPpair : MeasurePreserving (MeasurableEquiv.prodCongr e e)
      (μF.prod μF) ((μX.prod μY).prod (μX.prod μY)) :=
    MeasurePreserving.prod hMP hMP
  have hsource : Measurable (fun p : F × F =>
      R (e p.1).1 (e p.2).1 * H (e p.1).2 (e p.2).2) := by
    convert hf.comp (MeasurableEquiv.prodCongr e e).measurable using 1
    funext p
    rfl
  calc
    _ = ∫⁻ z : F × F,
        R (e z.1).1 (e z.2).1 * H (e z.1).2 (e z.2).2 ∂(μF.prod μF) :=
      lintegral_lintegral hsource.aemeasurable
    _ = ∫⁻ p : (X × Y) × (X × Y), f p.1 p.2
          ∂((μX.prod μY).prod (μX.prod μY)) := by
      exact hMPpair.lintegral_comp hf
    _ = _ := by
      rw [← lintegral_lintegral hf.aemeasurable]
      rw [lintegral_rect_pair_assoc hf]
      exact lintegral_rect_product hR hH

/-- Three successive free heat strands on one external label collapse to the
single strand across their total elapsed time. -/
theorem lintegral_heatKernel_chain_three {r s q : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hq : 0 < q) (a b : Plane) :
    (∫⁻ z : Plane, ∫⁻ z' : Plane,
      ENNReal.ofReal (heatKernel r (z - a)) *
        ENNReal.ofReal (heatKernel s (z' - z)) *
          ENNReal.ofReal (heatKernel q (b - z'))) =
      ENNReal.ofReal (heatKernel (r + s + q) (b - a)) := by
  have hinner (z : Plane) :
      (∫⁻ z' : Plane,
        ENNReal.ofReal (heatKernel r (z - a)) *
          (ENNReal.ofReal (heatKernel s (z' - z)) *
            ENNReal.ofReal (heatKernel q (b - z')))) =
        ENNReal.ofReal (heatKernel r (z - a)) *
          ENNReal.ofReal (heatKernel (s + q) (b - z)) := by
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_heatKernel_shifted_mul hs hq z b]
  calc
    _ = ∫⁻ z : Plane,
        ENNReal.ofReal (heatKernel r (z - a)) *
          ENNReal.ofReal (heatKernel (s + q) (b - z)) := by
      apply lintegral_congr
      intro z
      calc
        _ = ∫⁻ z' : Plane,
            ENNReal.ofReal (heatKernel r (z - a)) *
              (ENNReal.ofReal (heatKernel s (z' - z)) *
                ENNReal.ofReal (heatKernel q (b - z'))) := by
          apply lintegral_congr
          intro z'
          ring
        _ = _ := hinner z
    _ = ENNReal.ofReal (heatKernel (r + (s + q)) (b - a)) :=
      lintegral_heatKernel_shifted_mul hr (add_pos hs hq) a b
    _ = _ := by rw [add_assoc]

/-- Integrating a finite product of external three-step heat chains gives the
product of the single-label endpoint kernels. -/
theorem lintegral_fin_heatKernel_chain_three {k : ℕ} {r s q : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hq : 0 < q)
    (a b : Fin k → Plane) :
    (∫⁻ z : Fin k → Plane, ∫⁻ z' : Fin k → Plane,
      ∏ j : Fin k,
        ENNReal.ofReal (heatKernel r (z j - a j)) *
          ENNReal.ofReal (heatKernel s (z' j - z j)) *
            ENNReal.ofReal (heatKernel q (b j - z' j))) =
      ∏ j : Fin k, ENNReal.ofReal (heatKernel (r + s + q) (b j - a j)) := by
  let e : (Fin k → Plane) × (Fin k → Plane) ≃ᵐ (Fin k → Plane × Plane) :=
    (MeasurableEquiv.arrowProdEquivProdArrow Plane Plane (Fin k)).symm
  let f : Fin k → Plane × Plane → ℝ≥0∞ := fun j p =>
    ENNReal.ofReal (heatKernel r (p.1 - a j)) *
      ENNReal.ofReal (heatKernel s (p.2 - p.1)) *
        ENNReal.ofReal (heatKernel q (b j - p.2))
  have hf : ∀ j, Measurable (f j) := by
    intro j
    have h₁ : Measurable (fun p : Plane × Plane => heatKernel r (p.1 - a j)) :=
      (Critical2DKPZ.measurable_heatKernel r).comp
        (measurable_fst.sub measurable_const)
    have h₂ : Measurable (fun p : Plane × Plane => heatKernel s (p.2 - p.1)) :=
      (Critical2DKPZ.measurable_heatKernel s).comp
        (measurable_snd.sub measurable_fst)
    have h₃ : Measurable (fun p : Plane × Plane => heatKernel q (b j - p.2)) :=
      (Critical2DKPZ.measurable_heatKernel q).comp
        (measurable_const.sub measurable_snd)
    dsimp [f]
    exact ((h₁.ennreal_ofReal).mul (h₂.ennreal_ofReal)).mul (h₃.ennreal_ofReal)
  have hF : Measurable (fun p : Fin k → Plane × Plane => ∏ j, f j (p j)) := by
    apply Finset.measurable_fun_prod Finset.univ
    intro j hj
    exact (hf j).comp (measurable_pi_apply j)
  have hsource : Measurable (fun p : (Fin k → Plane) × (Fin k → Plane) =>
      ∏ j : Fin k,
        ENNReal.ofReal (heatKernel r (p.1 j - a j)) *
          ENNReal.ofReal (heatKernel s (p.2 j - p.1 j)) *
            ENNReal.ofReal (heatKernel q (b j - p.2 j))) := by
    have h := hF.comp e.measurable
    change Measurable (fun p : (Fin k → Plane) × (Fin k → Plane) =>
      ∏ j : Fin k, f j ((e p) j)) at h
    simpa [f, e, MeasurableEquiv.arrowProdEquivProdArrow] using h
  have hMP : MeasurePreserving e volume volume :=
    (volume_measurePreserving_arrowProdEquivProdArrow Plane Plane (Fin k)).symm
  have hfactor := Collision.lintegral_fin_nat_prod_eq_prod_collision
    (fun _ : Fin k => (volume : Measure (Plane × Plane))) f hf
  calc
    _ = ∫⁻ p : (Fin k → Plane) × (Fin k → Plane),
        (fun y : Fin k → Plane × Plane => ∏ j, f j (y j)) (e p) := by
      rw [Measure.volume_eq_prod]
      rw [lintegral_lintegral hsource.aemeasurable]
      apply lintegral_congr
      intro p
      rfl
    _ = ∫⁻ y : Fin k → Plane × Plane, ∏ j, f j (y j) :=
      hMP.lintegral_comp hF
    _ = ∏ j : Fin k, ∫⁻ p : Plane × Plane, f j p := hfactor
    _ = ∏ j : Fin k, ENNReal.ofReal (heatKernel (r + s + q) (b j - a j)) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Measure.volume_eq_prod]
      have hm : Measurable (fun p : Plane × Plane => f j p) := hf j
      rw [lintegral_prod (fun p : Plane × Plane => f j p) hm.aemeasurable]
      simpa [f] using lintegral_heatKernel_chain_three hr hs hq (a j) (b j)

/-- A collision diagram whose letters lie in a selected label set is the
reduced diagram times the free heat kernel on the complement. -/
theorem diagramKernel_subset_factor_of_forall₂ {n : ℕ} (S : Finset (Fin n))
    (θ : ℝ) (w : List (CollisionPair n)) (wS : List (CollisionPair S.card))
    (hRel : List.Forall₂
      (fun α γ => ∃ h₁ : α.1.1 ∈ S, ∃ h₂ : α.1.2 ∈ S,
        γ = collisionPairWithin S α h₁ h₂) w wS) :
    ∀ {t : ℝ}, 0 < t → ∀ x y : Configuration n,
      diagramKernel θ w t x y =
        diagramKernel θ wS t
          (fun i => x (S.orderEmbOfFin rfl i))
          (fun i => y (S.orderEmbOfFin rfl i)) *
        ∏ i : Fin Sᶜ.card,
          ENNReal.ofReal (heatKernel t
            (y (Sᶜ.orderEmbOfFin rfl i) - x (Sᶜ.orderEmbOfFin rfl i))) := by
  induction hRel with
  | nil =>
    intro t ht x y
    exact diagramKernel_nil_subset_factor S θ ht x y
  | @cons α γ w wS hPair hTail ih =>
    intro t ht x y
    rcases hPair with ⟨h₁, h₂, hγ⟩
    subst γ
    let γ := collisionPairWithin S α h₁ h₂
    let xS : Configuration S.card := fun i => x (S.orderEmbOfFin rfl i)
    let yS : Configuration S.card := fun i => y (S.orderEmbOfFin rfl i)
    let xC : Fin Sᶜ.card → Plane := fun i => x (Sᶜ.orderEmbOfFin rfl i)
    let yC : Fin Sᶜ.card → Plane := fun i => y (Sᶜ.orderEmbOfFin rfl i)
    let C : ℝ≥0∞ := ∏ i : Fin Sᶜ.card, ENNReal.ofReal
      (heatKernel t (yC i - xC i))
    let R (r u : ℝ) (z z' : FusedConfiguration γ) : ℝ≥0∞ :=
      ENNReal.ofReal (incomingKernel γ r z xS) *
        ENNReal.ofReal (collisionKernel γ θ (u - r) z z') *
          diagramKernel θ wS (t - u) (collisionEmbedding γ z') yS
    let H (r u : ℝ) (z z' : Fin Sᶜ.card → Plane) : ℝ≥0∞ :=
      ∏ i : Fin Sᶜ.card,
        ENNReal.ofReal (heatKernel r (z i - xC i)) *
          ENNReal.ofReal (heatKernel (u - r) (z' i - z i)) *
            ENNReal.ofReal (heatKernel (t - u) (yC i - z' i))
    have hCtop : C ≠ ⊤ := by
      apply ENNReal.prod_ne_top
      intro i hi
      exact ENNReal.ofReal_ne_top
    have hR (r u : ℝ) : Measurable (Function.uncurry (R r u)) := by
      have hI : Measurable (fun p : FusedConfiguration γ × FusedConfiguration γ =>
          ENNReal.ofReal (incomingKernel γ r p.1 xS)) := by
        exact ((measurable_incomingKernel γ).comp
          (measurable_const.prodMk (measurable_fst.prodMk measurable_const))).ennreal_ofReal
      have hJ : Measurable (fun p : FusedConfiguration γ × FusedConfiguration γ =>
          ENNReal.ofReal (collisionKernel γ θ (u - r) p.1 p.2)) := by
        exact ((measurable_collisionKernel γ).comp
          ((measurable_const.prodMk measurable_const).prodMk measurable_id)).ennreal_ofReal
      have hD : Measurable (fun p : FusedConfiguration γ × FusedConfiguration γ =>
          diagramKernel θ wS (t - u) (collisionEmbedding γ p.2) yS) := by
        exact measurable_diagramKernel_comp wS measurable_const measurable_const
          ((measurable_collisionEmbedding γ).comp measurable_snd) measurable_const
      exact (hI.mul hJ).mul hD
    have hH (r u : ℝ) : Measurable (Function.uncurry (H r u)) := by
      apply Finset.measurable_fun_prod Finset.univ
      intro i hi
      have h₁ : Measurable (fun p : (Fin Sᶜ.card → Plane) ×
          (Fin Sᶜ.card → Plane) => heatKernel r (p.1 i - xC i)) :=
        (measurable_heatKernel r).comp
          (((measurable_pi_apply i).comp measurable_fst).sub measurable_const)
      have h₂ : Measurable (fun p : (Fin Sᶜ.card → Plane) ×
          (Fin Sᶜ.card → Plane) => heatKernel (u - r) (p.2 i - p.1 i)) :=
        (measurable_heatKernel (u - r)).comp
          (((measurable_pi_apply i).comp measurable_snd).sub
            ((measurable_pi_apply i).comp measurable_fst))
      have h₃ : Measurable (fun p : (Fin Sᶜ.card → Plane) ×
          (Fin Sᶜ.card → Plane) => heatKernel (t - u) (yC i - p.2 i)) :=
        (measurable_heatKernel (t - u)).comp
          (measurable_const.sub ((measurable_pi_apply i).comp measurable_snd))
      exact ((h₁.ennreal_ofReal).mul (h₂.ennreal_ofReal)).mul (h₃.ennreal_ofReal)
    have hTail (u : ℝ) (z z' : FusedConfiguration α) (hu : 0 < t - u) :
        diagramKernel θ w (t - u) (collisionEmbedding α z') y =
          diagramKernel θ wS (t - u)
              (collisionEmbedding γ (fusedCoordinateSplit S α h₁ h₂ z').1) yS *
            ∏ i : Fin Sᶜ.card,
              ENNReal.ofReal (heatKernel (t - u)
                (yC i - (fusedCoordinateSplit S α h₁ h₂ z').2 i)) := by
      have h := ih hu (collisionEmbedding α z') y
      have hactive :
          (fun i => collisionEmbedding α z' (S.orderEmbOfFin rfl i)) =
            collisionEmbedding γ (fusedCoordinateSplit S α h₁ h₂ z').1 := by
        funext i
        exact collisionEmbedding_subset_active S α h₁ h₂ z' i
      have hexternal :
          (fun i => collisionEmbedding α z' (Sᶜ.orderEmbOfFin rfl i)) =
            (fusedCoordinateSplit S α h₁ h₂ z').2 := by
        funext i
        exact collisionEmbedding_subset_external S α h₁ h₂ z' i
      rw [hactive] at h
      have hprod :
          (∏ i : Fin Sᶜ.card, ENNReal.ofReal
            (heatKernel (t - u)
              (y (Sᶜ.orderEmbOfFin rfl i) -
                collisionEmbedding α z' (Sᶜ.orderEmbOfFin rfl i)))) =
            ∏ i : Fin Sᶜ.card, ENNReal.ofReal
              (heatKernel (t - u) (yC i - (fusedCoordinateSplit S α h₁ h₂ z').2 i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        change ENNReal.ofReal (heatKernel (t - u)
            (y (Sᶜ.orderEmbOfFin rfl i) -
              collisionEmbedding α z' (Sᶜ.orderEmbOfFin rfl i))) =
          ENNReal.ofReal (heatKernel (t - u)
            (y (Sᶜ.orderEmbOfFin rfl i) -
              (fusedCoordinateSplit S α h₁ h₂ z').2 i))
        rw [collisionEmbedding_subset_external S α h₁ h₂ z' i]
      rw [hprod] at h
      simpa [yS] using h
    have hPoint (r u : ℝ) (z z' : FusedConfiguration α)
        (hr : 0 < r) (hv : 0 < u - r) (hq : 0 < t - u) :
        ENNReal.ofReal (incomingKernel α r z x) *
            ENNReal.ofReal (collisionKernel α θ (u - r) z z') *
              diagramKernel θ w (t - u) (collisionEmbedding α z') y =
          R r u (fusedCoordinateSplit S α h₁ h₂ z).1
              (fusedCoordinateSplit S α h₁ h₂ z').1 *
            H r u (fusedCoordinateSplit S α h₁ h₂ z).2
              (fusedCoordinateSplit S α h₁ h₂ z').2 := by
      rw [ofReal_incomingKernel_subset_factor S α h₁ h₂ hr z x,
        ofReal_collisionKernel_subset_factor S α h₁ h₂ hv z z',
        hTail u z z' hq]
      simp only [R, H, xS, yS, xC, yC]
      calc
        _ = (ENNReal.ofReal (incomingKernel γ r
              (fusedCoordinateSplit S α h₁ h₂ z).1
              (fun i => x (S.orderEmbOfFin rfl i))) *
            ENNReal.ofReal (collisionKernel γ θ (u - r)
              (fusedCoordinateSplit S α h₁ h₂ z).1
              (fusedCoordinateSplit S α h₁ h₂ z').1) *
            diagramKernel θ wS (t - u)
              (collisionEmbedding γ (fusedCoordinateSplit S α h₁ h₂ z').1)
              (fun i => y (S.orderEmbOfFin rfl i))) *
          ((∏ i : Fin Sᶜ.card, ENNReal.ofReal
              (heatKernel r ((fusedCoordinateSplit S α h₁ h₂ z).2 i -
                x (Sᶜ.orderEmbOfFin rfl i)))) *
            (∏ i : Fin Sᶜ.card, ENNReal.ofReal
              (heatKernel (u - r) ((fusedCoordinateSplit S α h₁ h₂ z').2 i -
                (fusedCoordinateSplit S α h₁ h₂ z).2 i))) *
            (∏ i : Fin Sᶜ.card, ENNReal.ofReal
              (heatKernel (t - u) (y (Sᶜ.orderEmbOfFin rfl i) -
                (fusedCoordinateSplit S α h₁ h₂ z').2 i)))) := by ac_rfl
        _ = _ := by
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    have hSpatial (r u : ℝ) (hr : 0 < r) (hv : 0 < u - r) (hq : 0 < t - u) :
        (∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
          ENNReal.ofReal (incomingKernel α r z x) *
            ENNReal.ofReal (collisionKernel α θ (u - r) z z') *
              diagramKernel θ w (t - u) (collisionEmbedding α z') y) =
        (∫⁻ z : FusedConfiguration γ, ∫⁻ z' : FusedConfiguration γ,
          R r u z z') * C := by
      have hExternal : (∫⁻ z : Fin Sᶜ.card → Plane,
          ∫⁻ z' : Fin Sᶜ.card → Plane, H r u z z') = C := by
        have htime : r + (u - r) + (t - u) = t := by ring
        simpa [H, C, xC, yC, htime] using
          lintegral_fin_heatKernel_chain_three hr hv hq xC yC
      calc
        _ = ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
            R r u (fusedCoordinateSplit S α h₁ h₂ z).1
                (fusedCoordinateSplit S α h₁ h₂ z').1 *
              H r u (fusedCoordinateSplit S α h₁ h₂ z).2
                (fusedCoordinateSplit S α h₁ h₂ z').2 := by
          apply lintegral_congr
          intro z
          apply lintegral_congr
          intro z'
          exact hPoint r u z z' hr hv hq
        _ = (∫⁻ z : FusedConfiguration γ, ∫⁻ z' : FusedConfiguration γ,
              R r u z z') *
            ∫⁻ z : Fin Sᶜ.card → Plane, ∫⁻ z' : Fin Sᶜ.card → Plane,
              H r u z z' :=
          lintegral_pair_product (fusedCoordinateSplit S α h₁ h₂)
            (measurePreserving_fusedCoordinateSplit S α h₁ h₂) (hR r u) (hH r u)
        _ = _ := by rw [hExternal]
    calc
      diagramKernel θ (α :: w) t x y =
          ∫⁻ r in Set.Ioo 0 t, ∫⁻ u in Set.Ioo r t,
            ∫⁻ z : FusedConfiguration α, ∫⁻ z' : FusedConfiguration α,
              ENNReal.ofReal (incomingKernel α r z x) *
                ENNReal.ofReal (collisionKernel α θ (u - r) z z') *
                  diagramKernel θ w (t - u) (collisionEmbedding α z') y := rfl
      _ = ∫⁻ r in Set.Ioo 0 t, ∫⁻ u in Set.Ioo r t,
            (∫⁻ z : FusedConfiguration γ, ∫⁻ z' : FusedConfiguration γ,
              R r u z z') * C := by
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
          exact hSpatial r u hr.1 (sub_pos.mpr hu.1) (sub_pos.mpr hu.2)
      _ = (∫⁻ r in Set.Ioo 0 t, ∫⁻ u in Set.Ioo r t,
            ∫⁻ z : FusedConfiguration γ, ∫⁻ z' : FusedConfiguration γ,
              R r u z z') * C := by
          calc
            _ = ∫⁻ r in Set.Ioo 0 t,
                  (∫⁻ u in Set.Ioo r t,
                    ∫⁻ z : FusedConfiguration γ, ∫⁻ z' : FusedConfiguration γ,
                      R r u z z') * C := by
                apply lintegral_congr
                intro r
                exact lintegral_mul_const' C _ hCtop
            _ = _ := lintegral_mul_const' C _ hCtop
      _ = diagramKernel θ (γ :: wS) t xS yS * C := rfl

/-- Convert a finite sum over a subtype into an indicator sum over its carrier. -/
private theorem fintype_sum_wordSubtype_eq_sum_ite {ι M : Type*} [Fintype ι]
    [AddCommMonoid M] (p : ι → Prop) [DecidablePred p] (f : {i // p i} → M) :
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
    _ = (∑ i : {i // p i}, g i) + ∑ i : {i // ¬ p i}, g i := by
      rw [hfalse, add_zero]
    _ = ∑ i, g i := Fintype.sum_subtype_add_sum_subtype p g
    _ = _ := rfl

/-- The supported length-`m` diagram sum is the reduced diagram sum times
the free heat kernel on the spectator coordinates. -/
theorem diagramWordSum_subset_factor {n m : ℕ} (S : Finset (Fin n)) (θ : ℝ)
    {t : ℝ} (ht : 0 < t) (x y : Configuration n) :
    (∑ w : CollisionWord n m,
      if wordSupport w.1 ⊆ S then diagramKernel θ (List.ofFn w.1) t x y else 0) =
      (∑ w : CollisionWord S.card m,
        diagramKernel θ (List.ofFn w.1) t
          (fun i => x (S.orderEmbOfFin rfl i))
          (fun i => y (S.orderEmbOfFin rfl i))) *
        ∏ i : Fin Sᶜ.card,
          ENNReal.ofReal (heatKernel t
            (y (Sᶜ.orderEmbOfFin rfl i) - x (Sᶜ.orderEmbOfFin rfl i))) := by
  classical
  let p : CollisionWord n m → Prop := fun w => wordSupport w.1 ⊆ S
  let f : {w : CollisionWord n m // p w} → ℝ≥0∞ :=
    fun w => diagramKernel θ (List.ofFn w.1.1) t x y
  calc
    (∑ w : CollisionWord n m,
        if wordSupport w.1 ⊆ S then diagramKernel θ (List.ofFn w.1) t x y else 0) =
      ∑ w : {w : CollisionWord n m // p w}, f w := by
        symm
        simpa [p, f] using fintype_sum_wordSubtype_eq_sum_ite p f
    _ = ∑ w : CollisionWord S.card m,
        diagramKernel θ (List.ofFn (collisionWordInto S w).1) t x y := by
          symm
          exact (collisionWordSubsetEquiv S).sum_comp f
    _ = (∑ w : CollisionWord S.card m,
          diagramKernel θ (List.ofFn w.1) t
            (fun i => x (S.orderEmbOfFin rfl i))
            (fun i => y (S.orderEmbOfFin rfl i))) *
        ∏ i : Fin Sᶜ.card,
          ENNReal.ofReal (heatKernel t
            (y (Sᶜ.orderEmbOfFin rfl i) - x (Sᶜ.orderEmbOfFin rfl i))) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro w hw
          let wFull := collisionWordInto S w
          have hRel : List.Forall₂
              (fun α γ => ∃ h₁ : α.1.1 ∈ S, ∃ h₂ : α.1.2 ∈ S,
                γ = collisionPairWithin S α h₁ h₂)
              (List.ofFn wFull.1) (List.ofFn w.1) := by
            apply List.forall₂_iff_get.mpr
            refine ⟨by simp, ?_⟩
            intro i hi₁ hi₂
            have hi : i < m := by simpa using hi₁
            let j : Fin m := ⟨i, hi⟩
            have hleft : (List.ofFn wFull.1).get ⟨i, hi₁⟩ = wFull.1 j := by
              simp only [List.get_ofFn]
              exact congrArg wFull.1 (Fin.ext rfl)
            have hright : (List.ofFn w.1).get ⟨i, hi₂⟩ = w.1 j := by
              simp only [List.get_ofFn]
              exact congrArg w.1 (Fin.ext rfl)
            rw [hleft, hright]
            have hp := (collisionPairSubsetEquiv S (w.1 j)).2
            exact ⟨hp.1, hp.2,
              by
                change w.1 j =
                  collisionPairWithin S (collisionPairInto S (w.1 j)) _ _
                exact (collisionPairWithin_collisionPairInto S (w.1 j)).symm⟩
          have hfactor := diagramKernel_subset_factor_of_forall₂ S θ
            (List.ofFn wFull.1) (List.ofFn w.1) hRel ht x y
          simpa [wFull] using hfactor

/-- The mixed moment block is the sum of all diagrams supported in its active
labels, including the free diagram, with the spectator heat kernel factored
out. -/
theorem momentKernel_subset_factor {n : ℕ} (S : Finset (Fin n)) (θ : ℝ)
    {t : ℝ} (ht : 0 < t) (x y : Configuration n) :
    momentKernel S.card θ t
        (fun i => x (S.orderEmbOfFin rfl i))
        (fun i => y (S.orderEmbOfFin rfl i)) *
      ∏ i : Fin Sᶜ.card,
        ENNReal.ofReal (heatKernel t
          (y (Sᶜ.orderEmbOfFin rfl i) - x (Sᶜ.orderEmbOfFin rfl i))) =
      ENNReal.ofReal (freeKernel n t x y) +
        ∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
          if wordSupport w.1 ⊆ S then
            diagramKernel θ (List.ofFn w.1) t x y else 0 := by
  classical
  let C : ℝ≥0∞ := ∏ i : Fin Sᶜ.card,
    ENNReal.ofReal (heatKernel t
      (y (Sᶜ.orderEmbOfFin rfl i) - x (Sᶜ.orderEmbOfFin rfl i)))
  have hfree : ENNReal.ofReal (freeKernel S.card t
      (fun i => x (S.orderEmbOfFin rfl i))
      (fun i => y (S.orderEmbOfFin rfl i))) * C =
        ENNReal.ofReal (freeKernel n t x y) := by
    simpa [C, diagramKernel] using
      (diagramKernel_nil_subset_factor S θ ht x y).symm
  have hseries :
      (∑' m : ℕ, ∑ w : CollisionWord n (m + 1),
        if wordSupport w.1 ⊆ S then
          diagramKernel θ (List.ofFn w.1) t x y else 0) =
        (∑' m : ℕ, ∑ w : CollisionWord S.card (m + 1),
          diagramKernel θ (List.ofFn w.1) t
            (fun i => x (S.orderEmbOfFin rfl i))
            (fun i => y (S.orderEmbOfFin rfl i))) * C := by
    calc
      _ = ∑' m : ℕ,
          (∑ w : CollisionWord S.card (m + 1),
            diagramKernel θ (List.ofFn w.1) t
              (fun i => x (S.orderEmbOfFin rfl i))
              (fun i => y (S.orderEmbOfFin rfl i))) * C := by
            apply tsum_congr
            intro m
            simpa [C] using diagramWordSum_subset_factor
              (S := S) (θ := θ) (ht := ht) (x := x) (y := y) (m := m + 1)
      _ = _ := ENNReal.tsum_mul_right
  calc
    _ = (ENNReal.ofReal (freeKernel S.card t
          (fun i => x (S.orderEmbOfFin rfl i))
          (fun i => y (S.orderEmbOfFin rfl i))) +
        ∑' m : ℕ, ∑ w : CollisionWord S.card (m + 1),
          diagramKernel θ (List.ofFn w.1) t
            (fun i => x (S.orderEmbOfFin rfl i))
            (fun i => y (S.orderEmbOfFin rfl i))) * C := by
          rfl
    _ = _ := by rw [add_mul, hfree, ← hseries]

end Critical2DKPZ.SHF.Tsai

end
