/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Data.Finset.Sort

/-! # Splitting finite coordinates by an increasing subset enumeration

The subset and its complement retain their increasing label order. The
canonical product-space equivalences show that this regrouping preserves
arbitrary sigma-finite coordinate measures, including planar volume.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Separate the coordinates in a finite subset and its complement, in increasing order. -/
def splitFinsetCoordinates {n : ℕ} (S : Finset (Fin n)) (X : Type*) [MeasurableSpace X] :
    (Fin n → X) ≃ᵐ (Fin S.card → X) × (Fin Sᶜ.card → X) := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => X) (fun i => i ∈ S)
  let eS := MeasurableEquiv.piCongrLeft (fun _ : S => X) (S.orderIsoOfFin rfl).toEquiv
  let eCindex : Fin Sᶜ.card ≃ {i : Fin n // i ∉ S} :=
    (Sᶜ.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight fun i => Finset.mem_compl)
  let eC := MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // i ∉ S} => X) eCindex
  exact e.trans (MeasurableEquiv.prodCongr eS.symm eC.symm)

/-- The first component is restriction along the increasing enumeration of the subset. -/
theorem splitFinsetCoordinates_fst {n : ℕ} (S : Finset (Fin n))
    {X : Type*} [MeasurableSpace X] (x : Fin n → X) :
    (splitFinsetCoordinates S X x).1 = fun i => x (S.orderEmbOfFin rfl i) := rfl

/-- The second component uses the same increasing enumeration for the complement. -/
theorem splitFinsetCoordinates_snd {n : ℕ} (S : Finset (Fin n))
    {X : Type*} [MeasurableSpace X] (x : Fin n → X) :
    (splitFinsetCoordinates S X x).2 = fun i => x (Sᶜ.orderEmbOfFin rfl i) := rfl

/-- Subset regrouping preserves the product of arbitrary sigma-finite coordinate measures. -/
theorem measurePreserving_splitFinsetCoordinates {n : ℕ} (S : Finset (Fin n))
    {X : Type*} [MeasurableSpace X] (μ : Fin n → Measure X) [∀ i, SigmaFinite (μ i)] :
    MeasurePreserving (splitFinsetCoordinates S X) (Measure.pi μ)
      ((Measure.pi (fun i => μ (S.orderEmbOfFin rfl i))).prod
        (Measure.pi (fun i => μ (Sᶜ.orderEmbOfFin rfl i)))) := by
  classical
  let eS := MeasurableEquiv.piCongrLeft (fun _ : S => X) (S.orderIsoOfFin rfl).toEquiv
  let eCindex : Fin Sᶜ.card ≃ {i : Fin n // i ∉ S} :=
    (Sᶜ.orderIsoOfFin rfl).toEquiv.trans (Equiv.subtypeEquivRight fun i => Finset.mem_compl)
  let eC := MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // i ∉ S} => X) eCindex
  have hS := measurePreserving_piCongrLeft (fun i : S => μ i) (S.orderIsoOfFin rfl).toEquiv
  have hC := measurePreserving_piCongrLeft (fun i : {i : Fin n // i ∉ S} => μ i) eCindex
  have hsplit := measurePreserving_piEquivPiSubtypeProd μ (fun i => i ∈ S)
  have hF : Subtype.fintype (fun i : Fin n => i ∈ S) = Finset.Subtype.fintype S :=
    Subsingleton.elim _ _
  rw [hF] at hsplit
  exact ((hS.symm eS).prod (hC.symm eC)).comp hsplit

end Critical2DKPZ.SHF.Tsai

end
