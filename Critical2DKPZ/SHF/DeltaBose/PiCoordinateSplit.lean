/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! # Isolating one free planar coordinate in product volume -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Reconstruct a configuration from all the other coordinates and the selected coordinate. -/
noncomputable def insertCoordinate {ι : Type*} [DecidableEq ι] (j : ι)
    (v : {i : ι // i ≠ j} → Plane) (q : Plane) (i : ι) : Plane :=
  if h : i = j then q else v ⟨i, h⟩

/-- Inserting a coordinate gives the prescribed value at that coordinate. -/
@[simp] theorem insertCoordinate_same {ι : Type*} [DecidableEq ι] (j : ι)
    (v : {i : ι // i ≠ j} → Plane) (q : Plane) : insertCoordinate j v q j = q := by
  simp only [insertCoordinate, dite_true]

/-- Inserting a coordinate leaves every other coordinate unchanged. -/
@[simp] theorem insertCoordinate_other {ι : Type*} [DecidableEq ι] (j : ι)
    (v : {i : ι // i ≠ j} → Plane) (q : Plane) (i : {i : ι // i ≠ j}) :
    insertCoordinate j v q i.1 = v i := by
  simp only [insertCoordinate, i.2, dite_false]

/-- The equality-coordinate subspace has a canonical one-point index type. -/
@[instance_reducible] noncomputable def coordinateEqUnique {ι : Type*} (j : ι) :
    Unique {i : ι // i = j} :=
  ⟨⟨j, rfl⟩, fun i => Subtype.ext i.2⟩

/-- Identify the equality-coordinate product with its one planar coordinate. -/
noncomputable def coordinateEqEquiv {ι : Type*} [DecidableEq ι] (j : ι) :
    ({i : ι // i = j} → Plane) ≃ᵐ Plane where
  toFun f := f ⟨j, rfl⟩
  invFun q _ := q
  left_inv f := by
    funext i
    have hi : i = ⟨j, rfl⟩ := Subtype.ext i.2
    rw [hi]
  right_inv _ := rfl
  measurable_toFun := by
    exact measurable_pi_apply (⟨j, rfl⟩ : {i : ι // i = j})
  measurable_invFun := by
    apply Measurable.of_eval
    intro i
    change Measurable (fun q : Plane => q)
    exact measurable_id

/-- Separate a specified coordinate from a finite planar product. -/
noncomputable def splitCoordinate {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι) :
    (ι → Plane) ≃ᵐ ({i : ι // i ≠ j} → Plane) × Plane := by
  let e₁ := MeasurableEquiv.piEquivPiSubtypeProd
    (fun _ : ι => Plane) (fun i => i = j)
  exact e₁.trans ((MeasurableEquiv.prodCongr (coordinateEqEquiv j)
    (MeasurableEquiv.refl _)).trans MeasurableEquiv.prodComm)

/-- Splitting a configuration separates the distinguished coordinate from the remaining coordinates. -/
@[simp] theorem splitCoordinate_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι)
    (x : ι → Plane) : splitCoordinate j x = (fun i => x i.1, x j) := by
  change (fun i : {i : ι // i ≠ j} => x i.1,
    coordinateEqEquiv j (fun i : {i : ι // i = j} => x i.1)) =
    (fun i : {i : ι // i ≠ j} => x i.1, x j)
  apply Prod.ext
  · rfl
  · rfl

/-- The inverse coordinate split reinserts the distinguished coordinate. -/
theorem splitCoordinate_symm_apply {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι)
    (v : {i : ι // i ≠ j} → Plane) (q : Plane) :
    (splitCoordinate j).symm (v, q) = insertCoordinate j v q := by
  apply (splitCoordinate j).injective
  rw [MeasurableEquiv.apply_symm_apply, splitCoordinate_apply]
  apply Prod.ext
  · funext i
    simp [insertCoordinate, i.2]
  · simp [insertCoordinate]

/-- Splitting one coordinate preserves the ordinary product volumes exactly. -/
theorem measurePreserving_splitCoordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (j : ι) :
    MeasurePreserving (splitCoordinate j) := by
  let hUnique := coordinateEqUnique j
  have h1' := measurePreserving_piEquivPiSubtypeProd
      (fun _ : ι => (volume : Measure Plane)) (fun i => i = j)
  have hF₁ : Subtype.fintype (fun i : ι => i = j) =
      Fintype.subtypeEq j := Subsingleton.elim _ _
  have hF₂ : Subtype.fintype (fun i : ι => i ≠ j) =
      (inferInstance : Fintype {i : ι // i ≠ j}) := Subsingleton.elim _ _
  rw [hF₁, hF₂] at h1'
  have h1 : MeasurePreserving
      (MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : ι => Plane) (fun i => i = j))
      (Measure.pi fun _ : ι => (volume : Measure Plane))
      ((Measure.pi fun _ : {i : ι // i = j} => (volume : Measure Plane)).prod
        (Measure.pi fun _ : {i : ι // i ≠ j} => (volume : Measure Plane))) := by
    exact h1'
  have h2 : MeasurePreserving (coordinateEqEquiv j)
      (Measure.pi fun _ : {i : ι // i = j} => (volume : Measure Plane))
      (volume : Measure Plane) := by
    have hp := @measurePreserving_piUnique {i : ι // i = j}
        (inferInstance : Fintype {i : ι // i = j})
        (fun _ : {i : ι // i = j} => Plane) hUnique _
        (fun _ => (volume : Measure Plane))
    apply hp.congr (coordinateEqEquiv j).measurable
    filter_upwards with f
    change f ⟨j, rfl⟩ = f default
    exact congrArg f (hUnique.uniq _)
  have h3 := (h2.prod (MeasurePreserving.id
    (Measure.pi fun _ : {i : ι // i ≠ j} => (volume : Measure Plane)))).comp h1
  have h4 := (Measure.measurePreserving_swap (μ := (volume : Measure Plane))
    (ν := Measure.pi fun _ : {i : ι // i ≠ j} => (volume : Measure Plane))).comp h3
  have hmap : splitCoordinate j = (Prod.swap ∘ Prod.map (coordinateEqEquiv j) id ∘
      MeasurableEquiv.piEquivPiSubtypeProd
        (fun _ : ι => Plane) (fun i => i = j)) := by
    funext x
    rw [splitCoordinate_apply]
    simp [MeasurableEquiv.piEquivPiSubtypeProd, coordinateEqEquiv]
  have h5 : MeasurePreserving (splitCoordinate j)
      (Measure.pi fun _ : ι => (volume : Measure Plane))
      ((Measure.pi fun _ : {i : ι // i ≠ j} => (volume : Measure Plane)).prod
        (volume : Measure Plane)) := by
    apply h4.congr (splitCoordinate j).measurable
    filter_upwards with x
    exact congrFun hmap x
  simpa only [volume_pi, Measure.volume_eq_prod] using h5

/-- Fubini with the selected coordinate integrated first. -/
theorem lintegral_splitCoordinate {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι)
    {F : (ι → Plane) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ x : ι → Plane, F x) =
      ∫⁻ v : {i : ι // i ≠ j} → Plane, ∫⁻ q : Plane, F (insertCoordinate j v q) := by
  have hm := (measurePreserving_splitCoordinate j).symm
  have he := hm.lintegral_comp hF
  calc (∫⁻ x : ι → Plane, F x)
      = ∫⁻ p : ({i : ι // i ≠ j} → Plane) × Plane,
          F ((splitCoordinate j).symm p) := he.symm
    _ = ∫⁻ v : {i : ι // i ≠ j} → Plane, ∫⁻ q : Plane,
          F ((splitCoordinate j).symm (v, q)) :=
        lintegral_prod _ (hF.comp (splitCoordinate j).symm.measurable).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro v
      apply lintegral_congr
      intro q
      rw [splitCoordinate_symm_apply]

/-- Product decomposition compatible with the selected-coordinate disintegration. -/
theorem prod_splitCoordinate {ι M : Type*} [Fintype ι] [DecidableEq ι] [CommMonoid M]
    (j : ι) (f : ι → M) : (∏ i, f i) = f j * ∏ i : {i : ι // i ≠ j}, f i.1 := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ j)]
  congr 1
  exact Finset.prod_subtype _ (by simp) f

end Critical2DKPZ.DeltaBose
