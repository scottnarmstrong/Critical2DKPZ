/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic

/-! # A measure-preserving finite-coordinate model for fused collision spaces -/

@[expose] public noncomputable section

open MeasureTheory Measure

namespace Critical2DKPZ.SHF.Moments

/-- Store one center and its spectator coordinates as a function on an
option type. The center occupies `none`. -/
def fusedOptionMeasurableEquiv (ι X : Type*) [MeasurableSpace X] :
    (X × (ι → X)) ≃ᵐ (Option ι → X) where
  toFun p j := j.elim p.1 p.2
  invFun f := (f none, fun i => f (some i))
  left_inv p := by cases p; rfl
  right_inv f := by funext j; cases j <;> rfl
  measurable_toFun := Measurable.of_eval fun j => by
    cases j with
    | none => exact measurable_fst
    | some i => exact (measurable_pi_apply i).comp measurable_snd
  measurable_invFun := (measurable_pi_apply none).prodMk
    (Measurable.of_eval fun i => measurable_pi_apply (some i))



/-- The option-coordinate model uses the product volume, with no
Jacobian factor. -/
theorem measurePreserving_fusedOptionMeasurableEquiv (ι X : Type*) [Fintype ι]
    [MeasureSpace X] [SigmaFinite (volume : Measure X)] :
    MeasurePreserving (fusedOptionMeasurableEquiv ι X) := by
  let e := MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => X)
  have he : MeasurePreserving e.symm
      ((volume : Measure (ι → X)).prod (volume : Measure X)) volume := by
    refine ⟨e.symm.measurable, ?_⟩
    exact Measure.pi_map_piOptionEquivProd (fun _ : Option ι => (volume : Measure X))
  have hpoint : (fusedOptionMeasurableEquiv ι X : (X × (ι → X)) → (Option ι → X)) =
      e.symm ∘ Prod.swap := by
    funext p
    funext j
    cases j <;> rfl
  rw [hpoint]
  exact he.comp measurePreserving_swap

end Critical2DKPZ.SHF.Moments
