/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BrownianProjections
import Mathlib.Tactic

/-! # Adding the zero coordinate to Brownian finite-dimensional laws -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- Pad a vector indexed by the positive members of `I` with zero at time zero. -/
def padZero (I : Finset ℝ≥0) (x : (I.erase 0) → ℝ) : I → ℝ := fun i =>
  if hi : i.val = 0 then 0 else x ⟨i.val, Finset.mem_erase.mpr ⟨hi, i.property⟩⟩

/-- Padding is a continuous map of finite-dimensional real spaces. -/
theorem continuous_padZero (I : Finset ℝ≥0) : Continuous (padZero I) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : i.val = 0
  · simpa only [padZero, dite_eq_left hi] using (continuous_const : Continuous (fun _ : (I.erase 0) → ℝ => (0 : ℝ)))
  · simpa only [padZero, dite_eq_right hi] using
      (continuous_apply (⟨i.val, Finset.mem_erase.mpr ⟨hi, i.property⟩⟩ : I.erase 0))

/-- The Brownian coordinate at time zero vanishes almost surely. -/
theorem projectiveFamily_zero_ae (I : Finset ℝ≥0) (h0 : 0 ∈ I) :
    ∀ᵐ x ∂BrownianReal.projectiveFamily I, x (⟨0, h0⟩ : I) = 0 := by
  have h : MeasurePreserving (fun x : I → ℝ => x (⟨0, h0⟩ : I))
      (BrownianReal.projectiveFamily I) (gaussianReal 0 0) :=
    BrownianReal.measurePreserving_eval_projectiveFamily (⟨0, h0⟩ : I)
  apply ae_of_ae_map (μ := BrownianReal.projectiveFamily I) (p := fun y : ℝ => y = 0)
    h.measurable.aemeasurable
  rw [h.map_eq, gaussianReal_zero_var]
  simp

/-- Restriction followed by zero padding is the identity almost surely for a
Brownian projective vector. -/
theorem padZero_restrict_ae (I : Finset ℝ≥0) :
    (padZero I ∘ Finset.restrict₂ (π := fun _ : ℝ≥0 => ℝ) (Finset.erase_subset 0 I)) =ᵐ[
      BrownianReal.projectiveFamily I] id := by
  classical
  have hz : ∀ᵐ x ∂BrownianReal.projectiveFamily I, ∀ i : I, i.val = 0 → x i = 0 := by
    by_cases h0 : 0 ∈ I
    · filter_upwards [projectiveFamily_zero_ae I h0] with x hx
      intro i hi
      have heq : i = (⟨0, h0⟩ : I) := Subtype.ext hi
      simpa only [heq] using hx
    · filter_upwards [] with x
      intro i hi
      exact False.elim (h0 (hi ▸ i.property))
  filter_upwards [hz] with x hx
  funext i
  dsimp only [Function.comp_def, padZero, id_eq]
  split_ifs with hi
  · exact (hx i hi).symm
  · rfl

/-- Zero padding sends the Brownian law on the erased index set to the Brownian
law on the full index set. -/
theorem map_padZero_projectiveFamily (I : Finset ℝ≥0) :
    (BrownianReal.projectiveFamily (I.erase 0)).map (padZero I) = BrownianReal.projectiveFamily I := by
  have hres := BrownianReal.measurePreserving_restrict_projectiveFamily (Finset.erase_subset 0 I)
  rw [← hres.map_eq, Measure.map_map (continuous_padZero I).measurable hres.measurable]
  rw [Measure.map_congr (padZero_restrict_ae I), Measure.map_id]

end Critical2DKPZ.Extensions.ScaleLimit
