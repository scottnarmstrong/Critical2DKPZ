/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainKernels
public import Critical2DKPZ.SHF.Tsai.PiFormBounds
public import Critical2DKPZ.SHF.Tsai.FinsetCoordinateSplit
public import Critical2DKPZ.SHF.DeltaBose.MomentKernelFormBounds

/-! # Form bounds for mixed heat and delta-Bose blocks

A kernel with delta-Bose factors on selected labels and heat factors on their complement has
a finite form bound obtained by multiplying the bounds on the two groups.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Heat factors on a subset are the free kernel of its increasing enumeration. -/
theorem prod_heatKernel_finset_eq {n : ℕ} (S : Finset (Fin n)) {τ : ℝ} (hτ : 0 ≤ τ)
    (x y : Configuration n) :
    (∏ i ∈ S, ENNReal.ofReal (heatKernel τ (y i - x i))) =
      ENNReal.ofReal (freeKernel S.card τ (fun i => x (S.orderEmbOfFin rfl i))
        (fun i => y (S.orderEmbOfFin rfl i))) := by
  rw [freeKernel, ENNReal.ofReal_prod_of_nonneg (fun i _ => heatKernel_nonneg hτ _)]
  conv_lhs => rw [← S.map_orderEmbOfFin_univ rfl, Finset.prod_map]
  rfl

/-- Splitting the particle labels multiplies the two supplied moment-kernel form constants. -/
theorem formBound_mixedBlockKernel {n : ℕ} (S : Finset (Fin n)) (θ : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    {c d : ℝ≥0∞} (hS : FormBound volume volume (momentKernel S.card θ τ) c)
    (hC : FormBound volume volume (momentKernel Sᶜ.card θ τ) d) :
    FormBound volume volume (mixedBlockKernel n θ τ S) (c * d) := by
  have hKm (m : ℕ) : Measurable (Function.uncurry (momentKernel m θ τ)) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration m × Configuration m =>
        momentKernel m p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration m × Configuration m => ((θ, τ), q))
      (measurable_momentKernel m) (measurable_const.prodMk measurable_id)
  have hprod := formBound_prod volume volume volume volume
    (hKm S.card) (hKm Sᶜ.card) hS hC
  let e := splitFinsetCoordinates S Plane
  have he : MeasurePreserving e (volume : Measure (Configuration n))
      ((volume : Measure (Configuration S.card)).prod (volume : Measure (Configuration Sᶜ.card))) :=
    measurePreserving_splitFinsetCoordinates S (fun _ => volume)
  have hpull := formBound_pullback e e he he hprod
  apply hpull.mono _ le_rfl
  intro x y
  change mixedBlockKernel n θ τ S x y ≤
    momentKernel S.card θ τ (e x).1 (e y).1 * momentKernel Sᶜ.card θ τ (e x).2 (e y).2
  rw [mixedBlockKernel, prod_heatKernel_finset_eq _ hτ]
  exact mul_le_mul' le_rfl (freeKernel_le_momentKernel Sᶜ.card θ τ _ _)

/-- Every fixed positive-time mixed block has a finite positive form bound. -/
theorem exists_formBound_mixedBlockKernel (n : ℕ) (S : Finset (Fin n)) (θ : ℝ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ FormBound volume volume (mixedBlockKernel n θ τ S) c := by
  obtain ⟨C, rate, _, hC⟩ := exists_formBound_momentKernel S.card θ
  obtain ⟨C', rate', _, hC'⟩ := exists_formBound_momentKernel Sᶜ.card θ
  exact ⟨_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
    formBound_mixedBlockKernel S θ hτ.le (hC θ le_rfl τ hτ) (hC' θ le_rfl τ hτ)⟩

end Critical2DKPZ.SHF.Tsai

end
