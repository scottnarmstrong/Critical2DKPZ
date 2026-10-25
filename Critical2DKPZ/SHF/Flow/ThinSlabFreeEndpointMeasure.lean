/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.ThinSlabSeparatedEndpointIntegral

/-! # The continuum free-slab endpoint measure -/

@[expose] public noncomputable section

open MeasureTheory
open Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Tsai
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- Retain the outer endpoints of the two continuum blocks weighted by their free slab
connector. -/
def slabSeparatedFreeEndpointMeasure (θ a v b : ℝ) :
    Measure (Configuration 2 × Configuration 2) :=
  ((slabSeparatedMomentPiMeasure θ a b).withDensity
    (fun p => ENNReal.ofReal (freeKernel 2 v (p 0).2 (p 1).1))).map
      (fun p => ((p 0).1, (p 1).2))

private theorem measurable_slabFreeEndpointKernel (θ a v b : ℝ) :
    Measurable (Function.uncurry (slabTwoParticleFreeMiddleComp θ a v b)) := by
  have hKa := measurable_slabMomentKernelTwo θ a
  have hKb := measurable_slabMomentKernelTwo θ b
  have hC : Measurable (Function.uncurry
      (fun x y : Configuration 2 => ENNReal.ofReal (freeKernel 2 v x y))) := by
    have hp : Measurable (fun p : Configuration 2 × Configuration 2 => (v, p)) :=
      measurable_const.prodMk measurable_id
    exact ((measurable_freeKernel 2).comp hp).ennreal_ofReal
  exact measurable_spatialKernelComp volume hKa (measurable_spatialKernelComp volume hC hKb)

/-- The separated free-slab endpoint measure has the explicit three-kernel composition density.
The identity holds for every measurable endpoint test, including signed compact replica tests
once integrability is supplied. -/
theorem slabSeparatedFreeEndpointMeasure_eq (θ : ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (v : ℝ) :
    slabSeparatedFreeEndpointMeasure θ a v b =
      (volume.prod volume).withDensity
        (Function.uncurry (slabTwoParticleFreeMiddleComp θ a v b)) := by
  have hEnd : Measurable (fun p : Fin 2 → Configuration 2 × Configuration 2 =>
      ((p 0).1, (p 1).2)) := by fun_prop
  have hWeight : Measurable (fun p : Fin 2 → Configuration 2 × Configuration 2 =>
      ENNReal.ofReal (freeKernel 2 v (p 0).2 (p 1).1)) := by
    have hp : Measurable (fun p : Fin 2 → Configuration 2 × Configuration 2 =>
        (v, ((p 0).2, (p 1).1))) := by fun_prop
    exact ((measurable_freeKernel 2).comp hp).ennreal_ofReal
  have hKernel := measurable_slabFreeEndpointKernel θ a v b
  apply Measure.ext_of_lintegral
  intro H hH
  rw [slabSeparatedFreeEndpointMeasure, lintegral_map hH hEnd]
  have hwd := lintegral_withDensity_eq_lintegral_mul
    (slabSeparatedMomentPiMeasure θ a b) hWeight (hH.comp hEnd)
  simp only [Function.comp_def, Pi.mul_apply] at hwd
  rw [hwd]
  rw [lintegral_slabSeparatedMomentPiMeasure_freeEndpoint θ ha hb v
    (H := fun x y => H (x, y)) hH]
  rw [lintegral_withDensity_eq_lintegral_mul _ hKernel hH]
  exact (lintegral_prod _ (hKernel.mul hH).aemeasurable).symm

/-- The free-slab endpoint measure is dominated by the full-interval moment measure, since the
semigroup decomposition adds a nonnegative collision correction. -/
theorem slabSeparatedFreeEndpointMeasure_le_full (θ : ℝ) {a v b : ℝ}
    (ha : 0 < a) (hv : 0 < v) (hb : 0 < b) :
    slabSeparatedFreeEndpointMeasure θ a v b ≤
      slabMomentKernelEndpointMeasure θ (a + v + b) := by
  rw [slabSeparatedFreeEndpointMeasure_eq θ ha hb v]
  apply withDensity_mono
  filter_upwards [] with p
  change slabTwoParticleFreeMiddleComp θ a v b p.1 p.2 ≤
    momentKernel 2 θ (a + v + b) p.1 p.2
  rw [slabMomentKernelTwo_threeTime_split θ ha hv hb]
  exact le_add_right le_rfl

end Critical2DKPZ.SHF.Flow

end
