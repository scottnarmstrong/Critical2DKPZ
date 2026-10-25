/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.KernelMeasureLocalFiniteness
public import Critical2DKPZ.SHF.DeltaBose.MomentKernelFormBounds

/-! # Local finiteness of the full moment-kernel endpoint measure

The finite positive-time form bound controls bounded endpoint rectangles.
The canonical kernel-measure criterion gives local finiteness, hence the
sigma-finiteness needed for conditional Fubini arguments.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- The literal full moment-kernel endpoint measure is locally finite at every positive time. -/
theorem locallyFinite_momentKernelMeasure (n : ℕ) (θ : ℝ) {τ : ℝ} (hτ : 0 < τ) :
    IsLocallyFiniteMeasure (volume.withDensity (Function.uncurry (momentKernel n θ τ))) := by
  have hm : Measurable (Function.uncurry (momentKernel n θ τ)) :=
    Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n => ((θ, τ), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)
  obtain ⟨c, rate, _, hbound⟩ := exists_formBound_momentKernel n θ
  exact locallyFinite_kernelMeasure hm ENNReal.ofReal_ne_top (hbound θ le_rfl τ hτ)

end Critical2DKPZ.SHF.Tsai

end
