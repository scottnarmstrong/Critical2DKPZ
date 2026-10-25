/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MomentOperatorKernelAction
public import Critical2DKPZ.SHF.Tsai.CenteredKernel
import Critical2DKPZ.SHF.Tsai.MixedBlockFormBounds

/-! # Integral representatives of moment operators

For at most four particles and positive times, the moment operator on `L²` agrees almost
everywhere with integration against its kernel.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

private theorem measurable_fixed_momentKernel (n : ℕ) (θ t : ℝ) :
    Measurable (Function.uncurry (momentKernel n θ t)) :=
  Measurable.comp
    (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
      momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
    (f := fun q : Configuration n × Configuration n => ((θ, t), q))
    (measurable_momentKernel n) (measurable_const.prodMk measurable_id)


/-- For at most four particles and positive times, the moment operator applied to an `L²` function equals its kernel integral almost everywhere. -/
theorem coe_momentOperator_toLp_eq_kernelAction {n : ℕ} (hn : n ≤ 4) (θ : ℝ)
    {t : ℝ} (ht : 0 < t) {F : Configuration n → ℝ} (hF : MemLp F 2) :
    ⇑(momentOperator hn θ ht (hF.toLp F)) =ᵐ[volume]
      fun x => ∫ y, (momentKernel n θ t x y).toReal * F y := by
  obtain ⟨C, rate, _hC, hQ⟩ := exists_formBound_momentKernel n θ
  exact coe_momentOperator_toLp hn θ ht (measurable_fixed_momentKernel n θ t)
    ENNReal.ofReal_ne_top (hQ θ le_rfl t ht) hF



end Critical2DKPZ.SHF.Tsai

end
