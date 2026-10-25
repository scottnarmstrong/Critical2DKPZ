/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConfigurationKernelForms
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Integrable real tests against configuration kernel measures

A finite positive form bound gives absolute integrability of the actual
weighted form. The density is finite almost everywhere, so the endpoint
product is integrable against its literal kernel measure, including for
arbitrary `L²` representatives.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Endpoint products are integrable against a finite form-bounded kernel measure, with the exact real form. -/
theorem integrable_kernelMeasure_mul_and_integral {n : ℕ}
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    (F G : Configuration n → ℝ) (hF : MemLp F 2) (hG : MemLp G 2) :
    Integrable (fun q => F q.1 * G q.2) (volume.withDensity (Function.uncurry K)) ∧
      (∫ q, F q.1 * G q.2 ∂volume.withDensity (Function.uncurry K)) =
        ∫ x, ∫ y, F x * (K x y).toReal * G y := by
  have hI := (configurationKernel_real_form_bound hK hc hKF F G hF hG).1
  have hfin : ∀ᵐ q : Configuration n × Configuration n ∂volume, K q.1 q.2 < ⊤ :=
    (configurationKernel_ne_top_of_formBound hK hc hKF).mono (fun _ h => h.lt_top)
  have hweighted : Integrable (fun q : Configuration n × Configuration n =>
      (K q.1 q.2).toReal • (F q.1 * G q.2)) volume := by
    apply hI.congr
    exact Filter.Eventually.of_forall (fun q => by simp only [smul_eq_mul]; ring)
  refine ⟨(integrable_withDensity_iff_integrable_smul' hK hfin).2 hweighted, ?_⟩
  rw [integral_withDensity_eq_integral_toReal_smul hK hfin]
  calc
    _ = ∫ q : Configuration n × Configuration n, F q.1 * (K q.1 q.2).toReal * G q.2
        ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun q => by simp only [smul_eq_mul, Function.uncurry]; ring)
    _ = _ := integral_prod _ hI

end Critical2DKPZ.SHF.Tsai

end
