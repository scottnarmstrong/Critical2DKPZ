/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ChainPathIntegrals
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # The actual weighted path measure of a finite endpoint chain

Positive path integration identifies the chain measure with the endpoint
image of the connector-weighted product path measure. This representation
also transports integrability and signed pairings without a new convergence
or finiteness assumption on the chain.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The chain is the endpoint image of its literal connector-weighted finite product path measure. -/
theorem chainProduct_eq_map_weightedPath (μ : ℕ → Measure (Plane × Plane))
    [∀ k, SigmaFinite (μ k)] {w : ℕ → Plane → ℝ} (hw : ∀ k, Measurable (w k)) (K : ℕ) :
    chainProduct μ w K =
      ((Measure.pi (fun k : Fin (K + 1) => μ k)).withDensity
        (chainPathTest K w (fun _ => 1))).map
          (fun p => ((p 0).1, (p (Fin.last K)).2)) := by
  have he : Measurable (fun p : Fin (K + 1) → Plane × Plane => ((p 0).1, (p (Fin.last K)).2)) :=
    (measurable_pi_apply 0).fst.prodMk (measurable_pi_apply (Fin.last K)).snd
  have hW := measurable_chainPathTest K hw (measurable_const : Measurable (fun _ : Plane × Plane => (1 : ℝ≥0∞)))
  apply Measure.ext_of_lintegral
  intro F hF
  have hFe : Measurable (fun p : Fin (K + 1) → Plane × Plane =>
      F ((p 0).1, (p (Fin.last K)).2)) := hF.comp he
  rw [lintegral_chainProduct_eq_lintegral_path μ hw K hF, lintegral_map hF he,
    lintegral_withDensity_eq_lintegral_mul _ hW hFe]
  apply lintegral_congr
  intro p
  simp only [Pi.mul_apply, chainPathTest, mul_one]

/-- The positive connector path weight is finite everywhere. -/
theorem chainPathWeight_ne_top (K : ℕ) (w : ℕ → Plane → ℝ)
    (p : Fin (K + 1) → Plane × Plane) : chainPathTest K w (fun _ => 1) p ≠ ⊤ := by
  simp only [chainPathTest, mul_one]
  exact ENNReal.prod_ne_top (fun _ _ => ENNReal.ofReal_ne_top)

/-- An integrable chain test is integrable on the weighted path space and has its signed path integral. -/
theorem integral_chainProduct_eq_integral_weightedPath (μ : ℕ → Measure (Plane × Plane))
    [∀ k, SigmaFinite (μ k)] {w : ℕ → Plane → ℝ} (hw : ∀ k, Measurable (w k)) (K : ℕ)
    (F : Plane × Plane → ℝ) (hF : Integrable F (chainProduct μ w K)) :
    Integrable (fun p : Fin (K + 1) → Plane × Plane =>
      (chainPathTest K w (fun _ => 1) p).toReal * F ((p 0).1, (p (Fin.last K)).2))
        (Measure.pi (fun k : Fin (K + 1) => μ k)) ∧
    (∫ q, F q ∂chainProduct μ w K) = ∫ p : Fin (K + 1) → Plane × Plane,
      (chainPathTest K w (fun _ => 1) p).toReal * F ((p 0).1, (p (Fin.last K)).2)
        ∂Measure.pi (fun k : Fin (K + 1) => μ k) := by
  have he : Measurable (fun p : Fin (K + 1) → Plane × Plane => ((p 0).1, (p (Fin.last K)).2)) :=
    (measurable_pi_apply 0).fst.prodMk (measurable_pi_apply (Fin.last K)).snd
  have hW := measurable_chainPathTest K hw (measurable_const : Measurable (fun _ : Plane × Plane => (1 : ℝ≥0∞)))
  rw [chainProduct_eq_map_weightedPath μ hw K] at hF ⊢
  have hpath := (integrable_map_measure hF.aestronglyMeasurable he.aemeasurable).1 hF
  have hfinite : ∀ᵐ p ∂Measure.pi (fun k : Fin (K + 1) => μ k),
      chainPathTest K w (fun _ => 1) p < ⊤ :=
    Filter.Eventually.of_forall (fun p => lt_top_iff_ne_top.mpr (chainPathWeight_ne_top K w p))
  have hweighted := (integrable_withDensity_iff_integrable_smul' hW hfinite).1 hpath
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, smul_eq_mul] using hweighted
  · rw [integral_map he.aemeasurable hF.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul hW hfinite]
    rfl

end Critical2DKPZ.SHF.Tsai

end
