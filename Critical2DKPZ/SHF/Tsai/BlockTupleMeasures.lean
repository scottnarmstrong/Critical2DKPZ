/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ProductMeasureKernels
public import Critical2DKPZ.SHF.Tsai.BlockPositiveExtension
import Critical2DKPZ.Collision.RenewalStringCells
import Mathlib.MeasureTheory.Integral.Pi

/-! # Configuration endpoint tuples from one measure block

A finite product of endpoint measures can be regrouped into initial and terminal
configuration coordinates. Products of one-particle tests then factor under the tuple measure.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- A finite family of endpoint measures, grouping initial and terminal coordinates. -/
def endpointTupleMeasure {n : ℕ} (μ : Fin n → Measure (Plane × Plane)) :
    Measure (Configuration n × Configuration n) :=
  (Measure.pi μ).map (MeasurableEquiv.arrowProdEquivProdArrow Plane Plane (Fin n))

/-- The `n`-fold block measure, grouping all initial and all terminal coordinates. -/
def blockTupleMeasure (n : ℕ) (μ : Measure (Plane × Plane)) :
    Measure (Configuration n × Configuration n) := endpointTupleMeasure (fun _ : Fin n => μ)

/-- Endpoint tuples depend measurably on an everywhere locally finite family of measures. -/
theorem measurable_endpointTupleMeasure {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (B : Fin n → Ω → Measure (Plane × Plane)) (hB : ∀ i, Measurable (B i))
    (hlf : ∀ i ω, IsLocallyFiniteMeasure (B i ω)) :
    Measurable (fun ω => endpointTupleMeasure (fun i => B i ω)) := by
  exact (Measure.measurable_map _
    (MeasurableEquiv.arrowProdEquivProdArrow Plane Plane (Fin n)).measurable).comp
    (measurable_piMeasure_of_locallyFinite n B hB hlf)

/-- The endpoint tuple measure depends measurably on an everywhere locally finite block. -/
theorem measurable_blockTupleMeasure {Ω : Type*} [MeasurableSpace Ω] (n : ℕ)
    (B : Ω → Measure (Plane × Plane)) (hB : Measurable B)
    (hlf : ∀ ω, IsLocallyFiniteMeasure (B ω)) :
    Measurable (fun ω => blockTupleMeasure n (B ω)) :=
  measurable_endpointTupleMeasure (fun _ => B) (fun _ => hB) (fun _ => hlf)

/-- Arbitrary positive one-particle tests factor under the actual endpoint tuple measure. -/
theorem lintegral_endpointTupleMeasure_prod {n : ℕ} (μ : Fin n → Measure (Plane × Plane))
    [∀ i, SigmaFinite (μ i)] (F : Fin n → Plane × Plane → ℝ≥0∞)
    (hF : ∀ i, Measurable (F i)) :
    (∫⁻ q, ∏ i, F i (q.1 i, q.2 i) ∂endpointTupleMeasure μ) = ∏ i, ∫⁻ p, F i p ∂μ i := by
  have hm : Measurable (fun q : Configuration n × Configuration n => ∏ i, F i (q.1 i, q.2 i)) :=
    Finset.measurable_prod _ (fun i _ => (hF i).comp
      (((measurable_pi_apply i).comp measurable_fst).prodMk
        ((measurable_pi_apply i).comp measurable_snd)))
  rw [endpointTupleMeasure, lintegral_map hm
    (MeasurableEquiv.arrowProdEquivProdArrow Plane Plane (Fin n)).measurable]
  exact Collision.lintegral_fin_nat_prod_eq_prod_collision μ F hF

/-- Arbitrary real one-particle tests factor under the actual endpoint tuple measure. -/
theorem integral_endpointTupleMeasure_prod {n : ℕ} (μ : Fin n → Measure (Plane × Plane))
    [∀ i, SigmaFinite (μ i)] (F : Fin n → Plane × Plane → ℝ) :
    (∫ q, ∏ i, F i (q.1 i, q.2 i) ∂endpointTupleMeasure μ) = ∏ i, ∫ p, F i p ∂μ i := by
  rw [endpointTupleMeasure, integral_map_equiv]
  exact integral_fin_nat_prod_eq_prod F

/-- Positive tensor tests factor under the actual endpoint tuple measure. -/
theorem lintegral_endpointTupleMeasure_tensor {n : ℕ} (μ : Fin n → Measure (Plane × Plane))
    [∀ i, SigmaFinite (μ i)]
    (f g : Fin n → Plane → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i)) :
    (∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i) ∂endpointTupleMeasure μ) =
      ∏ i, ∫⁻ p, f i p.1 * g i p.2 ∂μ i := by
  have heq (q : Configuration n × Configuration n) :
      (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i) = ∏ i, f i (q.1 i) * g i (q.2 i) :=
    Finset.prod_mul_distrib.symm
  simp_rw [heq]
  exact lintegral_endpointTupleMeasure_prod μ (fun i p => f i p.1 * g i p.2)
    (fun i => ((hf i).comp measurable_fst).mul ((hg i).comp measurable_snd))


/-- Integrability of a one-particle endpoint tuple is exactly integrability in its endpoint measure. -/
theorem integrable_endpointTupleMeasure_one_iff (μ : Measure (Plane × Plane)) [SigmaFinite μ]
    (H : Plane × Plane → ℝ) :
    Integrable (fun q : Configuration 1 × Configuration 1 => H (q.1 0, q.2 0))
      (endpointTupleMeasure (fun _ : Fin 1 => μ)) ↔ Integrable H μ := by
  rw [endpointTupleMeasure, integrable_map_equiv]
  change Integrable (fun p : Fin 1 → Plane × Plane => H (p 0))
    (Measure.pi (fun _ : Fin 1 => μ)) ↔ Integrable H μ
  let e := MeasurableEquiv.piUnique (fun _ : Fin 1 => Plane × Plane)
  have he := measurePreserving_piUnique (fun _ : Fin 1 => μ)
  have h := he.integrable_comp_emb e.measurableEmbedding (g := H)
  have hdef : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simpa only [Function.comp_def, e, MeasurableEquiv.piUnique, Equiv.piUnique,
    MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, hdef] using h

/-- Positive tensor tests factor under the actual block tuple measure. -/
theorem lintegral_blockTupleMeasure_tensor (n : ℕ) (μ : Measure (Plane × Plane)) [SigmaFinite μ]
    (f g : Fin n → Plane → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i)) :
    (∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i) ∂blockTupleMeasure n μ) =
      ∏ i, ∫⁻ p, f i p.1 * g i p.2 ∂μ :=
  lintegral_endpointTupleMeasure_tensor (fun _ => μ) f g hf hg

/-- The block moment axiom evaluates every positive tensor test of the expected tuple measure. -/
theorem HasDeltaBoseMoments.lintegral_blockTupleMeasure_tensor
    {θ τ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Ω → Measure (Plane × Plane)} (hB : HasDeltaBoseMoments θ τ P B) (hτ : 0 < τ)
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n ≤ 4)
    (f g : Fin n → Plane → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (hg : ∀ i, Measurable (g i)) :
    (∫⁻ ω, ∫⁻ q, (∏ i, f i (q.1 i)) * ∏ i, g i (q.2 i) ∂blockTupleMeasure n (B ω) ∂P) =
      ∫⁻ x : Configuration n, ∫⁻ y : Configuration n,
        (∏ i, f i (x i)) * momentKernel n θ τ x y * ∏ i, g i (y i) := by
  rw [← hB.lintegral_prod_eq hτ hn1 hn f g hf hg]
  apply lintegral_congr_ae
  filter_upwards [hB.2.1] with ω hω
  let : IsLocallyFiniteMeasure (B ω) := hω
  exact Critical2DKPZ.SHF.Tsai.lintegral_blockTupleMeasure_tensor n (B ω) f g hf hg

end Critical2DKPZ.SHF.Tsai

end
