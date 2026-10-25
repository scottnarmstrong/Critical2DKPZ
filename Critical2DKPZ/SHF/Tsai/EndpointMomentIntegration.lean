/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.BlockTupleMeasures
public import Critical2DKPZ.SHF.Tsai.KernelMeasureRealForms
public import Critical2DKPZ.SHF.Tsai.TensorMoments
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! # Moment identities for real `L²` endpoint tests

A finite kernel moment measure gives integrability and the product-moment identity for
real `L²` endpoint representatives. The one-particle case gives integrability within
almost every random endpoint measure.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- A full endpoint tuple mean evaluates any integrable product of real one-particle tests. -/
theorem integral_prod_tests_of_endpointTuple_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} (C : Fin n → Ω → Measure (Plane × Plane))
    (hCm : ∀ i, Measurable (C i)) (hClf : ∀ i ω, IsLocallyFiniteMeasure (C i ω))
    (ν : Measure (Configuration n × Configuration n))
    (hmean : P.bind (fun ω => endpointTupleMeasure (fun i => C i ω)) = ν)
    (F : Fin n → Plane × Plane → ℝ)
    (hI : Integrable (fun q => ∏ i, F i (q.1 i, q.2 i)) ν) :
    Integrable (fun ω => ∏ i, ∫ p, F i p ∂C i ω) P ∧
      (∫ ω, ∏ i, (∫ p, F i p ∂C i ω) ∂P) = ∫ q, ∏ i, F i (q.1 i, q.2 i) ∂ν := by
  let H (q : Configuration n × Configuration n) := ∏ i, F i (q.1 i, q.2 i)
  let κ : Kernel Ω (Configuration n × Configuration n) :=
    ⟨fun ω => endpointTupleMeasure (fun i => C i ω), measurable_endpointTupleMeasure C hCm hClf⟩
  have hIcomp : Integrable H ((κ ∘ₖ Kernel.const Unit P) ()) := by
    change Integrable H (P.bind (fun ω => endpointTupleMeasure (fun i => C i ω)))
    rw [hmean]
    exact hI
  have hpoint (ω) : (∫ q, H q ∂κ ω) = ∏ i, ∫ p, F i p ∂C i ω := by
    let : ∀ i, IsLocallyFiniteMeasure (C i ω) := fun i => hClf i ω
    exact integral_endpointTupleMeasure_prod (fun i => C i ω) F
  have houter := hIcomp.integral_comp
  have heq := Kernel.integral_comp hIcomp
  change (∫ q, H q ∂P.bind (fun ω => endpointTupleMeasure (fun i => C i ω))) =
    ∫ ω, ∫ q, H q ∂κ ω ∂P at heq
  rw [hmean] at heq
  refine ⟨houter.congr (Filter.Eventually.of_forall hpoint), ?_⟩
  exact (integral_congr_ae (Filter.Eventually.of_forall fun ω => (hpoint ω).symm)).trans heq.symm

/-- A finite kernel moment measure evaluates products of arbitrary real `L²` endpoint pairings. -/
theorem integral_prod_pairings_of_endpointTuple_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {n : ℕ} (C : Fin n → Ω → Measure (Plane × Plane))
    (hCm : ∀ i, Measurable (C i)) (hClf : ∀ i ω, IsLocallyFiniteMeasure (C i ω))
    {K : Configuration n → Configuration n → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    (hmean : P.bind (fun ω => endpointTupleMeasure (fun i => C i ω)) =
      volume.withDensity (Function.uncurry K))
    (g g' : Fin n → Plane → ℝ) (hg : ∀ i, MemLp (g i) 2) (hg' : ∀ i, MemLp (g' i) 2) :
    Integrable (fun ω => ∏ i, ∫ p, g i p.1 * g' i p.2 ∂C i ω) P ∧
      (∫ ω, ∏ i, (∫ p, g i p.1 * g' i p.2 ∂C i ω) ∂P) =
        ∫ x, ∫ y, (∏ i, g i (x i)) * (K x y).toReal * ∏ i, g' i (y i) := by
  let F (x : Configuration n) := ∏ i, g i (x i)
  let G (y : Configuration n) := ∏ i, g' i (y i)
  let H (q : Configuration n × Configuration n) := F q.1 * G q.2
  obtain ⟨hI, hform⟩ := integrable_kernelMeasure_mul_and_integral hK hc hKF F G
    (memLp_configuration_tensor g hg) (memLp_configuration_tensor g' hg')
  have hIprod : Integrable (fun q : Configuration n × Configuration n =>
      ∏ i, g i (q.1 i) * g' i (q.2 i))
      (volume.withDensity (Function.uncurry K)) := by
    exact hI.congr (Filter.Eventually.of_forall fun q => Finset.prod_mul_distrib.symm)
  obtain ⟨houter, hmoment⟩ := integral_prod_tests_of_endpointTuple_mean P C hCm hClf
    _ hmean (fun i p => g i p.1 * g' i p.2) hIprod
  refine ⟨houter, hmoment.trans ?_⟩
  have heq : (∫ q, ∏ i, g i (q.1 i) * g' i (q.2 i)
      ∂volume.withDensity (Function.uncurry K)) =
      ∫ q, H q ∂volume.withDensity (Function.uncurry K) := by
    apply integral_congr_ae
    filter_upwards with q
    exact Finset.prod_mul_distrib
  exact heq.trans hform

/-- A one-particle kernel moment measure gives integrability inside almost every endpoint measure. -/
theorem ae_integrable_pairing_of_endpointTuple_mean {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (C : Ω → Measure (Plane × Plane)) (hCm : Measurable C)
    (hClf : ∀ ω, IsLocallyFiniteMeasure (C ω))
    {K : Configuration 1 → Configuration 1 → ℝ≥0∞} (hK : Measurable (Function.uncurry K))
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hKF : FormBound volume volume K c)
    (hmean : P.bind (fun ω => endpointTupleMeasure (fun _ : Fin 1 => C ω)) =
      volume.withDensity (Function.uncurry K))
    (g g' : Plane → ℝ) (hg : MemLp g 2) (hg' : MemLp g' 2) :
    ∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => g p.1 * g' p.2) (C ω) := by
  let F (x : Configuration 1) := g (x 0)
  let G (y : Configuration 1) := g' (y 0)
  have hF : MemLp F 2 := by
    simpa only [Fin.prod_univ_one] using memLp_configuration_tensor (fun _ : Fin 1 => g) (fun _ => hg)
  have hG : MemLp G 2 := by
    simpa only [Fin.prod_univ_one] using memLp_configuration_tensor (fun _ : Fin 1 => g') (fun _ => hg')
  let H (q : Configuration 1 × Configuration 1) := F q.1 * G q.2
  have hI := (integrable_kernelMeasure_mul_and_integral hK hc hKF F G hF hG).1
  let κ : Kernel Ω (Configuration 1 × Configuration 1) :=
    ⟨fun ω => endpointTupleMeasure (fun _ : Fin 1 => C ω),
      measurable_endpointTupleMeasure (fun _ => C) (fun _ => hCm) (fun _ => hClf)⟩
  have hIcomp : Integrable H ((κ ∘ₖ Kernel.const Unit P) ()) := by
    change Integrable H
      (P.bind (fun ω => endpointTupleMeasure (fun _ : Fin 1 => C ω)))
    rw [hmean]
    exact hI
  filter_upwards [hIcomp.ae_of_comp] with ω hω
  let : IsLocallyFiniteMeasure (C ω) := hClf ω
  exact (integrable_endpointTupleMeasure_one_iff (C ω) (fun p => g p.1 * g' p.2)).1 hω

end Critical2DKPZ.SHF.Tsai

end
