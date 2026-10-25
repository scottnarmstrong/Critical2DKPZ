/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointLimitUnit
public import Critical2DKPZ.NonGaussian.EndpointLimitScaling
public import Critical2DKPZ.NonGaussian.EndpointLimitExtraction
import Mathlib.Tactic

/-! # Endpoint concentration and deterministic limits from logarithmic perturbations -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction CompactlySupported Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.NonGaussian

/-- Vanishing logarithmic perturbations imply L¹ concentration of averaged endpoint pairings
against every compactly supported continuous terminal test; see KPZ Lemma 9.4. -/
theorem endpointPairing_average_concentrates_of_log_perturbation
    (hPerturb : ∀ (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF ϑ P Z)
      (_hsym : ShfSymmetriesAt ϑ P Z) (_hC12 : ToyJointAt ϑ P Z) (_hHeatStartLogInput : HeatStartLogAt ϑ P Z) (_hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
      (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (_hH : IsCriticalKPZ P Z H) {t : ℝ} (_ht : 0 < t)
      (ψ : TestFn) (_hψ : ∀ x, 0 ≤ ψ x) (_hψ₁ : ∫ x, ψ x = 1)
      (_hG : ∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) = gaussianReal m v)
      (f : Plane →ᵇ ℝ) {c : ℝ} (_hc : 0 < c) (_hf : ∀ y, c ≤ f y) (p : ℝ≥0∞) (_hp : p ≠ ⊤),
      Tendsto (fun r => eLpNorm (fun ω => avgLogField P Z r t ψ f ω -
          avgLogField P Z r t ψ (fun _ => 1) ω) p P) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) {t : ℝ} (ht : 0 < t)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₁ : ∫ x, ψ x = 1)
    (hG : ∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) = gaussianReal m v)
    (φ : C_c(Plane, ℝ)) :
    Tendsto (fun r => ∫ ω, |(∫ x, ψ x * endpointPairing Z r t x φ ω) -
        ∫ ω', (∫ x, ψ x * endpointPairing Z r t x φ ω') ∂P| ∂P) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  obtain ⟨C, hC⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  let M : ℝ := max C 1
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  have hbound (y : Plane) : |φ y| ≤ M := by
    have hb : |φ y| ≤ C := by
      simpa only [CompactlySupportedContinuousMap.coe_toContinuousMap, Real.norm_eq_abs] using hC y
    exact hb.trans (le_max_left _ _)
  let φ₀ : C_c(Plane, ℝ) := M⁻¹ • φ
  have hφ₀ (y : Plane) : |φ₀ y| ≤ 1 := by
    change |M⁻¹ * φ y| ≤ 1
    rw [abs_mul, abs_of_pos (inv_pos.mpr hM)]
    calc
      _ ≤ M⁻¹ * M := mul_le_mul_of_nonneg_left (hbound y) (inv_nonneg.mpr hM.le)
      _ = 1 := inv_mul_cancel₀ hM.ne'
  have hEq : φ = M • φ₀ := by
    ext y
    change φ y = M * (M⁻¹ * φ y)
    rw [← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul]
  have hunit := endpointPairing_average_concentrates_unit_of_log_perturbation
    hPerturb ϑ P Z hZ hsym hC12 hHeatStartLogInput hHeatStartLogFieldInput H hH ht ψ hψ hψ₁ hG φ₀ hφ₀
  have hs := hunit.const_mul |M|
  simp only [mul_zero] at hs
  apply hs.congr'
  exact Filter.Eventually.of_forall fun r => by
    have heq := endpointPairing_average_abs_centered_smul P Z r t ψ M φ₀
    have hEqFun : M • (φ₀ : Plane → ℝ) = (φ : Plane → ℝ) :=
      congrArg (fun f : C_c(Plane, ℝ) => (f : Plane → ℝ)) hEq.symm
    rw [hEqFun] at heq
    exact heq.symm

/-- Concentration of compact endpoint pairings gives a deterministic subprobability limit
along a subsequence. -/
theorem exists_endpoint_limit_of_log_perturbation
    (hPerturb : ∀ (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF ϑ P Z)
      (_hsym : ShfSymmetriesAt ϑ P Z) (_hC12 : ToyJointAt ϑ P Z) (_hHeatStartLogInput : HeatStartLogAt ϑ P Z) (_hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
      (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (_hH : IsCriticalKPZ P Z H) {t : ℝ} (_ht : 0 < t)
      (ψ : TestFn) (_hψ : ∀ x, 0 ≤ ψ x) (_hψ₁ : ∫ x, ψ x = 1)
      (_hG : ∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) = gaussianReal m v)
      (f : Plane →ᵇ ℝ) {c : ℝ} (_hc : 0 < c) (_hf : ∀ y, c ≤ f y) (p : ℝ≥0∞) (_hp : p ≠ ⊤),
      Tendsto (fun r => eLpNorm (fun ω => avgLogField P Z r t ψ f ω -
          avgLogField P Z r t ψ (fun _ => 1) ω) p P) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0))
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z) (hHeatStartLogFieldInput : HeatStartLogFieldAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H) {t : ℝ} (ht : 0 < t)
    (ψ : TestFn) (hψ : ∀ x, 0 ≤ ψ x) (hψ₁ : ∫ x, ψ x = 1)
    (hG : ∃ (m : ℝ) (v : NNReal), P.map (fun ω => H t 0 ω ψ) = gaussianReal m v) :
    ∃ (μ : Measure Plane) (r : ℕ → ℝ), IsFiniteMeasure μ ∧ μ Set.univ ≤ 1 ∧
      Tendsto r atTop (nhdsWithin 0 (Set.Ioi 0)) ∧ ∀ φ : C_c(Plane, ℝ),
        Tendsto (fun n => ∫ ω, |(∫ x, ψ x * endpointPairing Z (r n) t x φ ω) - ∫ y, φ y ∂μ| ∂P)
          atTop (𝓝 0) := by
  apply exists_endpoint_limit_of_pairing_concentration ϑ P Z hZ ht ψ hψ hψ₁
  intro φ
  exact endpointPairing_average_concentrates_of_log_perturbation
    hPerturb ϑ P Z hZ hsym hC12 hHeatStartLogInput hHeatStartLogFieldInput H hH ht ψ hψ hψ₁ hG φ

end Critical2DKPZ.NonGaussian
