/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.EndpointLimitKernel
public import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Deterministic mean endpoint measures -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal CompactlySupported

namespace Critical2DKPZ.NonGaussian

/-- The normalized endpoint kernel integrated over the environment and the starting point
with spatial weight equal to the positive part of `ψ`. -/
def endpointMeanMeasure {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (μ : Ω → Measure (Plane × Plane)) (hμ : Measurable μ)
    (r : ℝ) (hr : 0 < r) (ψ : Plane → ℝ) : Measure Plane :=
  endpointMeasureKernel μ hμ r hr ∘ₘ
    ((volume.withDensity (fun x => ENNReal.ofReal (ψ x))).prod P)

/-- The deterministic mean measure has mass at most one and represents the
expectations of all spatially averaged normalized endpoint pairings. -/
theorem endpointMeanMeasure_spec {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure (Plane × Plane)) (hμ : Measurable μ)
    (hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (r : ℝ) (hr : 0 < r) (ψ : Plane → ℝ) (hψ : Continuous ψ)
    (hψc : HasCompactSupport ψ) (hψ0 : ∀ x, 0 ≤ ψ x) (hψ1 : ∫ x, ψ x = 1) :
    IsFiniteMeasure (endpointMeanMeasure P μ hμ r hr ψ) ∧
      endpointMeanMeasure P μ hμ r hr ψ Set.univ ≤ 1 ∧
      ∀ φ : C_c(Plane, ℝ),
        Integrable (fun ω => ∫ x, ψ x *
          (∫ y, φ y ∂endpointTerminalMeasure (μ ω) r x)) P ∧
        (∫ ω, (∫ x, ψ x * (∫ y, φ y ∂endpointTerminalMeasure (μ ω) r x)) ∂P) =
          ∫ y, φ y ∂endpointMeanMeasure P μ hμ r hr ψ := by
  let K := endpointMeasureKernel μ hμ r hr
  let ρ : Measure Plane := volume.withDensity (fun x => ENNReal.ofReal (ψ x))
  let ν : Measure (Plane × Ω) := ρ.prod P
  have hψi : Integrable ψ := hψ.integrable_of_hasCompactSupport hψc
  have hρprob : IsProbabilityMeasure ρ := by
    constructor
    change volume.withDensity (fun x => ENNReal.ofReal (ψ x)) Set.univ = 1
    rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ,
      ← ofReal_integral_eq_lintegral_ofReal hψi (Filter.Eventually.of_forall hψ0), hψ1,
      ENNReal.ofReal_one]
  let : IsProbabilityMeasure ρ := hρprob
  let : IsProbabilityMeasure ν := inferInstance
  have hmass : endpointMeanMeasure P μ hμ r hr ψ Set.univ ≤ 1 := by
    change (ν.bind K) Set.univ ≤ 1
    rw [Measure.bind_apply MeasurableSet.univ K.aemeasurable]
    calc
      _ ≤ ∫⁻ _q : Plane × Ω, (1 : ℝ≥0∞) ∂ν :=
        lintegral_mono (endpointMeasureKernel_mass_le_one μ hμ r hr)
      _ = 1 := by simp
  have hfinite : IsFiniteMeasure (endpointMeanMeasure P μ hμ r hr ψ) :=
    ⟨hmass.trans_lt ENNReal.one_lt_top⟩
  let : IsFiniteMeasure (endpointMeanMeasure P μ hμ r hr ψ) := hfinite
  refine ⟨hfinite, hmass, ?_⟩
  intro φ
  let F : Plane × Ω → ℝ := fun q => ∫ y, φ y ∂K q
  obtain ⟨M, hφ⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have hM : 0 ≤ M := (norm_nonneg (φ 0)).trans (hφ 0)
  have hFm : StronglyMeasurable F := φ.continuous.stronglyMeasurable.integral_kernel
  have hbound (q : Plane × Ω) : ‖F q‖ ≤ M := by
    have hreal : (K q).real Set.univ ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal (by norm_num)
        (by simpa only [ENNReal.ofReal_one] using endpointMeasureKernel_mass_le_one μ hμ r hr q)
    calc
      _ ≤ M * (K q).real Set.univ :=
        norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hφ)
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left hreal hM
      _ = M := mul_one M
  have hFi : Integrable F ν :=
    Integrable.of_bound hFm.aestronglyMeasurable M (Filter.Eventually.of_forall hbound)
  have hEq (ω : Ω) (hω : IsLocallyFiniteMeasure (μ ω)) :
      (∫ x, F (x, ω) ∂ρ) =
        ∫ x, ψ x * (∫ y, φ y ∂endpointTerminalMeasure (μ ω) r x) := by
    change (∫ x, F (x, ω) ∂volume.withDensity (fun x => ENNReal.ofReal (ψ x))) = _
    rw [integral_withDensity_eq_integral_toReal_smul hψ.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change (ENNReal.ofReal (ψ x)).toReal • F (x, ω) = _
      rw [ENNReal.toReal_ofReal (hψ0 x), smul_eq_mul]
      change ψ x * (∫ y, φ y ∂endpointMeasureKernel μ hμ r hr (x, ω)) = _
      rw [endpointMeasureKernel_apply_of_isLocallyFinite μ hμ r hr x ω hω]
  have hAi : Integrable (fun ω => ∫ x, ψ x *
      (∫ y, φ y ∂endpointTerminalMeasure (μ ω) r x)) P :=
    hFi.integral_prod_right.congr (hlocal.mono fun ω hω => hEq ω hω)
  refine ⟨hAi, ?_⟩
  have hcomp : (∫ y, φ y ∂endpointMeanMeasure P μ hμ r hr ψ) = ∫ q, F q ∂ν := by
    have hi : Integrable (fun y => φ y) ((K ∘ₖ Kernel.const Unit ν) ()) := by
      rw [← Measure.comp_eq_comp_const_apply]
      exact φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    change (∫ y, φ y ∂(K ∘ₘ ν)) = ∫ q, F q ∂ν
    rw [Measure.comp_eq_comp_const_apply]
    exact ProbabilityTheory.Kernel.integral_comp (κ := Kernel.const Unit ν) (η := K) (a := ()) hi
  calc
    _ = ∫ ω, ∫ x, F (x, ω) ∂ρ ∂P :=
      integral_congr_ae (hlocal.mono fun ω hω => (hEq ω hω).symm)
    _ = ∫ q, F q ∂ν := (integral_prod_symm F hFi).symm
    _ = _ := hcomp.symm

end Critical2DKPZ.NonGaussian
