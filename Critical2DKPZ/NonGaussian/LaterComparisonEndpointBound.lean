/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Inputs
import Critical2DKPZ.SHF.Positivity.HeatBoundedIntegrability
import Mathlib.Tactic

/-! # Bounds for normalized endpoint pairings -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Critical2DKPZ.LocalSobolev
open Critical2DKPZ.SHF.Positivity
open scoped BoundedContinuousFunction CompactlySupported Topology

namespace Critical2DKPZ.NonGaussian

/-- A heat-start pairing against a terminal test between zero and one, divided by the flat
terminal mass, is an integrable random variable taking values in `[0,1]` almost surely. -/
theorem endpointPairing_between_zero_and_one_of {Ω : Type*} [MeasurableSpace Ω]
    (ϑ : ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) (x : Plane) (φ : C_c(Plane, ℝ))
    (hφ : ∀ y, 0 ≤ φ y ∧ φ y ≤ 1) :
    (∀ᵐ ω ∂P, 0 ≤ endpointPairing Z r t x φ ω ∧ endpointPairing Z r t x φ ω ≤ 1) ∧
      Integrable (endpointPairing Z r t x φ) P := by
  let gφ : Plane →ᵇ ℝ := φ.toBoundedContinuousFunction
  let g1 : Plane →ᵇ ℝ := 1
  have hφpair := isCriticalSHF_heat_bounded_pairing_integrable_bound
    ϑ P Z hZ hr.le hrt hr x gφ
  have h1pair := isCriticalSHF_heat_bounded_pairing_integrable_bound
    ϑ P Z hZ hr.le hrt hr x g1
  have hnumInt : Integrable
      (shfPairing Z r t (fun y => heatKernel r (y - x)) φ) P := by
    change Integrable (shfPairing Z r t (fun y => heatKernel r (y - x))
      (fun y => gφ y)) P
    exact hφpair.2.1
  have hdenInt : Integrable
      (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => (1 : ℝ))) P := by
    change Integrable (shfPairing Z r t (fun y => heatKernel r (y - x))
      (fun y => g1 y)) P
    exact h1pair.2.1
  have hnumPair : ∀ᵐ ω ∂P, Integrable
      (fun p : Plane × Plane => heatKernel r (p.1 - x) * φ p.2) (Z r t ω) := by
    change ∀ᵐ ω ∂P, Integrable
      (fun p : Plane × Plane => heatKernel r (p.1 - x) * gφ p.2) (Z r t ω)
    exact hφpair.1
  have hdenPair : ∀ᵐ ω ∂P, Integrable
      (fun p : Plane × Plane => heatKernel r (p.1 - x) * (1 : ℝ)) (Z r t ω) := by
    change ∀ᵐ ω ∂P, Integrable
      (fun p : Plane × Plane => heatKernel r (p.1 - x) * g1 p.2) (Z r t ω)
    exact h1pair.1
  have hdenpos : ∀ᵐ ω ∂P,
      0 < shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => (1 : ℝ)) ω := by
    have h := hsym.2.2.2.2.2.2 r t r x (0 : Plane →ᵇ ℝ) hr.le hrt hr
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using h.1
  have hnumle : ∀ᵐ ω ∂P,
      shfPairing Z r t (fun y => heatKernel r (y - x)) φ ω ≤
        shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => (1 : ℝ)) ω := by
    filter_upwards [hnumPair, hdenPair] with ω hnum hden
    change (∫ p, heatKernel r (p.1 - x) * φ p.2 ∂Z r t ω) ≤
      ∫ p, heatKernel r (p.1 - x) * (1 : ℝ) ∂Z r t ω
    apply integral_mono hnum hden
    intro p
    exact mul_le_mul_of_nonneg_left (hφ p.2).2 (heatKernel_nonneg hr.le (p.1 - x))
  have hnumNonneg : ∀ᵐ ω ∂P,
      0 ≤ shfPairing Z r t (fun y => heatKernel r (y - x)) φ ω := by
    filter_upwards [hnumPair] with ω hnum
    change 0 ≤ ∫ p, heatKernel r (p.1 - x) * φ p.2 ∂Z r t ω
    exact integral_nonneg fun p =>
      mul_nonneg (heatKernel_nonneg hr.le (p.1 - x)) (hφ p.2).1
  have hbound : ∀ᵐ ω ∂P,
      0 ≤ endpointPairing Z r t x φ ω ∧ endpointPairing Z r t x φ ω ≤ 1 := by
    filter_upwards [hdenpos, hnumle, hnumNonneg] with ω hden hle hnonneg
    change 0 ≤ _ / _ ∧ _ / _ ≤ 1
    exact ⟨div_nonneg hnonneg hden.le, (div_le_one₀ hden).2 hle⟩
  have hpairAE : AEMeasurable (endpointPairing Z r t x φ) P :=
    (hnumInt.aemeasurable.div hdenInt.aemeasurable)
  have hpairInt : Integrable (endpointPairing Z r t x φ) P := by
    apply (integrable_const (1 : ℝ)).mono' hpairAE.aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hω.1], hω.2⟩
  exact ⟨hbound, hpairInt⟩

end Critical2DKPZ.NonGaussian

end
