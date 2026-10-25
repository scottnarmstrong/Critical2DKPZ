/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.CovarianceConvergence
public import Critical2DKPZ.CovarianceKernel.WeakCovarianceKernelExistence
public import Critical2DKPZ.Spectral.BochnerSchwartzTestPairing
import Mathlib.Probability.Moments.Covariance

/-! # Spectral measure of the KPZ covariance kernel -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction ComplexConjugate Topology

universe u

namespace Critical2DKPZ.CovarianceKernel

/-- The locally square-integrable logarithmic envelope has ball integrals bounded by a constant plus π times the radius squared. -/
theorem covarianceLogEnvelope_integral_growth :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 1 ≤ R →
      ∫ z in Metric.closedBall (0 : Plane) R, covarianceLogEnvelope z ≤ K + Real.pi * R ^ 2 := by
  let B1 : Set Plane := Metric.closedBall 0 1
  let K : ℝ := ∫ z in B1, covarianceLogEnvelope z
  have hB1 : IsCompact B1 := isCompact_closedBall _ _
  have hmeasureB1 : (volume.restrict B1) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact ne_of_lt hB1.measure_lt_top
  have hEnvMem1 : MemLp covarianceLogEnvelope 2 (volume.restrict B1) :=
    covarianceLogEnvelope_memLp_two_on_compact B1 hB1
  have hEnvMem1one : MemLp covarianceLogEnvelope 1 (volume.restrict B1) :=
    hEnvMem1.mono_exponent_of_measure_support_ne_top
      (s := Set.univ) (by simp) hmeasureB1 (by norm_num)
  have hEnvInt1 : IntegrableOn covarianceLogEnvelope B1 volume :=
    memLp_one_iff_integrable.mp hEnvMem1one
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact setIntegral_nonneg hB1.measurableSet (fun z _ => (covarianceLogEnvelope_pos z).le)
  refine ⟨K, hKnonneg, fun R hR => ?_⟩
  let BR : Set Plane := Metric.closedBall 0 R
  let D : Set Plane := BR \ B1
  have hBR : IsCompact BR := isCompact_closedBall _ _
  have hmeasureBR : (volume.restrict BR) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact ne_of_lt hBR.measure_lt_top
  have hB1sub : B1 ⊆ BR := by
    intro z hz
    exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hz).trans hR)
  have hEnvMemR : MemLp covarianceLogEnvelope 2 (volume.restrict BR) :=
    covarianceLogEnvelope_memLp_two_on_compact BR hBR
  have hEnvMemRone : MemLp covarianceLogEnvelope 1 (volume.restrict BR) :=
    hEnvMemR.mono_exponent_of_measure_support_ne_top
      (s := Set.univ) (by simp) hmeasureBR (by norm_num)
  have hEnvIntR : IntegrableOn covarianceLogEnvelope BR volume :=
    memLp_one_iff_integrable.mp hEnvMemRone
  have hDmeas : MeasurableSet D := hBR.measurableSet.diff hB1.measurableSet
  have hEnvIntD : IntegrableOn covarianceLogEnvelope D volume :=
    hEnvIntR.mono_set (fun _ hz => hz.1)
  have hdecomp : BR = B1 ∪ D := by
    ext z
    simp only [D, Set.mem_union, Set.mem_sdiff]
    constructor
    · intro hz
      by_cases h : z ∈ B1
      · exact Or.inl h
      · exact Or.inr ⟨hz, h⟩
    · rintro (hz | ⟨hz, _⟩)
      · exact hB1sub hz
      · exact hz
  have hDenv : ∫ z in D, covarianceLogEnvelope z = volume.real D := by
    calc
      ∫ z in D, covarianceLogEnvelope z = ∫ z in D, (1 : ℝ) := by
        apply setIntegral_congr_fun hDmeas
        intro z hz
        have hzout : ¬ z ∈ B1 := hz.2
        have hnorm : 1 ≤ ‖z‖ := by
          apply le_of_not_ge
          intro hle
          apply hzout
          simpa [B1, Metric.mem_closedBall, dist_zero_right] using hle
        exact covarianceLogEnvelope_eq_one_of_one_le_norm z hnorm
      _ = volume.real D := by simp [Measure.real]
  have hsplit :
      (∫ z in BR, covarianceLogEnvelope z) = K + volume.real D := by
    rw [hdecomp, setIntegral_union (by
      dsimp [D]
      exact (disjoint_sdiff_self_left : Disjoint (BR \ B1) B1).symm)
      hDmeas hEnvInt1 hEnvIntD]
    rw [hDenv]
  have hvol : volume.real BR = Real.pi * R ^ 2 := by
    have hv := InnerProductSpace.volume_closedBall_of_dim_even
      (E := Plane) (k := 1) (by norm_num [Plane]) (0 : Plane) R
    have hRnonneg : 0 ≤ R := le_trans (by norm_num) hR
    dsimp [BR, Measure.real]
    rw [hv]
    simp [Plane, ENNReal.toReal_ofReal hRnonneg]
    rw [ENNReal.toReal_ofReal Real.pi_nonneg]
    ring
  have hDvol : volume.real D ≤ volume.real BR := by
    apply ENNReal.toReal_mono (ne_of_lt hBR.measure_lt_top)
    exact measure_mono (fun _ hz => hz.1)
  calc
    ∫ z in BR, covarianceLogEnvelope z = K + volume.real D := hsplit
    _ ≤ K + volume.real BR := by linarith
    _ = K + Real.pi * R ^ 2 := by rw [hvol]

/-- A nonnegative covariance kernel bounded by the logarithmic envelope has polynomial ball growth. -/
theorem covarianceKernel_polynomial_growth_of_logEnvelope
    (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hCnonneg : ∀ᵐ z : Plane ∂volume, 0 ≤ C z)
    (hbound : ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ z : Plane ∂volume,
      C z ≤ A * covarianceLogEnvelope z) :
    ∃ A : ℝ, ∃ k : ℕ, ∀ R : ℝ, 1 ≤ R →
      ∫ z in Metric.closedBall (0 : Plane) R, |C z| ≤ A * R ^ k := by
  obtain ⟨A₀, hA₀, hbound⟩ := hbound
  obtain ⟨K, hK, hKbound⟩ := covarianceLogEnvelope_integral_growth
  let A : ℝ := A₀ * (K + Real.pi)
  refine ⟨A, 2, fun R hR => ?_⟩
  let B : Set Plane := Metric.closedBall 0 R
  have hB : IsCompact B := isCompact_closedBall _ _
  have hCint : IntegrableOn (fun z : Plane => |C z|) B volume :=
    Spectral.integrable_abs_kernel_on_closedBall C hC R
  have hEnvMem : MemLp covarianceLogEnvelope 2 (volume.restrict B) :=
    covarianceLogEnvelope_memLp_two_on_compact B hB
  have hmeasureB : (volume.restrict B) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact ne_of_lt hB.measure_lt_top
  have hEnvMemone : MemLp covarianceLogEnvelope 1 (volume.restrict B) :=
    hEnvMem.mono_exponent_of_measure_support_ne_top
      (s := Set.univ) (by simp) hmeasureB (by norm_num)
  have hEnvInt : IntegrableOn covarianceLogEnvelope B volume :=
    memLp_one_iff_integrable.mp hEnvMemone
  have hAEnvInt : IntegrableOn (fun z : Plane => A₀ * covarianceLogEnvelope z) B volume :=
    hEnvInt.const_mul A₀
  have hpoint : ∀ᵐ z : Plane ∂volume.restrict B,
      |C z| ≤ A₀ * covarianceLogEnvelope z := by
    filter_upwards [ae_restrict_of_ae hCnonneg, ae_restrict_of_ae hbound] with z hz₀ hz
    rw [abs_of_nonneg hz₀]
    exact hz
  have hCmono := setIntegral_mono_ae_restrict hCint hAEnvInt hpoint
  have hEnvBound :
      ∫ z in B, covarianceLogEnvelope z ≤ K + Real.pi * R ^ 2 := by
    exact hKbound R hR
  have hA₀nonneg : 0 ≤ A₀ := hA₀
  have hCbound :
      ∫ z in B, |C z| ≤ A₀ * (K + Real.pi * R ^ 2) := by
    calc
      ∫ z in B, |C z| ≤ ∫ z in B, A₀ * covarianceLogEnvelope z := hCmono
      _ = A₀ * ∫ z in B, covarianceLogEnvelope z := by rw [integral_const_mul]
      _ ≤ A₀ * (K + Real.pi * R ^ 2) := mul_le_mul_of_nonneg_left hEnvBound hA₀nonneg
  have hKπ : 0 ≤ K + Real.pi := add_nonneg hK (le_of_lt Real.pi_pos)
  have hR2 : 1 ≤ R ^ 2 := by nlinarith
  have hprofile : K + Real.pi * R ^ 2 ≤ (K + Real.pi) * R ^ 2 := by
    nlinarith [hK, Real.pi_pos.le, hR2]
  change ∫ z in B, |C z| ≤ A * R ^ 2
  calc
    ∫ z in B, |C z| ≤ A₀ * (K + Real.pi * R ^ 2) := hCbound
    _ ≤ A₀ * ((K + Real.pi) * R ^ 2) :=
      mul_le_mul_of_nonneg_left hprofile hA₀nonneg
    _ = A * R ^ 2 := by dsimp [A]; ring

/-- An even, rotation-invariant covariance kernel with polynomial growth admits a locally finite spectral measure. -/
theorem exists_spectralMeasure_of_covarianceKernel
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (t : ℝ)
    (C : Plane → ℝ)
    (hC : ∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K))
    (hgrowth : ∃ (A : ℝ) (k : ℕ), ∀ R : ℝ, 1 ≤ R →
      ∫ z in Metric.closedBall 0 R, |C z| ≤ A * R ^ k)
    (heven : (fun z => C (-z)) =ᵐ[volume] C)
    (hrot : ∀ R : Plane ≃ₗᵢ[ℝ] Plane,
      LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 →
        (fun z => C (R z)) =ᵐ[volume] C)
    (hmem : ∀ f : TestFn, MemLp (fun ω => H t 0 ω f) 2 P)
    (hrep : ∀ f g : TestFn,
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2)) :
    ∃ ν : Measure Plane, IsLocallyFiniteMeasure ν ∧
      (∀ R : Plane ≃ₗᵢ[ℝ] Plane,
        LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 → ν.map R = ν) ∧
      ∀ f g : TestFn,
        cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
          ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν := by
  have hpos : ∀ f : TestFn, 0 ≤
      ∫ p : Plane × Plane, f p.1 * f p.2 * C (p.1 - p.2) := by
    intro f
    rw [← hrep f f]
    rw [ProbabilityTheory.covariance_self (hmem f).aemeasurable]
    exact ProbabilityTheory.variance_nonneg (fun ω => H t 0 ω f) P
  obtain ⟨ν, hνloc, _hνgrowth, hνrot, hνpair⟩ :=
    Spectral.exists_spectralMeasure_of_positiveType C hC hgrowth heven hpos
  refine ⟨ν, hνloc, ?_, ?_⟩
  · intro R hdet
    exact hνrot R (hrot R hdet)
  · intro f g
    calc
      cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
          ∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2) := hrep f g
      _ = ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν :=
          hνpair f g

/-- The stated symmetries, reversal law and covariance bounds give the KPZ field a rotation-invariant spectral measure. -/
theorem exists_kpz_spectralMeasure_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    (hC12 : LocalSobolev.ToyJointAt ϑ P Z) (hcov : SmallScales.FlatCovarianceAt P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (_hR7 : SmallScales.KpzTransportAt P H) {t : ℝ} (ht : 0 < t) :
    ∃ ν : Measure Plane, IsLocallyFiniteMeasure ν ∧
      (∀ R : Plane ≃ₗᵢ[ℝ] Plane,
        LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 → ν.map R = ν) ∧
      ∀ f g : TestFn,
        cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
          ∫ ξ, (Spectral.fourierKPZ f ξ * conj (Spectral.fourierKPZ g ξ)).re ∂ν := by
  obtain ⟨C, hC, hCnonneg, heven, hrot, ⟨A, hAnonneg, hboundBase⟩, hrep⟩ :=
    exists_kpz_covKernel_base_of ϑ P Z hZ hsym hrevL hC12 hcov H hH ht
  have hbound : ∀ᵐ z : Plane ∂volume, C z ≤ A * covarianceLogEnvelope z := by
    filter_upwards [hboundBase] with z hz
    simpa [covarianceLogEnvelope] using hz
  obtain ⟨Agrowth, k, hgrowth⟩ :=
    covarianceKernel_polynomial_growth_of_logEnvelope C hC hCnonneg
      ⟨A, hAnonneg, hbound⟩
  have hmem : ∀ f : TestFn, MemLp (fun ω => H t 0 ω f) 2 P := by
    intro f
    exact (kpz_cov_tendsto_of ϑ P Z hZ hsym hrevL hC12 H hH ht f f).1
  exact exists_spectralMeasure_of_covarianceKernel P H t C hC
    ⟨Agrowth, k, hgrowth⟩ heven hrot hmem hrep

end Critical2DKPZ.CovarianceKernel

end
