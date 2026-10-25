/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.CovarianceLimit
public import Critical2DKPZ.CovarianceKernel.Envelope
public import Critical2DKPZ.CovarianceKernel.RegularizedMeasurability
public import Critical2DKPZ.SmallScales.Inputs

/-! # Bounds on regularized covariance kernels -/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Critical2DKPZ.CovarianceKernel

/-- The covariance bound makes each regularized covariance kernel nonnegative away from the diagonal. -/
theorem regCovKernel_nonneg_of_flatCovariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hcov : SmallScales.FlatCovarianceAt P Z)
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hδt : δ < t / 2)
    (z : Plane) (hz : z ≠ 0) :
    0 ≤ regCovKernel P Z t δ z := by
  have htHalf : 0 < t / 2 := div_pos ht (by norm_num)
  obtain ⟨A, hA⟩ := hcov (t₀ := t / 2) (t₁ := t) htHalf
  have htIcc : t ∈ Set.Icc (t / 2) t := ⟨(by linarith [ht]), le_rfl⟩
  rcases hA t htIcc δ δ hδ hδt hδ hδt z 0 (by simpa using hz) with
    ⟨_, hnonneg, _⟩
  change 0 ≤ cov[kpzRegularized P Z t δ 0 z, kpzRegularized P Z t δ 0 0; P] at hnonneg
  change 0 ≤ cov[kpzRegularized P Z t δ 0 0, kpzRegularized P Z t δ 0 z; P]
  rw [covariance_comm]
  simpa [regCovKernel] using hnonneg

/-- The covariance bound supplies a common logarithmic upper envelope for all regularized covariance kernels. -/
theorem regCovKernel_le_of_flatCovariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hcov : SmallScales.FlatCovarianceAt P Z)
    {t : ℝ} (ht : 0 < t) :
    ∃ A : ℝ, ∀ δ : ℝ, 0 < δ → δ < t / 2 → ∀ z : Plane, z ≠ 0 →
      regCovKernel P Z t δ z ≤
        A * (1 + Real.log (1 + max 0 (Real.log ‖z‖⁻¹))) := by
  have htHalf : 0 < t / 2 := div_pos ht (by norm_num)
  obtain ⟨A, hA⟩ := hcov (t₀ := t / 2) (t₁ := t) htHalf
  have htIcc : t ∈ Set.Icc (t / 2) t := ⟨(by linarith [ht]), le_rfl⟩
  refine ⟨A, fun δ hδ hδt z hz => ?_⟩
  rcases hA t htIcc δ δ hδ hδt hδ hδt z 0 (by simpa using hz) with
    ⟨_, _, hupper⟩
  change cov[kpzRegularized P Z t δ 0 z, kpzRegularized P Z t δ 0 0; P] ≤
    A * (1 + Real.log (1 + max 0 (Real.log ‖z - 0‖⁻¹))) at hupper
  change cov[kpzRegularized P Z t δ 0 0, kpzRegularized P Z t δ 0 z; P] ≤
    A * (1 + Real.log (1 + max 0 (Real.log ‖z‖⁻¹)))
  rw [covariance_comm]
  simpa using hupper

/-- A measurable regularized covariance kernel bounded by the common logarithmic envelope is square-integrable on every compact set. -/
theorem regCovKernel_memLp_two_on_compact_of_flatCovariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hcov : SmallScales.FlatCovarianceAt P Z)
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hδt : δ < t / 2)
    (K : Set Plane) (hK : IsCompact K)
    (hmeas : AEStronglyMeasurable (fun z => regCovKernel P Z t δ z)
      (volume.restrict K)) :
    MemLp (fun z => regCovKernel P Z t δ z) 2 (volume.restrict K) := by
  obtain ⟨A, hA⟩ := regCovKernel_le_of_flatCovariance P Z hcov ht
  let z₀ : Plane := EuclideanSpace.single 0 (1 : ℝ)
  have hz₀ : z₀ ≠ 0 := by
    intro h
    have h0 := congrArg (fun z : Plane => z 0) h
    simp [z₀] at h0
  let δ₀ : ℝ := t / 4
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₀t : δ₀ < t / 2 := by dsimp [δ₀]; linarith
  have hcov₀ : 0 ≤ regCovKernel P Z t δ₀ z₀ :=
    regCovKernel_nonneg_of_flatCovariance P Z hcov ht hδ₀ hδ₀t z₀ hz₀
  have hA₀ : regCovKernel P Z t δ₀ z₀ ≤ A * covarianceLogEnvelope z₀ :=
    hA δ₀ hδ₀ hδ₀t z₀ hz₀
  have hA_nonneg : 0 ≤ A := by
    by_contra h
    have hAn : A < 0 := lt_of_not_ge h
    have hprod : A * covarianceLogEnvelope z₀ < 0 :=
      mul_neg_of_neg_of_pos hAn (covarianceLogEnvelope_pos z₀)
    linarith
  have hEnvelope : MemLp covarianceLogEnvelope 2 (volume.restrict K) :=
    covarianceLogEnvelope_memLp_two_on_compact K hK
  have hmajor : MemLp (fun z => A * covarianceLogEnvelope z) 2 (volume.restrict K) :=
    hEnvelope.const_mul A
  have hbound : ∀ᵐ z ∂volume.restrict K,
      ‖regCovKernel P Z t δ z‖ ≤ ‖A * covarianceLogEnvelope z‖ := by
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : Plane))] with z hz
    have hnonneg := regCovKernel_nonneg_of_flatCovariance P Z hcov ht hδ hδt z hz
    have hupper := hA δ hδ hδt z hz
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg hA_nonneg (le_of_lt (covarianceLogEnvelope_pos z)))]
    exact hupper
  exact hmajor.of_le hmeas hbound

/-- The covariance bound and joint measurability give local square-integrability of every regularized covariance
kernel at a scale below half the observation time. -/
theorem regCovKernel_memLp_two_on_compact_of_flatCovariance_measurable
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    (hcov : SmallScales.FlatCovarianceAt P Z)
    {t δ : ℝ} (ht : 0 < t) (hδ : 0 < δ) (hδt : δ < t / 2)
    (K : Set Plane) (hK : IsCompact K) :
    MemLp (fun z => regCovKernel P Z t δ z) 2 (volume.restrict K) := by
  apply regCovKernel_memLp_two_on_compact_of_flatCovariance P Z hcov ht hδ hδt K hK
  exact ((regCovKernel_aemeasurable_of ϑ P Z hZ hsym hrevL hδ
    (lt_trans hδt (half_lt_self ht))).restrict).aestronglyMeasurable

end Critical2DKPZ.CovarianceKernel

end
