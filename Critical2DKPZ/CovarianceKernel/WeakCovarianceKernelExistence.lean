/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.WeakLimitCovarianceRepresentation
public import Critical2DKPZ.CovarianceKernel.WeakLimitEvenness
public import Critical2DKPZ.CovarianceKernel.RegularizedRotation
public import Critical2DKPZ.CovarianceKernel.WeakLimitRotation

/-! # Existence and bounds for the KPZ covariance kernel -/

@[expose] public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.CovarianceKernel

/-- The KPZ field has an even, nonnegative, locally square-integrable covariance kernel with a logarithmic upper bound. -/
theorem exists_kpz_covKernel_base_of
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    (hC12 : LocalSobolev.ToyJointAt ϑ P Z)
    (hcov : SmallScales.FlatCovarianceAt P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) :
    ∃ C : Plane → ℝ, (∀ K : Set Plane, IsCompact K → MemLp C 2 (volume.restrict K)) ∧
      (∀ᵐ z, 0 ≤ C z) ∧ ((fun z => C (-z)) =ᵐ[volume] C) ∧
      (∀ R : Plane ≃ₗᵢ[ℝ] Plane, LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1 →
        (fun z => C (R z)) =ᵐ[volume] C) ∧
      (∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ z,
        C z ≤ A * covarianceLogEnvelope z) ∧
      (∀ f g : TestFn, cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
        ∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2)) := by
  obtain ⟨s, hs, v, hmem, hweak⟩ :=
    exists_weak_subseq_weighted_regCovKernel_of_flatCovariance ϑ P Z hZ hsym hrevL hcov ht
  let C : Plane → ℝ := weakLimitCovarianceKernel v
  obtain ⟨A, hAnonneg, horder⟩ :=
    weakLimitCovarianceKernel_order_bounds_of_flatCovariance P Z hcov ht s v hmem hweak
  have hevenV := weightedWeakCovarianceLimit_even_of_shfSymmetries
    ϑ P Z hZ hsym hrevL ht s v hmem hweak
  have hevenC : (fun z : Plane => C (-z)) =ᵐ[volume] C := by
    filter_upwards [hevenV] with z hz
    change v (-z) / covarianceDecayWeight (-z) = v z / covarianceDecayWeight z
    rw [hz]
    simp [covarianceDecayWeight, norm_neg]
  have hrotV (R : Plane ≃ₗᵢ[ℝ] Plane)
      (hdet : LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1) :
      (fun z : Plane => v (R z)) =ᵐ[volume] v := by
    apply weakLimitL2_invariant_of_invariant_seq R s v
      (fun n z => covarianceDecayWeight z *
        regCovKernel P Z t (t / ((n : ℝ) + 3)) z) hmem hweak
    intro n z
    have hδ : 0 < t / ((n : ℝ) + 3) := by positivity
    have hδt : t / ((n : ℝ) + 3) < t := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hd : 1 < (n : ℝ) + 3 := by linarith
      exact div_lt_self ht hd
    have hreg := regCovKernel_rotation_of_shfSymmetries
      ϑ P Z hZ hsym hrevL hδ hδt R hdet (R z)
    have hreg' : regCovKernel P Z t (t / ((n : ℝ) + 3)) (R z) =
        regCovKernel P Z t (t / ((n : ℝ) + 3)) z := by
      simpa using hreg
    simp only [covarianceDecayWeight, R.norm_map, hreg']
  have hrotC (R : Plane ≃ₗᵢ[ℝ] Plane)
      (hdet : LinearMap.det (R.toLinearEquiv : Plane →ₗ[ℝ] Plane) = 1) :
      (fun z : Plane => C (R z)) =ᵐ[volume] C := by
    filter_upwards [hrotV R hdet] with z hz
    change v (R z) / covarianceDecayWeight (R z) =
      v z / covarianceDecayWeight z
    rw [hz]
    congr 1
    simp [covarianceDecayWeight, R.norm_map]
  have hCmem : ∀ K : Set Plane, IsCompact K →
      MemLp C 2 (volume.restrict K) := by
    intro K hK
    exact weakLimitCovarianceKernel_memLp_two_on_compact v K hK
  have hCnonneg : ∀ᵐ z : Plane ∂volume, 0 ≤ C z := horder.mono fun z hz => hz.1
  have hCbound : ∀ᵐ z : Plane ∂volume, C z ≤ A * covarianceLogEnvelope z :=
    horder.mono fun z hz => hz.2
  refine ⟨C, hCmem, hCnonneg, hevenC, hrotC, ⟨A, hAnonneg, hCbound⟩, ?_⟩
  intro f g
  exact weakLimitCovarianceKernel_representation_of_flatCovariance
    ϑ P Z hZ hsym hrevL hC12 hcov H hH ht s hs v hmem hweak f g


end Critical2DKPZ.CovarianceKernel

end
