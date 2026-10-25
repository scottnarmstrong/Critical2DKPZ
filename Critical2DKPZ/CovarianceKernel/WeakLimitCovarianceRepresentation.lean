/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.WeakLimitKernelBounds
public import Critical2DKPZ.CovarianceKernel.WeakLimitPairings
public import Critical2DKPZ.CovarianceKernel.RegularizedPairingLimit

/-! # Covariance representation by the weak-limit kernel -/

@[expose] public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction ComplexConjugate Topology

namespace Critical2DKPZ.CovarianceKernel

/-- The weakly extracted covariance kernel represents the covariance of every pair of tested
limiting KPZ fields. Integrability of the weak-limit kernel and of the regularized kernels on
compact sets comes from `weakLimitCovarianceKernel_memLp_two_on_compact` and
`regCovKernel_memLp_two_on_compact_of_flatCovariance_measurable`. -/
theorem weakLimitCovarianceKernel_representation_of_flatCovariance
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    (hC12 : LocalSobolev.ToyJointAt ϑ P Z)
    (hcov : SmallScales.FlatCovarianceAt P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t)
    (s : ℕ → ℕ) (hs : StrictMono s) (v : Lp ℝ 2 (volume : Measure Plane))
    (hmem : ∀ n : ℕ, MemLp (fun z : Plane => covarianceDecayWeight z *
      regCovKernel P Z t (t / ((n : ℝ) + 3)) z) 2 volume)
    (hweak : ∀ g : Lp ℝ 2 (volume : Measure Plane),
      Tendsto (fun n => inner ℝ ((hmem (s n)).toLp (fun z : Plane => covarianceDecayWeight z *
        regCovKernel P Z t (t / ((s n : ℝ) + 3)) z)) g)
        atTop (𝓝 (inner ℝ v g)))
    (f g : TestFn) :
    cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] =
      ∫ p : Plane × Plane, f p.1 * g p.2 * weakLimitCovarianceKernel v (p.1 - p.2) := by
  let C : Plane → ℝ := weakLimitCovarianceKernel v
  let q : TestFn := Analysis.Sobolev.testFnConvolution f g
  have hCmem (K : Set Plane) (hK : IsCompact K) :
      MemLp C 2 (volume.restrict K) := by
    exact weakLimitCovarianceKernel_memLp_two_on_compact v K hK
  have hδpos (n : ℕ) : 0 < t / ((s n : ℝ) + 3) := by positivity
  have hδlt (n : ℕ) : t / ((s n : ℝ) + 3) < t / 2 := by
    have hn : (0 : ℝ) ≤ (s n : ℝ) := Nat.cast_nonneg _
    have hd : 0 < (s n : ℝ) + 3 := by positivity
    apply (div_lt_iff₀ hd).2
    nlinarith [ht, hn]
  have hδmem (n : ℕ) (K : Set Plane) (hK : IsCompact K) :
      MemLp (fun z : Plane => regCovKernel P Z t (t / ((s n : ℝ) + 3)) z) 2
        (volume.restrict K) :=
    regCovKernel_memLp_two_on_compact_of_flatCovariance_measurable
      ϑ P Z hZ hsym hrevL hcov ht (hδpos n) (hδlt n) K hK
  have hweakPair := weakLimitCovarianceKernel_testFnPairing_tendsto_of
    ϑ P Z hZ hsym hrevL hcov ht s v hmem hweak q
  have hregPair := regularized_covKernel_pairing_tendsto_of
    ϑ P Z hZ hsym hrevL hC12 H hH ht f g
  have hsAtTop : Tendsto s atTop atTop := hs.tendsto_atTop
  have hregPairSub := hregPair.comp hsAtTop
  have hregPair' : Tendsto (fun n : ℕ => ∫ z : Plane, q z *
      regCovKernel P Z t (t / ((s n : ℝ) + 3)) z) atTop
      (𝓝 (cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P])) := by
    apply hregPairSub.congr'
    filter_upwards [] with n
    exact Spectral.integral_testFnProduct_kernel_eq_integral_testFnConvolution
      (regCovKernel P Z t (t / ((s n : ℝ) + 3))) (hδmem n) f g
  have hlimEq := tendsto_nhds_unique hweakPair.2.2 hregPair'
  calc
    cov[fun ω => H t 0 ω f, fun ω => H t 0 ω g; P] = ∫ z : Plane, q z * C z := hlimEq.symm
    _ = ∫ p : Plane × Plane, f p.1 * g p.2 * C (p.1 - p.2) := by
      symm
      exact Spectral.integral_testFnProduct_kernel_eq_integral_testFnConvolution C hCmem f g

end Critical2DKPZ.CovarianceKernel

end
