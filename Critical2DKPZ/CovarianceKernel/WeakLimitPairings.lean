/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.WeakLimitKernel
public import Critical2DKPZ.Spectral.BochnerSchwartz

/-! # Test-function pairings of the weak covariance limit -/

@[expose] public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.CovarianceKernel

/-- The covariance pairing with any compactly supported smooth kernel test converges along the
weakly convergent subsequence. The integrability assertions are included explicitly. -/
theorem weakLimitCovarianceKernel_testFnPairing_tendsto_of
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    (hcov : SmallScales.FlatCovarianceAt P Z)
    {t : ℝ} (ht : 0 < t)
    (s : ℕ → ℕ) (v : Lp ℝ 2 (volume : Measure Plane))
    (hmem : ∀ n : ℕ, MemLp (fun z : Plane => covarianceDecayWeight z *
      regCovKernel P Z t (t / ((n : ℝ) + 3)) z) 2 volume)
    (hweak : ∀ g : Lp ℝ 2 (volume : Measure Plane),
      Tendsto (fun n => inner ℝ
        ((hmem (s n)).toLp (fun z : Plane => covarianceDecayWeight z *
          regCovKernel P Z t (t / ((s n : ℝ) + 3)) z)) g)
        atTop (𝓝 (inner ℝ v g)))
    (q : TestFn) :
    Integrable (fun z : Plane => q z * weakLimitCovarianceKernel v z) volume ∧
      (∀ n, Integrable (fun z : Plane => q z *
        regCovKernel P Z t (t / ((s n : ℝ) + 3)) z) volume) ∧
      Tendsto (fun n => ∫ z : Plane, q z *
        regCovKernel P Z t (t / ((s n : ℝ) + 3)) z) atTop
        (𝓝 (∫ z : Plane, q z * weakLimitCovarianceKernel v z)) := by
  let G : Plane → ℝ := fun z => q z * (covarianceDecayWeight z)⁻¹
  have hw : Continuous covarianceDecayWeight := by
    unfold covarianceDecayWeight
    refine Continuous.rpow_const (by fun_prop) fun z => Or.inl ?_
    positivity
  have hGcont : Continuous G := by
    have hinv : Continuous (fun z : Plane => (covarianceDecayWeight z)⁻¹) :=
      hw.inv₀ (fun z => (covarianceDecayWeight_pos z).ne')
    exact q.continuous.mul hinv
  have hGcompact : HasCompactSupport G := by
    change HasCompactSupport (fun z : Plane => q z * (covarianceDecayWeight z)⁻¹)
    exact q.hasCompactSupport.mul_right
  have hGmem : MemLp G 2 volume := hGcont.memLp_of_hasCompactSupport hGcompact
  have hCmem : ∀ K : Set Plane, IsCompact K →
      MemLp (weakLimitCovarianceKernel v) 2 (volume.restrict K) :=
    weakLimitCovarianceKernel_memLp_two_on_compact v
  have hCint : Integrable (fun z : Plane => q z * weakLimitCovarianceKernel v z) volume :=
    Spectral.integrable_testFn_kernel (weakLimitCovarianceKernel v) hCmem q
  have hδpos (n : ℕ) : 0 < t / ((s n : ℝ) + 3) := by positivity
  have hδlt (n : ℕ) : t / ((s n : ℝ) + 3) < t / 2 := by
    have hn0 : (0 : ℝ) ≤ (s n : ℝ) := Nat.cast_nonneg _
    have hden : 0 < (s n : ℝ) + 3 := by positivity
    apply (div_lt_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [ht, hn0]
  have hKmem (n : ℕ) (K : Set Plane) (hK : IsCompact K) :
      MemLp (fun z => regCovKernel P Z t (t / ((s n : ℝ) + 3)) z) 2
        (volume.restrict K) :=
    regCovKernel_memLp_two_on_compact_of_flatCovariance_measurable
      ϑ P Z hZ hsym hrevL hcov ht (hδpos n) (hδlt n) K hK
  have hKint (n : ℕ) : Integrable
      (fun z : Plane => q z * regCovKernel P Z t (t / ((s n : ℝ) + 3)) z) volume :=
    Spectral.integrable_testFn_kernel (fun z => regCovKernel P Z t
      (t / ((s n : ℝ) + 3)) z) (hKmem n) q
  have hleft (n : ℕ) :
      inner ℝ ((hmem (s n)).toLp (fun z : Plane => covarianceDecayWeight z *
        regCovKernel P Z t (t / ((s n : ℝ) + 3)) z)) (hGmem.toLp G) =
        ∫ z : Plane, q z * regCovKernel P Z t (t / ((s n : ℝ) + 3)) z := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    apply integral_congr_ae
    filter_upwards [(hmem (s n)).coeFn_toLp, hGmem.coeFn_toLp] with z h1 h2
    rw [h1, h2]
    dsimp [G]
    have hwpos := covarianceDecayWeight_pos z
    field_simp [hwpos.ne']
  have hright :
      inner ℝ v (hGmem.toLp G) =
        ∫ z : Plane, q z * weakLimitCovarianceKernel v z := by
    rw [L2.inner_def]
    simp only [Real.inner_apply]
    apply integral_congr_ae
    filter_upwards [hGmem.coeFn_toLp] with z hG
    rw [hG]
    dsimp [G, weakLimitCovarianceKernel]
    have hwpos := covarianceDecayWeight_pos z
    field_simp [hwpos.ne']
  refine ⟨hCint, hKint, ?_⟩
  have hlim := hweak (hGmem.toLp G)
  rw [← hright]
  apply hlim.congr'
  filter_upwards [] with n
  exact hleft n

end Critical2DKPZ.CovarianceKernel

end
