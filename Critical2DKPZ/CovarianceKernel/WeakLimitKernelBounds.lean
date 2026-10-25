/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.WeakLimitKernel
public import Critical2DKPZ.CovarianceKernel.WeakLimitOrder

/-! # Order bounds for the weak covariance kernel -/

@[expose] public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace Critical2DKPZ.CovarianceKernel

/-- A weighted weak limit of regularized covariance kernels remains nonnegative and bounded by the logarithmic envelope. -/
theorem weakLimitCovarianceKernel_order_bounds_of_flatCovariance
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hcov : SmallScales.FlatCovarianceAt P Z) {t : ℝ} (ht : 0 < t)
    (s : ℕ → ℕ) (v : Lp ℝ 2 (volume : Measure Plane))
    (hmem : ∀ n : ℕ, MemLp (fun z : Plane => covarianceDecayWeight z *
      regCovKernel P Z t (t / ((n : ℝ) + 3)) z) 2 volume)
    (hweak : ∀ g : Lp ℝ 2 (volume : Measure Plane),
      Tendsto (fun n => inner ℝ ((hmem (s n)).toLp (fun z : Plane => covarianceDecayWeight z *
        regCovKernel P Z t (t / ((s n : ℝ) + 3)) z)) g)
        atTop (𝓝 (inner ℝ v g))) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ z : Plane, 0 ≤ weakLimitCovarianceKernel v z ∧
      weakLimitCovarianceKernel v z ≤ A * covarianceLogEnvelope z := by
  let δn : ℕ → ℝ := fun n => t / ((s n : ℝ) + 3)
  let F : ℕ → Plane → ℝ := fun n z => covarianceDecayWeight z * regCovKernel P Z t (δn n) z
  let U : ℕ → Lp ℝ 2 (volume : Measure Plane) := fun n => (hmem (s n)).toLp (F n)
  let Gfun : Plane → ℝ := fun z => covarianceDecayWeight z * covarianceLogEnvelope z
  have hGmem : MemLp Gfun 2 volume := by
    simpa [Gfun] using covarianceDecayWeight_mul_covarianceLogEnvelope_memLp_two
  let G : Lp ℝ 2 (volume : Measure Plane) := hGmem.toLp Gfun
  obtain ⟨A, hAnonneg⟩ := regCovKernel_le_of_flatCovariance P Z hcov ht
  let z₀ : Plane := EuclideanSpace.single 0 (1 : ℝ)
  have hz₀ : z₀ ≠ 0 := by
    intro h
    have h0 := congrArg (fun z : Plane => z 0) h
    simp [z₀] at h0
  let δ₀ : ℝ := t / 4
  have hδ₀ : 0 < δ₀ := by dsimp [δ₀]; positivity
  have hδ₀t : δ₀ < t / 2 := by dsimp [δ₀]; linarith
  have hA₀ : regCovKernel P Z t δ₀ z₀ ≤ A * covarianceLogEnvelope z₀ := by
    simpa [covarianceLogEnvelope] using hAnonneg δ₀ hδ₀ hδ₀t z₀ hz₀
  have hnonneg₀ : 0 ≤ regCovKernel P Z t δ₀ z₀ :=
    regCovKernel_nonneg_of_flatCovariance P Z hcov ht hδ₀ hδ₀t z₀ hz₀
  have hAnonneg' : 0 ≤ A := by
    by_contra h
    have hAneg : A < 0 := lt_of_not_ge h
    have hGpos : 0 < covarianceLogEnvelope z₀ := covarianceLogEnvelope_pos z₀
    have hprod : A * covarianceLogEnvelope z₀ < 0 := mul_neg_of_neg_of_pos hAneg hGpos
    linarith
  have hδpos (n : ℕ) : 0 < δn n := by dsimp [δn]; positivity
  have hδlt (n : ℕ) : δn n < t / 2 := by
    dsimp [δn]
    have hn : (0 : ℝ) ≤ (s n : ℝ) := Nat.cast_nonneg _
    have hd : 0 < (s n : ℝ) + 3 := by positivity
    apply (div_lt_iff₀ hd).2
    nlinarith [ht, hn]
  have hUAE (n : ℕ) : ∀ᵐ z : Plane ∂volume, U n z = F n z := by
    dsimp [U, F, δn]
    exact (hmem (s n)).coeFn_toLp
  have hUseq_nonneg : ∀ n, ∀ᵐ z : Plane ∂volume, 0 ≤ U n z := by
    intro n
    filter_upwards [hUAE n, volume.ae_ne (0 : Plane)] with z hUz hz
    rw [hUz]
    exact mul_nonneg (covarianceDecayWeight_pos z).le
      (regCovKernel_nonneg_of_flatCovariance P Z hcov ht (hδpos n) (hδlt n) z hz)
  have hUseq_upper : ∀ n, ∀ᵐ z : Plane ∂volume,
      0 ≤ (A • G - U n) z := by
    intro n
    filter_upwards [Lp.coeFn_sub (A • G) (U n), Lp.coeFn_smul A G,
      hGmem.coeFn_toLp, hUAE n, volume.ae_ne (0 : Plane)] with z hsub hsmul hG hU hz
    have hupper := hAnonneg (δn n) (hδpos n) (hδlt n) z hz
    have hupper' : regCovKernel P Z t (δn n) z ≤ A * covarianceLogEnvelope z := by
      simpa [covarianceLogEnvelope] using hupper
    have hprod : covarianceDecayWeight z * regCovKernel P Z t (δn n) z ≤
        A * (covarianceDecayWeight z * covarianceLogEnvelope z) := by
      calc
        covarianceDecayWeight z * regCovKernel P Z t (δn n) z ≤
            covarianceDecayWeight z * (A * covarianceLogEnvelope z) :=
          mul_le_mul_of_nonneg_left hupper' (covarianceDecayWeight_pos z).le
        _ = A * (covarianceDecayWeight z * covarianceLogEnvelope z) := by ring
    rw [hsub]
    change 0 ≤ (A • G) z - U n z
    rw [hsmul]
    change 0 ≤ A * G z - U n z
    rw [hG, hU]
    change 0 ≤ A * (covarianceDecayWeight z * covarianceLogEnvelope z) -
      (covarianceDecayWeight z * regCovKernel P Z t (δn n) z)
    exact sub_nonneg.mpr hprod
  have hvnonneg : ∀ᵐ z : Plane ∂volume, 0 ≤ v z :=
    ae_nonneg_of_weak_L2_inner_tendsto U v (by simpa [U, F, δn] using hweak) hUseq_nonneg
  have hupperWeak : ∀ g : Lp ℝ 2 (volume : Measure Plane),
      Tendsto (fun n => inner ℝ (A • G - U n) g) atTop
        (𝓝 (inner ℝ (A • G - v) g)) := by
    intro g
    have hconst : Tendsto (fun _ : ℕ => A * inner ℝ G g) atTop
        (𝓝 (A * inner ℝ G g)) := tendsto_const_nhds
    have hlim := hconst.sub (hweak g)
    have hleft (n : ℕ) : inner ℝ (A • G - U n) g =
        A * inner ℝ G g - inner ℝ (U n) g := by
      simp [inner_sub_left, inner_smul_left]
    have hright : inner ℝ (A • G - v) g = A * inner ℝ G g - inner ℝ v g := by
      simp [inner_sub_left, inner_smul_left]
    rw [hright]
    apply hlim.congr'
    filter_upwards [] with n
    exact (hleft n).symm
  have huppernonneg : ∀ᵐ z : Plane ∂volume, 0 ≤ (A • G - v) z :=
    ae_nonneg_of_weak_L2_inner_tendsto (fun n => A • G - U n) (A • G - v)
      hupperWeak hUseq_upper
  refine ⟨A, hAnonneg', ?_⟩
  filter_upwards [hvnonneg, huppernonneg, Lp.coeFn_sub (A • G) v,
    Lp.coeFn_smul A G, hGmem.coeFn_toLp] with z hv hu hsub hsmul hG
  constructor
  · change 0 ≤ v z / covarianceDecayWeight z
    exact div_nonneg hv (covarianceDecayWeight_pos z).le
  · change v z / covarianceDecayWeight z ≤ A * covarianceLogEnvelope z
    have huv : v z ≤ A * (covarianceDecayWeight z * covarianceLogEnvelope z) := by
      change 0 ≤ (A • G - v) z at hu
      rw [hsub] at hu
      change 0 ≤ (A • G) z - v z at hu
      rw [hsmul] at hu
      change 0 ≤ A * G z - v z at hu
      rw [hG] at hu
      exact sub_nonneg.mp hu
    apply (div_le_iff₀ (covarianceDecayWeight_pos z)).2
    calc
      v z ≤ A * (covarianceDecayWeight z * covarianceLogEnvelope z) := huv
      _ = (A * covarianceLogEnvelope z) * covarianceDecayWeight z := by ring

end Critical2DKPZ.CovarianceKernel

end
