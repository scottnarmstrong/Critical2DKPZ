/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.CovarianceKernel.RegularizedBounds
public import Critical2DKPZ.CovarianceKernel.WeightedCompactness
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.UniformSpace.Cauchy

/-! # A weakly convergent subsequence of localized covariance kernels -/

@[expose] public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace Critical2DKPZ.CovarianceKernel

private instance instLpProbabilityExponentOneLe : Fact (1 ≤ (2 : ℝ≥0∞)) :=
  ⟨by norm_num⟩

private instance instLpProbabilityExponentNeTop : Fact ((2 : ℝ≥0∞) ≠ ∞) :=
  ⟨by simp⟩

private instance instPlaneCountablyGenerated : MeasurableSpace.CountablyGenerated Plane :=
  inferInstance

private instance instPlaneVolumeSeparable : MeasureTheory.IsSeparable (volume : Measure Plane) :=
  inferInstance

/-- The localized regularized covariance kernels are uniformly bounded in global `L²`. -/
theorem weighted_regCovKernel_memLp_norm_le_of_flatCovariance
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    (hcov : SmallScales.FlatCovarianceAt P Z)
    {t : ℝ} (ht : 0 < t) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ δ : ℝ, 0 < δ → δ < t / 2 →
      ∃ hF : MemLp (fun z => covarianceDecayWeight z * regCovKernel P Z t δ z) 2 volume,
        ‖hF.toLp (fun z => covarianceDecayWeight z * regCovKernel P Z t δ z)‖ ≤
          A * ‖covarianceDecayWeight_mul_covarianceLogEnvelope_memLp_two.toLp
            (fun z => covarianceDecayWeight z * covarianceLogEnvelope z)‖ := by
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
  have hAnonneg : 0 ≤ A := by
    by_contra h
    have hAn : A < 0 := lt_of_not_ge h
    have hprod : A * covarianceLogEnvelope z₀ < 0 :=
      mul_neg_of_neg_of_pos hAn (covarianceLogEnvelope_pos z₀)
    linarith
  refine ⟨A, hAnonneg, fun δ hδ hδt => ?_⟩
  let F : Plane → ℝ := fun z => covarianceDecayWeight z * regCovKernel P Z t δ z
  let G : Plane → ℝ := fun z => covarianceDecayWeight z * covarianceLogEnvelope z
  have hGmem : MemLp G 2 volume := by
    simpa [G] using covarianceDecayWeight_mul_covarianceLogEnvelope_memLp_two
  have hGpositive (z : Plane) : 0 < G z :=
    mul_pos (covarianceDecayWeight_pos z) (covarianceLogEnvelope_pos z)
  have hFstrong : AEStronglyMeasurable F volume := by
    have hweight : Measurable covarianceDecayWeight := by
      fun_prop [covarianceDecayWeight]
    have hkernel : AEMeasurable (fun z => regCovKernel P Z t δ z) volume :=
      regCovKernel_aemeasurable_of ϑ P Z hZ hsym hrevL hδ
        (lt_trans hδt (half_lt_self ht))
    exact (hweight.aemeasurable.mul hkernel).aestronglyMeasurable
  have hFbound : ∀ᵐ z ∂volume, ‖F z‖ ≤ A * ‖G z‖ := by
    filter_upwards [volume.ae_ne (0 : Plane)] with z hz
    have hnonneg := regCovKernel_nonneg_of_flatCovariance P Z hcov ht hδ hδt z hz
    have hupper := hA δ hδ hδt z hz
    have hprod : 0 ≤ covarianceDecayWeight z * regCovKernel P Z t δ z :=
      mul_nonneg (covarianceDecayWeight_pos z).le hnonneg
    have hGnorm : ‖G z‖ = G z := Real.norm_of_nonneg (hGpositive z).le
    have hFnorm : ‖F z‖ = F z := Real.norm_of_nonneg hprod
    change ‖covarianceDecayWeight z * regCovKernel P Z t δ z‖ ≤
      A * ‖covarianceDecayWeight z * covarianceLogEnvelope z‖
    rw [hFnorm, hGnorm]
    calc
      covarianceDecayWeight z * regCovKernel P Z t δ z ≤
          covarianceDecayWeight z * (A * covarianceLogEnvelope z) :=
        mul_le_mul_of_nonneg_left hupper (covarianceDecayWeight_pos z).le
      _ = A * (covarianceDecayWeight z * covarianceLogEnvelope z) := by ring
  have hFmem : MemLp F 2 volume := by
    apply MemLp.of_le_mul hGmem hFstrong
    filter_upwards [hFbound] with z hz
    exact hz
  refine ⟨hFmem, ?_⟩
  have hLpbound : ∀ᵐ z ∂volume,
      ‖(hFmem.toLp F) z‖ ≤ A * ‖(hGmem.toLp G) z‖ := by
    filter_upwards [hFmem.coeFn_toLp, hGmem.coeFn_toLp, hFbound] with z hFz hGz hz
    rw [hFz, hGz]
    exact hz
  have hnorm : ‖hFmem.toLp F‖ ≤ A * ‖hGmem.toLp G‖ :=
    Lp.norm_le_mul_norm_of_ae_le_mul hLpbound
  simpa [F, G] using hnorm

/-- After multiplication by a fixed polynomial decay weight, a sequence of regularized covariance kernels has a weakly convergent `L²` subsequence. -/
theorem exists_weak_subseq_weighted_regCovKernel_of_flatCovariance
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : LocalSobolev.ShfSymmetriesAt ϑ P Z)
    (hrevL : SmallScales.ShfReversalLawAt P Z)
    (hcov : SmallScales.FlatCovarianceAt P Z)
    {t : ℝ} (ht : 0 < t) :
    let δn : ℕ → ℝ := fun n => t / ((n : ℝ) + 3)
    let Fn : ℕ → Plane → ℝ := fun n z => covarianceDecayWeight z *
      regCovKernel P Z t (δn n) z
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ v : Lp ℝ 2 volume,
      ∃ hmem : ∀ n, MemLp (Fn n) 2 volume, ∀ g : Lp ℝ 2 volume,
        Tendsto (fun n => inner ℝ ((hmem (s n)).toLp (Fn (s n))) g)
          atTop (𝓝 (inner ℝ v g)) := by
  dsimp
  let δn : ℕ → ℝ := fun n => t / ((n : ℝ) + 3)
  let Fn : ℕ → Plane → ℝ := fun n z => covarianceDecayWeight z *
    regCovKernel P Z t (δn n) z
  have hδpos (n : ℕ) : 0 < δn n := by
    dsimp [δn]
    positivity
  have hδlt (n : ℕ) : δn n < t / 2 := by
    dsimp [δn]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hden : 0 < (n : ℝ) + 3 := by positivity
    apply (div_lt_iff₀ hden).2
    nlinarith [ht, hn0]
  obtain ⟨A, hAnonneg, hbound⟩ :=
    weighted_regCovKernel_memLp_norm_le_of_flatCovariance ϑ P Z hZ hsym hrevL hcov ht
  have hmem (n : ℕ) : MemLp (Fn n) 2 volume := by
    simpa [Fn, δn] using (hbound (δn n) (hδpos n) (hδlt n)).1
  let G : Plane → ℝ := fun z => covarianceDecayWeight z * covarianceLogEnvelope z
  let hG : MemLp G 2 volume := by
    simpa [G] using covarianceDecayWeight_mul_covarianceLogEnvelope_memLp_two
  have hnorm (n : ℕ) : ‖(hmem n).toLp (Fn n)‖ ≤
      A * ‖hG.toLp G‖ := by
    have hn := (hbound (δn n) (hδpos n) (hδlt n)).2
    simpa [Fn, δn, G, hG] using hn
  have hB : 0 ≤ A * ‖hG.toLp G‖ := mul_nonneg hAnonneg (norm_nonneg _)
  obtain ⟨s, hs, v, hv⟩ := exists_strictMono_subseq_L2_inner_tendsto_of_norm_le
    Fn hmem (A * ‖hG.toLp G‖) hB hnorm
  refine ⟨s, hs, v, hmem, fun g => ?_⟩
  simpa [Fn, δn] using hv g

end Critical2DKPZ.CovarianceKernel

end
