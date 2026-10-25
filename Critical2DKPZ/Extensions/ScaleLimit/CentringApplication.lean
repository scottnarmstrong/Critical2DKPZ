/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockErrorConvergence
public import Critical2DKPZ.Extensions.ScaleLimit.BlockVariance
public import Critical2DKPZ.Extensions.ScaleLimit.GeometricField
import Critical2DKPZ.Extensions.ScaleLimit.CentringLemma
import Critical2DKPZ.Extensions.ScaleLimit.ProbabilityZeroTools
import Critical2DKPZ.Extensions.Response.SpatialShift
import Mathlib.Tactic

/-! # Identification of the block variance and centring

The centring lemma is applied to the shifted positive-index block sequence,
the integrable field with initial value zero, and the positive clock
`sqrt (1 + log n)`. Eventual equality and asymptotic scalar factors restore
the formulas in the note.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The scalar CLT identifies the asymptotic variance and centring of the
independent logarithmic block sums. -/
theorem centring_application (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ →
      Tendsto (fun n : ℕ => variance (partialSum Z ρ n) P / Real.log n) atTop (𝓝 1) ∧
      TendstoInMeasure P (fun n ω =>
        ((Fheat Z (tau ρ n) 0 ω - ∫ ω', Fheat Z (tau ρ n) 0 ω' ∂P) -
          (partialSum Z ρ n ω - ∫ ω', partialSum Z ρ n ω' ∂P)) / Real.sqrt (Real.log n))
        atTop (fun _ => 0) := by
  obtain ⟨ρ₀, hρ₀, hE⟩ := block_oP_log ϑ P Z hZ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  let Y : ℕ → Ω → ℝ := fun j => logTrunc Z ρ (j + 1)
  have hsum (n : ℕ) : partialSumRange Y n = partialSum Z ρ n := by
    funext ω
    exact sum_range_add_one_eq_sum_Icc (fun j => logTrunc Z ρ j ω) n
  have hm (j : ℕ) : AEMeasurable (Y j) P := (measurable_logTrunc ϑ P Z hZ hρ1 j).aemeasurable
  have hb (j : ℕ) : ∀ᵐ ω ∂P, |Y j ω| ≤ Real.log 2 :=
    Filter.Eventually.of_forall (abs_logTrunc_le Z ρ (j + 1))
  obtain ⟨CV, _hCV0, hV⟩ := variance_partialSum_le ϑ P Z hZ hρ1
  have hvariance (n : ℕ) : variance (partialSumRange Y n) P ≤ CV * geometricNormalizer n ^ 2 := by
    rw [hsum, geometricNormalizer_sq]
    exact hV n
  have herrorS : TendstoInMeasure P (fun n ω =>
      (geometricField Z ρ n ω - partialSum Z ρ n ω) / geometricNormalizer n) atTop (fun _ => 0) := by
    apply (hE ρ hρ).congr' _ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [] with ω
    rw [geometricField_of_pos Z ρ (by omega : 0 < n)]
    rfl
  have herror : TendstoInMeasure P (fun n ω =>
      (geometricField Z ρ n ω - partialSumRange Y n ω) / geometricNormalizer n) atTop (fun _ => 0) := by
    simpa only [hsum] using herrorS
  have hc := centring_range P Y (iIndepFun_logTrunc ϑ P Z hZ hρ1) hm
    (Real.log 2) hb geometricNormalizer geometricNormalizer_tendsto_atTop CV hvariance
    (geometricField Z ρ) (integrable_geometricField ϑ P Z hZ hρ1) herror
    (scalar_clt_geometric_regular ϑ P Z hZ hρ1)
  have hv : Tendsto (fun n => variance (partialSum Z ρ n) P / geometricNormalizer n ^ 2)
      atTop (𝓝 1) := by simpa only [hsum] using hc.1
  have hd : Tendsto (fun n => ((∫ ω, geometricField Z ρ n ω ∂P) -
      ∫ ω, partialSum Z ρ n ω ∂P) / geometricNormalizer n) atTop (𝓝 0) := by
    simpa only [hsum] using hc.2
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun n : ℕ => geometricNormalizer n / Real.sqrt (Real.log n))
      atTop (𝓝 1) := by
    simpa only [geometricNormalizer, add_comm] using
      tendsto_sqrt_add_div_sqrt (fun n : ℕ => Real.log n) hlog 1
  have hv' : Tendsto (fun n => (variance (partialSum Z ρ n) P / geometricNormalizer n ^ 2) *
      (geometricNormalizer n / Real.sqrt (Real.log n)) ^ 2) atTop (𝓝 1) := by
    simpa only [one_pow, mul_one] using hv.mul (hr.pow 2)
  have hvfinal : Tendsto (fun n : ℕ => variance (partialSum Z ρ n) P / Real.log n) atTop (𝓝 1) := by
    apply hv'.congr'
    filter_upwards [eventually_ge_atTop 2] with n hn
    have ha := (geometricNormalizer_pos n).ne'
    have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hs := (Real.sqrt_pos.mpr hlogpos).ne'
    rw [div_pow, Real.sq_sqrt hlogpos.le]
    field_simp [ha, hlogpos.ne']
  have hdc := tendstoInMeasure_const_of_tendsto P hd
  have hsub := Response.tendstoInMeasure_sub P herrorS hdc
  have hcenter : TendstoInMeasure P (fun n ω =>
      ((geometricField Z ρ n ω - ∫ ω', geometricField Z ρ n ω' ∂P) -
        (partialSum Z ρ n ω - ∫ ω', partialSum Z ρ n ω' ∂P)) / geometricNormalizer n)
      atTop (fun _ => 0) := by
    apply hsub.congr _ _
    · intro n
      filter_upwards [] with ω
      ring
    · filter_upwards [] with ω
      simp
  have hscaled := tendstoInMeasure_mul_constSeq_zero P hcenter hr
  have hfinal : TendstoInMeasure P (fun n ω =>
      ((Fheat Z (tau ρ n) 0 ω - ∫ ω', Fheat Z (tau ρ n) 0 ω' ∂P) -
        (partialSum Z ρ n ω - ∫ ω', partialSum Z ρ n ω' ∂P)) / Real.sqrt (Real.log n))
      atTop (fun _ => 0) := by
    apply hscaled.congr' _ Filter.EventuallyEq.rfl
    filter_upwards [eventually_ge_atTop 2] with n hn
    filter_upwards [] with ω
    have hn0 : 0 < n := by omega
    have ha := (geometricNormalizer_pos n).ne'
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hs := (Real.sqrt_pos.mpr hlogpos).ne'
    simp only [geometricField_of_pos Z ρ hn0]
    field_simp [ha, hs]
  exact ⟨hvfinal, hfinal⟩

end Critical2DKPZ.Extensions.ScaleLimit
