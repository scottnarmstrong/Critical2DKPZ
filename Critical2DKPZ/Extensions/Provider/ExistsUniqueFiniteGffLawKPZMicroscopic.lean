/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.Assembly
public import Critical2DKPZ.Extensions.GffTangent.FiniteGaussian
import Critical2DKPZ.Extensions.ScaleLimit.SlutskyTools
import Critical2DKPZ.Extensions.Common.Canonical

/-!
# Theorem D: the Gaussian free field tangent

Ultraviolet removal and the linear Gaussian limit give the microscopic
finite-dimensional GFF limit on zero-integral tests, including degenerate
Gaussian laws. Rescaling identifies the limit for every associated KPZ field.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.Provider

universe u

private theorem tendstoInDistribution_of_eventually_map_eq
    {ι Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {l : Filter ι} {X Y : ι → Ω → E} {ν : Measure E} [IsProbabilityMeasure ν]
    (hY : TendstoInDistribution Y l id (fun _ => P) ν)
    (hX : ∀ i, AEMeasurable (X i) P)
    (hlaw : ∀ᶠ i in l, P.map (X i) = P.map (Y i)) :
    TendstoInDistribution X l id (fun _ => P) ν := by
  refine ⟨hX, aemeasurable_id, ?_⟩
  apply hY.tendsto.congr'
  filter_upwards [hlaw] with i hi
  exact ProbabilityMeasure.toMeasure_injective hi.symm

/-- **Theorem D** (the finite-dimensional Gaussian free field tangent). -/
theorem existsUnique_finiteGffLaw_and_kpz_microscopic_tendstoInDistribution (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (t : ℝ) (ht : 0 < t) (x : Plane) (n : ℕ) (f : Fin n → TestFn)
    (hf : ∀ i, (∫ y : Plane, f i y) = 0) :
    ∃! μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)),
      IsFiniteGffLaw f μ ∧
      TendstoInDistribution
        (fun (ε : ℝ) (ω : Ω) => WithLp.toLp 2
          (fun i : Fin n => Real.sqrt (Real.log ε⁻¹) * H t 0 ω ((f i).dilate ε x)))
        (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P) (μ : Measure _) := by
  obtain ⟨ν, hν, hνuniq⟩ :=
    Critical2DKPZ.Extensions.GffTangent.existsUnique_isFiniteGffLaw f hf
  refine ⟨ν, ⟨hν, ?_⟩, ?_⟩
  · let c : ℝ := t * Real.exp ϑ
    have hc : 0 < c := mul_pos ht (Real.exp_pos _)
    let l : ℝ → ℝ := Critical2DKPZ.Extensions.GffTangent.microscopicParameter ϑ
    let Zl : ℝ → ℝ → ℝ → Ω → Measure (Plane × Plane) :=
      fun r => Critical2DKPZ.Extensions.GffTangent.gffScaledFlow ϑ Z r
    have hZl : ∀ r, IsCriticalSHF (-r) P (Zl r) := fun r =>
      Critical2DKPZ.Extensions.GffTangent.gffScaledFlow_critical ϑ P Z hZ r
    let K : ℝ → Ω → EuclideanSpace ℝ (Fin n) := fun r ω => WithLp.toLp 2
      (fun i => Real.sqrt (r / 2) *
        Critical2DKPZ.Extensions.GffTangent.kField (-r) P (Zl r) (hZl r)
          (c * Real.exp r) (mul_pos hc (Real.exp_pos r)) (f i) ω)
    have hKtop : TendstoInDistribution K atTop id (fun _ => P) (ν : Measure _) := by
      simpa only [K, Zl] using
        (Critical2DKPZ.Extensions.GffTangent.target_gff
          hc P Zl hZl f hf ν hν)
    have hKmeas (r : ℝ) : AEMeasurable (K r) P := by
      apply (WithLp.measurable_toLp 2 (Fin n → ℝ)).comp_aemeasurable
      apply aemeasurable_pi_iff.mpr
      intro i
      exact (Critical2DKPZ.Extensions.GffTangent.kField_aemeasurable
        (-r) P (Zl r) (hZl r) (c * Real.exp r)
          (mul_pos hc (Real.exp_pos r)) (f i)).const_mul _
    have hKsmall : TendstoInDistribution (fun ε => K (l ε)) (𝓝[>] 0) id
        (fun _ => P) (ν : Measure _) := by
      refine ⟨fun ε => hKmeas (l ε), hKtop.aemeasurable_limit, ?_⟩
      exact hKtop.tendsto.comp
        (Critical2DKPZ.Extensions.GffTangent.microscopicParameter_tendsto ϑ)
    let q : ℝ → ℝ := fun ε => Real.sqrt (Real.log ε⁻¹) / Real.sqrt (l ε / 2)
    have hq : Tendsto q (𝓝[>] 0) (𝓝 1) := by
      exact Critical2DKPZ.Extensions.GffTangent.microscopic_normalization_tendsto ϑ
    have hqP : TendstoInMeasure P (fun ε (_ : Ω) => q ε) (𝓝[>] 0)
        (fun _ => (1 : ℝ)) :=
      Critical2DKPZ.Extensions.ScaleLimit.tendstoInMeasure_const_of_tendsto P hq
    have hscaled := hKsmall.continuous_comp_prodMk_of_tendstoInMeasure_const
      (g := fun p : EuclideanSpace ℝ (Fin n) × ℝ => p.2 • p.1)
      (by fun_prop) hqP (fun _ => aemeasurable_const)
    have hscaled' : TendstoInDistribution (fun ε ω => q ε • K (l ε) ω)
        (𝓝[>] 0) id (fun _ => P) (ν : Measure _) := by
      apply TendstoInDistribution.congr (fun _ => EventuallyEq.rfl) ?_ hscaled
      exact Eventually.of_forall fun ω => one_smul ℝ ω
    let X : ℝ → Ω → EuclideanSpace ℝ (Fin n) := fun ε ω => WithLp.toLp 2
      (fun i => Real.sqrt (Real.log ε⁻¹) * H t 0 ω ((f i).dilate ε x))
    have hXmeas (ε : ℝ) : AEMeasurable (X ε) P :=
      Critical2DKPZ.Extensions.GffTangent.microscopic_vector_aemeasurable
        ϑ P Z hZ H hH t ht ε x n f
    apply tendstoInDistribution_of_eventually_map_eq hscaled' hXmeas
    have hlpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < l ε :=
      (Critical2DKPZ.Extensions.GffTangent.microscopicParameter_tendsto ϑ).eventually_gt_atTop 0
    filter_upwards [self_mem_nhdsWithin, hlpos] with ε hε hlε
    have hεpos : 0 < ε := hε
    have hsqrt : Real.sqrt (l ε / 2) ≠ 0 := by positivity
    have hnorm : q ε * Real.sqrt (l ε / 2) = Real.sqrt (Real.log ε⁻¹) := by
      dsimp [q]
      exact div_mul_cancel₀ _ hsqrt
    have htime := Critical2DKPZ.Extensions.GffTangent.microscopic_horizon_eq ϑ t hεpos
    have hraw := Critical2DKPZ.Extensions.GffTangent.reduction_law_eq
      ϑ P Z hZ H hH t ht hεpos x n f
    let scale : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n) := fun v =>
      WithLp.toLp 2 (fun i => Real.sqrt (Real.log ε⁻¹) * v i)
    have hscale : Measurable scale := by fun_prop
    have hleft : P.map (X ε) = (P.map (fun ω i => H t 0 ω ((f i).dilate ε x))).map scale := by
      let U : Ω → Fin n → ℝ := fun ω i => H t 0 ω ((f i).dilate ε x)
      have hU : AEMeasurable U P := aemeasurable_pi_iff.mpr fun i =>
        Common.aemeasurable_pairing_of_isCriticalKPZ ϑ P Z hZ H hH t ht 0
          ((f i).dilate ε x)
      change P.map (scale ∘ U) = (P.map U).map scale
      exact (hscale.aemeasurable.map_map_of_aemeasurable hU).symm
    have hright : P.map (fun ω => q ε • K (l ε) ω) =
        (P.map (fun ω i => Critical2DKPZ.Extensions.GffTangent.kField
          (-(l ε)) P (Zl (l ε)) (hZl (l ε)) (t / ε ^ 2)
          (div_pos ht (pow_pos hεpos 2)) (f i) ω)).map scale := by
      let V : Ω → Fin n → ℝ := fun ω i => Critical2DKPZ.Extensions.GffTangent.kField
        (-(l ε)) P (Zl (l ε)) (hZl (l ε)) (t / ε ^ 2)
        (div_pos ht (pow_pos hεpos 2)) (f i) ω
      have hV : AEMeasurable V P := aemeasurable_pi_iff.mpr fun i =>
        Critical2DKPZ.Extensions.GffTangent.kField_aemeasurable
          (-(l ε)) P (Zl (l ε)) (hZl (l ε)) (t / ε ^ 2)
            (div_pos ht (pow_pos hεpos 2)) (f i)
      have heq : (fun ω => q ε • K (l ε) ω) = scale ∘ V := by
        funext ω
        ext i
        simp only [K, scale, Function.comp_def, V, PiLp.smul_apply, smul_eq_mul]
        simp only [htime]
        rw [← mul_assoc, hnorm]
      rw [heq]
      exact (hscale.aemeasurable.map_map_of_aemeasurable hV).symm
    rw [hleft, hright]
    exact congrArg (Measure.map scale) hraw
  · intro μ hμ
    exact Critical2DKPZ.Extensions.GffTangent.isFiniteGffLaw_unique hμ.1 hν

end Critical2DKPZ.Extensions.Provider
