/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.HeatStartSpatialAverage
public import Critical2DKPZ.SmallScales.ShrinkingMomentLowerBound
public import Critical2DKPZ.SmallScales.DeterministicComparison
public import Critical2DKPZ.Smoothing.ProfileL2Perturbation
public import Critical2DKPZ.Smoothing.SpatialL2
public import Critical2DKPZ.SHF.Positivity.HeatStartLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Bases
import Mathlib.Tactic

/-! # Shrinking-test variance from heat-start comparison bounds -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open Critical2DKPZ.SHF.Positivity
open scoped BoundedContinuousFunction CompactlySupported Distributions ENNReal Topology

universe u

namespace Critical2DKPZ.SmallScales

private theorem toReal_eLpNorm_two_eq_sqrt_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {f : Ω → ℝ}
    (hf : MemLp f 2 P) :
    (eLpNorm f 2 P).toReal = Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
  have hnormPow :
      (∫ ω, ‖f ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂P) ^
          (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ = (eLpNorm f 2 P).toReal := by
    rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    have hnonneg :
        0 ≤ (∫ ω, ‖f ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂P) ^
          (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := by positivity
    exact (ENNReal.toReal_ofReal hnonneg).symm
  have hsq :
      ∫ ω, ‖f ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂P = ∫ ω, f ω ^ 2 ∂P := by
    simp [ENNReal.toReal_ofNat, Real.norm_eq_abs, sq_abs]
  calc
    (eLpNorm f 2 P).toReal =
        (∫ ω, ‖f ω‖ ^ ENNReal.toReal (2 : ℝ≥0∞) ∂P) ^
          (ENNReal.toReal (2 : ℝ≥0∞))⁻¹ := hnormPow.symm
    _ = Real.sqrt (∫ ω, f ω ^ 2 ∂P) := by
      rw [hsq, Real.sqrt_eq_rpow]
      congr 1
      norm_num [ENNReal.toReal_ofNat]

private theorem heatKernel_le_two_mul_heatKernel {δ : ℝ} (hδ : 0 < δ)
    {y q u : Plane} (hyq : ‖y - q‖ ≤ 1) :
    heatKernel δ (u - y) ≤
      2 * Real.exp (1 / (2 * δ)) * heatKernel (2 * δ) (u - q) := by
  rw [heatKernel_eq_exp, heatKernel_eq_exp]
  have hcoef : (2 * Real.pi * δ)⁻¹ = 2 * (2 * Real.pi * (2 * δ))⁻¹ := by
    field_simp
  have hquad :
      -((2 * δ)⁻¹) * ‖u - y‖ ^ 2 + ((2 * (2 * δ))⁻¹) * ‖u - q‖ ^ 2 ≤
        1 / (2 * δ) := by
    have hplus := norm_add_sq_real (u - y) (y - q)
    have hminus := norm_sub_sq_real (u - y) (y - q)
    have hnorm : ‖u - q‖ ^ 2 = ‖(u - y) + (y - q)‖ ^ 2 := by
      congr 1
      abel_nf
    rw [hnorm]
    apply le_of_mul_le_mul_right ?_ (by positivity : 0 < 4 * δ)
    calc
      (-((2 * δ)⁻¹) * ‖u - y‖ ^ 2 +
          ((2 * (2 * δ))⁻¹) * ‖(u - y) + (y - q)‖ ^ 2) * (4 * δ) =
          -‖u - y‖ ^ 2 * 2 + ‖(u - y) + (y - q)‖ ^ 2 := by
            field_simp
            ring
      _ ≤ 2 := by
        have hnorm' : ‖y - q‖ ^ 2 ≤ 1 := by
          nlinarith [sq_nonneg (‖y - q‖), norm_nonneg (y - q)]
        have hidentity :
            -2 * ‖u - y‖ ^ 2 + ‖(u - y) + (y - q)‖ ^ 2 =
              -‖(u - y) - (y - q)‖ ^ 2 + 2 * ‖y - q‖ ^ 2 := by
          rw [hplus, hminus]
          ring
        calc
          _ = -2 * ‖u - y‖ ^ 2 + ‖(u - y) + (y - q)‖ ^ 2 := by ring
          _ = -‖(u - y) - (y - q)‖ ^ 2 + 2 * ‖y - q‖ ^ 2 := hidentity
          _ ≤ 2 := by nlinarith [sq_nonneg (‖(u - y) - (y - q)‖)]
      _ = (1 / (2 * δ)) * (4 * δ) := by field_simp; ring
  have hexp :
      Real.exp (-((2 * δ)⁻¹) * ‖u - y‖ ^ 2) ≤
        Real.exp (1 / (2 * δ)) *
          Real.exp (-((2 * (2 * δ))⁻¹) * ‖u - q‖ ^ 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  rw [hcoef]
  calc
    2 * (2 * Real.pi * (2 * δ))⁻¹ *
        Real.exp (-((2 * δ)⁻¹) * ‖u - y‖ ^ 2) ≤
        2 * (2 * Real.pi * (2 * δ))⁻¹ *
          (Real.exp (1 / (2 * δ)) *
            Real.exp (-((2 * (2 * δ))⁻¹) * ‖u - q‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = 2 * Real.exp (1 / (2 * δ)) *
        ((2 * Real.pi * (2 * δ))⁻¹ *
          Real.exp (-((2 * (2 * δ))⁻¹) * ‖u - q‖ ^ 2)) := by ring

private theorem measure_univ_pos_of_positive_integral
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Integrable f μ) (hnonneg : ∀ x, 0 ≤ f x)
    (hsupp : Function.support f = Set.univ) (hpos : 0 < ∫ x, f x ∂μ) :
    0 < μ Set.univ := by
  have hs := (integral_pos_iff_support_of_nonneg hnonneg hf).mp hpos
  simpa [hsupp] using hs

private theorem positive_integral_of_measure_univ_pos
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Integrable f μ) (hnonneg : ∀ x, 0 ≤ f x)
    (hsupp : Function.support f = Set.univ) (hmass : 0 < μ Set.univ) :
    0 < ∫ x, f x ∂μ := by
  apply (integral_pos_iff_support_of_nonneg hnonneg hf).2
  simpa [hsupp] using hmass

private theorem ae_integrable_heat_start_all_centers_of (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ y : Plane,
      Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - y)) (Z s t ω) := by
  classical
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense Plane
  have hq : ∀ᵐ ω ∂P, ∀ q : {q // q ∈ D},
      Integrable (fun p : Plane × Plane => heatKernel (2 * δ) (p.1 - q.1))
        (Z s t ω) := by
    exact (@ae_all_iff Ω (Measure Ω) _ _ P {q // q ∈ D} hDcount.to_subtype
      (fun ω q => Integrable
        (fun p : Plane × Plane => heatKernel (2 * δ) (p.1 - q.1)) (Z s t ω))).2
      (fun q => isCriticalSHF_ae_integrable_heat_start ϑ P Z hZ hs hst
        (mul_pos (by norm_num) hδ) q.1)
  filter_upwards [hq] with ω hω
  intro y
  obtain ⟨q, hqD, hdist⟩ := hDdense.exists_dist_lt y (by norm_num : (0 : ℝ) < 1)
  have hnorm : ‖y - q‖ ≤ 1 := by
    rw [← dist_eq_norm]
    exact hdist.le
  have hmajor := (hω ⟨q, hqD⟩).const_mul (2 * Real.exp (1 / (2 * δ)))
  apply hmajor.mono'
    (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).aestronglyMeasurable)
  filter_upwards [] with p
  change ‖heatKernel δ (p.1 - y)‖ ≤
    2 * Real.exp (1 / (2 * δ)) * heatKernel (2 * δ) (p.1 - q)
  rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hδ.le _)]
  exact heatKernel_le_two_mul_heatKernel hδ hnorm

private theorem continuous_heatKernel_pairing_of_doubled_integrability
    (μ : Measure (Plane × Plane)) {δ : ℝ} (hδ : 0 < δ)
    (hwide : ∀ q : Plane,
      Integrable (fun p : Plane × Plane => heatKernel (2 * δ) (p.1 - q)) μ) :
    Continuous (fun y : Plane => ∫ p, heatKernel δ (p.1 - y) ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro y₀
  let q : Plane := y₀
  let C : ℝ := 2 * Real.exp (1 / (2 * δ))
  have hnear : ∀ᶠ y in 𝓝 y₀, ‖y - q‖ ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds y₀ (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
    have hq : dist y₀ q < 1 / 2 := by simp [q]
    have hyq : dist y q < 1 := by
      calc
        dist y q ≤ dist y y₀ + dist y₀ q := dist_triangle _ _ _
        _ < 1 / 2 + 1 / 2 := add_lt_add hy hq
        _ = 1 := by norm_num
    rw [dist_eq_norm] at hyq
    exact hyq.le
  have hbound : ∀ᶠ y in 𝓝 y₀, ∀ᵐ p ∂μ,
      ‖heatKernel δ (p.1 - y)‖ ≤ C * heatKernel (2 * δ) (p.1 - q) := by
    filter_upwards [hnear] with y hy
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hδ.le _)]
    simpa only [C] using heatKernel_le_two_mul_heatKernel hδ hy
  have hFmeas : ∀ᶠ y in 𝓝 y₀,
      AEStronglyMeasurable (fun p : Plane × Plane => heatKernel δ (p.1 - y)) μ :=
    Filter.Eventually.of_forall fun y =>
      ((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).aestronglyMeasurable
  have hboundInt : Integrable (fun p : Plane × Plane => C * heatKernel (2 * δ) (p.1 - q)) μ :=
    (hwide q).const_mul C |>.congr (Filter.Eventually.of_forall fun p => by ring)
  have hlim : ∀ᵐ p ∂μ, Tendsto (fun y : Plane => heatKernel δ (p.1 - y))
      (𝓝 y₀) (𝓝 (heatKernel δ (p.1 - y₀))) := by
    filter_upwards [] with p
    exact (((continuous_heatKernel δ).comp (continuous_const.sub continuous_id)).continuousAt).tendsto
  have hcont := tendsto_integral_filter_of_dominated_convergence
    (fun p : Plane × Plane => C * heatKernel (2 * δ) (p.1 - q)) hFmeas hbound hboundInt hlim
  change Tendsto (fun y : Plane => ∫ p, heatKernel δ (p.1 - y) ∂μ)
    (𝓝 y₀) (𝓝 (∫ p, heatKernel δ (p.1 - y₀) ∂μ))
  exact hcont

private theorem ae_integrable_testFn_mul_kpzRegularizedReversed
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {t δ : ℝ}
    (hδ : 0 < δ) (hδt : δ < t) (ψ : TestFn) :
    ∀ᵐ ω ∂P, Integrable
      (fun y : Plane => ψ y * kpzRegularizedReversed P Z 0 t δ 0 y ω) := by
  have hlow := ae_integrable_heat_start_all_centers_of ϑ P Z hZ
    (show 0 ≤ δ by linarith) hδt hδ
  have hwide := ae_integrable_heat_start_all_centers_of ϑ P Z hZ
    (show 0 ≤ δ by linarith) hδt (mul_pos two_pos hδ)
  have hpos0 := hsym.2.2.2.2.2.2 δ t δ 0 (0 : Plane →ᵇ ℝ)
    (by positivity) hδt hδ
  filter_upwards [hlow, hwide, hpos0.1] with ω hlowω hwideω hposω
  have hposZ0 : 0 < ∫ p : Plane × Plane, heatKernel δ p.1 ∂(Z δ t ω) := by
    simpa [shfPairing] using hposω
  have hsupport0 : Function.support
      (fun p : Plane × Plane => heatKernel δ p.1) = Set.univ := by
    ext p
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact (heatKernel_pos hδ p.1).ne'
  have hmassPos : 0 < (Z δ t ω) Set.univ := by
    have hlow0 : Integrable (fun p : Plane × Plane => heatKernel δ p.1) (Z δ t ω) := by
      simpa only [sub_zero] using hlowω 0
    exact measure_univ_pos_of_positive_integral (Z δ t ω)
      (fun p : Plane × Plane => heatKernel δ p.1) hlow0
      (fun p => heatKernel_nonneg hδ.le p.1) hsupport0 hposZ0
  have hpos (y : Plane) : 0 < ∫ p : Plane × Plane,
      heatKernel δ (p.1 - y) ∂(Z δ t ω) := by
    have hsupport : Function.support
        (fun p : Plane × Plane => heatKernel δ (p.1 - y)) = Set.univ := by
      ext p
      simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
      exact (heatKernel_pos hδ (p.1 - y)).ne'
    exact positive_integral_of_measure_univ_pos (Z δ t ω)
      (fun p : Plane × Plane => heatKernel δ (p.1 - y)) (hlowω y)
      (fun p => heatKernel_nonneg hδ.le (p.1 - y)) hsupport hmassPos
  have hpairCont := continuous_heatKernel_pairing_of_doubled_integrability
    (Z δ t ω) hδ hwideω
  have hlogCont : Continuous (fun y : Plane =>
      Real.log (∫ p : Plane × Plane, heatKernel δ (p.1 - y) ∂(Z δ t ω))) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact ContinuousAt.comp (f := fun y : Plane =>
      ∫ p : Plane × Plane, heatKernel δ (p.1 - y) ∂(Z δ t ω))
      (g := Real.log) (x := y)
      (Real.continuousAt_log (ne_of_gt (hpos y))) hpairCont.continuousAt
  have hGcont : Continuous (fun y : Plane =>
      kpzRegularizedReversed P Z 0 t δ 0 y ω) := by
    have hGeq : (fun y : Plane => kpzRegularizedReversed P Z 0 t δ 0 y ω) =
        (fun y => Real.log (∫ p, heatKernel δ (p.1 - y) ∂(Z δ t ω)) -
          ∫ ω', Real.log (shfPairing Z δ t (fun z => heatKernel δ z) (fun _ => 1) ω') ∂P) := by
      funext y
      simp [kpzRegularizedReversed, shfPairing, zero_add]
    rw [hGeq]
    exact hlogCont.sub continuous_const
  apply (ψ.continuous.mul hGcont).integrable_of_hasCompactSupport
  exact HasCompactSupport.mul_right
    (f := fun y : Plane => ψ y)
    (f' := fun y => kpzRegularizedReversed P Z 0 t δ 0 y ω) ψ.hasCompactSupport

/-- For a nonnegative unit-mass test, the KPZ pairing variance is asymptotic to the double logarithm of inverse scale under the stated comparison and Gaussian-limit hypotheses. -/
theorem kpz_shrinking_variance_of_stages
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC12 : ToyJointAt ϑ P Z)
    (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    {t : ℝ} (ht : 0 < t) (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y)
    (hφ₁ : ∫ y, φ y = 1) (x : Plane)
    (hReg : ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ x : Plane,
      ∀ δ : ℝ, 0 < δ → δ ≤ ε ^ 2 →
        eLpNorm (fun ω => ∫ y, φ.dilate ε x y *
          (kpzRegularizedReversed P Z 0 t (ε ^ 2) 0 y ω -
            kpzRegularizedReversed P Z 0 t δ 0 y ω)) 2 P ≤ ENNReal.ofReal C)
    (hPoint : ∃ C ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      ∃ X : Ω → ℝ, P.map X = P.map (fun ω => H t 0 ω (φ.dilate ε x)) ∧
        Integrable (fun ω => X ω -
          (heatStartLog Z (ε ^ 2) t (ε ^ 2) (x + ε • barycentre φ) ω -
            ∫ ω', heatStartLog Z (ε ^ 2) t (ε ^ 2)
              (x + ε • barycentre φ) ω' ∂P)) P ∧
        ∫ ω, |X ω -
          (heatStartLog Z (ε ^ 2) t (ε ^ 2) (x + ε • barycentre φ) ω -
            ∫ ω', heatStartLog Z (ε ^ 2) t (ε ^ 2)
              (x + ε • barycentre φ) ω' ∂P)| ∂P ≤ C)
    (hCLT : TendstoInDistribution
      (fun ε ω => H t 0 ω (φ.dilate ε x) /
        Real.sqrt (Real.log (Real.log ε⁻¹)))
      (nhdsWithin 0 (Set.Ioi 0)) id (fun _ => P)
      (gaussianReal 0 ((∫ y, φ y) ^ 2).toNNReal)) :
    (∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      MemLp (fun ω => H t 0 ω (φ.dilate ε x)) 2 P) ∧
      Tendsto (fun ε => Var[fun ω => H t 0 ω (φ.dilate ε x); P] /
        Real.log (Real.log ε⁻¹))
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 1) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let L : ℝ → ℝ := fun ε => Real.log (Real.log ε⁻¹)
  have hL : Tendsto L l atTop := by
    dsimp [L, l]
    exact Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have hLpos : ∀ᶠ ε in l, 0 < L ε := hL.eventually_gt_atTop 0
  have ha : Tendsto (fun ε => Real.sqrt (L ε)) l atTop :=
    Real.tendsto_sqrt_atTop.comp hL
  obtain ⟨Cmom, δM, hδM, hmoment⟩ :=
    heatStartLog_moments_le_of ϑ P Z hZ hsym hHeatStartLogInput
      (τ₀ := t / 2) (τ₁ := t) (by linarith)
  obtain ⟨Creg, εreg, hεreg, hreg⟩ := hReg
  obtain ⟨Cpoint, εpoint, hεpoint, hpoint⟩ := hPoint
  let Creg' : ℝ := max Creg 0
  let Cpoint' : ℝ := max Cpoint 0
  let D : ℝ := Creg' + 1
  let K : ℝ := Real.log 2 + Cmom
  have hCreg' : 0 ≤ Creg' := by dsimp [Creg']; positivity
  have hCpoint' : 0 ≤ Cpoint' := by dsimp [Cpoint']; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hKlarge : Tendsto (fun ε => L ε + K) l atTop := by
    exact tendsto_atTop_add_const_right l K hL
  rcases hC12 t ht with ⟨Xfun, hXmeas, hXrate, hXlim, hXlattice, hXlaw⟩
  have hSigmaLe : shfSigma Z ≤ (inferInstance : MeasurableSpace Ω) := by
    dsimp [shfSigma]
    apply iSup_le
    intro s
    apply iSup_le
    intro v
    apply iSup_le
    intro hsv
    exact (hZ.1 s v hsv.1 hsv.2).comap_le
  have hUpper : ∀ᶠ ε in l,
      MemLp (fun ω => H t 0 ω (φ.dilate ε x)) 2 P ∧
        (∫ ω, (H t 0 ω (φ.dilate ε x)) ^ 2 ∂P ≤
          (Real.sqrt (L ε + K) + D) ^ 2) ∧
        |∫ ω, H t 0 ω (φ.dilate ε x) ∂P| ≤ Cpoint' := by
    let εLogBound : ℝ := Real.sqrt (Real.exp (-(Real.exp (-Cmom))))
    let εTailBound : ℝ := min εLogBound (Real.exp (-1))
    let εDurationBound : ℝ := min (Real.sqrt (t / 2))
      (min (Real.sqrt δM) εTailBound)
    let εBound : ℝ := min (min εreg εpoint) εDurationBound
    have hεBound : 0 < εBound := by
      dsimp [εBound]
      positivity
    have hsmall : ∀ᶠ ε in l, 0 < ε ∧ ε < εBound := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hεBound)]
        with ε hε hεlt
      exact ⟨hε, hεlt⟩
    have hLmom : ∀ᶠ ε in l, 0 < L ε + Cmom := by
      filter_upwards [hKlarge.eventually_gt_atTop (Real.log 2)] with ε hε
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      dsimp [K] at hε
      linarith
    filter_upwards [hsmall, hLpos, hLmom] with ε ⟨hε, hεbound⟩ hLε hLmomε
    have hAEMeasH : AEMeasurable (fun ω => H t 0 ω (φ.dilate ε x)) P := by
      have haε : 0 < Real.sqrt (L ε) := Real.sqrt_pos.2 hLε
      have hN := hCLT.forall_aemeasurable ε
      have hmul := hN.const_mul (Real.sqrt (L ε))
      have heq : (fun ω => Real.sqrt (L ε) *
          (H t 0 ω (φ.dilate ε x) / Real.sqrt (L ε))) =
          fun ω => H t 0 ω (φ.dilate ε x) := by
        funext ω
        field_simp [ne_of_gt haε]
      exact hmul.congr (Filter.Eventually.of_forall fun ω => congrFun heq ω)
    have hepsTests : ε < min εreg εpoint :=
      lt_of_lt_of_le hεbound (min_le_left _ _)
    have hεreg' : ε < εreg := lt_of_lt_of_le hepsTests (min_le_left _ _)
    have hεpoint' : ε < εpoint := lt_of_lt_of_le hepsTests (min_le_right _ _)
    have hrest' : ε < εDurationBound :=
      lt_of_lt_of_le hεbound (min_le_right _ _)
    have hεdur : ε < Real.sqrt (t / 2) :=
      lt_of_lt_of_le hrest' (min_le_left _ _)
    have hrest'' : ε < min (Real.sqrt δM) εTailBound :=
      lt_of_lt_of_le hrest' (min_le_right _ _)
    have hεδM : ε < Real.sqrt δM := lt_of_lt_of_le hrest'' (min_le_left _ _)
    have hrest''' : ε < εTailBound :=
      lt_of_lt_of_le hrest'' (min_le_right _ _)
    have hεlog : ε < Real.exp (-1) := lt_of_lt_of_le hrest''' (min_le_right _ _)
    have hεδlog : ε < Real.sqrt (Real.exp (-(Real.exp (-Cmom)))) :=
      lt_of_lt_of_le hrest''' (min_le_left _ _)
    have hεsqpos : 0 < ε ^ 2 := sq_pos_of_pos hε
    have hεsqT : ε ^ 2 < t / 2 := by
      have hsq := (sq_lt_sq₀ hε.le (Real.sqrt_nonneg _)).2 hεdur
      rw [Real.sq_sqrt (by positivity : 0 ≤ t / 2)] at hsq
      exact hsq
    have hεsqM : ε ^ 2 ≤ δM := by
      have hsq := (sq_lt_sq₀ hε.le (Real.sqrt_nonneg _)).2 hεδM
      have hsq' : ε ^ 2 < δM := by simpa [Real.sq_sqrt hδM.le] using hsq
      exact hsq'.le
    have hεsqlog : ε ^ 2 ≤ Real.exp (-(Real.exp (-Cmom))) := by
      have hsq := (sq_lt_sq₀ hε.le (Real.sqrt_nonneg _)).2 hεδlog
      have hsq' : ε ^ 2 < Real.exp (-(Real.exp (-Cmom))) := by
        simpa [Real.sq_sqrt (Real.exp_nonneg _)] using hsq
      exact hsq'.le
    have hdurlo : t / 2 ≤ t - ε ^ 2 := by linarith
    have hdurhi : t - ε ^ 2 ≤ t := by nlinarith [sq_nonneg ε]
    have hMomAt (y : Plane) := hmoment (ε ^ 2) t (ε ^ 2)
      (sq_nonneg ε) hdurlo hdurhi hεsqpos hεsqM y
    have hψpos : ∀ y, 0 ≤ (φ.dilate ε x) y := by
      intro y
      simp only [TestFn.dilate]
      exact mul_nonneg (sq_nonneg ε⁻¹) (hφ _)
    have hψmass : ∫ y, φ.dilate ε x y = 1 := by
      simpa only [mul_one, hφ₁] using
        (integral_testFn_dilate_mul φ hε x (fun _ => (1 : ℝ)))
    have hAvg := heatStartLog_centered_average_memLp_and_sq_le ϑ P Z hZ hsym
      (τ₀ := t / 2) (τ₁ := t) (s := ε ^ 2) (T := t) (δ := ε ^ 2)
      (C := Cmom) (δM := δM) (by linarith) hmoment
      (sq_nonneg ε) hdurlo hdurhi hεsqpos hεsqM
      hεsqlog
      (φ.dilate ε x) hψpos hψmass
    let R : Ω → ℝ := fun ω => ∫ y, φ.dilate ε x y *
      (heatStartLog Z (ε ^ 2) t (ε ^ 2) y ω -
        ∫ ω', heatStartLog Z (ε ^ 2) t (ε ^ 2) 0 ω' ∂P)
    have hRmem : MemLp R 2 P := by
      simpa only [R] using hAvg.1
    have hRsq : ∫ ω, R ω ^ 2 ∂P ≤ L ε + K := by
      have h := hAvg.2
      have hlogEq : Real.log (Real.log (ε ^ 2)⁻¹) + Cmom = L ε + K := by
        have hlogε : Real.log ε < -1 := by
          calc
            Real.log ε < Real.log (Real.exp (-1)) := Real.log_lt_log hε hεlog
            _ = -1 := Real.log_exp _
        have hloginv : 0 < Real.log ε⁻¹ := by rw [Real.log_inv]; linarith
        rw [show (ε ^ 2)⁻¹ = (ε⁻¹) ^ 2 by field_simp, Real.log_pow,
          Real.log_mul (by norm_num) hloginv.ne']
        simp [L, K]
        ring
      rw [hlogEq] at h
      calc
        ∫ ω, R ω ^ 2 ∂P = ∫ ω, |R ω| ^ 2 ∂P := by
          apply integral_congr_ae
          filter_upwards [] with ω
          rw [sq_abs]
        _ = ∫ ω, |∫ y, φ.dilate ε x y *
              (heatStartLog Z (ε ^ 2) t (ε ^ 2) y ω -
                ∫ ω', heatStartLog Z (ε ^ 2) t (ε ^ 2) 0 ω' ∂P)| ^ 2 ∂P := rfl
        _ ≤ L ε + K := h
    have hRnonneg : 0 ≤ L ε + K := by
      have hnonneg : 0 ≤ ∫ ω, R ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
      exact hnonneg.trans hRsq
    have hRnorm : eLpNorm R 2 P ≤ ENNReal.ofReal (Real.sqrt (L ε + K)) :=
      Critical2DKPZ.Smoothing.eLpNorm_le_of_integral_sq_le P hRmem hRsq
    let ψ : TestFn := φ.dilate ε x
    let Xtoy : Ω → ℝ := Xfun 0 0 ψ
    let Rδ : ℝ → Ω → ℝ := fun δ ω => ∫ y, ψ y *
      kpzRegularizedReversed P Z 0 t δ 0 y ω
    have hEpsIntegrable := ae_integrable_testFn_mul_kpzRegularizedReversed
      ϑ P Z hZ hsym (t := t) (δ := ε ^ 2)
      (sq_pos_of_pos hε) (by linarith [ht, hεsqT]) ψ
    have hToyApprox := hXlim 0 0 ψ 2 (by norm_num) (by linarith [ht])
      (by norm_num) (by norm_num)
    have hδposEvent : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        0 < δ := self_mem_nhdsWithin
    have hδleEvent : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        δ < ε ^ 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds hεsqpos)
    have hδerrEvent : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        eLpNorm (fun ω => Rδ δ ω - Xtoy ω) 2 P < 1 :=
      hToyApprox.eventually (Iio_mem_nhds zero_lt_one)
    have hδall : ∀ᶠ δ : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)),
        0 < δ ∧ δ < ε ^ 2 ∧ eLpNorm (fun ω => Rδ δ ω - Xtoy ω) 2 P < 1 := by
      filter_upwards [hδposEvent, hδleEvent, hδerrEvent] with δ hpos hlt herr
      exact ⟨hpos, hlt, herr⟩
    have hδne : NeBot (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) :=
      nhdsWithin_Ioi_neBot le_rfl
    obtain ⟨δ, hδall⟩ := @Filter.Eventually.exists ℝ _ _ hδne hδall
    rcases hδall with ⟨hδpos, hδlt, hδerr⟩
    have hDeltaIntegrable := ae_integrable_testFn_mul_kpzRegularizedReversed
      ϑ P Z hZ hsym (t := t) (δ := δ) hδpos
      (lt_trans hδlt (lt_trans hεsqT (by linarith [ht]))) ψ
    have hregAt := hreg ε hε hεreg' x δ
      hδpos (le_of_lt hδlt)
    have hregAt' : eLpNorm (fun ω => R ω - Rδ δ ω) 2 P ≤ ENNReal.ofReal Creg := by
      have hpointwise : (fun ω => R ω - Rδ δ ω) =ᵐ[P]
          (fun ω => ∫ y, ψ y *
            (kpzRegularizedReversed P Z 0 t (ε ^ 2) 0 y ω -
              kpzRegularizedReversed P Z 0 t δ 0 y ω)) := by
        filter_upwards [hEpsIntegrable, hDeltaIntegrable] with ω hEps hDelta
        have hR : R ω = ∫ y, ψ y *
            kpzRegularizedReversed P Z 0 t (ε ^ 2) 0 y ω := by
          simp [R, ψ, kpzRegularizedReversed, heatStartLog, shfPairing]
        calc
          R ω - Rδ δ ω =
              (∫ y, ψ y * kpzRegularizedReversed P Z 0 t (ε ^ 2) 0 y ω) -
                ∫ y, ψ y * kpzRegularizedReversed P Z 0 t δ 0 y ω := by
                  rw [hR]
          _ = ∫ y, ψ y *
              (kpzRegularizedReversed P Z 0 t (ε ^ 2) 0 y ω -
                kpzRegularizedReversed P Z 0 t δ 0 y ω) :=
            calc
              _ = ∫ y, ψ y * kpzRegularizedReversed P Z 0 t (ε ^ 2) 0 y ω -
                    ψ y * kpzRegularizedReversed P Z 0 t δ 0 y ω :=
                (integral_sub hEps hDelta).symm
              _ = _ := by
                congr 1
                funext y
                ring
      rw [eLpNorm_congr_ae hpointwise]
      simpa [ψ] using hregAt
    have hDiffBound : eLpNorm (fun ω => R ω - Xtoy ω) 2 P ≤ ENNReal.ofReal D := by
      calc
        _ = eLpNorm (fun ω => (R ω - Rδ δ ω) + (Rδ δ ω - Xtoy ω)) 2 P := by
          congr 1
          funext ω
          ring
        _ ≤ eLpNorm (fun ω => R ω - Rδ δ ω) 2 P +
            eLpNorm (fun ω => Rδ δ ω - Xtoy ω) 2 P := eLpNorm_add_le (by norm_num)
        _ ≤ ENNReal.ofReal Creg' + 1 := by
          refine add_le_add ?_ (le_of_lt hδerr)
          exact (hregAt'.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
        _ = ENNReal.ofReal D := by
          dsimp [D]
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hCreg' (by norm_num)]
    have hDiffMem : MemLp (fun ω => R ω - Xtoy ω) 2 P := by
      rw [memLp_iff]
      exact hDiffBound.trans_lt ENNReal.ofReal_lt_top
    have hXtoyMem : MemLp Xtoy 2 P := by
      have hfun : (fun ω => R ω - (R ω - Xtoy ω)) = Xtoy := by
        funext ω
        ring
      rw [← hfun]
      exact hRmem.sub hDiffMem
    have hXtoyNorm : eLpNorm Xtoy 2 P ≤ ENNReal.ofReal (Real.sqrt (L ε + K) + D) := by
      calc
        eLpNorm Xtoy 2 P = eLpNorm (fun ω => R ω - (R ω - Xtoy ω)) 2 P := by
          congr 1
          funext ω
          ring
        _ ≤ eLpNorm R 2 P + eLpNorm (fun ω => R ω - Xtoy ω) 2 P :=
          eLpNorm_sub_le (by norm_num)
        _ ≤ ENNReal.ofReal (Real.sqrt (L ε + K)) + ENNReal.ofReal D :=
          add_le_add hRnorm hDiffBound
        _ = ENNReal.ofReal (Real.sqrt (L ε + K) + D) :=
          (ENNReal.ofReal_add (Real.sqrt_nonneg _) hD).symm
    have hToySigmaMeas : AEMeasurable
        (fun (ω : Ω) (i : Fin 1) => Xfun 0 0 ψ ω) P := by
      apply AEMeasurable.of_eval
      intro i
      exact ((hXmeas 0 0 ψ (by norm_num) (by linarith [ht])).mono
        hSigmaLe le_rfl).aemeasurable
    have hHvecMeas : AEMeasurable
        (fun (ω : Ω) (i : Fin 1) => H t 0 ω ψ) P := by
      apply AEMeasurable.of_eval
      intro i
      simpa [ψ] using hAEMeasH
    have hToyMapVec := hXlaw H hH 1 (fun _ : Fin 1 => (0 : ℝ))
      (fun _ => (0 : Plane →ᵇ ℝ)) (fun _ => ψ)
      (by intro i; exact ⟨le_rfl, ht⟩)
    have hToyIdentVec : IdentDistrib (fun (ω : Ω) (i : Fin 1) => Xfun 0 0 ψ ω)
        (fun (ω : Ω) (i : Fin 1) => H t 0 ω ψ) P P :=
      ⟨hToySigmaMeas, hHvecMeas, by simpa only [sub_zero] using hToyMapVec⟩
    let Xvec : Ω → Fin 1 → ℝ := fun ω i => Xfun 0 0 ψ ω
    let Hvec : Ω → Fin 1 → ℝ := fun ω i => H t 0 ω ψ
    have hproj := hToyIdentVec.comp (measurable_pi_apply (0 : Fin 1))
    have hleft : (fun ω => (fun f : Fin 1 → ℝ => f 0) (Xvec ω)) = Xtoy := by
      funext ω
      rfl
    have hright : (fun ω => (fun f : Fin 1 → ℝ => f 0) (Hvec ω)) =
        (fun ω => H t 0 ω ψ) := by
      funext ω
      rfl
    have hToyIdent : IdentDistrib Xtoy (fun ω => H t 0 ω ψ) P P := by
      refine ⟨?_, ?_, ?_⟩
      · exact hproj.aemeasurable_fst.congr
          (Filter.Eventually.of_forall (fun ω => congrFun hleft ω))
      · exact hproj.aemeasurable_snd.congr
          (Filter.Eventually.of_forall (fun ω => congrFun hright ω))
      · calc
          P.map Xtoy = P.map (fun ω => (fun f : Fin 1 → ℝ => f 0) (Xvec ω)) := by
            rw [← hleft]
          _ = P.map (fun ω => (fun f : Fin 1 → ℝ => f 0) (Hvec ω)) := hproj.map_eq
          _ = P.map (fun ω => H t 0 ω ψ) := by rw [hright]
    have hHmem : MemLp (fun ω => H t 0 ω ψ) 2 P := hToyIdent.memLp_snd hXtoyMem
    have hHnorm : eLpNorm (fun ω => H t 0 ω ψ) 2 P ≤
        ENNReal.ofReal (Real.sqrt (L ε + K) + D) := by
      rw [← hToyIdent.eLpNorm_eq]
      exact hXtoyNorm
    have hHsq : ∫ ω, (H t 0 ω ψ) ^ 2 ∂P ≤
        (Real.sqrt (L ε + K) + D) ^ 2 :=
      Critical2DKPZ.Smoothing.integral_sq_le_of_eLpNorm_le P hHmem
        (Real.sqrt (L ε + K) + D) (by positivity) hHnorm |>.2
    obtain ⟨Xpt, hXptMap, hXptDiffInt, hXptDiffBound⟩ :=
      hpoint ε hε hεpoint'
    let b : Plane := x + ε • barycentre φ
    let Yb : Ω → ℝ := fun ω => heatStartLog Z (ε ^ 2) t (ε ^ 2) b ω
    let mB : ℝ := ∫ ω, Yb ω ∂P
    let Gb : Ω → ℝ := fun ω => Yb ω - mB
    have hYbMem : MemLp Yb 2 P := (hMomAt b).1
    have hYbInt : Integrable Yb P := hYbMem.integrable (by norm_num)
    have hGbInt : Integrable Gb P := hYbInt.sub (integrable_const mB)
    have hGmean : ∫ ω, Gb ω ∂P = 0 := by
      rw [show Gb = fun ω => Yb ω - mB by rfl, integral_sub hYbInt (integrable_const mB)]
      simp [mB]
    have hXptInt : Integrable Xpt P := by
      have heq : Xpt = fun ω => (Xpt ω - Gb ω) + Gb ω := by
        funext ω
        ring
      rw [heq]
      exact hXptDiffInt.add hGbInt
    have hXptMean : |∫ ω, Xpt ω ∂P| ≤ Cpoint' := by
      have hmeanEq : ∫ ω, Xpt ω ∂P = ∫ ω, (Xpt ω - Gb ω) ∂P := by
        have hsum := integral_add hXptDiffInt hGbInt
        rw [hGmean, add_zero] at hsum
        calc
          ∫ ω, Xpt ω ∂P = ∫ ω, ((Xpt ω - Gb ω) + Gb ω) ∂P := by
            congr 1
            funext ω
            ring
          _ = ∫ ω, (Xpt ω - Gb ω) ∂P := hsum
      rw [hmeanEq]
      calc
        |∫ ω, (Xpt ω - Gb ω) ∂P| ≤
            ∫ ω, |Xpt ω - Gb ω| ∂P := abs_integral_le_integral_abs
        _ ≤ Cpoint' := hXptDiffBound.trans (le_max_left _ _)
    have hXptAEMeas : AEMeasurable Xpt P := hXptInt.aemeasurable
    have hHIdentPt : IdentDistrib Xpt (fun ω => H t 0 ω (φ.dilate ε x)) P P :=
      ⟨hXptAEMeas, hAEMeasH, hXptMap⟩
    have hHmean : |∫ ω, H t 0 ω (φ.dilate ε x) ∂P| ≤ Cpoint' := by
      rw [← hHIdentPt.integral_eq]
      exact hXptMean
    exact ⟨hHmem, hHsq, hHmean⟩
  let V : ℝ → ℝ := fun ε =>
    Var[fun ω => H t 0 ω (φ.dilate ε x); P] / L ε
  let B : ℝ → ℝ := fun ε =>
    (Real.sqrt (L ε + K) + D) ^ 2 / L ε
  have hKdiv : Tendsto (fun ε => K / L ε) l (𝓝 0) := by
    simpa using tendsto_const_nhds.div_atTop hL
  have hSqrtArg : Tendsto (fun ε => 1 + K / L ε) l (𝓝 1) := by
    simpa using tendsto_const_nhds.add hKdiv
  have hSqrt : Tendsto (fun ε => Real.sqrt (1 + K / L ε)) l (𝓝 1) := by
    have h := Real.continuous_sqrt.continuousAt.tendsto.comp hSqrtArg
    change Tendsto (fun ε => Real.sqrt (1 + K / L ε)) l (𝓝 (Real.sqrt 1)) at h
    simpa only [Real.sqrt_one] using h
  have hDdiv : Tendsto (fun ε => D / Real.sqrt (L ε)) l (𝓝 0) :=
    tendsto_const_nhds.div_atTop ha
  have hG : Tendsto
      (fun ε => Real.sqrt (1 + K / L ε) + D / Real.sqrt (L ε)) l (𝓝 1) := by
    simpa using hSqrt.add hDdiv
  have hGsq : Tendsto
      (fun ε => (Real.sqrt (1 + K / L ε) + D / Real.sqrt (L ε)) ^ 2) l (𝓝 1) := by
    simpa using hG.pow 2
  have hLplus : ∀ᶠ ε in l, 0 < L ε + K := hKlarge.eventually_gt_atTop 0
  have hBeq : B =ᶠ[l]
      fun ε => (Real.sqrt (1 + K / L ε) + D / Real.sqrt (L ε)) ^ 2 := by
    filter_upwards [hLpos, hLplus] with ε hLε hLplusε
    have hsqrtDiv : Real.sqrt (L ε + K) / Real.sqrt (L ε) =
        Real.sqrt (1 + K / L ε) := by
      calc
        Real.sqrt (L ε + K) / Real.sqrt (L ε) =
            Real.sqrt ((L ε + K) / L ε) := (Real.sqrt_div hLplusε.le (L ε)).symm
        _ = Real.sqrt (1 + K / L ε) := by
          congr 1
          field_simp [ne_of_gt hLε]
    have hsqrtL : (Real.sqrt (L ε)) ^ 2 = L ε := Real.sq_sqrt hLε.le
    calc
      (Real.sqrt (L ε + K) + D) ^ 2 / L ε =
          ((Real.sqrt (L ε + K) + D) / Real.sqrt (L ε)) ^ 2 := by
            field_simp [ne_of_gt hLε, ne_of_gt (Real.sqrt_pos.2 hLε)]
            rw [hsqrtL]
      _ = (Real.sqrt (L ε + K) / Real.sqrt (L ε) +
          D / Real.sqrt (L ε)) ^ 2 := by rw [add_div]
      _ = (Real.sqrt (1 + K / L ε) + D / Real.sqrt (L ε)) ^ 2 := by
        rw [hsqrtDiv]
  have hB : Tendsto B l (𝓝 1) := hGsq.congr' hBeq.symm
  have hCLTstd : TendstoInDistribution
      (fun ε ω => H t 0 ω (φ.dilate ε x) / Real.sqrt (L ε))
      l id (fun _ => P) (gaussianReal 0 1) := by
    simpa [L, hφ₁] using hCLT
  have hLowerVar (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
      ∀ᶠ ε in l, 1 - η ≤ V ε := by
    let b : ℝ := 1 - η / 4
    have hbpos : 0 < b := by dsimp [b]; linarith
    have hb : b < 1 := by dsimp [b]; linarith
    have hnormLower := eventually_eLpNorm_ge_of_tendstoInDistribution P
      (fun ε ω => H t 0 ω (φ.dilate ε x)) (fun ε => Real.sqrt (L ε))
      hCLTstd hb
    have hLbig : ∀ᶠ ε in l, 2 * Cpoint' ^ 2 / η < L ε :=
      hL.eventually_gt_atTop (2 * Cpoint' ^ 2 / η)
    filter_upwards [hUpper, hnormLower, hLbig] with ε hU hnorm hLlarge
    have hLε : 0 < L ε := by
      have := hLlarge
      have hnonneg : 0 ≤ 2 * Cpoint' ^ 2 / η := by positivity
      exact lt_of_le_of_lt hnonneg this
    have haε : 0 < Real.sqrt (L ε) := Real.sqrt_pos.2 hLε
    have hYmem : MemLp
        (fun ω => H t 0 ω (φ.dilate ε x) / Real.sqrt (L ε)) 2 P := by
      simpa [div_eq_mul_inv, mul_comm] using
        hU.1.const_mul ((Real.sqrt (L ε))⁻¹)
    have hnormReal : b ≤
        (eLpNorm (fun ω => H t 0 ω (φ.dilate ε x) / Real.sqrt (L ε)) 2 P).toReal := by
      calc
        b = (ENNReal.ofReal b).toReal := (ENNReal.toReal_ofReal hbpos.le).symm
        _ ≤ (eLpNorm (fun ω => H t 0 ω (φ.dilate ε x) / Real.sqrt (L ε)) 2 P).toReal :=
          ENNReal.toReal_mono hYmem.eLpNorm_ne_top hnorm
    have hYsqInt : Integrable
        (fun ω => (H t 0 ω (φ.dilate ε x) / Real.sqrt (L ε)) ^ 2) P := by
      have h := hYmem.integrable_norm_pow'
      simpa [Real.norm_eq_abs, abs_div, abs_of_pos haε, sq_abs, div_pow] using h
    have hYnorm := toReal_eLpNorm_two_eq_sqrt_integral_sq P hYmem
    have hYsqrt : b ≤ Real.sqrt
        (∫ ω, (H t 0 ω (φ.dilate ε x) / Real.sqrt (L ε)) ^ 2 ∂P) := by
      simpa only [hYnorm] using hnormReal
    have hHsqInt : Integrable (fun ω => (H t 0 ω (φ.dilate ε x)) ^ 2) P := by
      have h := hU.1.integrable_norm_pow'
      simpa [Real.norm_eq_abs, sq_abs] using h
    have hscale :
        ∫ ω, (H t 0 ω (φ.dilate ε x) / Real.sqrt (L ε)) ^ 2 ∂P =
          (∫ ω, (H t 0 ω (φ.dilate ε x)) ^ 2 ∂P) / L ε := by
      have hfun (ω : Ω) :
          (H t 0 ω (φ.dilate ε x) / Real.sqrt (L ε)) ^ 2 =
            (Real.sqrt (L ε))⁻¹ ^ 2 * (H t 0 ω (φ.dilate ε x)) ^ 2 := by
        field_simp [ne_of_gt haε]
      have hsqroot : (Real.sqrt (L ε)) ^ 2 = L ε := Real.sq_sqrt hLε.le
      calc
        _ = ∫ ω, (Real.sqrt (L ε))⁻¹ ^ 2 *
            (H t 0 ω (φ.dilate ε x)) ^ 2 ∂P := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall hfun
        _ = (Real.sqrt (L ε))⁻¹ ^ 2 *
            ∫ ω, (H t 0 ω (φ.dilate ε x)) ^ 2 ∂P := integral_const_mul _ _
        _ = _ := by rw [inv_pow, hsqroot]; ring
    have hYnonneg : 0 ≤
        ∫ ω, (H t 0 ω (φ.dilate ε x) / Real.sqrt (L ε)) ^ 2 ∂P :=
      integral_nonneg fun ω => sq_nonneg _
    have hsecondLower : b ^ 2 ≤
        (∫ ω, (H t 0 ω (φ.dilate ε x)) ^ 2 ∂P) / L ε := by
      have hsq := (sq_le_sq₀ hbpos.le (Real.sqrt_nonneg _)).2 hYsqrt
      rw [Real.sq_sqrt hYnonneg, hscale] at hsq
      exact hsq
    have hmeanSq :
        (∫ ω, H t 0 ω (φ.dilate ε x) ∂P) ^ 2 ≤ Cpoint' ^ 2 := by
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg _) hCpoint').2 hU.2.2
    have hmeanSqDiv :
        (∫ ω, H t 0 ω (φ.dilate ε x) ∂P) ^ 2 / L ε ≤ Cpoint' ^ 2 / L ε :=
      div_le_div_of_nonneg_right hmeanSq hLε.le
    have hCpdiv : Cpoint' ^ 2 / L ε < η / 2 := by
      apply (div_lt_iff₀ hLε).2
      have hlarge' := (div_lt_iff₀ hη).1 hLlarge
      nlinarith
    have hbSq : 1 - η / 2 ≤ b ^ 2 := by
      dsimp [b]
      nlinarith [sq_nonneg η]
    have hVarEq := variance_eq_sub hU.1
    have hVarIdentity :
        Var[fun ω => H t 0 ω (φ.dilate ε x); P] / L ε =
          (∫ ω, (H t 0 ω (φ.dilate ε x)) ^ 2 ∂P) / L ε -
            (∫ ω, H t 0 ω (φ.dilate ε x) ∂P) ^ 2 / L ε := by
      rw [hVarEq]
      simp only [Pi.pow_apply]
      field_simp [ne_of_gt hLε]
    have hfinal : 1 - η ≤
        (∫ ω, (H t 0 ω (φ.dilate ε x)) ^ 2 ∂P) / L ε -
          (∫ ω, H t 0 ω (φ.dilate ε x) ∂P) ^ 2 / L ε := by
      linarith
    calc
      1 - η ≤ Var[fun ω => H t 0 ω (φ.dilate ε x); P] / L ε := by
        rw [hVarIdentity]
        exact hfinal
      _ = V ε := rfl
  have hUpperVar (η : ℝ) (hη : 0 < η) : ∀ᶠ ε in l, V ε < 1 + η := by
    have hBlt : ∀ᶠ ε in l, B ε < 1 + η :=
      hB.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hUpper, hBlt, hLpos] with ε hU hBε hLε
    have hVarle := variance_le_expectation_sq hU.1.aemeasurable.aestronglyMeasurable
    calc
      V ε = Var[fun ω => H t 0 ω (φ.dilate ε x); P] / L ε := rfl
      _ ≤ (∫ ω, (H t 0 ω (φ.dilate ε x)) ^ 2 ∂P) / L ε :=
        div_le_div_of_nonneg_right hVarle hLε.le
      _ ≤ (Real.sqrt (L ε + K) + D) ^ 2 / L ε :=
        div_le_div_of_nonneg_right hU.2.1 hLε.le
      _ = B ε := rfl
      _ < 1 + η := hBε
  refine ⟨hUpper.mono fun ε hε => hε.1, ?_⟩
  apply Metric.tendsto_nhds.2
  intro η hη
  let θ : ℝ := min (η / 2) (1 / 2)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθ1 : θ < 1 := by dsimp [θ]; linarith [min_le_right (η / 2) (1 / 2)]
  have hθη : θ < η := by
    dsimp [θ]
    by_cases hη' : η ≤ 1
    · calc
        min (η / 2) (1 / 2) ≤ η / 2 := min_le_left _ _
        _ < η := by linarith
    · calc
        min (η / 2) (1 / 2) ≤ 1 / 2 := min_le_right _ _
        _ < η := by linarith
  have hlow := hLowerVar θ hθ hθ1
  have hupp := hUpperVar θ hθ
  filter_upwards [hlow, hupp] with ε hlowε huppε
  have hdist : |V ε - 1| < η := by
    rw [abs_lt]
    constructor <;> linarith
  simpa only [Real.dist_eq] using hdist

end Critical2DKPZ.SmallScales

end
