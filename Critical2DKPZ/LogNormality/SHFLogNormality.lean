/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LogNormality.LatticeLogNormality
public import Critical2DKPZ.Definitions.IsCriticalSHF
public import Critical2DKPZ.Definitions.ShfPairing
import Critical2DKPZ.JointConvergence.HeatStartLogConvergence
import Critical2DKPZ.JointConvergence.MomentConvergence
import Critical2DKPZ.LogNormality.LatticeInputs
public import Critical2DKPZ.SHF.Limit.Basic
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

/-! # SHF log-normality from lattice log-normality -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Limit
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.LogNormality

open Critical2DKPZ Critical2DKPZ.Blocks Critical2DKPZ.OnePoint Critical2DKPZ.Polymer
  Critical2DKPZ.FutureProfiles

private theorem tendstoInMeasure_const_of_tendsto {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] {l : Filter ι} {c : ι → ℝ} {c₀ : ℝ}
    (hc : Tendsto c l (𝓝 c₀)) :
    TendstoInMeasure μ (fun i _ => c i) l (fun _ => c₀) := by
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hclose := (Metric.tendsto_nhds.mp hc) ε hε
  have hzero : ∀ᶠ i in l, μ {ω | ε ≤ ‖c i - c₀‖} = 0 := by
    filter_upwards [hclose] with i hi
    have hnorm : ‖c i - c₀‖ < ε := by simpa [Real.dist_eq] using hi
    have hset : {ω : Ω | ε ≤ ‖c i - c₀‖} = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro ω hω
      exact (not_le_of_gt hnorm) hω
    rw [hset, measure_empty]
  have heq : (fun i => μ {ω | ε ≤ ‖c i - c₀‖}) =ᶠ[l] fun _ => 0 := by
    filter_upwards [hzero] with i hi
    exact hi
  exact tendsto_const_nhds.congr' heq.symm

private theorem tendstoInDistribution_centered_div_of_integral_tendsto
    {Ω' Ω : Type*} [MeasurableSpace Ω'] [MeasurableSpace Ω]
    (μ : Measure Ω') [IsProbabilityMeasure μ] (P : Measure Ω) [IsProbabilityMeasure P]
    {X : ℕ → Ω' → ℝ} {Y : Ω → ℝ}
    (hX : TendstoInDistribution X atTop Y (fun _ => μ) P)
    (hmean : Tendsto (fun k => ∫ ω, X k ω ∂μ) atTop
      (𝓝 (∫ ω, Y ω ∂P))) (s : ℝ) :
    TendstoInDistribution
      (fun k ω => (X k ω - ∫ ω', X k ω' ∂μ) / s) atTop
      (fun ω => (Y ω - ∫ ω', Y ω' ∂P) / s) (fun _ => μ) P := by
  let m : ℕ → ℝ := fun k => ∫ ω, X k ω ∂μ
  let m₀ : ℝ := ∫ ω, Y ω ∂P
  have hm : Tendsto m atTop (𝓝 m₀) := by simpa [m, m₀] using hmean
  have hmMeasure : TendstoInMeasure μ (fun k _ => m k) atTop (fun _ => m₀) :=
    tendstoInMeasure_const_of_tendsto μ hm
  have hpair := hX.prodMk_of_tendstoInMeasure_const X (fun k _ => m k) Y
    hmMeasure (fun _ => measurable_const.aemeasurable)
  have hcomp := hpair.continuous_comp
    (g := fun p : ℝ × ℝ => (p.1 - p.2) / s) (by fun_prop)
  simpa [m, m₀, Function.comp_def] using hcomp

/-- For each smoothing scale and spatial point, even-size lattice logarithms converge in law to
the SHF logarithm, and their Bochner integrals converge to its Bochner integral.
This condition does not require integrability of the limiting logarithm. -/
def LogHeatPairingLimit (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ x : Plane,
    TendstoInDistribution
      (fun (k : ℕ) (ω : Disorder) => Real.log (smoothedP2Plane (criticalBeta ϑ (2 * k))
        (evenCeil (ε ^ 2 * (2 * k : ℕ))) (2 * k) (latticePoint (2 * k) x) ω))
      atTop (fun ω => Real.log (shfPairing Z (ε ^ 2) 1
        (fun y => heatKernel (ε ^ 2) (y - x)) (fun _ => 1) ω))
      (fun _ => disorderLaw) P ∧
    Tendsto (fun k : ℕ => ∫ ω, Real.log (smoothedP2Plane (criticalBeta ϑ (2 * k))
        (evenCeil (ε ^ 2 * (2 * k : ℕ))) (2 * k) (latticePoint (2 * k) x) ω) ∂disorderLaw)
      atTop (𝓝 (∫ ω, Real.log (shfPairing Z (ε ^ 2) 1
        (fun y => heatKernel (ε ^ 2) (y - x)) (fun _ => 1) ω) ∂P))

/-- Heat-start pairing convergence implies convergence in law of the even-size lattice log
masses and convergence of their centring integrals. -/
theorem logHeatPairingLimit_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hpair : ∀ {s t δ : ℝ}, 0 ≤ s → s < t → 0 < δ → ∀ (x : Plane) (g : Plane →ᵇ ℝ),
      (∀ᵐ ω ∂P, Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x) * g p.2) (Z s t ω)) ∧
      Integrable (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) P ∧
      (∫ ω, |shfPairing Z s t (fun y => heatKernel δ (y - x)) g ω| ∂P ≤ ‖g‖) ∧
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) => ∫ p, heatKernel δ (p.1 - x) * g p.2
          ∂(Critical2DKPZ.SHF.Limit.polymerMeasure ϑ N s t ω))
        atTop (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) (fun _ => disorderLaw) P)
    (hjoint : ∀ (k : ℕ) (s t δ : Fin k → ℝ) (x : Fin k → Plane) (g : Fin k → (Plane →ᵇ ℝ)),
      (∀ i, 0 ≤ s i ∧ s i < t i ∧ 0 < δ i) →
      TendstoInDistribution
        (fun (N : ℕ) (ω : Disorder) (i : Fin k) =>
          ∫ p, heatKernel (δ i) (p.1 - x i) * g i p.2
            ∂(Critical2DKPZ.SHF.Limit.polymerMeasure ϑ N (s i) (t i) ω))
        atTop (fun ω i => shfPairing Z (s i) (t i) (fun y => heatKernel (δ i) (y - x i)) (g i) ω)
        (fun _ => disorderLaw) P)
    (hpos : ∀ (s t δ : ℝ) (x : Plane) (h₀ : Plane →ᵇ ℝ), 0 ≤ s → s < t → 0 < δ →
      (∀ᵐ ω ∂P, 0 < shfPairing Z s t (fun y => heatKernel δ (y - x))
        (fun y => Real.exp (h₀ y)) ω) ∧
      AEMeasurable (fun ω =>
        Real.log (shfPairing Z s t (fun y => heatKernel δ (y - x))
          (fun y => Real.exp (h₀ y)) ω)) P) :
    LogHeatPairingLimit ϑ P Z := by
  intro ε hε hε1 x
  have hε2pos : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hε2lt : ε ^ 2 < 1 := by
    have hmul := mul_lt_mul_of_pos_right hε1 hε
    nlinarith
  let h₀ : Plane →ᵇ ℝ := 0
  let svec : Fin 1 → ℝ := fun _ => ε ^ 2
  let δvec : Fin 1 → ℝ := fun _ => ε ^ 2
  let xvec : Fin 1 → Plane := fun _ => x
  have hparams : ∀ i : Fin 1, 0 ≤ svec i ∧ svec i < 1 ∧ 0 < δvec i := by
    intro i
    simp only [svec, δvec]
    exact ⟨sq_nonneg _, hε2lt, hε2pos⟩
  have hHeatStartLogInput := JointConvergence.heatStart_log_tendsto_of ϑ P Z hZ hpair hjoint hpos
    1 h₀ 1 svec δvec xvec hparams
  let Profile : ℕ → Disorder → ℝ := fun N ω =>
    Real.log (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * ε ^ 2)) (evenCeil (N * 1))
      (fun w => srwKernel (evenCeil (N * ε ^ 2)) (w - latticePoint N x))
      (cellAverage N fun y => Real.exp (h₀ y)) ω)
  let Y : Ω → ℝ := fun ω => Real.log
    (shfPairing Z (ε ^ 2) 1 (fun y => heatKernel (ε ^ 2) (y - x)) (fun _ => 1) ω)
  have hdistProfile : TendstoInDistribution Profile atTop Y (fun _ => disorderLaw) P := by
    have h := hHeatStartLogInput.2.1.continuous_comp (continuous_apply (0 : Fin 1))
    simpa only [Profile, Y, svec, δvec, xvec, Function.comp_def, Function.comp_apply, h₀,
      BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using h
  have h2k : Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ => k) (g := fun k => 2 * k)
    · intro k
      omega
    · exact tendsto_id
  let Smooth : ℕ → Disorder → ℝ := fun k ω =>
    Real.log (smoothedP2Plane (criticalBeta ϑ (2 * k))
      (evenCeil (ε ^ 2 * (2 * k : ℕ))) (2 * k) (latticePoint (2 * k) x) ω)
  have hdistProfileEven :
      TendstoInDistribution (fun k ω => Profile (2 * k) ω) atTop Y
        (fun _ => disorderLaw) P := by
    refine ⟨fun k => hdistProfile.forall_aemeasurable (2 * k), hdistProfile.aemeasurable_limit, ?_⟩
    exact hdistProfile.tendsto.comp h2k
  have hprofileEq : ∀ᶠ k : ℕ in atTop,
      (fun ω => Profile (2 * k) ω) =ᵐ[disorderLaw] Smooth k := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk
    filter_upwards [] with ω
    have hcell := profileP2Fun_cellAverage_one_eq_smoothedP2Plane
      (criticalBeta ϑ (2 * k)) (show Even (2 * k : ℕ) from ⟨k, by omega⟩)
      (by omega) (s := ε ^ 2) (sq_nonneg ε) hε2lt.le x ω
    dsimp [Profile, Smooth, h₀]
    simpa only [mul_comm, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
      Real.exp_zero] using congrArg Real.log hcell
  have hdistSmooth : TendstoInDistribution Smooth atTop Y (fun _ => disorderLaw) P := by
    refine ⟨?_, hdistProfileEven.aemeasurable_limit, ?_⟩
    · intro k
      simpa only [Smooth, Function.comp_def] using
        (Real.measurable_log.comp (Polymer.measurable_smoothedP2Plane
          (criticalBeta ϑ (2 * k)) (evenCeil (ε ^ 2 * (2 * k : ℕ))) (2 * k)
          (latticePoint (2 * k) x))).aemeasurable
    · apply Tendsto.congr' ?_ hdistProfileEven.tendsto
      filter_upwards [hprofileEq] with k hk
      apply Subtype.ext
      exact Measure.map_congr hk
  obtain ⟨C₂, hC₂⟩ := log_smoothedP2Plane_sq_integral_bounded ϑ hε hε1
  have hC₂even : ∀ᶠ k : ℕ in atTop,
      Integrable (fun ω => Real.log (smoothedP2Plane (criticalBeta ϑ (2 * k))
        (evenCeil (ε ^ 2 * (2 * k : ℕ))) (2 * k) 0 ω) ^ 2) disorderLaw ∧
      ∫ ω, Real.log (smoothedP2Plane (criticalBeta ϑ (2 * k))
        (evenCeil (ε ^ 2 * (2 * k : ℕ))) (2 * k) 0 ω) ^ 2 ∂disorderLaw ≤ C₂ := by
    filter_upwards [h2k.eventually hC₂] with k hk
    simpa only [Function.comp_apply] using hk
  have hInt : ∀ᶠ k : ℕ in atTop,
      Integrable (fun ω => |Smooth k ω| ^ ((2 : ℕ) : ℝ)) disorderLaw := by
    filter_upwards [hC₂even] with k hk
    let β := criticalBeta ϑ (2 * k)
    let m := evenCeil (ε ^ 2 * (2 * k : ℕ))
    let n := 2 * k
    let z := latticePoint (2 * k) x
    have hident := identDistrib_smoothedP2Plane_translate β m n z
    have hidentSq : IdentDistrib
        (fun ω => (Real.log (smoothedP2Plane β m n z ω)) ^ 2)
        (fun ω => (Real.log (smoothedP2Plane β m n 0 ω)) ^ 2)
        disorderLaw disorderLaw := by
      simpa only [Function.comp_def, Function.comp_apply] using
        hident.comp (by fun_prop : Measurable (fun r : ℝ => (Real.log r) ^ 2))
    have htranslated : Integrable (fun ω => (Real.log
        (smoothedP2Plane β m n z ω)) ^ 2) disorderLaw :=
      hidentSq.integrable_iff.2 (by simpa only [β, m, n] using hk.1)
    have heq : (fun ω => |Smooth k ω| ^ ((2 : ℕ) : ℝ)) =
        fun ω => (Real.log (smoothedP2Plane β m n z ω)) ^ 2 := by
      funext ω
      simp only [Smooth, β, m, n, z, Real.rpow_natCast, sq_abs]
    rw [heq]
    exact htranslated
  have hM : ∀ᶠ k : ℕ in atTop,
      ∫ ω, |Smooth k ω| ^ ((2 : ℕ) : ℝ) ∂disorderLaw ≤ C₂ := by
    filter_upwards [hC₂even] with k hk
    let β := criticalBeta ϑ (2 * k)
    let m := evenCeil (ε ^ 2 * (2 * k : ℕ))
    let n := 2 * k
    let z := latticePoint (2 * k) x
    have hident := identDistrib_smoothedP2Plane_translate β m n z
    have hidentSq : IdentDistrib
        (fun ω => (Real.log (smoothedP2Plane β m n z ω)) ^ 2)
        (fun ω => (Real.log (smoothedP2Plane β m n 0 ω)) ^ 2)
        disorderLaw disorderLaw := by
      simpa only [Function.comp_def, Function.comp_apply] using
        hident.comp (by fun_prop : Measurable (fun r : ℝ => (Real.log r) ^ 2))
    have hboundSq : ∫ ω, (Real.log (smoothedP2Plane β m n z ω)) ^ 2 ∂disorderLaw ≤ C₂ := by
      calc
        _ = ∫ ω, (Real.log (smoothedP2Plane β m n 0 ω)) ^ 2 ∂disorderLaw := hidentSq.integral_eq
        _ ≤ C₂ := by simpa only [β, m, n] using hk.2
    have heq : (fun ω => |Smooth k ω| ^ ((2 : ℕ) : ℝ)) =
        fun ω => (Real.log (smoothedP2Plane β m n z ω)) ^ 2 := by
      funext ω
      simp only [Smooth, β, m, n, z, Real.rpow_natCast, sq_abs]
    calc
      _ = ∫ ω, (Real.log (smoothedP2Plane β m n z ω)) ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        exact congrFun heq ω
      _ ≤ C₂ := hboundSq
  have hmeans := JointConvergence.tendsto_integral_of_tendstoInDistribution
    hdistSmooth (by norm_num : 1 < ((2 : ℕ) : ℝ)) hM hInt
  exact ⟨hdistSmooth, hmeans⟩

/-- Under the block-moment and profile estimates and `LogHeatPairingLimit`, the centred heat-start
logarithm divided by `√(log log ε⁻¹)` converges in law to `N(0,1)` as `ε ↓ 0`
(KPZ, Theorem 8.1).
The centring uses the Bochner integral in `LogHeatPairingLimit`, without a separate integrability
assumption in that condition. -/
theorem shf_logNormality_of (hC6 : BlockMomentsBound) (hPE : ProfileEstimatesBound)
    (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (_hZ : IsCriticalSHF ϑ P Z)
    (hlim : LogHeatPairingLimit ϑ P Z) (x : Plane) :
    TendstoInDistribution
      (fun (ε : Set.Ioo (0 : ℝ) 1) ω =>
        (Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1
            (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω) -
          ∫ ω', Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1
            (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω') ∂P) /
          Real.sqrt (Real.log (Real.log (ε : ℝ)⁻¹)))
      (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0))) id (fun _ => P)
      (gaussianReal 0 1) := by
  have hmeas : ∀ ε : Set.Ioo (0 : ℝ) 1,
      AEMeasurable (fun ω =>
        (Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1
            (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω) -
          ∫ ω', Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1
            (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω') ∂P) /
          Real.sqrt (Real.log (Real.log (ε : ℝ)⁻¹))) P := by
    intro ε
    have hlimε := hlim (ε : ℝ) ε.2.1 ε.2.2 x
    have hy : AEMeasurable (fun ω => Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1
        (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω)) P :=
      hlimε.1.aemeasurable_limit
    have hcont : Continuous (fun z : ℝ => (z -
        ∫ ω', Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1
          (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω') ∂P) /
          Real.sqrt (Real.log (Real.log (ε : ℝ)⁻¹))) := by fun_prop
    exact hcont.measurable.comp_aemeasurable hy
  apply (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hmeas
    (by fun_prop : AEMeasurable id (gaussianReal 0 1))).2
  intro h
  rw [Metric.tendsto_nhds]
  intro η hη
  have hη2 : 0 < η / 2 := by linarith
  obtain ⟨εLat, hεLat, hLat⟩ := lattice_logNormality_of hC6 hPE ϑ h (η / 2) hη2
  let εcut : ℝ := min εLat (Real.exp (-1))
  have hεcut : 0 < εcut := by dsimp [εcut]; positivity
  have hsmallReal : ∀ᶠ r : ℝ in nhdsWithin 0 (Set.Ioi 0), r < εcut :=
    eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hεcut)
  have hsmall : ∀ᶠ ε : Set.Ioo (0 : ℝ) 1 in
      Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0)), (ε : ℝ) < εcut :=
    hsmallReal.comap Subtype.val
  filter_upwards [hsmall] with ε hεcut'
  have hεpos : 0 < (ε : ℝ) := ε.2.1
  have hε1 : (ε : ℝ) < 1 := ε.2.2
  have hεLat' : (ε : ℝ) < εLat := lt_of_lt_of_le hεcut' (min_le_left _ _)
  have hεexp : (ε : ℝ) < Real.exp (-1) := lt_of_lt_of_le hεcut' (min_le_right _ _)
  have hlogε : Real.log (ε : ℝ) < -1 := by
    have h := Real.log_lt_log hεpos hεexp
    simpa using h
  have hlogInv : 1 < Real.log (ε : ℝ)⁻¹ := by
    rw [Real.log_inv]
    linarith
  have hscalePos : 0 < Real.sqrt (Real.log (Real.log (ε : ℝ)⁻¹)) :=
    Real.sqrt_pos.mpr (Real.log_pos hlogInv)
  let s : ℝ := Real.sqrt (Real.log (Real.log (ε : ℝ)⁻¹))
  have hs : 0 < s := by simpa [s] using hscalePos
  let Y : Ω → ℝ := fun ω => Real.log (shfPairing Z ((ε : ℝ) ^ 2) 1
    (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω)
  let rawX : ℕ → Disorder → ℝ := fun k ω => Real.log
    (smoothedP2Plane (criticalBeta ϑ (2 * k))
      (evenCeil ((ε : ℝ) ^ 2 * (2 * k : ℕ))) (2 * k) (latticePoint (2 * k) x) ω)
  let raw0 : ℕ → Disorder → ℝ := fun k ω => Real.log
    (smoothedP2Plane (criticalBeta ϑ (2 * k))
      (evenCeil ((ε : ℝ) ^ 2 * (2 * k : ℕ))) (2 * k) 0 ω)
  have hlimε := hlim (ε : ℝ) hεpos hε1 x
  have hcentered := tendstoInDistribution_centered_div_of_integral_tendsto
    disorderLaw P hlimε.1 hlimε.2 s
  have hIntTend : Tendsto
      (fun k => ∫ ω, h ((rawX k ω - ∫ ω', rawX k ω' ∂disorderLaw) / s) ∂disorderLaw)
      atTop (𝓝 (∫ ω, h ((Y ω - ∫ ω', Y ω' ∂P) / s) ∂P)) := by
    exact (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      hcentered.forall_aemeasurable hcentered.aemeasurable_limit).1 hcentered h
  have hLatN : ∀ᶠ N : ℕ in atTop,
      |∫ ω, h ((Real.log (smoothedP2Plane (criticalBeta ϑ N)
          (evenCeil ((ε : ℝ) ^ 2 * N)) N 0 ω) -
        ∫ ω', Real.log (smoothedP2Plane (criticalBeta ϑ N)
          (evenCeil ((ε : ℝ) ^ 2 * N)) N 0 ω') ∂disorderLaw) / s) ∂disorderLaw -
      ∫ z, h z ∂gaussianReal 0 1| ≤ η / 2 := by
    simpa only [s] using hLat (ε : ℝ) hεpos hεLat'
  have hdouble : Tendsto (fun k : ℕ => 2 * k) atTop atTop := by
    apply tendsto_atTop_mono (f := fun k : ℕ => k) (g := fun k => 2 * k)
    · intro k
      omega
    · exact tendsto_id
  have hLatK : ∀ᶠ k : ℕ in atTop,
      |∫ ω, h ((raw0 k ω - ∫ ω', raw0 k ω' ∂disorderLaw) / s) ∂disorderLaw -
        ∫ z, h z ∂gaussianReal 0 1| ≤ η / 2 := by
    filter_upwards [hdouble.eventually hLatN] with k hk
    simpa [raw0, s] using hk
  have htrans : ∀ k : ℕ,
      ∫ ω, h ((rawX k ω - ∫ ω', rawX k ω' ∂disorderLaw) / s) ∂disorderLaw =
        ∫ ω, h ((raw0 k ω - ∫ ω', raw0 k ω' ∂disorderLaw) / s) ∂disorderLaw := by
    intro k
    have hmass := identDistrib_smoothedP2Plane_translate
      (criticalBeta ϑ (2 * k)) (evenCeil ((ε : ℝ) ^ 2 * (2 * k : ℕ)))
      (2 * k) (latticePoint (2 * k) x)
    have hlog : IdentDistrib (rawX k) (raw0 k) disorderLaw disorderLaw := by
      change IdentDistrib
        (Real.log ∘ smoothedP2Plane (criticalBeta ϑ (2 * k))
          (evenCeil ((ε : ℝ) ^ 2 * (2 * k : ℕ))) (2 * k) (latticePoint (2 * k) x))
        (Real.log ∘ smoothedP2Plane (criticalBeta ϑ (2 * k))
          (evenCeil ((ε : ℝ) ^ 2 * (2 * k : ℕ))) (2 * k) 0) disorderLaw disorderLaw
      exact hmass.comp Real.measurable_log
    have hmeans : ∫ ω, rawX k ω ∂disorderLaw = ∫ ω, raw0 k ω ∂disorderLaw :=
      hlog.integral_eq
    have htest := hlog.comp (by fun_prop : Measurable fun z : ℝ =>
      h ((z - ∫ ω', raw0 k ω' ∂disorderLaw) / s))
    calc
      _ = ∫ ω, h ((rawX k ω - ∫ ω', raw0 k ω' ∂disorderLaw) / s) ∂disorderLaw := by
        rw [hmeans]
      _ = _ := htest.integral_eq
  have hLatKx : ∀ᶠ k : ℕ in atTop,
      |∫ ω, h ((rawX k ω - ∫ ω', rawX k ω' ∂disorderLaw) / s) ∂disorderLaw -
        ∫ z, h z ∂gaussianReal 0 1| ≤ η / 2 := by
    filter_upwards [hLatK] with k hk
    rw [htrans k]
    exact hk
  have hIcc : ∀ᶠ k : ℕ in atTop,
      (∫ ω, h ((rawX k ω - ∫ ω', rawX k ω' ∂disorderLaw) / s) ∂disorderLaw) ∈
        Set.Icc ((∫ z, h z ∂gaussianReal 0 1) - η / 2)
          ((∫ z, h z ∂gaussianReal 0 1) + η / 2) := by
    filter_upwards [hLatKx] with k hk
    rw [abs_le] at hk
    exact ⟨by linarith, by linarith⟩
  have hlimitIcc := isClosed_Icc.mem_of_tendsto hIntTend hIcc
  have hlimAbs :
      |(∫ ω, h ((Y ω - ∫ ω', Y ω' ∂P) / s) ∂P) -
        ∫ z, h z ∂gaussianReal 0 1| ≤ η / 2 := by
    rw [abs_le]
    exact ⟨by linarith [hlimitIcc.1], by linarith [hlimitIcc.2]⟩
  have hstrict :
      |(∫ ω, h ((Y ω - ∫ ω', Y ω' ∂P) / s) ∂P) -
        ∫ z, h z ∂gaussianReal 0 1| < η := by linarith
  simpa [Y, s, Real.dist_eq] using hstrict

end Critical2DKPZ.LogNormality

end
