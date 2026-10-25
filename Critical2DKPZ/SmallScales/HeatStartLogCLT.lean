/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SmallScales.HeatStartMoments
import Critical2DKPZ.Assembly.RegularizedInvariance
import Critical2DKPZ.Analysis.Heat.Moments
import Critical2DKPZ.SmallScales.DeterministicComparison
import Critical2DKPZ.SHF.Positivity.HeatPairingEhrhard
import Critical2DKPZ.JointConvergence.LogHeatFieldMeasurability
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # The heat-start logarithmic central limit theorem -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open Critical2DKPZ.SHF.Positivity
open scoped BoundedContinuousFunction Topology

universe u

namespace Critical2DKPZ.SmallScales

/-- Parabolic scaling extends heat-start logarithmic normality to every positive horizon. -/
theorem heatStartLog_logNormality_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hC8 : SmallScaleSHFLogNormality.{u})
    {T : ℝ} (hT : 0 < T) (x : Plane) :
    TendstoInDistribution
      (fun (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) ω =>
        (heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω -
          ∫ ω', heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω' ∂P) /
          Real.sqrt (Real.log (Real.log (ε : ℝ)⁻¹)))
      (Filter.comap Subtype.val (nhdsWithin 0 (Set.Ioi 0))) id (fun _ => P) (gaussianReal 0 1) := by
  let lT := Filter.comap (Subtype.val : Set.Ioo (0 : ℝ) (Real.sqrt T) → ℝ)
    (nhdsWithin 0 (Set.Ioi 0))
  let l1 := Filter.comap (Subtype.val : Set.Ioo (0 : ℝ) 1 → ℝ)
    (nhdsWithin 0 (Set.Ioi 0))
  let rT : ℝ := Real.sqrt T
  have hrT : 0 < rT := Real.sqrt_pos.mpr hT
  let εmap : Set.Ioo (0 : ℝ) (Real.sqrt T) → Set.Ioo (0 : ℝ) 1 := fun ε =>
    ⟨(ε : ℝ) / rT, div_pos ε.2.1 hrT,
      (div_lt_one hrT).2 ε.2.2⟩
  have hvalWithin : Tendsto (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) => (ε : ℝ)) lT
      (nhdsWithin 0 (Set.Ioi 0)) := Filter.tendsto_comap
  have hvalNhd : Tendsto (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) => (ε : ℝ)) lT (𝓝 0) :=
    hvalWithin.mono_right nhdsWithin_le_nhds
  have hscaledNhd : Tendsto (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) => (ε : ℝ) / rT)
      lT (𝓝 0) := by
    simpa only [Function.comp_def, id_eq, zero_div] using
      (continuous_id.div_const rT).continuousAt.tendsto.comp hvalNhd
  have hscaledWithin : Tendsto (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) => (ε : ℝ) / rT)
      lT (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hscaledNhd
    filter_upwards [] with ε
    exact Set.mem_Ioi.mpr (div_pos ε.2.1 hrT)
  have hεmap : Tendsto εmap lT l1 := by
    change Tendsto εmap lT ((nhdsWithin 0 (Set.Ioi 0)).comap Subtype.val)
    rw [Filter.tendsto_comap_iff]
    simpa only [εmap, Function.comp_def] using hscaledWithin
  let ZT : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun s t ω =>
    ENNReal.ofReal T⁻¹ • (Z (T * s) (T * t) ω).map
      (fun p => (rT⁻¹ • p.1, rT⁻¹ • p.2))
  have hZT : IsCriticalSHF (ϑ + Real.log T) P ZT := by
    simpa only [ZT, rT] using hsym.2.2.2.1 T hT
  have hC8unit := hC8 (ϑ + Real.log T) P ZT hZT (rT⁻¹ • x)
  let U : Set.Ioo (0 : ℝ) 1 → Ω → ℝ := fun η ω =>
    (heatStartLog ZT ((η : ℝ) ^ 2) 1 ((η : ℝ) ^ 2) (rT⁻¹ • x) ω -
      ∫ ω', heatStartLog ZT ((η : ℝ) ^ 2) 1 ((η : ℝ) ^ 2) (rT⁻¹ • x) ω' ∂P) /
      Real.sqrt (Real.log (Real.log (η : ℝ)⁻¹))
  have hC8reindexed : TendstoInDistribution (fun ε => U (εmap ε)) lT id
      (fun _ => P) (gaussianReal 0 1) := by
    refine ⟨fun ε => ?_,
      hC8unit.aemeasurable_limit, ?_⟩
    · simpa only [U, heatStartLog] using hC8unit.forall_aemeasurable (εmap ε)
    · exact hC8unit.tendsto.comp hεmap
  have hrootNe : rT ≠ 0 := ne_of_gt hrT
  have htime (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) :
      T * ((εmap ε : ℝ) ^ 2) = (ε : ℝ) ^ 2 := by
    dsimp [εmap, rT]
    rw [div_pow, Real.sq_sqrt hT.le]
    field_simp [hT.ne']
  have hkernel (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) (y : Plane) :
      heatKernel ((εmap ε : ℝ) ^ 2) (rT⁻¹ • y - rT⁻¹ • x) =
        T * heatKernel ((ε : ℝ) ^ 2) (y - x) := by
    have ha2 : rT⁻¹ ^ 2 = T⁻¹ := by
      dsimp [rT]
      rw [inv_pow, Real.sq_sqrt hT.le]
    have hscale := heatKernel_scaling (a := rT⁻¹) (u := (ε : ℝ) ^ 2)
      (inv_pos.mpr hrT) (y - x)
    calc
      heatKernel ((εmap ε : ℝ) ^ 2) (rT⁻¹ • y - rT⁻¹ • x) =
          heatKernel (rT⁻¹ ^ 2 * (ε : ℝ) ^ 2) (rT⁻¹ • (y - x)) := by
        congr 1
        · dsimp [εmap, rT]
          rw [div_pow, Real.sq_sqrt hT.le]
          rw [ha2, div_eq_mul_inv]
          ring
        · rw [← smul_sub]
      _ = (rT⁻¹ ^ 2)⁻¹ * heatKernel ((ε : ℝ) ^ 2) (y - x) := hscale
      _ = T * heatKernel ((ε : ℝ) ^ 2) (y - x) := by rw [ha2, inv_inv]
  have hpair (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) (ω : Ω) :
      shfPairing ZT ((εmap ε : ℝ) ^ 2) 1
          (fun y => heatKernel ((εmap ε : ℝ) ^ 2) (y - (rT⁻¹ • x))) (fun _ => 1) ω =
        shfPairing Z ((ε : ℝ) ^ 2) T
          (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω := by
    have htransport := Critical2DKPZ.Assembly.shfPairing_scaleTransport Z T rT hrootNe
      (ENNReal.ofReal T⁻¹) ((εmap ε : ℝ) ^ 2) 1
      (fun y => heatKernel ((εmap ε : ℝ) ^ 2) (y - (rT⁻¹ • x))) (fun _ => 1) ω
    calc
      _ = (ENNReal.ofReal T⁻¹).toReal *
          shfPairing Z (T * ((εmap ε : ℝ) ^ 2)) (T * 1)
            (fun y => heatKernel ((εmap ε : ℝ) ^ 2) (rT⁻¹ • y - rT⁻¹ • x))
            (fun _ => 1) ω := by
              simpa only [ZT] using htransport
      _ = T⁻¹ * shfPairing Z ((ε : ℝ) ^ 2) T
          (fun y => heatKernel ((εmap ε : ℝ) ^ 2) (rT⁻¹ • y - rT⁻¹ • x))
          (fun _ => 1) ω := by
            rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hT.le), htime, mul_one]
      _ = T⁻¹ * shfPairing Z ((ε : ℝ) ^ 2) T
          (fun y => T * heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω := by
            congr 3
            funext y
            exact hkernel ε y
      _ = shfPairing Z ((ε : ℝ) ^ 2) T
          (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω := by
            simp only [Critical2DKPZ.shfPairing, mul_one]
            rw [integral_const_mul]
            field_simp [hT.ne']
  have hpairPosOrig (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) :
      ∀ᵐ ω ∂P, 0 < shfPairing Z ((ε : ℝ) ^ 2) T
        (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω := by
    have hεT : (ε : ℝ) ^ 2 < T := by
      have hprod := mul_pos (sub_pos.mpr ε.2.2) (add_pos hrT ε.2.1)
      have hrT2 : rT ^ 2 = T := by dsimp [rT]; exact Real.sq_sqrt hT.le
      nlinarith [hprod]
    have h := isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
      ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x (0 : Plane →ᵇ ℝ)
      (sq_nonneg _) hεT (sq_pos_of_pos ε.2.1)
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using h.1
  have hpairPosZT (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) :
      ∀ᵐ ω ∂P, 0 < shfPairing ZT ((εmap ε : ℝ) ^ 2) 1
        (fun y => heatKernel ((εmap ε : ℝ) ^ 2) (y - (rT⁻¹ • x))) (fun _ => 1) ω := by
    have hε'pos : 0 < (εmap ε : ℝ) := (εmap ε).2.1
    have hε'lt : (εmap ε : ℝ) ^ 2 < 1 := by
      have hlt := (εmap ε).2.2
      nlinarith
    have h := isCriticalSHF_heat_pairing_pos_isEhrhardType (ϑ + Real.log T) P ZT hZT
      ((εmap ε : ℝ) ^ 2) 1 ((εmap ε : ℝ) ^ 2) (rT⁻¹ • x)
      (0 : Plane →ᵇ ℝ) (sq_nonneg _) hε'lt (sq_pos_of_pos hε'pos)
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using h.1
  have hlogEq (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) :
      (fun ω => heatStartLog ZT ((εmap ε : ℝ) ^ 2) 1 ((εmap ε : ℝ) ^ 2)
        (rT⁻¹ • x) ω) =ᵐ[P] fun ω => heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω := by
    filter_upwards [hpairPosZT ε, hpairPosOrig ε] with ω hposT hpos
    dsimp [heatStartLog]
    calc
      Real.log (shfPairing ZT ((εmap ε : ℝ) ^ 2) 1
          (fun y => heatKernel ((εmap ε : ℝ) ^ 2) (y - rT⁻¹ • x)) (fun _ => 1) ω) =
        Real.log (Real.exp (Real.log (shfPairing ZT ((εmap ε : ℝ) ^ 2) 1
          (fun y => heatKernel ((εmap ε : ℝ) ^ 2) (y - rT⁻¹ • x)) (fun _ => 1) ω))) := by
            rw [Real.exp_log hposT]
      _ = Real.log (Real.exp (Real.log (shfPairing Z ((ε : ℝ) ^ 2) T
          (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω))) := by
            rw [hpair ε ω]
      _ = Real.log (shfPairing Z ((ε : ℝ) ^ 2) T
          (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => 1) ω) := by
            rw [Real.exp_log hpos]
  have hlogMeanEq (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) :
      ∫ ω, heatStartLog ZT ((εmap ε : ℝ) ^ 2) 1 ((εmap ε : ℝ) ^ 2)
        (rT⁻¹ • x) ω ∂P =
      ∫ ω, heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω ∂P := by
    exact integral_congr_ae (hlogEq ε)
  let A : Set.Ioo (0 : ℝ) (Real.sqrt T) → ℝ := fun ε =>
    Real.log (Real.log (ε : ℝ)⁻¹)
  let B : Set.Ioo (0 : ℝ) (Real.sqrt T) → ℝ := fun ε =>
    Real.log (Real.log ((εmap ε : ℝ)⁻¹))
  let R : Set.Ioo (0 : ℝ) (Real.sqrt T) → ℝ := fun ε => Real.sqrt (B ε / A ε)
  have hlogInv : Tendsto (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) =>
      Real.log (ε : ℝ)⁻¹) lT atTop :=
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hvalWithin)
  have hA : Tendsto A lT atTop := by
    exact Real.tendsto_log_atTop.comp (by simpa only [A] using hlogInv)
  have hB : Tendsto B lT atTop := by
    have hvalMap : Tendsto (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) =>
        (εmap ε : ℝ)) lT (nhdsWithin 0 (Set.Ioi 0)) := hscaledWithin
    exact Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.comp hvalMap))
  have hBA : Tendsto (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) => B ε - A ε) lT (𝓝 0) := by
    have hc : Real.log rT = Real.log rT := rfl
    have hinner (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) :
        Real.log ((εmap ε : ℝ)⁻¹) = Real.log (ε : ℝ)⁻¹ + Real.log rT := by
      have he := (εmap ε).2.1
      calc
        Real.log ((εmap ε : ℝ)⁻¹) = Real.log (rT / (ε : ℝ)) := by
          congr 1
          dsimp [εmap]
          rw [inv_div]
        _ = Real.log rT - Real.log (ε : ℝ) :=
          Real.log_div hrootNe (ne_of_gt ε.2.1)
        _ = Real.log (ε : ℝ)⁻¹ + Real.log rT := by rw [Real.log_inv]; ring
    have hEq : (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) => B ε - A ε) =ᶠ[lT]
        fun ε => Real.log (Real.log (ε : ℝ)⁻¹ + Real.log rT) -
          Real.log (Real.log (ε : ℝ)⁻¹) := by
      filter_upwards [] with ε
      simp only [A, B, hinner]
    have h := (Real.tendsto_log_comp_add_sub_log (Real.log rT)).comp hlogInv
    exact h.congr' hEq.symm
  have hBAdiv : Tendsto (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) =>
      (B ε - A ε) / A ε) lT (𝓝 0) := hBA.div_atTop hA
  have hBdivA : Tendsto (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) => B ε / A ε)
      lT (𝓝 1) := by
    have hEq : (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) => 1 + (B ε - A ε) / A ε) =ᶠ[lT]
        fun ε => B ε / A ε := by
      filter_upwards [hA.eventually_gt_atTop 0] with ε hAε
      have hAne : A ε ≠ 0 := ne_of_gt hAε
      field_simp [hAne]
      ring
    have hone : Tendsto (fun _ : Set.Ioo (0 : ℝ) (Real.sqrt T) => (1 : ℝ))
        lT (𝓝 1) := tendsto_const_nhds
    have h : Tendsto (fun ε : Set.Ioo (0 : ℝ) (Real.sqrt T) =>
        1 + (B ε - A ε) / A ε) lT (𝓝 1) := by
      simpa only [add_zero] using hone.add hBAdiv
    exact h.congr' hEq
  have hR : Tendsto R lT (𝓝 1) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hBdivA
    simpa only [R, Function.comp_def, Real.sqrt_one] using hsqrt
  have hFactorMeasure : TendstoInMeasure P (fun ε ω => R ε) lT (1 : Ω → ℝ) := by
    rw [tendstoInMeasure_iff_norm]
    intro η hη
    have hclose := (Metric.tendsto_nhds.mp hR) η hη
    have hzero : ∀ᶠ ε in lT, P {ω | η ≤ ‖R ε - (1 : ℝ)‖} = 0 := by
      filter_upwards [hclose] with ε hε
      have hnorm : ‖R ε - 1‖ < η := by simpa [Real.dist_eq] using hε
      have hset : {ω : Ω | η ≤ ‖R ε - (1 : ℝ)‖} = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        intro ω hω
        exact (not_le_of_gt hnorm) hω
      rw [hset, measure_empty]
    have heq : (fun ε => P {ω | η ≤ ‖R ε - (1 : ℝ)‖}) =ᶠ[lT] fun _ => 0 := by
      filter_upwards [hzero] with ε hε
      exact hε
    exact tendsto_const_nhds.congr' heq.symm
  let V : Set.Ioo (0 : ℝ) (Real.sqrt T) → Ω → ℝ := fun ε ω =>
    (heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω -
      ∫ ω', heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω' ∂P) /
      Real.sqrt (A ε)
  have hUnitMean : ∀ ε, U (εmap ε) =ᵐ[P] fun ω =>
      (heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω -
        ∫ ω', heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω' ∂P) /
        Real.sqrt (B ε) := by
    intro ε
    filter_upwards [hlogEq ε] with ω hω
    simp only [U, B]
    rw [hω, hlogMeanEq ε]
  have hUnitCLT : TendstoInDistribution (fun (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) ω =>
      (heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω -
        ∫ ω', heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω' ∂P) /
        Real.sqrt (B ε)) lT id (fun _ => P) (gaussianReal 0 1) := by
    exact hC8reindexed.congr hUnitMean (Filter.EventuallyEq.rfl)
  have hSlutsky := hUnitCLT.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun q : ℝ × ℝ => q.1 * q.2)
    (by fun_prop)
    hFactorMeasure
    (fun ε => aemeasurable_const)
  have hratioPos : ∀ᶠ ε in lT, 0 < A ε ∧ 0 < B ε :=
    (hA.eventually_gt_atTop 0).and (hB.eventually_gt_atTop 0)
  have hTargetEq : ∀ᶠ ε in lT, (fun ω => V ε ω) =ᵐ[P]
      fun ω => ((heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω -
        ∫ ω', heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω' ∂P) /
        Real.sqrt (B ε)) * R ε := by
    filter_upwards [hratioPos] with ε hpos
    filter_upwards [] with ω
    simp only [V, R]
    have hsqrt : Real.sqrt (B ε / A ε) = Real.sqrt (B ε) / Real.sqrt (A ε) :=
      Real.sqrt_div hpos.2.le (A ε)
    rw [hsqrt]
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hpos.1),
      ne_of_gt (Real.sqrt_pos.mpr hpos.2)]
  have hTargetMeas (ε : Set.Ioo (0 : ℝ) (Real.sqrt T)) : AEMeasurable (V ε) P := by
    have hεT : (ε : ℝ) ^ 2 < T := by
      have hprod := mul_pos (sub_pos.mpr ε.2.2) (add_pos hrT ε.2.1)
      have hrT2 : rT ^ 2 = T := by dsimp [rT]; exact Real.sq_sqrt hT.le
      nlinarith [hprod]
    have hlog := isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
      ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x (0 : Plane →ᵇ ℝ)
      (sq_nonneg _) hεT (sq_pos_of_pos ε.2.1)
    have hlogMeas : AEMeasurable (heatStartLog Z ((ε : ℝ) ^ 2) T
        ((ε : ℝ) ^ 2) x) P := by
      change AEMeasurable (fun ω => Real.log (shfPairing Z ((ε : ℝ) ^ 2) T
        (fun y => heatKernel ((ε : ℝ) ^ 2) (y - x)) (fun _ => (1 : ℝ)) ω)) P
      simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hlog.2.1
    exact (hlogMeas.sub_const _).div_const _
  have hTargetMaps : ∀ᶠ ε in lT,
      P.map (V ε) = P.map (fun ω => ((heatStartLog Z ((ε : ℝ) ^ 2) T
        ((ε : ℝ) ^ 2) x ω -
        ∫ ω', heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω' ∂P) /
        Real.sqrt (B ε)) * R ε) := by
    filter_upwards [hTargetEq] with ε hε
    simpa only [Prod.fst, Prod.snd] using Measure.map_congr hε
  refine ⟨hTargetMeas, by fun_prop, ?_⟩
  have hlimitAE : (fun ω : ℝ => ((id ω, (1 : ℝ)).1 * (id ω, 1).2)) =ᵐ[gaussianReal 0 1]
      id := by
    filter_upwards [] with ω
    simp only [id_eq, mul_one]
  have hSlutskyId := hSlutsky.congr (fun _ => Filter.EventuallyEq.rfl) hlimitAE
  have hTargetProb : (fun ε => (⟨P.map (V ε), inferInstance⟩ : ProbabilityMeasure ℝ)) =ᶠ[lT]
      fun ε => ⟨P.map (fun ω => ((heatStartLog Z ((ε : ℝ) ^ 2) T
        ((ε : ℝ) ^ 2) x ω -
        ∫ ω', heatStartLog Z ((ε : ℝ) ^ 2) T ((ε : ℝ) ^ 2) x ω' ∂P) /
        Real.sqrt (B ε)) * R ε), inferInstance⟩ := by
    filter_upwards [hTargetMaps] with ε hε
    exact Subtype.ext hε
  exact Tendsto.congr' hTargetProb.symm hSlutskyId.tendsto

/-- The heat-start logarithm of a critical SHF is integrable at every positive smoothing scale. -/
theorem heatStartLog_integrable_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) :
    Integrable (heatStartLog Z s t δ x) P := by
  let h₀ : Plane →ᵇ ℝ := 0
  let Y : Ω → ℝ := fun ω => shfPairing Z s t
    (fun y => heatKernel δ (y - x)) (fun _ => 1) ω
  let L : Ω → ℝ := heatStartLog Z s t δ x
  obtain ⟨hYint, hYmean⟩ := heatStart_integral_eq_one ϑ P Z hZ hs hst hδ x
  have hlogPkg := isCriticalSHF_heat_pairing_pos_isEhrhardType ϑ P Z hZ
    s t δ x h₀ hs hst hδ
  have hterminal : (fun _ : Plane => Real.exp (0 : ℝ)) = fun _ => (1 : ℝ) := by
    funext y
    exact Real.exp_zero
  have hpairTerminal (ω : Ω) :
      shfPairing Z s t (fun y => heatKernel δ (y - x))
        (fun _ => Real.exp (0 : ℝ)) ω = Y ω := by
    rw [hterminal]
  have hlogEq : (fun ω => Real.log (shfPairing Z s t
      (fun y => heatKernel δ (y - x))
      (fun _ => Real.exp (0 : ℝ)) ω)) =ᵐ[P] L := by
    filter_upwards [] with ω
    dsimp [L, heatStartLog]
    rw [hterminal]
  have hYpos : ∀ᵐ ω ∂P, 0 < Y ω := by
    filter_upwards [hlogPkg.1] with ω hω
    rw [← hpairTerminal]
    exact hω
  have hLmeas : AEMeasurable L P := hlogPkg.2.1.congr hlogEq
  have hEhrhard : IsEhrhardType (P.map L) := by
    rw [← Measure.map_congr hlogEq]
    exact hlogPkg.2.2
  have hExpL : (fun ω => Real.exp (L ω)) =ᵐ[P] Y := by
    filter_upwards [hYpos] with ω hω
    dsimp [L, Y, heatStartLog]
    exact Real.exp_log hω
  have hExpLInt : Integrable (fun ω => Real.exp (L ω)) P := hYint.congr hExpL.symm
  have hExpLawInt : Integrable (fun r : ℝ => Real.exp r) (P.map L) :=
    (integrable_map_measure (by fun_prop) hLmeas).2 hExpLInt
  have hExpLawMean : ∫ r, Real.exp r ∂P.map L = 1 := by
    calc
      ∫ r, Real.exp r ∂P.map L = ∫ ω, Real.exp (L ω) ∂P :=
        integral_map hLmeas (by fun_prop)
      _ = ∫ ω, Y ω ∂P := integral_congr_ae hExpL
      _ = 1 := hYmean
  have hMom := Critical2DKPZ.Provider.ehrhardType_momentBounds
    (P.map L) hEhrhard hExpLawInt hExpLawMean
  have hLawIdMeas : AEStronglyMeasurable (id : ℝ → ℝ) (P.map L) := by fun_prop
  have hLawIdMem : MemLp (id : ℝ → ℝ) 2 (P.map L) :=
    (memLp_two_iff_integrable_sq hLawIdMeas).2 hMom.1
  have hLawIdInt : Integrable (id : ℝ → ℝ) (P.map L) :=
    hLawIdMem.integrable (by norm_num)
  have hLInt : Integrable L P :=
    (integrable_map_measure (by fun_prop) hLmeas).mp hLawIdInt
  simpa only [L] using hLInt

/-- The heat-start logarithm has a distribution independent of its spatial center under the stated symmetry hypothesis. -/
theorem heatStartLog_identDistrib_of (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t)
    (hδ : 0 < δ) (x : Plane) :
    IdentDistrib (heatStartLog Z s t δ x) (heatStartLog Z s t δ 0) P P := by
  let Zshift : ℝ → ℝ → Ω → Measure (Plane × Plane) := fun a b ω =>
    (Z a b ω).map fun p => (p.1 + -x, p.2 + -x)
  have hZshift : IsCriticalSHF ϑ P Zshift := by
    simpa only [Zshift] using hsym.1 (-x)
  let hbase := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ 0
    (1 : Plane →ᵇ ℝ)
  let htranslated := isCriticalSHF_heat_bounded_pairing ϑ P Zshift hZshift hs hst hδ 0
    (1 : Plane →ᵇ ℝ)
  let Y0 : Ω → ℝ := fun ω =>
    shfPairing Z s t (fun y => heatKernel δ (y - 0)) (fun _ => 1) ω
  let Yx : Ω → ℝ := fun ω =>
    shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun _ => 1) ω
  let Yshift : Ω → ℝ := fun ω =>
    shfPairing Zshift s t (fun y => heatKernel δ (y - 0)) (fun _ => 1) ω
  have hpair (ω : Ω) :
      Yshift ω = Yx ω := by
    have h := Critical2DKPZ.Assembly.shfPairing_compAffine Z s t (-x)
      (LinearIsometryEquiv.refl ℝ Plane) (fun y => heatKernel δ (y - 0))
      (fun _ => 1) ω
    have hZmap :
        (fun p : Plane × Plane =>
          (-x + (LinearIsometryEquiv.refl ℝ Plane) p.1,
            -x + (LinearIsometryEquiv.refl ℝ Plane) p.2)) =
          (fun p => (p.1 + -x, p.2 + -x)) := by
      funext p
      apply Prod.ext
      · change -x + p.1 = p.1 + -x
        abel
      · change -x + p.2 = p.2 + -x
        abel
    have hkernel :
        (fun y : Plane => heatKernel δ
          (-x + (LinearIsometryEquiv.refl ℝ Plane) y - 0)) =
          (fun y => heatKernel δ (y - x)) := by
      funext y
      congr 1
      change -x + y - 0 = y - x
      abel
    change shfPairing (fun a b ω => (Z a b ω).map (fun p => (p.1 + -x, p.2 + -x)))
      s t (fun y => heatKernel δ (y - 0)) (fun _ => 1) ω = _
    rw [← hZmap]
    rw [hkernel] at h
    simpa only [sub_zero] using h
  have htranslated' := htranslated.2.2.2.congr
    (fun _ => Filter.EventuallyEq.rfl)
    (Filter.Eventually.of_forall hpair)
  have hmap : P.map Y0 = P.map Yx := by
    have hlim := tendsto_nhds_unique hbase.2.2.2.tendsto htranslated'.tendsto
    exact congrArg ProbabilityMeasure.toMeasure hlim
  have hYxInt : Integrable Yx P := by
    have hae : Yshift =ᵐ[P] Yx := Filter.Eventually.of_forall hpair
    exact htranslated.2.1.congr hae
  have hPairIdent : IdentDistrib Yx Y0 P P :=
    ⟨hYxInt.aemeasurable, hbase.2.1.aemeasurable, hmap.symm⟩
  have hLogIdent := hPairIdent.comp Real.measurable_log
  change IdentDistrib (fun ω => Real.log
    (shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun _ => 1) ω))
    (fun ω => Real.log
      (shfPairing Z s t (fun y => heatKernel δ (y - 0)) (fun _ => 1) ω)) P P
  exact hLogIdent

private theorem heatKernel_le_two_mul_heatKernel {δ : ℝ} (hδ : 0 < δ)
    {y q u : Plane} (hyq : ‖y - q‖ ≤ 1) :
    heatKernel δ (u - y) ≤
      2 * Real.exp (1 / (2 * δ)) * heatKernel (2 * δ) (u - q) := by
  rw [heatKernel_eq_exp, heatKernel_eq_exp]
  have hcoef : (2 * Real.pi * δ)⁻¹ = 2 * (2 * Real.pi * (2 * δ))⁻¹ := by
    field_simp
  have hquad :
      -((2 * δ)⁻¹) * ‖u - y‖ ^ 2 +
        ((2 * (2 * δ))⁻¹) * ‖u - q‖ ^ 2 ≤ 1 / (2 * δ) := by
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
    apply Real.exp_le_exp.mpr
    linarith [hquad]
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
    (μ : Measure Plane) {δ : ℝ} (hδ : 0 < δ)
    (hwide : ∀ q : Plane, Integrable (fun u : Plane => heatKernel (2 * δ) (u - q)) μ) :
    Continuous (fun y : Plane => ∫ u, heatKernel δ (u - y) ∂μ) := by
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
  have hbound : ∀ᶠ y in 𝓝 y₀, ∀ᵐ u ∂μ,
      ‖heatKernel δ (u - y)‖ ≤ C * heatKernel (2 * δ) (u - q) := by
    filter_upwards [hnear] with y hy
    filter_upwards [] with u
    rw [Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg hδ.le _)]
    simpa only [C] using heatKernel_le_two_mul_heatKernel hδ hy
  have hFmeas : ∀ᶠ y in 𝓝 y₀,
      AEStronglyMeasurable (fun u : Plane => heatKernel δ (u - y)) μ :=
    Filter.Eventually.of_forall fun y =>
      ((continuous_heatKernel δ).comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have hboundInt : Integrable (fun u : Plane => C * heatKernel (2 * δ) (u - q)) μ :=
    (hwide q).const_mul C |>.congr (Filter.Eventually.of_forall fun u => by ring)
  have hlim : ∀ᵐ u ∂μ, Tendsto (fun y : Plane => heatKernel δ (u - y))
      (𝓝 y₀) (𝓝 (heatKernel δ (u - y₀))) := by
    filter_upwards [] with u
    exact (((continuous_heatKernel δ).comp (continuous_const.sub continuous_id)).continuousAt).tendsto
  have hcont := tendsto_integral_filter_of_dominated_convergence
    (fun u : Plane => C * heatKernel (2 * δ) (u - q)) hFmeas hbound hboundInt hlim
  change Tendsto (fun y : Plane => ∫ u, heatKernel δ (u - y) ∂μ)
    (𝓝 y₀) (𝓝 (∫ u, heatKernel δ (u - y₀) ∂μ))
  exact hcont

private theorem continuous_testFn_affine_sub_const (φ : TestFn) (F : Plane → ℝ)
    (hF : Continuous F) (x : Plane) (ε c : ℝ) :
    Continuous (fun z : Plane => φ z * (F (x + ε • z) - c)) := by
  let A : Plane → Plane := fun z => x + ε • z
  have hA : Continuous A := by
    change Continuous (fun z : Plane => x + ε • z)
    fun_prop
  change Continuous (fun z => φ z * (F (A z) - c))
  exact φ.continuous.mul ((hF.comp hA).sub continuous_const)


private theorem integrable_testFn_affine_continuous_sub_const (φ : TestFn)
    (F : Plane → ℝ) (hF : Continuous F) (x : Plane) (ε c : ℝ) :
    Integrable (fun z : Plane => φ z * (F (x + ε • z) - c)) := by
  apply (continuous_testFn_affine_sub_const φ F hF x ε c).integrable_of_hasCompactSupport
  exact HasCompactSupport.mul_right
    (f := fun z : Plane => φ z)
    (f' := fun z => F (x + ε • z) - c) φ.hasCompactSupport

private theorem heatStartLog_average_lower_bound_ae_of (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) {T : ℝ} (_hT : 0 < T)
    (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y) (hφ₁ : ∫ y, φ y = 1) (x : Plane)
    {ε : ℝ} (hε : 0 < ε) (hεT : ε ^ 2 < T) :
    ∀ᵐ ω ∂P, -(∫ z, φ z * ‖z - barycentre φ‖ ^ 2) / 2 ≤
      (∫ y, φ.dilate ε x y * heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
        heatStartLog Z (ε ^ 2) T (ε ^ 2) (x + ε • barycentre φ) ω := by
  let δ : ℝ := ε ^ 2
  let b : Plane := x + ε • barycentre φ
  have hlow := ae_integrable_heat_start_all_centers_of ϑ P Z hZ
    (sq_nonneg ε) hεT (sq_pos_of_pos hε)
  have hwide := ae_integrable_heat_start_all_centers_of ϑ P Z hZ
    (sq_nonneg ε) hεT (mul_pos two_pos (sq_pos_of_pos hε))
  have hpos0 := hsym.2.2.2.2.2.2 δ T δ 0 (0 : Plane →ᵇ ℝ)
    (by dsimp [δ]; positivity) hεT (by dsimp [δ]; exact sq_pos_of_pos hε)
  filter_upwards [hlow, hwide, hpos0.1] with ω hlowω hwideω hposω
  let μ : Measure Plane := (Z δ T ω).map Prod.fst
  have hlowμ (y : Plane) : Integrable (fun u : Plane => heatKernel δ (u - y)) μ := by
    have hpull : Integrable
        ((fun u : Plane => heatKernel δ (u - y)) ∘ Prod.fst) (Z δ T ω) := by
      change Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - y)) (Z δ T ω)
      simpa only [δ] using hlowω y
    exact (integrable_map_measure
      (((measurable_heatKernel δ).comp (measurable_id.sub_const y)).aestronglyMeasurable)
      measurable_fst.aemeasurable).mpr hpull
  have hwideμ (y : Plane) : Integrable (fun u : Plane => heatKernel (2 * δ) (u - y)) μ := by
    have hpull : Integrable
        ((fun u : Plane => heatKernel (2 * δ) (u - y)) ∘ Prod.fst) (Z δ T ω) := by
      change Integrable (fun p : Plane × Plane => heatKernel (2 * δ) (p.1 - y))
        (Z δ T ω)
      simpa only [δ] using hwideω y
    exact (integrable_map_measure
      (((measurable_heatKernel (2 * δ)).comp (measurable_id.sub_const y)).aestronglyMeasurable)
      measurable_fst.aemeasurable).mpr hpull
  have hpairEq (y : Plane) :
      shfPairing Z δ T (fun u => heatKernel δ (u - y)) (fun _ => 1) ω =
        ∫ u, heatKernel δ (u - y) ∂μ := by
    calc
      shfPairing Z δ T (fun u => heatKernel δ (u - y)) (fun _ => 1) ω =
          ∫ p, heatKernel δ (p.1 - y) ∂(Z δ T ω) := by
            simp only [shfPairing, mul_one]
      _ = ∫ u, heatKernel δ (u - y) ∂μ :=
        (integral_map measurable_fst.aemeasurable
          (hlowμ y).aestronglyMeasurable).symm
  have hposZ0 : 0 < ∫ p : Plane × Plane, heatKernel δ p.1 ∂(Z δ T ω) := by
    simpa [shfPairing] using hposω
  have hsupport0 : Function.support
      (fun p : Plane × Plane => heatKernel δ p.1) = Set.univ := by
    ext p
    simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
    exact (heatKernel_pos (sq_pos_of_pos hε) p.1).ne'
  have hmassPos : 0 < μ Set.univ := by
    have hInt0 : Integrable
        (fun p : Plane × Plane => heatKernel δ p.1) (Z δ T ω) := by
      convert hlowω (0 : Plane) using 1
      funext p
      congr 1
      exact (sub_zero p.1).symm
    have hsupp := (integral_pos_iff_support_of_nonneg
      (fun p : Plane × Plane => heatKernel_nonneg (sq_pos_of_pos hε).le p.1)
      hInt0).mp hposZ0
    rw [hsupport0] at hsupp
    simpa only [μ, Measure.map_apply_of_aemeasurable measurable_fst.aemeasurable
      MeasurableSet.univ, Set.preimage_univ] using hsupp
  have hpμ (y : Plane) : 0 < ∫ u, heatKernel δ (u - y) ∂μ := by
    apply (integral_pos_iff_support_of_nonneg
      (fun u => heatKernel_nonneg (sq_pos_of_pos hε).le (u - y)) (hlowμ y)).2
    have hsupp : Function.support (fun u : Plane => heatKernel δ (u - y)) = Set.univ := by
      ext u
      simp only [Function.mem_support, ne_eq, Set.mem_univ, iff_true]
      exact (heatKernel_pos (sq_pos_of_pos hε) (u - y)).ne'
    rw [hsupp]
    exact hmassPos
  have hfirstZ : Integrable
      (fun p : Plane × Plane => heatKernel δ (p.1 - b) • p.1) (Z δ T ω) := by
    let C : ℝ := (1 + ‖b‖) * (2 * Real.exp (1 / (2 * δ))) + 8 * δ
    have hmajor : Integrable
        (fun p : Plane × Plane => C * heatKernel (2 * δ) (p.1 - b)) (Z δ T ω) := by
      have h := (hwideω b).const_mul C
      simpa only [δ, mul_comm] using h
    apply hmajor.mono'
      (((continuous_heatKernel δ).comp (continuous_fst.sub continuous_const)).smul
        continuous_fst).aestronglyMeasurable
    filter_upwards [] with p
    change ‖heatKernel δ (p.1 - b) • p.1‖ ≤ C * heatKernel (2 * δ) (p.1 - b)
    have hr : ‖p.1 - b‖ ≤ 1 + ‖p.1 - b‖ ^ 2 := by
      nlinarith [sq_nonneg (‖p.1 - b‖ - 1 / 2)]
    have hu : ‖p.1‖ ≤ 1 + ‖p.1 - b‖ ^ 2 + ‖b‖ := by
      calc
        ‖p.1‖ = ‖(p.1 - b) + b‖ := by congr 1; abel_nf
        _ ≤ ‖p.1 - b‖ + ‖b‖ := norm_add_le _ _
        _ ≤ 1 + ‖p.1 - b‖ ^ 2 + ‖b‖ := by linarith
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (heatKernel_nonneg (sq_pos_of_pos hε).le (p.1 - b))]
    have hk := heatKernel_le_two_mul_heatKernel (sq_pos_of_pos hε) (by simp)
      (u := p.1) (y := b) (q := b)
    have hpow := norm_pow_mul_heatKernel_le (sq_pos_of_pos hε) 1 (p.1 - b)
    have hpow' : ‖p.1 - b‖ ^ 2 * heatKernel δ (p.1 - b) ≤
        8 * δ * heatKernel (2 * δ) (p.1 - b) := by
      have hpow0 := hpow
      have hfac : (Nat.factorial 1 : ℝ) = 1 := by norm_num
      rw [Nat.mul_one, hfac, pow_one] at hpow0
      have hpow1 : ‖p.1 - b‖ ^ 2 * heatKernel δ (p.1 - b) ≤
          2 * (4 * δ) * heatKernel (2 * δ) (p.1 - b) := by
        simpa only [one_mul, mul_one] using hpow0
      calc
        _ ≤ 2 * (4 * δ) * heatKernel (2 * δ) (p.1 - b) := hpow1
        _ = 8 * δ * heatKernel (2 * δ) (p.1 - b) := by ring
    calc
      heatKernel δ (p.1 - b) * ‖p.1‖ ≤
          heatKernel δ (p.1 - b) *
            (1 + ‖p.1 - b‖ ^ 2 + ‖b‖) :=
        mul_le_mul_of_nonneg_left hu (heatKernel_nonneg (sq_pos_of_pos hε).le _)
      _ = (1 + ‖b‖) * heatKernel δ (p.1 - b) +
          ‖p.1 - b‖ ^ 2 * heatKernel δ (p.1 - b) := by ring
      _ ≤ (1 + ‖b‖) * (2 * Real.exp (1 / (2 * δ)) *
            heatKernel (2 * δ) (p.1 - b)) +
          8 * δ * heatKernel (2 * δ) (p.1 - b) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hk (by positivity)) hpow'
      _ = C * heatKernel (2 * δ) (p.1 - b) := by dsimp [C]; ring
  have hfirstμ : Integrable
      (fun u : Plane => heatKernel δ (u - b) • u) μ := by
    exact (integrable_map_measure
      (((continuous_heatKernel δ).comp (continuous_id.sub continuous_const)).smul
        continuous_id).aestronglyMeasurable measurable_fst.aemeasurable).mpr hfirstZ
  have hpairCont := continuous_heatKernel_pairing_of_doubled_integrability μ
    (sq_pos_of_pos hε) hwideμ
  have hlogCont : Continuous (fun y : Plane =>
      Real.log (∫ u, heatKernel δ (u - y) ∂μ)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    have hpairAt : ContinuousAt (fun y : Plane =>
        ∫ u, heatKernel δ (u - y) ∂μ) y := hpairCont.continuousAt
    exact ContinuousAt.comp
      (f := fun y : Plane => ∫ u, heatKernel δ (u - y) ∂μ)
      (g := Real.log) (x := y)
      (Real.continuousAt_log (ne_of_gt (hpμ y))) hpairAt
  let F : Plane → ℝ := fun y => Real.log (∫ u, heatKernel δ (u - y) ∂μ)
  have hFcont : Continuous F := by simpa only [F] using hlogCont
  have hlogInt : Integrable (fun z : Plane => φ z * (F (x + ε • z) - F b)) := by
    exact integrable_testFn_affine_continuous_sub_const φ F hFcont x ε (F b)
  have hlogInt' : Integrable (fun z : Plane => φ z *
      (Real.log (∫ u, heatKernel δ (u - (x + ε • z)) ∂μ) -
        Real.log (∫ u, heatKernel δ (u - b) ∂μ))) := by
    simpa only [F] using hlogInt
  have hdet := heatLog_average_sub_lower_bound μ φ hφ hφ₁ x hε
    hlowμ hpμ hfirstμ hlogInt'
  have hlogEq (y : Plane) : F y =
      heatStartLog Z δ T δ y ω := by
    dsimp [F, heatStartLog]
    exact congrArg Real.log (hpairEq y).symm
  have hlogEqb : Real.log (∫ u, heatKernel δ (u - b) ∂μ) =
      heatStartLog Z δ T δ b ω := by
    simpa only [b] using hlogEq b
  have hlogEq' (y : Plane) : Real.log (∫ u, heatKernel δ (u - y) ∂μ) =
      heatStartLog Z δ T δ y ω := by
    simpa only [F] using hlogEq y
  simpa only [δ, hlogEq', hlogEqb] using hdet.2

/-- The averaged heat-start log differs from its barycentric value by an amount controlled in
mean absolute value by the second moment of the test function. -/
theorem heatStartLog_average_sub_le_of (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (hZ : IsCriticalSHF ϑ P Z) (hsym : ShfSymmetriesAt ϑ P Z)
    {T : ℝ} (hT : 0 < T) (φ : TestFn) (hφ : ∀ y, 0 ≤ φ y)
    (hφ₁ : ∫ y, φ y = 1) (x : Plane) {ε : ℝ} (hε : 0 < ε) (hεT : ε ^ 2 < T) :
    Integrable (fun ω => (∫ y, φ.dilate ε x y *
        heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
      heatStartLog Z (ε ^ 2) T (ε ^ 2) (x + ε • barycentre φ) ω) P ∧
      ∫ ω, |(∫ y, φ.dilate ε x y *
          heatStartLog Z (ε ^ 2) T (ε ^ 2) y ω) -
        heatStartLog Z (ε ^ 2) T (ε ^ 2) (x + ε • barycentre φ) ω| ∂P ≤
        ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by
  let δ : ℝ := ε ^ 2
  let w : Plane → ℝ := φ.dilate ε x
  let Y : Plane × Ω → ℝ := fun q => heatStartLog Z δ T δ q.1 q.2
  let A : Plane × Ω → ℝ := fun q => w q.1 * Y q
  let X : Ω → ℝ := fun ω => (∫ y, A (y, ω) ∂volume) -
    Y (x + ε • barycentre φ, ω)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsδ : 0 ≤ δ := le_of_lt hδ
  have hδT : δ < T := by simpa only [δ] using hεT
  have hwcont : Continuous w := by simpa only [w] using (φ.dilate ε x).continuous
  have hwcs : HasCompactSupport w := by
    simpa only [w] using (φ.dilate ε x).hasCompactSupport
  have hYjoint : AEMeasurable Y (volume.prod P) := by
    let μ : Ω → Measure (Plane × Plane) := Z δ T
    have hlocal : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
      filter_upwards [hZ.2.1 δ T hsδ hδT] with ω hω
      exact hω.1
    have h := Critical2DKPZ.JointConvergence.aemeasurable_log_heatPairing_joint P μ
      (hZ.1 δ T hsδ hδT) hlocal δ hδ (fun _ : Plane => (1 : ℝ))
      measurable_const (fun _ => by norm_num)
    simpa only [Y, μ, heatStartLog, shfPairing, mul_one] using h
  have hAmeas : AEMeasurable A (volume.prod P) := by
    exact ((hwcont.measurable.comp measurable_fst).aemeasurable).mul hYjoint
  have hident (y : Plane) : IdentDistrib (fun ω => Y (y, ω))
      (fun ω => Y (0, ω)) P P :=
    heatStartLog_identDistrib_of ϑ P Z hZ hsym hsδ hδT hδ y
  have hYint (y : Plane) : Integrable (fun ω => Y (y, ω)) P :=
    heatStartLog_integrable_of ϑ P Z hZ hsδ hδT hδ y
  have hYabs0 : Integrable (fun ω => |Y (0, ω)|) P := (hYint 0).abs
  let C : ℝ := ∫ ω, |Y (0, ω)| ∂P
  have hYabsEq (y : Plane) : ∫ ω, |Y (y, ω)| ∂P = C := by
    have h := (hident y).norm.integral_eq
    simpa only [Real.norm_eq_abs, C] using h
  have hYmean (y : Plane) : ∫ ω, Y (y, ω) ∂P = ∫ ω, Y (0, ω) ∂P :=
    (hident y).integral_eq
  have hwabs : Integrable (fun y : Plane => |w y|) :=
    (hwcont.integrable_of_hasCompactSupport hwcs).norm
  have hCw : Integrable (fun y : Plane => C * |w y|) := hwabs.const_mul C
  have hAsection (y : Plane) : Integrable (fun ω => A (y, ω)) P := by
    simpa only [A, Y] using (hYint y).const_mul (w y)
  have hAnorm (y : Plane) : ∫ ω, ‖A (y, ω)‖ ∂P = C * |w y| := by
    calc
      ∫ ω, ‖A (y, ω)‖ ∂P = |w y| * ∫ ω, |Y (y, ω)| ∂P := by
        simp only [A, Y, Real.norm_eq_abs, abs_mul]
        rw [integral_const_mul]
      _ = C * |w y| := by rw [hYabsEq y]; ring
  have hAprod : Integrable A (volume.prod P) := by
    apply (integrable_prod_iff hAmeas.aestronglyMeasurable).2
    constructor
    · exact Filter.Eventually.of_forall hAsection
    · have hnorm : (fun y : Plane => ∫ ω, ‖A (y, ω)‖ ∂P) =
          fun y => C * |w y| := by
        funext y
        exact hAnorm y
      rw [hnorm]
      exact hCw
  have hAvgInt : Integrable (fun ω => ∫ y, A (y, ω) ∂volume) P :=
    hAprod.integral_prod_right
  have hpointInt : Integrable (fun ω => Y (x + ε • barycentre φ, ω)) P :=
    hYint (x + ε • barycentre φ)
  have hXInt : Integrable X P := hAvgInt.sub hpointInt
  have hweightMass : ∫ y, w y = 1 := by
    dsimp [w]
    simpa only [mul_one, hφ₁] using integral_testFn_dilate_mul φ hε x (fun _ => 1)
  have hweightedMean (y : Plane) :
      ∫ ω, A (y, ω) ∂P = w y * ∫ ω, Y (0, ω) ∂P := by
    calc
      ∫ ω, A (y, ω) ∂P = ∫ ω, w y * Y (y, ω) ∂P := by rfl
      _ = w y * ∫ ω, Y (y, ω) ∂P := integral_const_mul _ _
      _ = w y * ∫ ω, Y (0, ω) ∂P := by rw [hYmean y]
  have hAvgMean : ∫ ω, (∫ y, A (y, ω) ∂volume) ∂P =
      ∫ ω, Y (0, ω) ∂P := by
    calc
      _ = ∫ q, A q ∂(volume.prod P) := (integral_prod_symm A hAprod).symm
      _ = ∫ y, (∫ ω, A (y, ω) ∂P) ∂volume := integral_prod A hAprod
      _ = ∫ y, w y * (∫ ω, Y (0, ω) ∂P) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall hweightedMean
      _ = ∫ ω, Y (0, ω) ∂P := by rw [integral_mul_const, hweightMass, one_mul]
  have hpointMean : ∫ ω, Y (x + ε • barycentre φ, ω) ∂P =
      ∫ ω, Y (0, ω) ∂P := hYmean (x + ε • barycentre φ)
  have hXmean : ∫ ω, X ω ∂P = 0 := by
    change ∫ ω, ((∫ y, A (y, ω) ∂volume) -
      Y (x + ε • barycentre φ, ω)) ∂P = 0
    rw [integral_sub hAvgInt hpointInt, hAvgMean, hpointMean]
    ring
  have hcostNonneg : 0 ≤ ∫ z, φ z * ‖z - barycentre φ‖ ^ 2 :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall fun z =>
      mul_nonneg (hφ z) (sq_nonneg _))
  let B : ℝ := (∫ z, φ z * ‖z - barycentre φ‖ ^ 2) / 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hbound : ∀ᵐ ω ∂P, -B ≤ X ω := by
    filter_upwards [heatStartLog_average_lower_bound_ae_of ϑ P Z hZ hsym hT
      φ hφ hφ₁ x hε hεT] with ω hω
    have hBform : -B = -(∫ z, φ z * ‖z - barycentre φ‖ ^ 2) / 2 := by
      dsimp [B]
      ring
    rw [hBform]
    simpa only [X, A, Y, w, δ] using hω
  have hscalar := integral_abs_le_of_mean_zero_of_lower_bound P hXInt hXmean hB hbound
  have hresult : ∫ ω, |X ω| ∂P ≤ ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by
    calc
      ∫ ω, |X ω| ∂P ≤ 2 * B := hscalar.2
      _ = ∫ y, φ y * ‖y - barycentre φ‖ ^ 2 := by
        dsimp [B]
        ring
  refine ⟨?_, ?_⟩
  · simpa only [X, A, Y, w, δ] using hXInt
  · simpa only [X, A, Y, w, δ] using hresult

end Critical2DKPZ.SmallScales

end
