/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.HeatStartLogMean
public import Critical2DKPZ.LocalSobolev.ReversalLaw
public import Critical2DKPZ.Differentiation.RandomHeat
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic

/-! # Heat-density collapse at a flat SHF endpoint -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev Critical2DKPZ.SmallScales
open scoped BoundedContinuousFunction ENNReal Topology

universe u

namespace Critical2DKPZ.NonGaussian

private noncomputable def heatEvalFirst (δ : ℝ) (x : Plane)
    (μ : Measure (Plane × Plane)) : ℝ :=
  (∫⁻ p, ENNReal.ofReal (heatKernel δ (p.1 - x)) ∂μ).toReal

private theorem measurable_heatEvalFirst (δ : ℝ) (x : Plane) :
    Measurable (heatEvalFirst δ x) := by
  unfold heatEvalFirst
  exact (Measure.measurable_lintegral
    (ENNReal.measurable_ofReal.comp ((measurable_heatKernel δ).comp
      (measurable_fst.sub_const x)))).ennreal_toReal

private theorem heatEvalFirst_map_swap (δ : ℝ) (x : Plane)
    (μ : Measure (Plane × Plane)) :
    heatEvalFirst δ x (μ.map Prod.swap) =
      (∫⁻ p, ENNReal.ofReal (heatKernel δ (p.2 - x)) ∂μ).toReal := by
  change (∫⁻ p : Plane × Plane,
      ENNReal.ofReal (heatKernel δ (p.1 - x)) ∂Measure.map Prod.swap μ).toReal = _
  congr 1
  exact lintegral_map
    (ENNReal.measurable_ofReal.comp ((measurable_heatKernel δ).comp
      (measurable_fst.sub_const x))) measurable_swap

private theorem heatPairing_eq_heatEvalFirst (δ : ℝ) (hδ : 0 < δ) (x : Plane)
    (μ : Measure (Plane × Plane)) :
    (∫ p, heatKernel δ (p.2 - x) ∂μ) =
      (∫⁻ p, ENNReal.ofReal (heatKernel δ (p.2 - x)) ∂μ).toReal := by
  apply integral_eq_lintegral_of_nonneg_ae
  · exact Filter.Eventually.of_forall fun p => heatKernel_nonneg hδ.le _
  · exact ((measurable_heatKernel δ).comp (measurable_snd.sub_const x)).aestronglyMeasurable

private theorem heatStartPairing_eq_heatEvalFirst (δ : ℝ) (hδ : 0 < δ) (x : Plane)
    (μ : Measure (Plane × Plane)) :
    (∫ p, heatKernel δ (p.1 - x) ∂μ) = heatEvalFirst δ x μ := by
  unfold heatEvalFirst
  apply integral_eq_lintegral_of_nonneg_ae
  · exact Filter.Eventually.of_forall fun p => heatKernel_nonneg hδ.le _
  · exact ((measurable_heatKernel δ).comp (measurable_fst.sub_const x)).aestronglyMeasurable

/-- Reversal identifies the law of the flat-endpoint heat pairing with the law of a heat-start pairing. -/
private theorem flatEndpoint_heatPairing_law (ϑ : ℝ) {Ω : Type u}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) :
    P.map (fun ω => shfPairing Z s t (fun _ => 1)
        (fun y => heatKernel δ (y - x)) ω) =
      P.map (fun ω => shfPairing Z 0 (t - s)
        (fun y => heatKernel δ (y - x)) (fun _ => 1) ω) := by
  let W : Ω → Measure (Plane × Plane) := fun ω => (Z s t ω).map Prod.swap
  let V : Ω → Measure (Plane × Plane) := fun ω => Z 0 (t - s) ω
  have hτ : 0 < t - s := sub_pos.mpr hst
  have hτt : t - s ≤ t := by linarith
  let F : Ω → Fin 1 → Measure (Plane × Plane) := fun ω i =>
    (Z (t - (t - s)) (t - 0) ω).map Prod.swap
  let G : Ω → Fin 1 → Measure (Plane × Plane) := fun ω i => Z 0 (t - s) ω
  have hrev := shfReversal_measureLaw_of ϑ P Z hZ t 1
    (fun _ => 0) (fun _ => t - s) (fun _ => ⟨le_rfl, hτ, hτt⟩)
  have hW : Measurable W := by
    dsimp [W]
    exact (Measure.measurable_map Prod.swap measurable_swap).comp (hZ.1 s t hs hst)
  have hV : Measurable V := by
    dsimp [V]
    exact hZ.1 0 (t - s) (le_rfl) hτ
  have hF : Measurable F := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp [F]
    exact (Measure.measurable_map Prod.swap measurable_swap).comp
      (hZ.1 (t - (t - s)) (t - 0) (by linarith) (by linarith))
  have hG : Measurable G := by
    apply measurable_pi_iff.mpr
    intro i
    dsimp [G]
    exact hZ.1 0 (t - s) le_rfl hτ
  have hproj : Measurable (fun v : Fin 1 → Measure (Plane × Plane) => v 0) :=
    measurable_pi_apply 0
  have hWlaw : P.map W = P.map V := by
    calc
      P.map W = P.map (fun ω => F ω 0) :=
        Measure.map_congr (Filter.Eventually.of_forall fun ω => by simp [F, W])
      _ = (P.map F).map (fun v => v 0) := (Measure.map_map hproj hF).symm
      _ = (P.map G).map (fun v => v 0) := by rw [hrev]
      _ = P.map (fun ω => G ω 0) := Measure.map_map hproj hG
      _ = P.map V := Measure.map_congr (Filter.Eventually.of_forall fun ω => by simp [G, V])
  have hEval := measurable_heatEvalFirst δ x
  have hlaw : P.map (fun ω => heatEvalFirst δ x (W ω)) =
      P.map (fun ω => heatEvalFirst δ x (V ω)) := by
    calc
      P.map (fun ω => heatEvalFirst δ x (W ω)) = (P.map W).map (heatEvalFirst δ x) :=
        (Measure.map_map hEval hW).symm
      _ = (P.map V).map (heatEvalFirst δ x) := by rw [hWlaw]
      _ = P.map (fun ω => heatEvalFirst δ x (V ω)) := Measure.map_map hEval hV
  have hleft (ω : Ω) : heatEvalFirst δ x (W ω) =
      shfPairing Z s t (fun _ => 1) (fun y => heatKernel δ (y - x)) ω := by
    rw [heatEvalFirst_map_swap]
    unfold shfPairing
    simp only [one_mul]
    exact (heatPairing_eq_heatEvalFirst δ hδ x (Z s t ω)).symm
  have hright (ω : Ω) : heatEvalFirst δ x (V ω) =
      shfPairing Z 0 (t - s) (fun y => heatKernel δ (y - x)) (fun _ => 1) ω := by
    unfold V shfPairing
    simp only [mul_one]
    exact (heatStartPairing_eq_heatEvalFirst δ hδ x (Z 0 (t - s) ω)).symm
  rw [← Measure.map_congr (Filter.Eventually.of_forall hleft), hlaw,
    Measure.map_congr (Filter.Eventually.of_forall hright)]

/-- At each fixed spatial point, the flat SHF endpoint heat density tends to zero in probability
as the heat scale vanishes. -/
theorem shf_heatDensity_tendstoInMeasure_of (hVD : Smoothing.PropVDBound) (ϑ : ℝ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (hsq : HeatStartSqAt P Z) (hdense : DenseSHFAt ϑ P Z)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (x : Plane) :
    TendstoInMeasure P
      (fun δ ω => shfPairing Z s t (fun _ => 1)
        (fun y => heatKernel δ (y - x)) ω)
      (nhdsWithin 0 (Set.Ioi 0)) (fun _ => 0) := by
  have hτ : 0 < t - s := sub_pos.mpr hst
  obtain ⟨C, δ₀, hδ₀, hmean⟩ :=
    heatStartLog_mean_asymp_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense
      (τ₀ := t - s) (τ₁ := t - s) hτ
  obtain ⟨C₂, δ₂, hδ₂, hmom⟩ :=
    heatStartLog_moments_le_of ϑ P Z hZ hsym hHeatStartLogInput
      (τ₀ := t - s) (τ₁ := t - s) hτ
  let L : ℝ → Ω → ℝ := fun δ ω => heatStartLog Z 0 (t - s) δ x ω
  let A : ℝ → ℝ := fun δ => -∫ ω, L δ ω ∂P
  have hloglog : Tendsto (fun δ : ℝ => Real.log (Real.log δ⁻¹))
      (nhdsWithin 0 (Set.Ioi 0)) atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero)
  have hscaled : Tendsto (fun δ : ℝ => (1 / 2 : ℝ) * Real.log (Real.log δ⁻¹))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := hloglog.const_mul_atTop (by norm_num)
  have hA : Tendsto A (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    have hlarge := hscaled.eventually_ge_atTop (b + C + 1)
    have hsmall := nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (Iio_mem_nhds hδ₀)
    filter_upwards [hlarge, hsmall, self_mem_nhdsWithin] with δ hlarge hsmall hδ
    have hlogmean := hmean 0 (t - s) δ le_rfl (by simp) (by simp) hδ hsmall x
    have hbound : |(∫ ω, L δ ω ∂P) +
        (1 / 2 : ℝ) * Real.log (Real.log δ⁻¹)| ≤ C := by
      simpa only [L, heatStartLog] using hlogmean.2
    have hhigh := (abs_le.mp hbound).2
    dsimp [A]
    linarith
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  let B : ℝ := max 1 (2 * |Real.log ε|)
  have hAevent := hA.eventually_ge_atTop B
  have hmomEvent := nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (Iio_mem_nhds hδ₂)
  have hsmallMean := nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)) (Iio_mem_nhds hδ₀)
  have htailBound : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
      P {ω | ε ≤ |shfPairing Z s t (fun _ => 1)
          (fun y => heatKernel δ (y - x)) ω|} ≤ ENNReal.ofReal (8 / A δ) := by
    filter_upwards [hAevent, hmomEvent, hsmallMean, self_mem_nhdsWithin] with δ hAδ hδ₂' hδ₀' hδ
    let a := A δ
    let Y : Ω → ℝ := fun ω => shfPairing Z 0 (t - s)
      (fun y => heatKernel δ (y - x)) (fun _ => 1) ω
    let X : Ω → ℝ := fun ω => shfPairing Z s t (fun _ => 1)
      (fun y => heatKernel δ (y - x)) ω
    have hδlt : δ ≤ δ₂ := hδ₂'.le
    have hδlt₀ : δ < δ₀ := hδ₀'
    obtain ⟨hLmem, hA_nonneg, hvar, _hupper⟩ :=
      hmom 0 (t - s) δ le_rfl (by simp) (by simp) hδ hδlt x
    have hAeq : a = -∫ ω, L δ ω ∂P := rfl
    have hApos : 0 < a := lt_of_lt_of_le (by dsimp [B]; positivity) hAδ
    have hvar' : Var[L δ; P] ≤ 2 * a := by rw [hAeq]; nlinarith [hvar]
    have hAmean : (∫ ω, L δ ω ∂P) = -a := by dsimp [a, A]; ring
    have hB : 2 * |Real.log ε| ≤ a := le_trans (le_max_right _ _) hAδ
    have hlogε : -|Real.log ε| ≤ Real.log ε := neg_abs_le _
    have hthreshold : a / 2 ≤ a + Real.log ε := by nlinarith
    have hpos : ∀ᵐ ω ∂P, 0 < Y ω := by
      simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using
        (hsym.2.2.2.2.2.2 0 (t - s) δ x (0 : Plane →ᵇ ℝ) le_rfl hτ hδ).1
    have hsubset : ∀ᵐ ω ∂P, ε ≤ |Y ω| →
        a / 2 ≤ |L δ ω - ∫ z, L δ z ∂P| := by
      filter_upwards [hpos] with ω hω
      intro hωε
      have hYge : ε ≤ Y ω := by simpa [abs_of_pos hω] using hωε
      have hlog := Real.log_le_log hε hYge
      have hdev : a / 2 ≤ L δ ω - ∫ z, L δ z ∂P := by
        rw [hAmean]
        dsimp [L, heatStartLog] at hlog ⊢
        linarith
      exact hdev.trans (le_abs_self _)
    have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hLmem
      (show 0 < a / 2 by positivity)
    have hsubsetMeasure := measure_mono_ae hsubset
    have hrate : Var[L δ; P] / (a / 2) ^ 2 ≤ 8 / a := by
      rw [div_le_iff₀ (sq_pos_of_ne_zero (by positivity))]
      have hid : 8 / a * (a / 2) ^ 2 = 2 * a := by field_simp; ring
      rw [hid]
      exact hvar'
    have hYbound : P {ω | ε ≤ |Y ω|} ≤ ENNReal.ofReal (8 / a) := by
      calc
        P {ω | ε ≤ |Y ω|} ≤ P {ω | a / 2 ≤ |L δ ω - ∫ z, L δ z ∂P|} := hsubsetMeasure
        _ ≤ ENNReal.ofReal (Var[L δ; P] / (a / 2) ^ 2) := hcheb
        _ ≤ ENNReal.ofReal (8 / a) := ENNReal.ofReal_le_ofReal hrate
    have hlaw := flatEndpoint_heatPairing_law ϑ P Z hZ hs hst hδ x
    have hset : MeasurableSet {z : ℝ | ε ≤ |z|} :=
      measurableSet_le measurable_const measurable_abs
    have hXmeas : AEMeasurable X P := by
      have h := (measurable_heatEvalFirst δ x).comp
        ((Measure.measurable_map Prod.swap measurable_swap).comp (hZ.1 s t hs hst))
      exact h.aemeasurable.congr (Filter.Eventually.of_forall fun ω => (by
        dsimp [X]
        rw [heatEvalFirst_map_swap]
        unfold shfPairing
        simp only [one_mul]
        exact (heatPairing_eq_heatEvalFirst δ hδ x (Z s t ω)).symm))
    have hYmeas : AEMeasurable Y P := by
      have h := (measurable_heatEvalFirst δ x).comp (hZ.1 0 (t - s) le_rfl hτ)
      exact h.aemeasurable.congr (Filter.Eventually.of_forall fun ω => by
        dsimp [Y, heatEvalFirst]
        unfold shfPairing
        simp only [mul_one]
        exact (heatStartPairing_eq_heatEvalFirst δ hδ x (Z 0 (t - s) ω)).symm)
    have hlawMeasure : P {ω | ε ≤ |X ω|} = P {ω | ε ≤ |Y ω|} := by
      calc
        P {ω | ε ≤ |X ω|} = (P.map X) {z | ε ≤ |z|} :=
          (Measure.map_apply_of_aemeasurable hXmeas hset).symm
        _ = (P.map Y) {z | ε ≤ |z|} := by rw [hlaw]
        _ = P {ω | ε ≤ |Y ω|} := Measure.map_apply_of_aemeasurable hYmeas hset
    simpa [X, Y, a] using hlawMeasure.trans_le hYbound
  have hrate : Tendsto (fun δ : ℝ => ENNReal.ofReal (8 / A δ))
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    have hAinv := Filter.Tendsto.inv_tendsto_atTop hA
    have hreal : Tendsto (fun δ : ℝ => 8 / A δ) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
      simpa [div_eq_mul_inv, mul_comm] using hAinv.const_mul 8
    simpa using ENNReal.tendsto_ofReal hreal
  have htailNorm : ∀ᶠ δ in nhdsWithin 0 (Set.Ioi 0),
      P {ω | ε ≤ ‖shfPairing Z s t (fun _ => 1)
        (fun y => heatKernel δ (y - x)) ω - 0‖} ≤ ENNReal.ofReal (8 / A δ) := by
    filter_upwards [htailBound] with δ hδ
    simpa only [Real.norm_eq_abs, sub_zero] using hδ
  exact ENNReal.tendsto_nhds_zero.mpr fun η hη => by
    filter_upwards [htailNorm, hrate.eventually (Iio_mem_nhds hη)] with δ htail hrateδ
    exact (lt_of_le_of_lt htail hrateδ).le

end Critical2DKPZ.NonGaussian

end
