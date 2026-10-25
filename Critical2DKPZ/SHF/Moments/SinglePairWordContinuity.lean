/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordSpatial
import Critical2DKPZ.Analysis.Heat.Semigroup
import Mathlib.Tactic

/-! # Continuity of the continuum tested two-particle future profile -/

@[expose] public section

noncomputable section

namespace Critical2DKPZ.SHF.Moments

open MeasureTheory Filter
open scoped CompactlySupported Topology

/-- The terminal heat convolution of one compact pair test. -/
def pairTwoTerminalConvolution (φ : C_c(Plane × Plane, ℝ))
    (q : ℝ) (a w : Plane) : ℝ :=
  ∫ y : Plane, φ (a, y) * heatKernel q (y - w)

/-- The terminal convolution integrand is integrable, and its integral is
bounded by the uniform norm of the test, uniformly in both spatial arguments. -/
theorem pairTwoTerminalConvolution_integrable_bound
    (φ : C_c(Plane × Plane, ℝ)) {q : ℝ} (hq : 0 < q) (a w : Plane) :
    Integrable (fun y : Plane => φ (a, y) * heatKernel q (y - w)) ∧
      |pairTwoTerminalConvolution φ q a w| ≤ ‖φ.toBoundedContinuousFunction‖ := by
  let M : ℝ := ‖φ.toBoundedContinuousFunction‖
  have hheat : Integrable (fun y : Plane => heatKernel q (y - w)) :=
    (integrable_heatKernel hq).comp_sub_right w
  have hmajorant : Integrable (fun y : Plane => M * heatKernel q (y - w)) :=
    hheat.const_mul M
  have hmeas : AEStronglyMeasurable (fun y : Plane => φ (a, y) * heatKernel q (y - w)) :=
    ((φ.continuous.comp (continuous_const.prodMk continuous_id)).mul
      ((continuous_heatKernel q).comp (continuous_id.sub continuous_const))).aestronglyMeasurable
  have hbound (y : Plane) : ‖φ (a, y) * heatKernel q (y - w)‖ ≤ M * heatKernel q (y - w) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hq.le _)]
    exact mul_le_mul_of_nonneg_right (φ.toBoundedContinuousFunction.norm_coe_le_norm _)
      (heatKernel_nonneg hq.le _)
  refine ⟨hmajorant.mono' hmeas (Eventually.of_forall hbound), ?_⟩
  have he := norm_integral_le_of_norm_le hmajorant (Eventually.of_forall hbound)
  rw [integral_const_mul, integral_heatKernel_sub hq w, mul_one] at he
  exact he

/-- Positive terminal times give joint continuity in time, incoming endpoint,
and collision location. Compact terminal support supplies a common majorant. -/
theorem continuousAt_pairTwoTerminalConvolution
    (φ : C_c(Plane × Plane, ℝ)) (p : ℝ × Plane × Plane) (hp : 0 < p.1) :
    ContinuousAt (fun p : ℝ × Plane × Plane =>
      pairTwoTerminalConvolution φ p.1 p.2.1 p.2.2) p := by
  let K : Set Plane := Prod.snd '' tsupport φ
  have hK : IsCompact K := φ.hasCompactSupport.image continuous_snd
  let M : ℝ := ‖φ.toBoundedContinuousFunction‖
  let H : ℝ := (2 * Real.pi * (p.1 / 2))⁻¹
  have hM : 0 ≤ M := norm_nonneg _
  have hH : 0 < H := by dsimp [H]; positivity
  let B : Plane → ℝ := K.indicator (fun _ => M * H)
  have hB : Integrable B :=
    (integrableOn_const (C := M * H) hK.measure_ne_top).integrable_indicator hK.measurableSet
  have htime : ∀ᶠ p' : ℝ × Plane × Plane in 𝓝 p, p.1 / 2 < p'.1 :=
    continuous_fst.continuousAt.tendsto.eventually (Ioi_mem_nhds (half_lt_self hp))
  apply continuousAt_of_dominated (bound := B)
  · exact Eventually.of_forall fun p' =>
      ((φ.continuous.comp (continuous_const.prodMk continuous_id)).mul
        ((continuous_heatKernel p'.1).comp (continuous_id.sub continuous_const))).aestronglyMeasurable
  · filter_upwards [htime] with p' hp'
    apply Eventually.of_forall
    intro y
    by_cases hzero : φ (p'.2.1, y) = 0
    · by_cases hy : y ∈ K <;> simp [hzero, B, hy, mul_nonneg hM hH.le]
    · have hy : y ∈ K := ⟨(p'.2.1, y), subset_closure (Function.mem_support.mpr hzero), rfl⟩
      have hpos : 0 < p'.1 := (half_pos hp).trans hp'
      have hheat : heatKernel p'.1 (y - p'.2.2) ≤ H := by
        apply (heatKernel_le_at_zero hpos.le _).trans
        apply (inv_le_inv₀ (by positivity) (by positivity)).2
        exact mul_le_mul_of_nonneg_left hp'.le (by positivity)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hpos.le _)]
      have he := mul_le_mul (φ.toBoundedContinuousFunction.norm_coe_le_norm (p'.2.1, y))
        hheat (heatKernel_nonneg hpos.le _) hM
      exact he.trans_eq (by simp [B, hy, M])
  · exact hB
  · apply Eventually.of_forall
    intro y
    have hφ : ContinuousAt (fun p' : ℝ × Plane × Plane => φ (p'.2.1, y)) p :=
      φ.continuous.continuousAt.comp
        (continuous_snd.fst.continuousAt.prodMk continuousAt_const)
    have hc : ContinuousAt (fun p' : ℝ × Plane => heatKernel p'.1 p'.2)
        (p.1, y - p.2.2) := DeltaBose.continuousOn_heatKernel.continuousAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hp)
    have harg : ContinuousAt (fun p' : ℝ × Plane × Plane => (p'.1, y - p'.2.2)) p :=
      continuousAt_fst.prodMk (continuousAt_const.sub continuous_snd.snd.continuousAt)
    have hheat : ContinuousAt (fun p' : ℝ × Plane × Plane => heatKernel p'.1 (y - p'.2.2)) p :=
      hc.tendsto.comp harg.tendsto
    exact hφ.mul hheat

/-- At a fixed positive terminal time the terminal convolution is continuous
in its collision location. -/
theorem continuous_pairTwoTerminalConvolution_location
    (φ : C_c(Plane × Plane, ℝ)) {q : ℝ} (hq : 0 < q) (a : Plane) :
    Continuous (pairTwoTerminalConvolution φ q a) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  have h := continuousAt_pairTwoTerminalConvolution φ (q, a, w) hq
  have harg : ContinuousAt (fun w' : Plane => (q, a, w')) w :=
    continuousAt_const.prodMk (continuousAt_const.prodMk continuousAt_id)
  exact h.tendsto.comp harg.tendsto

/-- The spatial convolution of the two terminal profiles, with the scalar
renewal density kept outside the integral. -/
def pairTwoTestedSpatialProfile (θ v q : ℝ)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) : ℝ :=
  (16 * Real.pi) * DeltaBose.scalarDensity θ v *
    ∫ d : Plane, heatKernel (v / 2) d *
      pairTwoTerminalConvolution (φ 0) q (a 0) (z + d) *
      pairTwoTerminalConvolution (φ 1) q (a 1) (z + d)

private theorem heatKernel_half_time_slab_le
    {u v : ℝ} (hu : 0 < u) (hlo : u / 2 ≤ v) (hhi : v ≤ 2 * u) (d : Plane) :
    heatKernel (v / 2) d ≤ 4 * heatKernel u d := by
  have hv : 0 < v := (half_pos hu).trans_le hlo
  have hcoef : (2 * Real.pi * (v / 2))⁻¹ ≤ 4 * (2 * Real.pi * u)⁻¹ := by
    have h := (inv_le_inv₀ (by positivity : 0 < 2 * Real.pi * (v / 2))
      (by positivity : 0 < 2 * Real.pi * (u / 4))).2
        (mul_le_mul_of_nonneg_left (by linarith only [hlo]) (by positivity))
    have heq : (2 * Real.pi * (u / 4))⁻¹ = 4 * (2 * Real.pi * u)⁻¹ := by field_simp
    exact h.trans_eq heq
  have hexp : Real.exp (-‖d‖ ^ 2 / (2 * (v / 2))) ≤
      Real.exp (-‖d‖ ^ 2 / (2 * u)) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_div]
    apply neg_le_neg
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (by linarith only [hhi])
  unfold heatKernel
  calc
    _ ≤ (4 * (2 * Real.pi * u)⁻¹) * Real.exp (-‖d‖ ^ 2 / (2 * u)) :=
      mul_le_mul hcoef hexp (Real.exp_nonneg _) (by positivity)
    _ = _ := by ring

private theorem integrable_pairTwoSpatialProfile_integrand
    {v q : ℝ} (hv : 0 < v) (hq : 0 < q)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    Integrable (fun d : Plane => heatKernel (v / 2) d *
      pairTwoTerminalConvolution (φ 0) q (a 0) (z + d) *
      pairTwoTerminalConvolution (φ 1) q (a 1) (z + d)) := by
  let M : Fin 2 → ℝ := fun i => ‖(φ i).toBoundedContinuousFunction‖
  have hM (i : Fin 2) : 0 ≤ M i := norm_nonneg _
  have hbound (d : Plane) : ‖heatKernel (v / 2) d *
      pairTwoTerminalConvolution (φ 0) q (a 0) (z + d) *
      pairTwoTerminalConvolution (φ 1) q (a 1) (z + d)‖ ≤
        (M 0 * M 1) * heatKernel (v / 2) d := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (heatKernel_nonneg (by positivity) _)]
    have h₀ := (pairTwoTerminalConvolution_integrable_bound (φ 0) hq (a 0) (z + d)).2
    have h₁ := (pairTwoTerminalConvolution_integrable_bound (φ 1) hq (a 1) (z + d)).2
    calc
      _ ≤ (heatKernel (v / 2) d * M 0) * M 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h₀ (heatKernel_nonneg (by positivity) _))
          h₁ (abs_nonneg _) (mul_nonneg (heatKernel_nonneg (half_pos hv).le d) (hM 0))
      _ = _ := by ring
  have hcont : Continuous (fun d : Plane => heatKernel (v / 2) d *
      pairTwoTerminalConvolution (φ 0) q (a 0) (z + d) *
      pairTwoTerminalConvolution (φ 1) q (a 1) (z + d)) := by
    exact ((continuous_heatKernel (v / 2)).mul
      ((continuous_pairTwoTerminalConvolution_location (φ 0) hq (a 0)).comp
        (continuous_const.add continuous_id))).mul
      ((continuous_pairTwoTerminalConvolution_location (φ 1) hq (a 1)).comp
        (continuous_const.add continuous_id))
  exact ((integrable_heatKernel (half_pos hv)).const_mul (M 0 * M 1)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall hbound)

private theorem continuousAt_pairTwoSpatialIntegrand
    (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (p : (ℝ × ℝ) × (Fin 2 → Plane) × Plane)
    (hv : 0 < p.1.1) (hq : 0 < p.1.2) (d : Plane) :
    ContinuousAt (fun p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
      heatKernel (p'.1.1 / 2) d *
        pairTwoTerminalConvolution (φ 0) p'.1.2 (p'.2.1 0) (p'.2.2 + d) *
        pairTwoTerminalConvolution (φ 1) p'.1.2 (p'.2.1 1) (p'.2.2 + d)) p := by
  have hheat : ContinuousAt (fun p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
      heatKernel (p'.1.1 / 2) d) p := by
    have hc := DeltaBose.continuousOn_heatKernel.continuousAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds (half_pos hv)) (x := (p.1.1 / 2, d))
    have harg : ContinuousAt (fun p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
        (p'.1.1 / 2, d)) p :=
      (continuous_fst.fst.continuousAt.div_const 2).prodMk continuousAt_const
    exact hc.tendsto.comp harg.tendsto
  have hterminal (i : Fin 2) : ContinuousAt
      (fun p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
        pairTwoTerminalConvolution (φ i) p'.1.2 (p'.2.1 i) (p'.2.2 + d)) p := by
    have hc := continuousAt_pairTwoTerminalConvolution (φ i)
      (p.1.2, p.2.1 i, p.2.2 + d) hq
    have harg : ContinuousAt (fun p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
        (p'.1.2, p'.2.1 i, p'.2.2 + d)) p :=
      continuous_fst.snd.continuousAt.prodMk
        (((continuous_apply i).comp continuous_snd.fst).continuousAt.prodMk
          (continuous_snd.snd.continuousAt.add_const d))
    exact hc.tendsto.comp harg.tendsto
  exact (hheat.mul (hterminal 0)).mul (hterminal 1)

private theorem continuousAt_pairTwoSpatialProfile_integral
    (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (p : (ℝ × ℝ) × (Fin 2 → Plane) × Plane)
    (hv : 0 < p.1.1) (hq : 0 < p.1.2) :
    ContinuousAt (fun p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
      ∫ d : Plane, heatKernel (p'.1.1 / 2) d *
        pairTwoTerminalConvolution (φ 0) p'.1.2 (p'.2.1 0) (p'.2.2 + d) *
        pairTwoTerminalConvolution (φ 1) p'.1.2 (p'.2.1 1) (p'.2.2 + d)) p := by
  let M : Fin 2 → ℝ := fun i => ‖(φ i).toBoundedContinuousFunction‖
  have hM (i : Fin 2) : 0 ≤ M i := norm_nonneg _
  let B : Plane → ℝ := fun d => (4 * M 0 * M 1) * heatKernel p.1.1 d
  have hB : Integrable B := (integrable_heatKernel hv).const_mul _
  have hnear : ∀ᶠ p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane in 𝓝 p,
      p.1.1 / 2 < p'.1.1 ∧ p'.1.1 < 2 * p.1.1 ∧ 0 < p'.1.2 := by
    have hv' := continuous_fst.fst.continuousAt.tendsto.eventually
      (Ioo_mem_nhds (half_lt_self hv) (by linarith only [hv] : p.1.1 < 2 * p.1.1))
    have hq' := continuous_fst.snd.continuousAt.tendsto.eventually (Ioi_mem_nhds hq)
    filter_upwards [hv', hq'] with p' hv' hq'
    exact ⟨hv'.1, hv'.2, hq'⟩
  apply continuousAt_of_dominated (bound := B)
  · filter_upwards [hnear] with p' hp'
    exact (integrable_pairTwoSpatialProfile_integrand
      ((half_pos hv).trans hp'.1) hp'.2.2 φ p'.2.1 p'.2.2).aestronglyMeasurable
  · filter_upwards [hnear] with p' hp'
    apply Eventually.of_forall
    intro d
    have h₀ := (pairTwoTerminalConvolution_integrable_bound (φ 0) hp'.2.2 (p'.2.1 0) (p'.2.2 + d)).2
    have h₁ := (pairTwoTerminalConvolution_integrable_bound (φ 1) hp'.2.2 (p'.2.1 1) (p'.2.2 + d)).2
    have hheat := heatKernel_half_time_slab_le hv hp'.1.le hp'.2.1.le d
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (heatKernel_nonneg (by linarith only [hp'.1, hv]) _)]
    calc
      _ ≤ (4 * heatKernel p.1.1 d * M 0) * M 1 :=
        mul_le_mul (mul_le_mul hheat h₀ (abs_nonneg _)
          (mul_nonneg (by norm_num) (heatKernel_nonneg hv.le d))) h₁
          (abs_nonneg _) (mul_nonneg (mul_nonneg (by norm_num) (heatKernel_nonneg hv.le d)) (hM 0))
      _ = B d := by dsimp [B]; ring
  · exact hB
  · apply Eventually.of_forall
    intro d
    exact continuousAt_pairTwoSpatialIntegrand φ p hv hq d

/-- The spatially integrated terminal profiles are jointly continuous at
positive renewal and terminal times, including their incoming and collision
locations. -/
theorem continuousAt_pairTwoTestedSpatialProfile
    (θ : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ))
    (p : (ℝ × ℝ) × (Fin 2 → Plane) × Plane)
    (hv : 0 < p.1.1) (hq : 0 < p.1.2) :
    ContinuousAt (fun p : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
      pairTwoTestedSpatialProfile θ p.1.1 p.1.2 φ p.2.1 p.2.2) p := by
  have hInt := continuousAt_pairTwoSpatialProfile_integral φ p hv hq
  have hscalar : ContinuousAt (fun p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
      DeltaBose.scalarDensity θ p'.1.1) p := by
    have hc : ContinuousAt (fun r : ℝ × ℝ => DeltaBose.scalarDensity r.1 r.2) (θ, p.1.1) :=
      DeltaBose.continuousOn_scalarDensity.continuousAt
        ((isOpen_lt continuous_const continuous_snd).mem_nhds hv)
    have harg : ContinuousAt (fun p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane => (θ, p'.1.1)) p :=
      continuousAt_const.prodMk continuous_fst.fst.continuousAt
    exact ContinuousAt.comp' (f := fun p' : (ℝ × ℝ) × (Fin 2 → Plane) × Plane => (θ, p'.1.1))
      (g := fun r : ℝ × ℝ => DeltaBose.scalarDensity r.1 r.2) hc harg
  dsimp only [pairTwoTestedSpatialProfile]
  exact ((continuousAt_const.mul hscalar).mul hInt)

/-- The continuum spatial profile is dominated by the scalar renewal density,
with integrability of its spatial integrand stated explicitly. -/
theorem pairTwoTestedSpatialProfile_integrable_bound
    (θ v q : ℝ) (hv : 0 < v) (hq : 0 < q)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    Integrable (fun d : Plane => heatKernel (v / 2) d *
      pairTwoTerminalConvolution (φ 0) q (a 0) (z + d) *
      pairTwoTerminalConvolution (φ 1) q (a 1) (z + d)) ∧
    |pairTwoTestedSpatialProfile θ v q φ a z| ≤
      16 * Real.pi * DeltaBose.scalarDensity θ v *
        ‖(φ 0).toBoundedContinuousFunction‖ * ‖(φ 1).toBoundedContinuousFunction‖ := by
  let M : Fin 2 → ℝ := fun i => ‖(φ i).toBoundedContinuousFunction‖
  have hM (i : Fin 2) : 0 ≤ M i := norm_nonneg _
  refine ⟨integrable_pairTwoSpatialProfile_integrand hv hq φ a z, ?_⟩
  have hb (d : Plane) : ‖heatKernel (v / 2) d *
      pairTwoTerminalConvolution (φ 0) q (a 0) (z + d) *
      pairTwoTerminalConvolution (φ 1) q (a 1) (z + d)‖ ≤
      (M 0 * M 1) * heatKernel (v / 2) d := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (heatKernel_nonneg (half_pos hv).le _)]
    have h₀ := (pairTwoTerminalConvolution_integrable_bound (φ 0) hq (a 0) (z + d)).2
    have h₁ := (pairTwoTerminalConvolution_integrable_bound (φ 1) hq (a 1) (z + d)).2
    calc
      _ ≤ (heatKernel (v / 2) d * M 0) * M 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left h₀ (heatKernel_nonneg (half_pos hv).le _))
          h₁ (abs_nonneg _) (mul_nonneg (heatKernel_nonneg (half_pos hv).le _) (hM 0))
      _ = _ := by ring
  have he := norm_integral_le_of_norm_le
    ((integrable_heatKernel (half_pos hv)).const_mul (M 0 * M 1)) (Eventually.of_forall hb)
  rw [integral_const_mul, integral_heatKernel (half_pos hv), mul_one] at he
  have hρ := (DeltaBose.scalarDensity_pos θ hv).le
  unfold pairTwoTestedSpatialProfile
  rw [abs_mul, abs_of_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 16 * Real.pi) hρ)]
  calc
    _ ≤ (16 * Real.pi * DeltaBose.scalarDensity θ v) * (M 0 * M 1) :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = _ := by ring

/-- The spatial profile is continuous throughout the open renewal-time interval
of every positive total horizon. -/
theorem continuousOn_pairTwoTestedSpatialProfile_time
    (θ H : ℝ) (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    ContinuousOn (fun u => pairTwoTestedSpatialProfile θ u (H - u) φ a z)
      (Set.Ioo 0 H) := by
  intro u hu
  have hc := continuousAt_pairTwoTestedSpatialProfile θ φ ((u, H - u), a, z)
    hu.1 (sub_pos.mpr hu.2)
  have harg : ContinuousAt (fun v : ℝ => ((v, H - v), a, z)) u :=
    (continuousAt_id.prodMk (continuousAt_const.sub continuousAt_id)).prodMk continuousAt_const
  have h : ContinuousAt (fun v => pairTwoTestedSpatialProfile θ v (H - v) φ a z) u :=
    ContinuousAt.comp'
      (f := fun v : ℝ => ((v, H - v), a, z))
      (g := fun p : (ℝ × ℝ) × (Fin 2 → Plane) × Plane =>
        pairTwoTestedSpatialProfile θ p.1.1 p.1.2 φ p.2.1 p.2.2) hc harg
  exact h.continuousWithinAt

end Critical2DKPZ.SHF.Moments

end
