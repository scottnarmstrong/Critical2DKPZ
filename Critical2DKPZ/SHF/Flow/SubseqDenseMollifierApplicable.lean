/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.SubseqDenseMollifier
public import Critical2DKPZ.SHF.Tsai.HeatKernelL2
public import Critical2DKPZ.SHF.Tsai.CompactTensorTests
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Applicability of compact mollifiers for dense subsequential limits -/

@[expose] public section

open MeasureTheory
open Filter
open scoped CompactlySupported Convolution Pointwise Topology

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Tsai

/-- A shrinking rescaling of the canonical localizer bump. -/
noncomputable def subseqDenseMollifierBump (n : ℕ) : ContDiffBump (0 : Plane) where
  rIn := 1 / ((n : ℝ) + 1)
  rOut := 2 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply div_lt_div_of_pos_right
    · norm_num
    · positivity

/-- The bump rescaling agrees with the canonical localizer at the rescaled argument. -/
theorem subseqDenseMollifierBump_apply (n : ℕ) (x : Plane) :
    subseqDenseMollifierBump n x = Critical2DKPZ.localizerBump 0
      (((n : ℝ) + 1) • x) := by
  let a : ℝ := (n : ℝ) + 1
  have ha : 0 < a := by dsimp [a]; positivity
  rw [(subseqDenseMollifierBump n).apply,
    (Critical2DKPZ.localizerBump 0).apply]
  simp only [subseqDenseMollifierBump, Critical2DKPZ.localizerBump]
  have hratio : (2 / a) / (1 / a) = (2 : ℝ) := by field_simp [ha.ne']
  have hinv : (1 / a : ℝ)⁻¹ = a := by field_simp [ha.ne']
  rw [hratio, hinv]
  norm_num [a]

/-- The shrinking bump density is exactly the scaled normalized profile. -/
theorem subseqDenseMollifier_eq_normedBump (n : ℕ) :
    subseqDenseMollifier n = fun x => (subseqDenseMollifierBump n).normed volume x := by
  funext x
  let a : ℝ := (n : ℝ) + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hd : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  have hscale := Measure.integral_comp_smul volume
    (Critical2DKPZ.localizerBump 0) a
  rw [hd, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg a)), smul_eq_mul] at hscale
  have hintegral :
      (∫ y : Plane, subseqDenseMollifierBump n y) = (a ^ 2)⁻¹ *
        ∫ y : Plane, Critical2DKPZ.localizerBump 0 y := by
    calc
      (∫ y : Plane, subseqDenseMollifierBump n y) =
          ∫ y : Plane, Critical2DKPZ.localizerBump 0 (a • y) := by
            apply integral_congr_ae
            filter_upwards [] with y
            exact subseqDenseMollifierBump_apply n y
      _ = (a ^ 2)⁻¹ * ∫ y : Plane, Critical2DKPZ.localizerBump 0 y := hscale
  rw [subseqDenseMollifier, subseqDenseMollifierBase]
  change a ^ 2 * (Critical2DKPZ.localizerBump 0).normed volume (a • x) =
    (subseqDenseMollifierBump n).normed volume x
  rw [(subseqDenseMollifierBump n).normed_def x,
    subseqDenseMollifierBump_apply n x, hintegral,
    (Critical2DKPZ.localizerBump 0).normed_def (a • x)]
  have hI : (∫ y : Plane, Critical2DKPZ.localizerBump 0 y) ≠ 0 :=
    (Critical2DKPZ.localizerBump 0).integral_pos.ne'
  field_simp [ha.ne', hI]
  simp [a]

/-- The convolution action is the usual additive-group convolution. -/
theorem mollifierAction_eq_convolution (w φ : Plane → ℝ) (x : Plane) :
    mollifierAction w φ x = (w ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] φ) x := by
  change (∫ y, w (x - y) * φ y) = ∫ y, w y * φ (x - y)
  have h := integral_sub_left_eq_self (fun y : Plane => w (x - y) * φ y) volume x
  simpa only [sub_sub_cancel] using h.symm

/-- Compact continuous inputs are approximated pointwise by the rescaled compact profiles. -/
theorem tendsto_mollifierAction_subseqDenseMollifier_compact (g : C_c(Plane, ℝ)) (x : Plane) :
    Tendsto (fun n => mollifierAction (subseqDenseMollifier n) g x) atTop (𝓝 (g x)) := by
  have hpoint (n : ℕ) : mollifierAction (subseqDenseMollifier n) g x =
      ((subseqDenseMollifierBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (g : Plane → ℝ)) x := by
    rw [mollifierAction_eq_convolution, subseqDenseMollifier_eq_normedBump]
  have hscale : Tendsto (fun n : ℕ => (subseqDenseMollifierBump n).rOut)
      atTop (𝓝 0) := by
    change Tendsto (fun n : ℕ => (2 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0)
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (2 : ℝ)
    simpa only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, one_mul, zero_mul,
      mul_comm] using h
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure Plane)) (φ := subseqDenseMollifierBump) hscale g.continuous x
  exact h.congr' (Eventually.of_forall fun n => (hpoint n).symm)

/-- Convolution with the rescaled profiles has a uniform operator bound on spatial `L²`. -/
theorem exists_subseqDenseMollifierAction_uniform_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n (φ : Plane → ℝ), MemLp φ 2 →
      MemLp (mollifierAction (subseqDenseMollifier n) φ) 2 ∧
      eLpNorm (mollifierAction (subseqDenseMollifier n) φ) 2 ≤
        ENNReal.ofReal C * eLpNorm φ 2 := by
  obtain ⟨C, hC0, hC⟩ := subseqDenseMollifier_le_heatKernel
  refine ⟨C, hC0, fun n φ hφ => ?_⟩
  obtain ⟨hknonneg, _, _, _, hkLp⟩ := subseqDenseMollifier_spec n
  let a : ℝ := (n : ℝ) + 1
  let t : ℝ := 1 / (2 * Real.pi * a ^ 2)
  have ha : 0 < a := by dsimp [a]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hφabs : MemLp (fun y : Plane => |φ y|) 2 := hφ.abs
  have hrow (x : Plane) : Integrable (fun y => subseqDenseMollifier n (x - y) * |φ y|) :=
    integrable_mollifierAction_integrand hkLp hφabs x
  have hrowHeat (x : Plane) : Integrable (fun y => heatKernel t (x - y) * |φ y|) :=
    integrable_mollifierAction_integrand (memLp_heatKernel ht) hφabs x
  have hpoint (x : Plane) :
      ‖mollifierAction (subseqDenseMollifier n) φ x‖ ≤
        C * mollifierAction (heatKernel t) (fun y => |φ y|) x := by
    have hnorm :
        ‖mollifierAction (subseqDenseMollifier n) φ x‖ ≤
          ∫ y, subseqDenseMollifier n (x - y) * |φ y| := by
      calc
        _ ≤ ∫ y, ‖subseqDenseMollifier n (x - y) * φ y‖ := norm_integral_le_integral_norm _
        _ = ∫ y, subseqDenseMollifier n (x - y) * |φ y| := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp [Real.norm_eq_abs, abs_of_nonneg (hknonneg _)]
    have hmajor : Integrable (fun y => C * (heatKernel t (x - y) * |φ y|)) :=
      (hrowHeat x).const_mul C
    have hcmp :
        (∫ y, subseqDenseMollifier n (x - y) * |φ y|) ≤
          ∫ y, C * (heatKernel t (x - y) * |φ y|) := by
      apply integral_mono (hrow x) hmajor
      intro y
      have hC' : subseqDenseMollifier n (x - y) ≤ C * heatKernel t (x - y) := by
        simpa [t, a] using hC n (x - y)
      calc
        subseqDenseMollifier n (x - y) * |φ y| ≤
            (C * heatKernel t (x - y)) * |φ y| :=
              mul_le_mul_of_nonneg_right hC' (abs_nonneg _)
        _ = C * (heatKernel t (x - y) * |φ y|) := by ring
    calc
      ‖mollifierAction (subseqDenseMollifier n) φ x‖ ≤
          ∫ y, subseqDenseMollifier n (x - y) * |φ y| := hnorm
      _ ≤ ∫ y, C * (heatKernel t (x - y) * |φ y|) := hcmp
      _ = C * mollifierAction (heatKernel t) (fun y => |φ y|) x := by
        rw [mollifierAction, integral_const_mul]
  have hconv : AEStronglyMeasurable
      (fun x => mollifierAction (subseqDenseMollifier n) φ x) volume := by
    have h := AEStronglyMeasurable.convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure Plane))
      (subseqDenseMollifier_spec n).2.1.continuous.aestronglyMeasurable hφ.aestronglyMeasurable
    exact h.congr (Eventually.of_forall fun x =>
      (mollifierAction_eq_convolution (subseqDenseMollifier n) φ x).symm)
  have hheat := mollifierAction_heat_memLp_and_eLpNorm_le ht (fun y => |φ y|) hφabs
  have hheatNonneg (x : Plane) : 0 ≤ mollifierAction (heatKernel t) (fun y => |φ y|) x := by
    rw [mollifierAction]
    exact integral_nonneg fun y => mul_nonneg (heatKernel_nonneg ht.le _) (abs_nonneg _)
  have hupper : MemLp
      (fun x => C * mollifierAction (heatKernel t) (fun y => |φ y|) x) 2 :=
    hheat.1.const_mul C
  have hmem : MemLp (mollifierAction (subseqDenseMollifier n) φ) 2 :=
    hupper.mono' hconv (Eventually.of_forall hpoint)
  have hnorm : eLpNorm (mollifierAction (subseqDenseMollifier n) φ) 2 ≤
      eLpNorm (fun x => C * mollifierAction (heatKernel t) (fun y => |φ y|) x) 2 :=
    eLpNorm_mono_ae_real (p := (2 : ENNReal)) hconv (Eventually.of_forall hpoint)
  have hupperEq : eLpNorm
      (fun x => C * mollifierAction (heatKernel t) (fun y => |φ y|) x) 2 =
      ENNReal.ofReal C * eLpNorm
        (mollifierAction (heatKernel t) (fun y => |φ y|)) 2 := by
    rw [show (fun x => C * mollifierAction (heatKernel t) (fun y => |φ y|) x) =
        C • mollifierAction (heatKernel t) (fun y => |φ y|) from by
      funext x; simp [smul_eq_mul], eLpNorm_const_smul]
    rw [Real.enorm_eq_ofReal hC0]
  have hAbs : eLpNorm (fun y : Plane => |φ y|) 2 = eLpNorm φ 2 := by
    apply eLpNorm_congr_enorm_ae
    · exact hφabs.aestronglyMeasurable
    · exact hφ.aestronglyMeasurable
    · filter_upwards [] with x
      simp
  refine ⟨hmem, ?_⟩
  calc
    eLpNorm (mollifierAction (subseqDenseMollifier n) φ) 2 ≤
        eLpNorm (fun x => C * mollifierAction (heatKernel t) (fun y => |φ y|) x) 2 := hnorm
    _ = ENNReal.ofReal C * eLpNorm
        (mollifierAction (heatKernel t) (fun y => |φ y|)) 2 := hupperEq
    _ ≤ ENNReal.ofReal C * eLpNorm (fun y => |φ y|) 2 := by
      gcongr
      exact hheat.2
    _ = ENNReal.ofReal C * eLpNorm φ 2 := by rw [hAbs]

/-- Compact continuous inputs converge in spatial `L²` under the shrinking profiles. -/
theorem tendsto_eLpNorm_subseqDenseMollifier_sub_compact (g : C_c(Plane, ℝ)) :
    Tendsto (fun n => eLpNorm (mollifierAction (subseqDenseMollifier n) g - (g : Plane → ℝ)) 2)
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hbound⟩ := exists_subseqDenseMollifierAction_uniform_bound
  have hg : MemLp (g : Plane → ℝ) 2 :=
    g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport
  have hpointwise (x : Plane) := tendsto_mollifierAction_subseqDenseMollifier_compact g x
  let K : Set Plane := tsupport (g : Plane → ℝ) + Metric.closedBall (0 : Plane) (2 : ℝ)
  have htscompact : IsCompact (tsupport (g : Plane → ℝ)) := by
    simpa [HasCompactSupport, tsupport] using g.hasCompactSupport
  have hK : IsCompact K := htscompact.add (isCompact_closedBall (0 : Plane) 2)
  let B : ℝ := (2 * ‖g.toBoundedContinuousFunction‖) ^ 2
  have hB : 0 ≤ B := by positivity
  have hmajor : Integrable (K.indicator fun _ : Plane => B) volume :=
    (integrableOn_const (μ := volume) (s := K) (C := B) hK.measure_ne_top).integrable_indicator
      hK.measurableSet
  have hconv (n : ℕ) : AEStronglyMeasurable
      (fun x => mollifierAction (subseqDenseMollifier n) g x) volume := by
    have h := AEStronglyMeasurable.convolution
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure Plane))
      (subseqDenseMollifier_spec n).2.1.continuous.aestronglyMeasurable hg.aestronglyMeasurable
    exact h.congr (Eventually.of_forall fun x =>
      (mollifierAction_eq_convolution (subseqDenseMollifier n) g x).symm)
  have hTbound (n : ℕ) (x : Plane) :
      ‖mollifierAction (subseqDenseMollifier n) g x‖ ≤ ‖g.toBoundedContinuousFunction‖ := by
    obtain ⟨hpos, hcd, hcompact, hint, hmem⟩ := subseqDenseMollifier_spec n
    have hkernelBase : Integrable (subseqDenseMollifier n) volume :=
      hcd.continuous.integrable_of_hasCompactSupport hcompact
    let e : Plane ≃ᵐ Plane := MeasurableEquiv.subLeft x
    have hkernelInt : Integrable (fun y => subseqDenseMollifier n (x - y)) volume := by
      change Integrable (subseqDenseMollifier n ∘ e) volume
      exact ((volume.measurePreserving_sub_left x).integrable_comp_emb e.measurableEmbedding).mpr
        hkernelBase
    have hrow : Integrable (fun y => subseqDenseMollifier n (x - y) * |g y|) volume :=
      integrable_mollifierAction_integrand hmem hg.abs x
    have hnorm : ‖mollifierAction (subseqDenseMollifier n) g x‖ ≤
        ∫ y, subseqDenseMollifier n (x - y) * |g y| := by
      calc
        _ ≤ ∫ y, ‖subseqDenseMollifier n (x - y) * g y‖ := norm_integral_le_integral_norm _
        _ = ∫ y, subseqDenseMollifier n (x - y) * |g y| := by
          apply integral_congr_ae
          filter_upwards [] with y
          simp [Real.norm_eq_abs, abs_of_nonneg (hpos _)]
    have hgBound (y : Plane) : |g y| ≤ ‖g.toBoundedContinuousFunction‖ := by
      rw [← Real.norm_eq_abs]
      exact g.toBoundedContinuousFunction.norm_coe_le_norm y
    have hcmp' : (∫ y, subseqDenseMollifier n (x - y) * |g y|) ≤
        ∫ y, ‖g.toBoundedContinuousFunction‖ * subseqDenseMollifier n (x - y) := by
      apply integral_mono hrow (hkernelInt.const_mul ‖g.toBoundedContinuousFunction‖)
      intro y
      calc
        subseqDenseMollifier n (x - y) * |g y| ≤
            subseqDenseMollifier n (x - y) * ‖g.toBoundedContinuousFunction‖ :=
              mul_le_mul_of_nonneg_left (hgBound y) (hpos (x - y))
        _ = ‖g.toBoundedContinuousFunction‖ * subseqDenseMollifier n (x - y) := by ring
    have hcmp : (∫ y, subseqDenseMollifier n (x - y) * |g y|) ≤
        ‖g.toBoundedContinuousFunction‖ * ∫ y, subseqDenseMollifier n (x - y) := by
      calc
        _ ≤ ∫ y, ‖g.toBoundedContinuousFunction‖ * subseqDenseMollifier n (x - y) := hcmp'
        _ = ‖g.toBoundedContinuousFunction‖ * ∫ y, subseqDenseMollifier n (x - y) :=
          integral_const_mul _ _
    have hintx : (∫ y, subseqDenseMollifier n (x - y)) = 1 := by
      rw [integral_sub_left_eq_self (fun y : Plane => subseqDenseMollifier n y) volume x, hint]
    calc
      _ ≤ ∫ y, subseqDenseMollifier n (x - y) * |g y| := hnorm
      _ ≤ ‖g.toBoundedContinuousFunction‖ * ∫ y, subseqDenseMollifier n (x - y) := hcmp
      _ = ‖g.toBoundedContinuousFunction‖ := by rw [hintx, mul_one]
  have hconvSupport (n : ℕ) :
      Function.support (fun x : Plane => mollifierAction (subseqDenseMollifier n) g x) ⊆ K := by
    intro x hx
    have hxconv : x ∈ Function.support
        ((subseqDenseMollifier n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (g : Plane → ℝ)) := by
      change mollifierAction (subseqDenseMollifier n) g x ≠ 0 at hx
      change ((subseqDenseMollifier n) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        (g : Plane → ℝ)) x ≠ 0
      simpa only [← mollifierAction_eq_convolution] using hx
    have hsupp := support_convolution_subset_swap
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := (volume : Measure Plane))
        (f := subseqDenseMollifier n) (g := (g : Plane → ℝ))
    have hkball : Function.support (subseqDenseMollifier n) ⊆
        Metric.closedBall (0 : Plane) 2 := by
      rw [subseqDenseMollifier_eq_normedBump n, (subseqDenseMollifierBump n).support_normed_eq]
      intro y hy
      have hy' : ‖y‖ < 2 / ((n : ℝ) + 1) := by
        have hyR : dist y (0 : Plane) < (subseqDenseMollifierBump n).rOut :=
          Metric.mem_ball.mp hy
        simpa [dist_eq_norm, subseqDenseMollifierBump] using hyR
      have ha : 1 ≤ (n : ℝ) + 1 := by
        exact_mod_cast (show 1 ≤ n + 1 by omega)
      apply Metric.mem_closedBall.mpr
      simpa [dist_eq_norm] using
        hy'.le.trans (div_le_self (by norm_num : (0 : ℝ) ≤ 2) ha)
    have hsum : Function.support (g : Plane → ℝ) +
        Function.support (subseqDenseMollifier n) ⊆ K := by
      intro z hz
      rcases Set.mem_add.mp hz with ⟨y, hy, v, hv, rfl⟩
      apply Set.mem_add.mpr
      exact ⟨y, subset_closure hy, v, hkball hv, rfl⟩
    exact hsum (hsupp hxconv)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun x : Plane => ‖mollifierAction (subseqDenseMollifier n) g x - g x‖ ^ 2) volume := by
    exact (((hconv n).sub hg.aestronglyMeasurable).norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hboundSq (n : ℕ) (x : Plane) :
      ‖mollifierAction (subseqDenseMollifier n) g x - g x‖ ^ 2 ≤
        K.indicator (fun _ : Plane => B) x := by
    by_cases hx : x ∈ K
    · simp only [Set.indicator_of_mem hx]
      have htriangle := norm_sub_le (mollifierAction (subseqDenseMollifier n) g x) (g x)
      have hgx : ‖g x‖ ≤ ‖g.toBoundedContinuousFunction‖ :=
        g.toBoundedContinuousFunction.norm_coe_le_norm x
      have herrorBound : ‖mollifierAction (subseqDenseMollifier n) g x - g x‖ ≤
          2 * ‖g.toBoundedContinuousFunction‖ := by
        have hle := htriangle.trans (add_le_add (hTbound n x) hgx)
        nlinarith
      have herrorBound' : |mollifierAction (subseqDenseMollifier n) g x - g x| ≤
          2 * ‖g.toBoundedContinuousFunction‖ := by
        simpa [Real.norm_eq_abs] using herrorBound
      dsimp [B]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2 herrorBound'
    · have hzeroT : mollifierAction (subseqDenseMollifier n) g x = 0 := by
        by_contra hne
        have hxmem : x ∈ Function.support
            (fun x : Plane => mollifierAction (subseqDenseMollifier n) g x) := hne
        exact hx (hconvSupport n hxmem)
      have hzeroG : g x = 0 := by
        by_contra hne
        have hxg : x ∈ Function.support (g : Plane → ℝ) := hne
        have hxts : x ∈ tsupport (g : Plane → ℝ) := subset_closure hxg
        apply hx
        change x ∈ tsupport (g : Plane → ℝ) + Metric.closedBall (0 : Plane) 2
        exact ⟨x, hxts, 0, by simp⟩
      simp [hx, hzeroT, hzeroG]
  have hlimSq (x : Plane) : Tendsto
      (fun n => ‖mollifierAction (subseqDenseMollifier n) g x - g x‖ ^ 2) atTop (𝓝 0) := by
    have h := (hpointwise x).sub_const (g x)
    have hnorm := h.norm
    have hsq := (continuousAt_id.pow 2).tendsto.comp hnorm
    simpa [Function.comp_def, Real.norm_eq_abs, sq_abs] using hsq
  have hDCT := tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure Plane)) (fun x => K.indicator (fun _ : Plane => B) x)
      (Eventually.of_forall hmeas)
      (Eventually.of_forall fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖mollifierAction
          (subseqDenseMollifier n) g x - g x‖))]
        exact hboundSq n x)
      hmajor (Eventually.of_forall fun x => hlimSq x)
  have hInt : Tendsto
      (fun n => ∫ x : Plane, ‖mollifierAction (subseqDenseMollifier n) g x - g x‖ ^ 2)
      atTop (𝓝 0) := by simpa using hDCT
  have hMem (n : ℕ) : MemLp
      (fun x => mollifierAction (subseqDenseMollifier n) g x - g x) 2 :=
    (hbound n g hg).1.sub hg
  have hformula (n : ℕ) : eLpNorm
      (fun x => mollifierAction (subseqDenseMollifier n) g x - g x) 2 =
        ENNReal.ofReal (Real.sqrt (∫ x : Plane,
          ‖mollifierAction (subseqDenseMollifier n) g x - g x‖ ^ 2)) := by
    simpa [Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, one_div] using
      (hMem n).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (∫ x : Plane,
      ‖mollifierAction (subseqDenseMollifier n) g x - g x‖ ^ 2)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hInt
  have hfinal : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.sqrt (∫ x : Plane,
      ‖mollifierAction (subseqDenseMollifier n) g x - g x‖ ^ 2))) atTop (𝓝 0) := by
    simpa [Function.comp_def, ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hroot
  exact hfinal.congr' (Eventually.of_forall fun n => (hformula n).symm)

/-- The strong-approximation error is controlled by a compact comparison test. -/
theorem eLpNorm_subseqDenseMollifier_sub_le_of_comparison (C : ℝ)
    (hbound : ∀ n (φ : Plane → ℝ), MemLp φ 2 →
      MemLp (mollifierAction (subseqDenseMollifier n) φ) 2 ∧
        eLpNorm (mollifierAction (subseqDenseMollifier n) φ) 2 ≤
          ENNReal.ofReal C * eLpNorm φ 2)
    (n : ℕ)
    (φ ψ : Plane → ℝ) (hφ : MemLp φ 2) (hψ : MemLp ψ 2) :
    eLpNorm (mollifierAction (subseqDenseMollifier n) φ - φ) 2 ≤
      (ENNReal.ofReal C + 1) *
        eLpNorm (φ - ψ) 2 +
      eLpNorm (mollifierAction (subseqDenseMollifier n) ψ - ψ) 2 := by
  let D := φ - ψ
  let E := mollifierAction (subseqDenseMollifier n) ψ - ψ
  have hkernel : MemLp (subseqDenseMollifier n) 2 := (subseqDenseMollifier_spec n).2.2.2.2
  have hfun : mollifierAction (subseqDenseMollifier n) φ - φ =
      (mollifierAction (subseqDenseMollifier n) D + E) - D := by
    dsimp only [D, E]
    rw [mollifierAction_sub hkernel hφ hψ]
    funext x
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [hfun]
  have hp : (1 : ENNReal) ≤ 2 := by norm_num
  have hsub := eLpNorm_sub_le (f := mollifierAction (subseqDenseMollifier n) D + E)
    (g := D) (μ := (volume : Measure Plane)) hp
  have hadd := eLpNorm_add_le (f := mollifierAction (subseqDenseMollifier n) D)
    (g := E) (μ := (volume : Measure Plane)) hp
  have hD : MemLp D 2 := hφ.sub hψ
  have hcontract := (hbound n D hD).2
  have hfirst := add_le_add hadd (le_refl (eLpNorm D 2))
  have hsecond := add_le_add (add_le_add hcontract (le_refl (eLpNorm E 2)))
    (le_refl (eLpNorm D 2))
  have hsum := (hsub.trans hfirst).trans hsecond
  have heq : (ENNReal.ofReal C * eLpNorm D 2 + eLpNorm E 2) + eLpNorm D 2 =
      (ENNReal.ofReal C + 1) * eLpNorm D 2 + eLpNorm E 2 := by
    rw [add_mul, one_mul]
    ac_rfl
  exact hsum.trans_eq heq

/-- The rescaled compact profiles approximate the identity strongly on arbitrary spatial `L²`. -/
theorem tendsto_eLpNorm_subseqDenseMollifier_sub (φ : Plane → ℝ) (hφ : MemLp φ 2) :
    Tendsto (fun n => eLpNorm (mollifierAction (subseqDenseMollifier n) φ - φ) 2)
      atTop (𝓝 0) := by
  obtain ⟨C, hC0, hbound⟩ := exists_subseqDenseMollifierAction_uniform_bound
  obtain ⟨ψ, hψmem, hψlim⟩ := exists_compactTest_tendsto_eLpNorm_sub φ hφ
  let M : ENNReal := ENNReal.ofReal C + 1
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hMtop : M ≠ ⊤ := by dsimp [M]; finiteness
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  let δ : ENNReal := ε / 2 / M
  have hδpos : 0 < δ := by dsimp [δ]; exact ENNReal.div_pos hhalf.ne' hMtop
  have hsmallEvent := (ENNReal.tendsto_nhds_zero.1 hψlim) δ hδpos
  obtain ⟨j, hj⟩ := Filter.eventually_atTop.1 hsmallEvent
  let g : C_c(Plane, ℝ) := ψ j
  have hdist : eLpNorm (φ - (g : Plane → ℝ)) 2 ≤ δ := by
    exact hj j le_rfl
  have hMdist : M * eLpNorm (φ - (g : Plane → ℝ)) 2 ≤ ε / 2 := by
    calc
      M * eLpNorm (φ - (g : Plane → ℝ)) 2 ≤ M * δ := by gcongr
      _ = ε / 2 := by
        dsimp [δ, M]
        rw [mul_comm, ENNReal.div_mul_cancel hMpos.ne' hMtop]
  have hcompact := tendsto_eLpNorm_subseqDenseMollifier_sub_compact g
  have htail := (ENNReal.tendsto_nhds_zero.1 hcompact) (ε / 2) hhalf
  filter_upwards [htail] with n hn
  have hcmp := eLpNorm_subseqDenseMollifier_sub_le_of_comparison C hbound n φ
    (g : Plane → ℝ) hφ (hψmem j)
  have hadd : M * eLpNorm (φ - (g : Plane → ℝ)) 2 +
      eLpNorm (mollifierAction (subseqDenseMollifier n) (g : Plane → ℝ) -
        (g : Plane → ℝ)) 2 ≤ ε / 2 + ε / 2 :=
    add_le_add hMdist hn
  have heq : ε / 2 + ε / 2 = ε := by rw [ENNReal.add_halves]
  exact hcmp.trans (hadd.trans_eq heq)

/-- The shrinking bump family satisfies Tsai's exact `L²`-applicable mollifier conditions. -/
theorem isL2ApplicableMollifier_subseqDenseMollifier :
    IsL2ApplicableMollifier subseqDenseMollifier := by
  obtain ⟨C, hC0, hbound⟩ := exists_subseqDenseMollifierAction_uniform_bound
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n x
    exact (subseqDenseMollifier_spec n).1 x
  · intro n
    exact (subseqDenseMollifier_spec n).2.1.continuous
  · intro n
    exact (subseqDenseMollifier_spec n).2.2.2.2
  · intro n
    refine ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top, fun φ hφ => ?_⟩
    change MemLp (mollifierAction (subseqDenseMollifier n) φ) 2 ∧
      eLpNorm (mollifierAction (subseqDenseMollifier n) φ) 2 ≤
        ENNReal.ofReal C * eLpNorm φ 2
    exact hbound n φ hφ
  · exact tendsto_eLpNorm_subseqDenseMollifier_sub

end Critical2DKPZ.SHF.Flow

end
