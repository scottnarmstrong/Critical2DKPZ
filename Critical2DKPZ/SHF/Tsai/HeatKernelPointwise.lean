/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.HeatKernelL2
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Pointwise approximation by planar heat convolution

A change of scale writes every heat convolution against the fixed unit-time
Gaussian density. Bounded continuous tests then converge by dominated
convergence as the positive heat times tend to zero.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Scaling heat time to `a²` gives a convolution against the fixed unit-time Gaussian. -/
theorem mollifierAction_heat_sq_scaling {a : ℝ} (ha : 0 < a) (φ : Plane → ℝ) (x : Plane) :
    mollifierAction (heatKernel (a ^ 2)) φ x =
      ∫ z : Plane, heatKernel 1 z * φ (x - a • z) := by
  let f (y : Plane) := heatKernel (a ^ 2) y * φ (x - y)
  have hchange : mollifierAction (heatKernel (a ^ 2)) φ x = ∫ y, f y := by
    have h := integral_sub_left_eq_self (fun y : Plane => heatKernel (a ^ 2) (x - y) * φ y) volume x
    simpa only [mollifierAction, sub_sub_cancel] using h.symm
  have hscale (z : Plane) : f (a • z) = (a ^ 2)⁻¹ * (heatKernel 1 z * φ (x - a • z)) := by
    dsimp only [f]
    have h := heatKernel_scaling (u := 1) ha z
    rw [mul_one] at h
    rw [h, mul_assoc]
  have hd : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  have hs := Measure.integral_comp_smul volume f a
  rw [hd, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg a)), smul_eq_mul] at hs
  have hscaled : (∫ z, f (a • z)) = (a ^ 2)⁻¹ * (∫ z : Plane, heatKernel 1 z * φ (x - a • z)) := by
    simp_rw [hscale]
    exact integral_const_mul _ _
  rw [hscaled] at hs
  have heq := mul_left_cancel₀ (inv_ne_zero (pow_ne_zero 2 ha.ne')) hs
  exact hchange.trans heq.symm

/-- Heat convolution approaches a bounded continuous test pointwise for every positive
sequence of heat times tending to zero. -/
theorem tendsto_mollifierAction_heat_pointwise_of_bounded (t : ℕ → ℝ)
    (ht : ∀ n, 0 < t n) (htlim : Tendsto t atTop (𝓝 0))
    (g : Plane → ℝ) (hg : Continuous g) (C : ℝ) (hC : ∀ y, ‖g y‖ ≤ C) (x : Plane) :
    Tendsto (fun n => mollifierAction (heatKernel (t n)) g x) atTop (𝓝 (g x)) := by
  let F (n : ℕ) (z : Plane) := heatKernel 1 z * g (x - Real.sqrt (t n) • z)
  have hargcont (n : ℕ) : Continuous (fun z : Plane => x - Real.sqrt (t n) • z) :=
    continuous_const.sub (continuous_const_smul (Real.sqrt (t n)))
  have hGcont (n : ℕ) : Continuous (fun z : Plane => g (x - Real.sqrt (t n) • z)) :=
    hg.comp (hargcont n)
  have hFcont (n : ℕ) : Continuous (F n) := (continuous_heatKernel 1).mul (hGcont n)
  have hfm (n) : AEStronglyMeasurable (F n) volume := (hFcont n).aestronglyMeasurable
  have hbound (n) (z : Plane) : ‖F n z‖ ≤ heatKernel 1 z * C := by
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (heatKernel_nonneg zero_le_one _)]
    exact mul_le_mul_of_nonneg_left (hC _) (heatKernel_nonneg zero_le_one _)
  have ha : Tendsto (fun n => Real.sqrt (t n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp htlim
  have hlim (z : Plane) : Tendsto (fun n => F n z) atTop (𝓝 (heatKernel 1 z * g x)) := by
    have harg : Tendsto (fun n => x - Real.sqrt (t n) • z) atTop (𝓝 x) := by
      simpa only [Function.comp_def, zero_smul, sub_zero] using tendsto_const_nhds.sub (ha.smul_const z)
    exact tendsto_const_nhds.mul ((hg.tendsto x).comp harg)
  have hDCT := tendsto_integral_filter_of_dominated_convergence (fun z : Plane => heatKernel 1 z * C)
    (Eventually.of_forall hfm) (Eventually.of_forall (fun n => Eventually.of_forall (hbound n)))
    ((integrable_heatKernel zero_lt_one).mul_const C) (Eventually.of_forall hlim)
  rw [integral_mul_const, integral_heatKernel zero_lt_one, one_mul] at hDCT
  apply hDCT.congr
  intro n
  rw [show t n = Real.sqrt (t n) ^ 2 from (Real.sq_sqrt (ht n).le).symm,
    mollifierAction_heat_sq_scaling (Real.sqrt_pos.2 (ht n))]

end Critical2DKPZ.SHF.Tsai

end
