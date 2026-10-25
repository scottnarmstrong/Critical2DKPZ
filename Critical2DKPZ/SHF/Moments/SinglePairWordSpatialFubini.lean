/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordContinuity
public import Critical2DKPZ.SHF.Moments.SinglePairWordTerminal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Spatial Fubini for the tested two-particle future profile -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory
open scoped CompactlySupported

private theorem terminal_pair_heat_integrable
    {v q : ℝ} (hv : 0 < v) (hq : 0 < q) (z : Plane)
    (ψ₀ ψ₁ : C_c(Plane, ℝ)) :
    Integrable (fun p : Plane × (Plane × Plane) =>
      heatKernel v (p.1 - z) * ((ψ₀ p.2.1 * heatKernel q (p.2.1 - p.1)) *
        (ψ₁ p.2.2 * heatKernel q (p.2.2 - p.1))))
      ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume)) := by
  let H : ℝ := (2 * Real.pi * q)⁻¹
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hψ₀ : Integrable (fun y => |ψ₀ y|) := by
    have hi : Integrable (fun y : Plane => ψ₀ y) (volume : Measure Plane) :=
      ψ₀.continuous.integrable_of_hasCompactSupport (μ := volume) ψ₀.hasCompactSupport
    simpa only [Real.norm_eq_abs] using hi.norm
  have hψ₁ : Integrable (fun y => |ψ₁ y|) := by
    have hi : Integrable (fun y : Plane => ψ₁ y) (volume : Measure Plane) :=
      ψ₁.continuous.integrable_of_hasCompactSupport (μ := volume) ψ₁.hasCompactSupport
    simpa only [Real.norm_eq_abs] using hi.norm
  have hmajor : Integrable (fun p : Plane × (Plane × Plane) =>
      heatKernel v (p.1 - z) * (H^2 * (|ψ₀ p.2.1| * |ψ₁ p.2.2|)))
      ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume)) := by
    have h := ((integrable_heatKernel hv).comp_sub_right z).mul_prod
      ((hψ₀.mul_prod hψ₁).const_mul (H^2))
    exact h
  have hcont : Continuous (fun p : Plane × (Plane × Plane) =>
      heatKernel v (p.1 - z) * ((ψ₀ p.2.1 * heatKernel q (p.2.1 - p.1)) *
        (ψ₁ p.2.2 * heatKernel q (p.2.2 - p.1)))) := by
    have hw : Continuous (fun p : Plane × (Plane × Plane) => heatKernel v (p.1 - z)) :=
      (continuous_heatKernel v).comp (continuous_fst.sub continuous_const)
    have h₀ : Continuous (fun p : Plane × (Plane × Plane) => ψ₀ p.2.1 * heatKernel q (p.2.1 - p.1)) :=
      (ψ₀.continuous.comp continuous_snd.fst).mul
        ((continuous_heatKernel q).comp (continuous_snd.fst.sub continuous_fst))
    have h₁ : Continuous (fun p : Plane × (Plane × Plane) => ψ₁ p.2.2 * heatKernel q (p.2.2 - p.1)) :=
      (ψ₁.continuous.comp continuous_snd.snd).mul
        ((continuous_heatKernel q).comp (continuous_snd.snd.sub continuous_fst))
    exact hw.mul (h₀.mul h₁)
  have hmeas : AEStronglyMeasurable (fun p : Plane × (Plane × Plane) =>
      heatKernel v (p.1 - z) * ((ψ₀ p.2.1 * heatKernel q (p.2.1 - p.1)) *
        (ψ₁ p.2.2 * heatKernel q (p.2.2 - p.1))))
      ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume)) := hcont.aestronglyMeasurable
  apply hmajor.mono' hmeas
  apply Filter.Eventually.of_forall
  intro p
  have h₀ := mul_le_mul_of_nonneg_left (heatKernel_le_at_zero hq.le (p.2.1 - p.1)) (abs_nonneg (ψ₀ p.2.1))
  have h₁ := mul_le_mul_of_nonneg_left (heatKernel_le_at_zero hq.le (p.2.2 - p.1)) (abs_nonneg (ψ₁ p.2.2))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg hv.le _),
    abs_mul, abs_mul, abs_mul, abs_of_nonneg (heatKernel_nonneg hq.le _),
    abs_of_nonneg (heatKernel_nonneg hq.le _)]
  apply mul_le_mul_of_nonneg_left _ (heatKernel_nonneg hv.le _)
  calc
    _ ≤ (|ψ₀ p.2.1| * H) * (|ψ₁ p.2.2| * H) :=
      mul_le_mul h₀ h₁ (mul_nonneg (abs_nonneg _) (heatKernel_nonneg hq.le _))
        (mul_nonneg (abs_nonneg _) hH)
    _ = H^2 * (|ψ₀ p.2.1| * |ψ₁ p.2.2|) := by ring

/-- Spatial Fubini identifies the convolution of the two terminal sections
with the terminal-test integral against the future spatial kernel. -/
theorem pairTwoTestedSpatialProfile_eq_tested_futureSpatialProfile
    (θ : ℝ) {q v : ℝ} (hv : 0 < v) (hvq : v < q)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    pairTwoTestedSpatialProfile θ v (q - v) φ a z =
      (16 * Real.pi) * ∫ y₀ : Plane, ∫ y₁ : Plane,
        φ 0 (a 0, y₀) * φ 1 (a 1, y₁) *
          pairTwoFutureSpatialProfile θ q v z ![y₀, y₁] := by
  let ψ₀ := terminalSectionTest (φ 0) (a 0)
  let ψ₁ := terminalSectionTest (φ 1) (a 1)
  let F : Plane → (Plane × Plane) → ℝ := fun w y =>
    heatKernel (v / 2) (w - z) * ((ψ₀ y.1 * heatKernel (q - v) (y.1 - w)) *
      (ψ₁ y.2 * heatKernel (q - v) (y.2 - w)))
  have hF : Integrable (Function.uncurry F) ((volume : Measure Plane).prod ((volume : Measure Plane).prod volume)) := by
    exact terminal_pair_heat_integrable (half_pos hv) (sub_pos.mpr hvq) z ψ₀ ψ₁
  have hswap := integral_integral_swap hF
  have hinner (w : Plane) : (∫ y : Plane × Plane, F w y ∂(volume : Measure Plane).prod volume) =
      heatKernel (v / 2) (w - z) *
        pairTwoTerminalConvolution (φ 0) (q - v) (a 0) w *
        pairTwoTerminalConvolution (φ 1) (q - v) (a 1) w := by
    rw [show (fun y => F w y) = fun y => heatKernel (v / 2) (w - z) *
      ((ψ₀ y.1 * heatKernel (q - v) (y.1 - w)) *
        (ψ₁ y.2 * heatKernel (q - v) (y.2 - w))) from rfl,
      integral_const_mul,
      integral_prod_mul (μ := (volume : Measure Plane)) (ν := (volume : Measure Plane))
        (fun y : Plane => ψ₀ y * heatKernel (q - v) (y - w))
        (fun y : Plane => ψ₁ y * heatKernel (q - v) (y - w))]
    simp only [ψ₀, ψ₁, terminalSectionTest_apply, pairTwoTerminalConvolution]
    ring
  have hleft : (∫ w : Plane, ∫ y : Plane × Plane, F w y ∂(volume : Measure Plane).prod volume) =
      ∫ d : Plane, heatKernel (v / 2) d *
        pairTwoTerminalConvolution (φ 0) (q - v) (a 0) (z + d) *
        pairTwoTerminalConvolution (φ 1) (q - v) (a 1) (z + d) := by
    simp_rw [hinner]
    have h := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun w : Plane => heatKernel (v / 2) (w - z) *
      pairTwoTerminalConvolution (φ 0) (q - v) (a 0) w *
      pairTwoTerminalConvolution (φ 1) (q - v) (a 1) w) z
    simpa only [add_sub_cancel_right, add_comm z] using h.symm
  rw [hleft] at hswap
  have hpoint (y₀ y₁ : Plane) :
      DeltaBose.scalarDensity θ v * (∫ w : Plane, F w (y₀, y₁)) =
        φ 0 (a 0, y₀) * φ 1 (a 1, y₁) * pairTwoFutureSpatialProfile θ q v z ![y₀, y₁] := by
    dsimp only [F, pairTwoFutureSpatialProfile]
    simp only [ψ₀, ψ₁, terminalSectionTest_apply]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    simp_rw [← integral_const_mul]
    congr 1
    funext w
    ring
  calc
    pairTwoTestedSpatialProfile θ v (q - v) φ a z =
        (16 * Real.pi) * (DeltaBose.scalarDensity θ v *
          ∫ y : Plane × Plane, (∫ w : Plane, F w y) ∂(volume : Measure Plane).prod volume) := by
      rw [pairTwoTestedSpatialProfile, hswap]
      ring
    _ = (16 * Real.pi) * (∫ y₀ : Plane, ∫ y₁ : Plane,
        DeltaBose.scalarDensity θ v * (∫ w : Plane, F w (y₀, y₁))) := by
      have hy : Integrable (fun y : Plane × Plane => ∫ w : Plane, F w y)
          ((volume : Measure Plane).prod volume) := by
        exact hF.integral_prod_right
      have he := integral_prod (fun y : Plane × Plane => ∫ w : Plane, F w y) hy
      rw [he]
      simp_rw [integral_const_mul]
    _ = _ := by simp_rw [hpoint]

end Critical2DKPZ.SHF.Moments
