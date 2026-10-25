/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordSpatialFubini
import Mathlib.Tactic

/-! # Absolute terminal integrals of the continuum two-particle spatial profile -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory
open scoped CompactlySupported

private def absolutePairTest (φ : C_c(Plane × Plane, ℝ)) : C_c(Plane × Plane, ℝ) where
  toFun p := |φ p|
  continuous_toFun := φ.continuous.abs
  hasCompactSupport' := φ.hasCompactSupport.abs


private theorem absolutePairTest_norm_le (φ : C_c(Plane × Plane, ℝ)) :
    ‖(absolutePairTest φ).toBoundedContinuousFunction‖ ≤ ‖φ.toBoundedContinuousFunction‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
  intro p
  change |(|φ p|)| ≤ ‖φ.toBoundedContinuousFunction‖
  rw [abs_abs]
  exact φ.toBoundedContinuousFunction.norm_coe_le_norm p

/-- The continuum spatial renewal kernel is nonnegative at its interior times. -/
theorem pairTwoFutureSpatialProfile_nonneg
    (θ : ℝ) {q v : ℝ} (hv : 0 < v) (hvq : v < q) (z : Plane) (y : Fin 2 → Plane) :
    0 ≤ pairTwoFutureSpatialProfile θ q v z y := by
  rw [pairTwoFutureSpatialProfile]
  apply mul_nonneg (DeltaBose.scalarDensity_pos θ hv).le
  apply integral_nonneg
  intro w
  exact mul_nonneg (heatKernel_nonneg (half_pos hv).le _)
    (mul_nonneg (heatKernel_nonneg (sub_pos.mpr hvq).le _) (heatKernel_nonneg (sub_pos.mpr hvq).le _))

private theorem futureSpatialProfile_test_integrable
    (θ : ℝ) {q v : ℝ} (hv : 0 < v) (hvq : v < q)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    Integrable (fun y : Plane × Plane => φ 0 (a 0, y.1) * φ 1 (a 1, y.2) *
      pairTwoFutureSpatialProfile θ q v z ![y.1, y.2])
      ((volume : Measure Plane).prod volume) := by
  let C : ℝ := DeltaBose.scalarDensity θ v * (2 * Real.pi * (q / 2))⁻¹ *
    (2 * Real.pi * (2 * (q - v)))⁻¹
  have hρ := (DeltaBose.scalarDensity_pos θ hv).le
  have hq : 0 < q := hv.trans hvq
  have hbound (y : Plane × Plane) : pairTwoFutureSpatialProfile θ q v z ![y.1, y.2] ≤ C := by
    rw [pairTwoFutureSpatialProfile_eq_centerGap hv hvq]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    have hc := heatKernel_le_at_zero (half_pos hq).le ((1 / 2 : ℝ) • (y.1 + y.2) - z)
    have hg := heatKernel_le_at_zero (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sub_pos.mpr hvq).le) (y.2 - y.1)
    have hh := mul_le_mul hc hg (heatKernel_nonneg (by positivity : 0 ≤ 2 * (q - v)) _)
      (by positivity : 0 ≤ (2 * Real.pi * (q / 2))⁻¹)
    calc
      _ = DeltaBose.scalarDensity θ v *
          (heatKernel (q / 2) ((1 / 2 : ℝ) • (y.1 + y.2) - z) *
            heatKernel (2 * (q - v)) (y.2 - y.1)) := by ring
      _ ≤ DeltaBose.scalarDensity θ v *
          ((2 * Real.pi * (q / 2))⁻¹ * (2 * Real.pi * (2 * (q - v)))⁻¹) :=
        mul_le_mul_of_nonneg_left hh hρ
      _ = C := by dsimp [C]; ring
  have hk : Continuous (fun y : Plane × Plane => pairTwoFutureSpatialProfile θ q v z ![y.1, y.2]) := by
    have he : (fun y : Plane × Plane => pairTwoFutureSpatialProfile θ q v z ![y.1, y.2]) =
        fun y => DeltaBose.scalarDensity θ v *
          (heatKernel (q / 2) ((1 / 2 : ℝ) • (y.1 + y.2) - z) *
            heatKernel (2 * (q - v)) (y.2 - y.1)) := by
      funext y
      simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, mul_comm] using
        pairTwoFutureSpatialProfile_eq_centerGap (θ := θ) hv hvq z ![y.1, y.2]
    rw [he]
    exact continuous_const.mul
      (((continuous_heatKernel (q / 2)).comp
        (((continuous_fst.add continuous_snd).const_smul (1 / 2 : ℝ)).sub continuous_const)).mul
        ((continuous_heatKernel (2 * (q - v))).comp (continuous_snd.sub continuous_fst)))
  have hψ (i : Fin 2) : Integrable (fun y : Plane => |φ i (a i, y)|) (volume : Measure Plane) := by
    have hi : Integrable (terminalSectionTest (φ i) (a i)) (volume : Measure Plane) :=
      (terminalSectionTest (φ i) (a i)).continuous.integrable_of_hasCompactSupport
        (μ := volume) (terminalSectionTest (φ i) (a i)).hasCompactSupport
    simpa only [Real.norm_eq_abs, terminalSectionTest_apply] using hi.norm
  have hmajor := ((hψ 0).mul_prod (hψ 1)).mul_const C
  apply hmajor.mono'
    ((((φ 0).continuous.comp (continuous_const.prodMk continuous_fst)).mul
      ((φ 1).continuous.comp (continuous_const.prodMk continuous_snd))).mul hk).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro y
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_nonneg (pairTwoFutureSpatialProfile_nonneg θ hv hvq z ![y.1, y.2])]
  exact mul_le_mul_of_nonneg_left (hbound y) (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The tested future spatial kernel is integrable in both terminal locations,
and its absolute integral is bounded by an integrable scalar renewal density.
The bound is uniform up to both renewal-time endpoints. -/
theorem pairTwoFutureSpatialProfile_test_integrable_bound
    (θ : ℝ) {q v : ℝ} (hv : 0 < v) (hvq : v < q)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (a : Fin 2 → Plane) (z : Plane) :
    Integrable (fun y : Plane × Plane => φ 0 (a 0, y.1) * φ 1 (a 1, y.2) *
      pairTwoFutureSpatialProfile θ q v z ![y.1, y.2]) ((volume : Measure Plane).prod volume) ∧
    (∫ y : Plane × Plane, ‖φ 0 (a 0, y.1) * φ 1 (a 1, y.2) *
      pairTwoFutureSpatialProfile θ q v z ![y.1, y.2]‖ ∂(volume : Measure Plane).prod volume) ≤
        DeltaBose.scalarDensity θ v * ‖(φ 0).toBoundedContinuousFunction‖ *
          ‖(φ 1).toBoundedContinuousFunction‖ := by
  refine ⟨futureSpatialProfile_test_integrable θ hv hvq φ a z, ?_⟩
  let Φ : Fin 2 → C_c(Plane × Plane, ℝ) := fun i => absolutePairTest (φ i)
  let I : ℝ := ∫ y : Plane × Plane, ‖φ 0 (a 0, y.1) * φ 1 (a 1, y.2) *
    pairTwoFutureSpatialProfile θ q v z ![y.1, y.2]‖ ∂(volume : Measure Plane).prod volume
  have hn : I = ∫ y : Plane × Plane, Φ 0 (a 0, y.1) * Φ 1 (a 1, y.2) *
      pairTwoFutureSpatialProfile θ q v z ![y.1, y.2] ∂(volume : Measure Plane).prod volume := by
    apply integral_congr_ae
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg (pairTwoFutureSpatialProfile_nonneg θ hv hvq z ![y.1, y.2])]
    rfl
  have he : (16 * Real.pi) * I = pairTwoTestedSpatialProfile θ v (q - v) Φ a z := by
    rw [pairTwoTestedSpatialProfile_eq_tested_futureSpatialProfile θ hv hvq Φ a z, hn]
    congr 1
    exact integral_prod _ (futureSpatialProfile_test_integrable θ hv hvq Φ a z)
  have hb := (le_abs_self (pairTwoTestedSpatialProfile θ v (q - v) Φ a z)).trans
    (pairTwoTestedSpatialProfile_integrable_bound θ v (q - v) hv (sub_pos.mpr hvq) Φ a z).2
  rw [← he] at hb
  have ht : I ≤ DeltaBose.scalarDensity θ v * ‖(Φ 0).toBoundedContinuousFunction‖ *
      ‖(Φ 1).toBoundedContinuousFunction‖ := by
    apply (mul_le_mul_iff_right₀ (show 0 < 16 * Real.pi by positivity)).mp
    convert hb using 1
    ring
  have h₀ : ‖(Φ 0).toBoundedContinuousFunction‖ ≤ ‖(φ 0).toBoundedContinuousFunction‖ :=
    absolutePairTest_norm_le (φ 0)
  have h₁ : ‖(Φ 1).toBoundedContinuousFunction‖ ≤ ‖(φ 1).toBoundedContinuousFunction‖ :=
    absolutePairTest_norm_le (φ 1)
  exact ht.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left h₀ (DeltaBose.scalarDensity_pos θ hv).le) h₁
    (norm_nonneg _) (mul_nonneg (DeltaBose.scalarDensity_pos θ hv).le (norm_nonneg _)))

end Critical2DKPZ.SHF.Moments
