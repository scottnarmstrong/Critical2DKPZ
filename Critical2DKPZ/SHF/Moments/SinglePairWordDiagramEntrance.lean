/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordCenterConvolution
public import Critical2DKPZ.SHF.Moments.SinglePairWordSpatialL1
public import Critical2DKPZ.SHF.Flow.TwoParticleCenterGap
public import Critical2DKPZ.SHF.DeltaBose.CausalComposition
import Mathlib.Tactic

/-! # The positive two-particle diagram in entrance and future coordinates -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open MeasureTheory Filter
open scoped ENNReal

/-- Integration in the collision center of an interior future spatial kernel.
Both integrability and the center-gap expression are explicit. -/
theorem pairTwo_entrance_futureSpatialProfile_integral
    (θ : ℝ) {T r v : ℝ} (hr : 0 < r) (hrT : r < T)
    (hv : 0 < v) (hvT : v < T - r) (x y : DeltaBose.Configuration 2) :
    Integrable (fun z : Plane =>
      (heatKernel r (z - x 0) * heatKernel r (z - x 1)) *
        pairTwoFutureSpatialProfile θ (T - r) v z y) ∧
    (∫ z : Plane, (heatKernel r (z - x 0) * heatKernel r (z - x 1)) *
        pairTwoFutureSpatialProfile θ (T - r) v z y) =
      DeltaBose.scalarDensity θ v * heatKernel (2 * (T - r - v)) (y 1 - y 0) *
        (heatKernel (2 * r) (x 1 - x 0) *
          heatKernel (T / 2) ((1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1))) := by
  let b : Plane := (1 / 2 : ℝ) • (y 0 + y 1)
  let c : ℝ := DeltaBose.scalarDensity θ v * heatKernel (2 * (T - r - v)) (y 1 - y 0)
  obtain ⟨hi, he⟩ := pairTwo_entrance_center_convolution hr hrT (x 0) (x 1) b
  have hp (z : Plane) :
      (heatKernel r (z - x 0) * heatKernel r (z - x 1)) *
        pairTwoFutureSpatialProfile θ (T - r) v z y =
      c * ((heatKernel r (z - x 0) * heatKernel r (z - x 1)) *
        heatKernel ((T - r) / 2) (b - z)) := by
    rw [pairTwoFutureSpatialProfile_eq_centerGap hv hvT]
    dsimp [c, b]
    ring
  constructor
  · simpa only [hp] using hi.const_mul c
  · simp only [hp, integral_const_mul, he]
    rfl

/-- The positive delta-Bose diagram is the entrance-time integral of the
complete future spatial kernel, with the period-correct coefficient `4π`.
The second clock is the elapsed renewal duration. -/
theorem pairTwo_diagram_eq_entrance_futureSpatialProfile
    (θ T : ℝ) (x y : DeltaBose.Configuration 2) :
    DeltaBose.diagramKernel θ [DeltaBose.pairTwo] T x y =
      ∫⁻ r in Set.Ioo (0 : ℝ) T, ∫⁻ v in Set.Ioo (0 : ℝ) (T - r),
        ENNReal.ofReal (4 * Real.pi * (∫ z : Plane,
          (heatKernel r (z - x 0) * heatKernel r (z - x 1)) *
            pairTwoFutureSpatialProfile θ (T - r) v z y)) := by
  change DeltaBose.twoParticleCorrection θ T x y = _
  rw [SHF.Flow.twoParticleCorrection_eq_centerGap]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  rw [DeltaBose.lintegral_Ioo_sub_right]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [(pairTwo_entrance_futureSpatialProfile_integral θ hr.1 hr.2
    (sub_pos.mpr hu.1) (by linarith only [hu.2]) x y).2]
  have he : T - r - (u - r) = T - u := by ring
  rw [he]
  have hρ := (DeltaBose.scalarDensity_pos θ (sub_pos.mpr hu.1)).le
  have hgapr := heatKernel_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hr.1.le) (x 1 - x 0)
  have hgapq := heatKernel_nonneg (show 0 ≤ 2 * (T - u) by linarith only [hu.2]) (y 1 - y 0)
  rw [← ENNReal.ofReal_mul hgapr,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * Real.pi * DeltaBose.scalarDensity θ (u - r)),
    ← ENNReal.ofReal_mul (by positivity : 0 ≤
      4 * Real.pi * DeltaBose.scalarDensity θ (u - r) *
        (heatKernel (2 * r) (x 1 - x 0) * heatKernel (2 * (T - u)) (y 1 - y 0)))]
  congr 1
  ring

end Critical2DKPZ.SHF.Moments
