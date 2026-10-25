/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.TwoParticleCenterGap
import Mathlib.Tactic

/-! # The relative-coordinate two-particle kernel -/

@[expose] public section

open MeasureTheory Set
open Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Flow

/-- The free relative-coordinate heat strand. -/
noncomputable def twoParticleGapFreeKernel (h : ℝ) (x y : Plane) : ℝ≥0∞ :=
  ENNReal.ofReal (heatKernel (2 * h) (y - x))

/-- One resummed collision interval in the relative coordinate. -/
noncomputable def twoParticleGapCollisionKernel (θ h : ℝ) (x y : Plane) : ℝ≥0∞ :=
  ∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h,
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
        (ENNReal.ofReal (heatKernel (2 * r) x) *
          ENNReal.ofReal (heatKernel (2 * (h - u)) y))

/-- The relative-coordinate kernel: free gap propagation plus one resummed
collision interval. -/
noncomputable def twoParticleGapKernel (θ h : ℝ) (x y : Plane) : ℝ≥0∞ :=
  twoParticleGapFreeKernel h x y + twoParticleGapCollisionKernel θ h x y

/-- For each fixed initial gap `x`, the two-particle gap kernel is measurable in the terminal gap `y`. -/
theorem measurable_twoParticleGapKernel (θ h : ℝ) (x : Plane) :
    Measurable (twoParticleGapKernel θ h x) := by
  change Measurable (fun y : Plane => ENNReal.ofReal (heatKernel (2 * h) (y - x)) +
    ∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h,
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
        (ENNReal.ofReal (heatKernel (2 * r) x) *
          ENNReal.ofReal (heatKernel (2 * (h - u)) y)))
  have hfree : Measurable (fun y : Plane => ENNReal.ofReal (heatKernel (2 * h) (y - x))) :=
    ((measurable_heatKernel (2 * h)).comp (measurable_id.sub_const x)).ennreal_ofReal
  have hcollision : Measurable (fun y : Plane =>
      ∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h,
        ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
          (ENNReal.ofReal (heatKernel (2 * r) x) *
            ENNReal.ofReal (heatKernel (2 * (h - u)) y))) := by
    let F : ℝ → ℝ → Plane → ℝ≥0∞ := fun r u y =>
      ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
        (ENNReal.ofReal (heatKernel (2 * r) x) *
          ENNReal.ofReal (heatKernel (2 * (h - u)) y))
    have hF : Measurable (fun q : (Plane × ℝ) × ℝ => F q.1.2 q.2 q.1.1) := by
      dsimp [F]
      have hmCoeff : Measurable (fun q : (Plane × ℝ) × ℝ =>
          4 * Real.pi * scalarDensity θ (q.2 - q.1.2)) := by
        exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
          Measurable (fun q : (Plane × ℝ) × ℝ => (θ, q.2 - q.1.2))))
      have hmX : Measurable (fun q : (Plane × ℝ) × ℝ => heatKernel (2 * q.1.2) x) := by
        unfold heatKernel
        fun_prop
      have hmY : Measurable (fun q : (Plane × ℝ) × ℝ =>
          heatKernel (2 * (h - q.2)) q.1.1) := by
        unfold heatKernel
        fun_prop
      exact hmCoeff.ennreal_ofReal.mul
        (hmX.ennreal_ofReal.mul hmY.ennreal_ofReal)
    have hInner : Measurable (fun p : Plane × ℝ =>
        ∫⁻ u in Ioo p.2 h, F p.2 u p.1) :=
      measurable_lintegral_Ioo measurable_snd measurable_const hF
    exact measurable_lintegral_Ioo measurable_const measurable_const hInner
  exact hfree.add hcollision

/-- The collision correction separates as the center heat kernel times the
relative collision contribution. -/
theorem twoParticleCorrection_eq_centerGapProduct {θ h : ℝ}
    (x y : Configuration 2) :
    twoParticleCorrection θ h x y =
      ENNReal.ofReal (heatKernel (h / 2)
        ((1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1))) *
        (∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h,
          ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
            (ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) *
              ENNReal.ofReal (heatKernel (2 * (h - u)) (y 1 - y 0)))) := by
  rw [twoParticleCorrection_eq_centerGap]
  let C : ℝ≥0∞ := ENNReal.ofReal (heatKernel (h / 2)
    ((1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1)))
  let G : ℝ → ℝ → ℝ≥0∞ := fun r u =>
    ENNReal.ofReal (4 * Real.pi * scalarDensity θ (u - r)) *
      (ENNReal.ofReal (heatKernel (2 * r) (x 1 - x 0)) *
        ENNReal.ofReal (heatKernel (2 * (h - u)) (y 1 - y 0)))
  have hG : Measurable (Function.uncurry G) := by
    dsimp [G]
    have hmCoeff : Measurable (fun p : ℝ × ℝ =>
        4 * Real.pi * scalarDensity θ (p.2 - p.1)) := by
      exact measurable_const.mul (measurable_scalarDensity.comp (by fun_prop :
        Measurable (fun p : ℝ × ℝ => (θ, p.2 - p.1))))
    have hmX : Measurable (fun p : ℝ × ℝ => heatKernel (2 * p.1) (x 1 - x 0)) := by
      unfold heatKernel
      fun_prop
    have hmY : Measurable (fun p : ℝ × ℝ => heatKernel (2 * (h - p.2)) (y 1 - y 0)) := by
      unfold heatKernel
      fun_prop
    exact hmCoeff.ennreal_ofReal.mul
      (hmX.ennreal_ofReal.mul hmY.ennreal_ofReal)
  have hInner (r : ℝ) : Measurable (fun u : ℝ => G r u) := by
    dsimp [G]
    have hmScalar : Measurable (fun u : ℝ => scalarDensity θ (u - r)) := by
      exact measurable_scalarDensity.comp (by fun_prop : Measurable (fun u : ℝ => (θ, u - r)))
    have hmX : Measurable (fun _ : ℝ => heatKernel (2 * r) (x 1 - x 0)) := measurable_const
    have hmY : Measurable (fun u : ℝ => heatKernel (2 * (h - u)) (y 1 - y 0)) := by
      unfold heatKernel
      fun_prop
    exact (measurable_const.mul hmScalar).ennreal_ofReal.mul
      (hmX.ennreal_ofReal.mul hmY.ennreal_ofReal)
  have hOuter : Measurable (fun r : ℝ => ∫⁻ u in Ioo r h, G r u) := by
    exact measurable_lintegral_Ioo measurable_id measurable_const hG
  have hfactor (r : ℝ) :
      (∫⁻ u in Ioo r h, G r u * C) = C * ∫⁻ u in Ioo r h, G r u := by
    calc
      (∫⁻ u in Ioo r h, G r u * C) = ∫⁻ u in Ioo r h, C * G r u := by
        apply lintegral_congr_ae
        filter_upwards [] with u
        exact mul_comm _ _
      _ = C * ∫⁻ u in Ioo r h, G r u :=
        lintegral_const_mul C (hInner r)
  calc
    (∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h, G r u * C) =
        ∫⁻ r in Ioo (0 : ℝ) h, C * ∫⁻ u in Ioo r h, G r u := by
          apply lintegral_congr_ae
          filter_upwards [] with r
          exact hfactor r
    _ = C * ∫⁻ r in Ioo (0 : ℝ) h, ∫⁻ u in Ioo r h, G r u :=
      lintegral_const_mul C hOuter
    _ = _ := by
      dsimp [C, G]

/-- The two-particle moment kernel is the product of the center heat kernel
and the relative-coordinate kernel. -/
theorem momentKernel_two_eq_centerGapProduct {θ h : ℝ}
    (hh : 0 < h) (x y : Configuration 2) :
    momentKernel 2 θ h x y =
      ENNReal.ofReal (heatKernel (h / 2)
        ((1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1))) *
        twoParticleGapKernel θ h (x 1 - x 0) (y 1 - y 0) := by
  rw [momentKernel_two]
  let C : ℝ≥0∞ := ENNReal.ofReal (heatKernel (h / 2)
    ((1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1)))
  have hfree : heatKernel h (y 0 - x 0) * heatKernel h (y 1 - x 1) =
      heatKernel (h / 2)
          ((1 / 2 : ℝ) • (y 0 + y 1) - (1 / 2 : ℝ) • (x 0 + x 1)) *
        heatKernel (2 * h) ((y 1 - y 0) - (x 1 - x 0)) := by
    simpa only [freeKernel, Fin.prod_univ_two] using freeKernel_two_center_gap hh x y
  have hfreeENN : ENNReal.ofReal (heatKernel h (y 0 - x 0) * heatKernel h (y 1 - x 1)) =
      C * ENNReal.ofReal (heatKernel (2 * h) ((y 1 - y 0) - (x 1 - x 0))) := by
    rw [hfree, ENNReal.ofReal_mul (heatKernel_nonneg (div_nonneg hh.le
      (by norm_num : (0 : ℝ) ≤ 2)) _)]
  rw [hfreeENN, twoParticleCorrection_eq_centerGapProduct x y]
  dsimp [twoParticleGapKernel, twoParticleGapFreeKernel,
    twoParticleGapCollisionKernel, C]
  rw [← mul_add]

end Critical2DKPZ.SHF.Flow

end
