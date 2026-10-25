/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Semigroup
public import Critical2DKPZ.Definitions.KpzRegularized
public import Critical2DKPZ.Definitions.TestFnCompAffine
public import Critical2DKPZ.Definitions.TestFnScale
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Deterministic affine and scaling identities for regularized fields -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace Critical2DKPZ.Assembly

/-- Pairing transport under the affine action on both coordinates. -/
theorem shfPairing_compAffine {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (s t : ℝ) (z : Plane) (R : Plane ≃ₗᵢ[ℝ] Plane) (f g : Plane → ℝ) (ω : Ω) :
    shfPairing (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2)) s t f g ω =
      shfPairing Z s t (fun y => f (z + R y)) (fun y => g (z + R y)) ω := by
  let A : Plane ≃ₜ Plane := R.toHomeomorph.trans (Homeomorph.addLeft z)
  let e := A.toMeasurableEquiv.prodCongr A.toMeasurableEquiv
  have he : (fun p : Plane × Plane => (A p.1, A p.2)) = e := by
    funext p
    rfl
  change (∫ p, f p.1 * g p.2 ∂Measure.map (fun p : Plane × Plane => (A p.1, A p.2))
      (Z s t ω)) = _
  rw [he, integral_map_equiv e]
  rfl

/-- Pairing transport under a spatial dilation and a scalar change of measure. -/
theorem shfPairing_scaleTransport {Ω : Type*}
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (a r : ℝ) (hr : r ≠ 0)
    (c : ℝ≥0∞)
    (s t : ℝ) (f g : Plane → ℝ) (ω : Ω) :
    shfPairing (fun s u ω => c • (Z (a * s) (a * u) ω).map
        (fun p => (r⁻¹ • p.1, r⁻¹ • p.2))) s t f g ω =
      c.toReal * shfPairing Z (a * s) (a * t)
        (fun y => f (r⁻¹ • y)) (fun y => g (r⁻¹ • y)) ω := by
  let S : Plane ≃ₜ Plane := Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr))
  let e := S.toMeasurableEquiv.prodCongr S.toMeasurableEquiv
  have he : (fun p : Plane × Plane => (S p.1, S p.2)) = e := by
    funext p
    rfl
  simp only [shfPairing]
  change (∫ p, f p.1 * g p.2 ∂
      c • Measure.map (fun p : Plane × Plane => (S p.1, S p.2))
        (Z (a * s) (a * t) ω)) = _
  rw [integral_smul_measure, he, integral_map_equiv e, smul_eq_mul]
  rfl

/-- The regularized field after affine transport differs by exactly its centering constant. -/
theorem kpzRegularized_compAffine_pointwise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (z : Plane)
    (R : Plane ≃ₗᵢ[ℝ] Plane) (y : Plane) (ω : Ω) :
    kpzRegularized P
        (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2)) t δ 0 y ω =
      kpzRegularized P Z t δ 0 (R.symm y - R.symm z) ω +
        (∫ ω', Real.log (shfPairing Z 0 (t - δ) (fun _ => 1)
          (fun x => heatKernel δ x) ω') ∂P) -
        ∫ ω', Real.log (shfPairing
          (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2))
          0 (t - δ) (fun _ => 1) (fun x => heatKernel δ x) ω') ∂P := by
  simp [kpzRegularized]
  have hnum := shfPairing_compAffine Z 0 (t - δ) z R (fun _ => 1)
    (fun x => heatKernel δ (x - y)) ω
  have hnum' : shfPairing
      (fun s u ω => (Z s u ω).map fun p => (z + R p.1, z + R p.2))
      0 (t - δ) (fun _ => 1) (fun x => heatKernel δ (x - y)) ω =
      shfPairing Z 0 (t - δ) (fun _ => 1)
        (fun x => heatKernel δ (x - (R.symm y - R.symm z))) ω := by
    have hR : R (R.symm y - R.symm z) = y - z := by simp
    have harg (x : Plane) : z + R x - y = R (x - (R.symm y - R.symm z)) := by
      calc
        z + R x - y = R x - (y - z) := by abel
        _ = R x - R (R.symm y - R.symm z) := by rw [hR]
        _ = R (x - (R.symm y - R.symm z)) :=
          (map_sub R x (R.symm y - R.symm z)).symm
    calc
      _ = shfPairing Z 0 (t - δ) (fun _ => 1)
          (fun x => heatKernel δ (z + R x - y)) ω := hnum
      _ = shfPairing Z 0 (t - δ) (fun _ => 1)
          (fun x => heatKernel δ (x - (R.symm y - R.symm z))) ω := by
            congr 2
            funext x
            have hnorm : ‖z + R x - y‖ = ‖x - (R.symm y - R.symm z)‖ := by
              rw [harg x, R.norm_map]
            rw [heatKernel, heatKernel, hnorm]
  rw [hnum']

/-- The regularized field is exactly covariant under positive parabolic scaling. -/
theorem kpzRegularized_scale_pointwise {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) {a : ℝ}
    (ha : 0 < a) (t δ : ℝ) (y : Plane) (ω : Ω) :
    kpzRegularized P
        (fun s u ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * u) ω).map
          fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2))
        t δ 0 y ω = kpzRegularized P Z (a * t) (a * δ) 0
          (Real.sqrt a • y) ω := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hr0 : Real.sqrt a ≠ 0 := hr.ne'
  have hpair (x : Plane) (ω : Ω) :
      shfPairing
          (fun s u ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * u) ω).map
            fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2))
          0 (t - δ) (fun _ => 1) (fun q => heatKernel δ (q - x)) ω =
      shfPairing Z 0 (a * t - a * δ) (fun _ => 1)
          (fun p => heatKernel (a * δ) (p - Real.sqrt a • x)) ω := by
    rw [shfPairing_scaleTransport Z a (Real.sqrt a) hr0 (ENNReal.ofReal a⁻¹)
      0 (t - δ) (fun _ => 1) (fun q => heatKernel δ (q - x)) ω]
    have hkernel (p : Plane) :
        heatKernel δ ((Real.sqrt a)⁻¹ • p - x) =
          a * heatKernel (a * δ) (p - Real.sqrt a • x) := by
      have hv : Real.sqrt a • ((Real.sqrt a)⁻¹ • p - x) = p - Real.sqrt a • x := by
        simp [smul_sub, smul_inv_smul₀ hr0]
      have hs := heatKernel_scaling (a := Real.sqrt a) (u := δ) hr
        ((Real.sqrt a)⁻¹ • p - x)
      rw [Real.sq_sqrt ha.le, hv] at hs
      calc
        heatKernel δ ((Real.sqrt a)⁻¹ • p - x) =
            a * (a⁻¹ * heatKernel δ ((Real.sqrt a)⁻¹ • p - x)) := by
              field_simp [ha.ne']
        _ = a * heatKernel (a * δ) (p - Real.sqrt a • x) := by rw [← hs]
    have hc : (ENNReal.ofReal a⁻¹).toReal = a⁻¹ := by
      rw [ENNReal.toReal_ofReal (inv_nonneg.mpr ha.le)]
    rw [hc]
    simp only [shfPairing, mul_zero]
    change a⁻¹ * (∫ p, 1 * heatKernel δ ((Real.sqrt a)⁻¹ • p.2 - x)
      ∂(Z 0 (a * (t - δ)) ω)) =
        ∫ p, 1 * heatKernel (a * δ) (p.2 - Real.sqrt a • x)
          ∂(Z 0 (a * t - a * δ) ω)
    have hfun : (fun p : Plane × Plane =>
        1 * heatKernel δ ((Real.sqrt a)⁻¹ • p.2 - x)) =
        (fun p => a * heatKernel (a * δ) (p.2 - Real.sqrt a • x)) := by
      funext p
      rw [one_mul, hkernel]
    rw [hfun, integral_const_mul]
    field_simp [ha.ne']
  have hcent :
      (∫ ω', Real.log (shfPairing
          (fun s u ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * u) ω).map
            fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2))
          0 (t - δ) (fun _ => 1) (fun q => heatKernel δ q) ω') ∂P) =
        ∫ ω', Real.log (shfPairing Z 0 (a * t - a * δ) (fun _ => 1)
          (fun p => heatKernel (a * δ) p) ω') ∂P := by
    apply integral_congr_ae
    filter_upwards with ω'
    simpa [sub_zero] using congrArg Real.log (hpair 0 ω')
  simp [kpzRegularized]
  rw [hpair y ω, hcent]


/-- Test-function covariance for positive parabolic scaling. -/
theorem kpzRegularized_scale {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) {a : ℝ}
    (ha : 0 < a) (t δ : ℝ) (φ : TestFn) (ω : Ω) :
    ∫ y, (φ.scale a) y * kpzRegularized P Z (a * t) (a * δ) 0 y ω =
      ∫ y, φ y * kpzRegularized P
        (fun s u ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * u) ω).map
          fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2))
        t δ 0 y ω := by
  have hr : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hdim : Module.finrank ℝ Plane = 2 := by simp [Plane]
  have hscale : (Real.sqrt a)⁻¹ ^ 2 = a⁻¹ := by
    rw [inv_pow, Real.sq_sqrt ha.le]
  have hscaleFn (y : Plane) : (φ.scale a) y =
      (Real.sqrt a)⁻¹ ^ 2 * φ ((Real.sqrt a)⁻¹ • y) := rfl
  simp_rw [hscaleFn, hscale]
  have hcomp :=
    (MeasureTheory.Measure.integral_comp_inv_smul (μ := (volume : Measure Plane))
      (fun x : Plane => φ x * kpzRegularized P Z (a * t) (a * δ) 0
        (Real.sqrt a • x) ω) (Real.sqrt a))
  rw [hdim] at hcomp
  have hc : |(Real.sqrt a) ^ 2| = a := by
    calc
      |(Real.sqrt a) ^ 2| = (Real.sqrt a) ^ 2 := abs_of_nonneg (sq_nonneg _)
      _ = a := Real.sq_sqrt ha.le
  rw [hc] at hcomp
  calc
    _ = a⁻¹ * ∫ y, φ ((Real.sqrt a)⁻¹ • y) * kpzRegularized P Z (a * t) (a * δ)
          0 y ω := by
            rw [show (fun y : Plane => a⁻¹ * φ ((Real.sqrt a)⁻¹ • y) *
                kpzRegularized P Z (a * t) (a * δ) 0 y ω) =
              (fun y => a⁻¹ * (φ ((Real.sqrt a)⁻¹ • y) *
                kpzRegularized P Z (a * t) (a * δ) 0 y ω)) by
                  funext y
                  ring]
            rw [integral_const_mul]
    _ = a⁻¹ * (a * ∫ x, φ x * kpzRegularized P Z (a * t) (a * δ) 0
          (Real.sqrt a • x) ω) := by
            congr 1
            have hs : (fun y : Plane => φ ((Real.sqrt a)⁻¹ • y) *
                kpzRegularized P Z (a * t) (a * δ) 0 y ω) =
              (fun y => (fun x : Plane => φ x * kpzRegularized P Z (a * t) (a * δ) 0
                (Real.sqrt a • x) ω) ((Real.sqrt a)⁻¹ • y)) := by
                  funext y
                  have hcancel : Real.sqrt a • ((Real.sqrt a)⁻¹ • y) = y := by
                    simp [smul_inv_smul₀ hr.ne']
                  change φ ((Real.sqrt a)⁻¹ • y) *
                    kpzRegularized P Z (a * t) (a * δ) 0 y ω = _
                  simp [hcancel]
            rw [hs, hcomp, smul_eq_mul]
    _ = ∫ x, φ x * kpzRegularized P Z (a * t) (a * δ) 0
          (Real.sqrt a • x) ω := by field_simp [ha.ne']
    _ = ∫ x, φ x * kpzRegularized P
          (fun s u ω => ENNReal.ofReal a⁻¹ • (Z (a * s) (a * u) ω).map
            fun p => ((Real.sqrt a)⁻¹ • p.1, (Real.sqrt a)⁻¹ • p.2))
          t δ 0 x ω := by
      apply integral_congr_ae
      filter_upwards with x
      exact congrArg (fun v => φ x * v)
        (kpzRegularized_scale_pointwise P Z ha t δ x ω).symm

end Critical2DKPZ.Assembly

end
