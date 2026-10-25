/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedCollisionScalar
public import Critical2DKPZ.SHF.Tsai.ConjugatedIntegralBounds
public import Critical2DKPZ.SHF.DeltaBose.LaplaceComposition
public import Critical2DKPZ.SHF.DeltaBose.PathKernel
public import Critical2DKPZ.SHF.DeltaBose.ScalarLaplace
import Mathlib.Tactic

/-! # Logarithmic Laplace gain for conjugated collision blocks -/

@[expose] public noncomputable section

open MeasureTheory Set Critical2DKPZ.DeltaBose Critical2DKPZ.SHF.Flow
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- The canonical scalar collision resolvent gives one logarithmic gain
for a conjugated `Lᵖ` collision block. -/
theorem weightedFormBound_laplace_collision_conj {n : ℕ} (α : CollisionPair n) (θ : ℝ)
    {p a rate : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hrate : 2 * n * a ^ 2 < rate)
    (hθ : θ < Real.log (rate - 2 * n * a ^ 2)) :
    WeightedFormBound volume volume (fun y => -(a * fusedOneNorm α y))
      (fun z => a * fusedOneNorm α z) p (p / (p - 1))
      (laplaceTimeKernel rate (collisionTimeKernel α θ))
      (ENNReal.ofReal ((2 : ℝ) ^ n * (4 * Real.pi * (Real.log (rate - 2 * n * a ^ 2) - θ)⁻¹))) := by
  let g : ℝ := 2 * n * a ^ 2
  have hshift : 0 < rate - g := sub_pos.mpr hrate
  let K : ℝ → FusedConfiguration α → FusedConfiguration α → ℝ≥0∞ := fun t y z =>
    laplaceTimeWeight rate t * ENNReal.ofReal (collisionKernel α θ t y z)
  let c : ℝ → ℝ≥0∞ := fun t => laplaceTimeWeight rate t *
    ENNReal.ofReal (weightGrowth n a t * (4 * Real.pi * scalarDensity θ t))
  have hw : Measurable (fun t : ℝ => laplaceTimeWeight rate t) := by
    unfold laplaceTimeWeight
    fun_prop
  have hKm : Measurable (fun q : ℝ × FusedConfiguration α × FusedConfiguration α =>
      K q.1 q.2.1 q.2.2) := (hw.comp measurable_fst).mul (measurable_collisionTimeKernel α θ)
  have hj : Measurable (fun t : ℝ => scalarDensity θ t) :=
    Measurable.comp (g := fun q : ℝ × ℝ => scalarDensity q.1 q.2)
      (f := fun t : ℝ => (θ, t)) measurable_scalarDensity (measurable_const.prodMk measurable_id)
  have hcm : Measurable c := by
    have hGrowth : Measurable (weightGrowth n a) := by unfold weightGrowth; fun_prop
    exact hw.mul ((hGrowth.mul (measurable_const.mul hj)).ennreal_ofReal)
  have hbound (t : ℝ) (ht : t ∈ Ioi 0) :
      WeightedFormBound volume volume (fun y => -(a * fusedOneNorm α y))
        (fun z => a * fusedOneNorm α z) p (p / (p - 1)) (K t) (c t) :=
    weightedFormBound_const_mul (d := laplaceTimeWeight rate t) ENNReal.ofReal_ne_top
      (weightedFormBound_collision_conj_scalar α θ hp ha ht)
  have h := WeightedFormBound.setLIntegral_param (κ := volume) measurableSet_Ioi hKm hcm hbound
  have hdamped : (∫⁻ t in Ioi 0, ENNReal.ofReal (Real.exp (-((rate - g) * t)) * scalarDensity θ t)) =
      ENNReal.ofReal ((Real.log (rate - g) - θ)⁻¹) := by
    have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t : ℝ => Real.exp (-((rate - g) * t)) * scalarDensity θ t) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (Real.exp_pos _).le (scalarDensity_pos θ ht).le
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_scalarDensity_laplace hshift hθ) hn,
      integral_scalarDensity_laplace hshift hθ]
  have hpoint (t : ℝ) : c t = ENNReal.ofReal ((2 : ℝ) ^ n * (4 * Real.pi)) *
      ENNReal.ofReal (Real.exp (-((rate - g) * t)) * scalarDensity θ t) := by
    dsimp [c, laplaceTimeWeight]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ n * (4 * Real.pi))]
    congr 1
    have he : Real.exp (-(rate * t)) * Real.exp (g * t) = Real.exp (-((rate - g) * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = ((2 : ℝ) ^ n * (4 * Real.pi)) *
          ((Real.exp (-(rate * t)) * Real.exp (g * t)) * scalarDensity θ t) := by
        unfold weightGrowth g
        ring
      _ = _ := by rw [he]
  have hc : (∫⁻ t in Ioi 0, c t) =
      ENNReal.ofReal ((2 : ℝ) ^ n * (4 * Real.pi * (Real.log (rate - g) - θ)⁻¹)) := by
    calc
      _ = ∫⁻ t in Ioi 0, ENNReal.ofReal ((2 : ℝ) ^ n * (4 * Real.pi)) *
          ENNReal.ofReal (Real.exp (-((rate - g) * t)) * scalarDensity θ t) := by
        exact lintegral_congr hpoint
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hdamped,
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) ^ n * (4 * Real.pi))]
        congr 1
        ring
  rw [hc] at h
  exact h

end Critical2DKPZ.SHF.Tsai

end
