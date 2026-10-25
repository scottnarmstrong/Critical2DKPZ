/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceDiagram
public import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceEndpointProduct
import Critical2DKPZ.SHF.Tsai.ConjugatedAverageAlgebra
import Critical2DKPZ.SHF.Tsai.ConjugatedLaplaceAverage
import Critical2DKPZ.SHF.Tsai.ConjugatedDiagramTimeComparison
import Mathlib.Tactic

/-! # Pointwise conjugated diagram estimates from Laplace averaging -/

@[expose] public noncomputable section

open MeasureTheory Critical2DKPZ.DeltaBose
open scoped ENNReal

namespace Critical2DKPZ.SHF.Tsai

/-- Apply the adjustable Laplace window to a complete diagram and cancel
its complementary endpoint factors. The remaining bound is a literal scalar
expression with one logarithmic factor per collision. -/
theorem weightedFormBound_averaged_diagram_conj {n : ℕ} (θ : ℝ) {p a lam t : ℝ}
    (hp : 1 < p) (ha : 0 ≤ a) (ht : 0 < t)
    (hrEndpoint : conjugatedEndpointShift n hp ha < lam)
    (hrSwap : conjugatedSwappingThreshold n hp ha ≤ lam)
    (hrCollision : 2 * n * a ^ 2 < lam)
    (hθ : θ < Real.log (lam - 2 * n * a ^ 2))
    (hWindow : 1 / (lam - conjugatedEndpointShift n hp ha) ≤ t)
    (α : CollisionPair n) (w : List (CollisionPair n)) (hword : collisionListNoAdjacentRepeat (α :: w)) :
    WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
      (fun y => a * configurationOneNorm y) p (p / (p - 1)) (diagramKernel θ (α :: w) t)
      (ENNReal.ofReal (Real.exp (lam * (t + 1 / (lam - conjugatedEndpointShift n hp ha))) *
        (2 : ℝ) ^ (n * (2 * (w.length + 1) + 1)) * conjugatedEndpointProductConstant n hp ha *
        (((2 : ℝ) ^ n * (4 * Real.pi)) / (Real.log (lam - 2 * n * a ^ 2) - θ)) *
        (conjugatedSwappingConstant n hp ha * ((2 : ℝ) ^ n * (4 * Real.pi)) /
          (Real.log (lam - 2 * n * a ^ 2) - θ)) ^ w.length)) := by
  let δ : ℝ := 1 / (lam - conjugatedEndpointShift n hp ha)
  let K : TimeKernel (Configuration n) (Configuration n) := fun q =>
    diagramKernel θ (α :: w) q.1 q.2.1 q.2.2
  let C : ℝ := (2 : ℝ) ^ (n * (2 * (w.length + 1) + 1))
  let F : ℝ≥0∞ := ENNReal.ofReal δ⁻¹ * ENNReal.ofReal (Real.exp (lam * (t + δ))) * ENNReal.ofReal C
  have hδ : 0 < δ := one_div_pos.mpr (sub_pos.mpr hrEndpoint)
  have hWindow' : δ ≤ t := hWindow
  have hRate : 0 ≤ lam :=
    (zero_le_one.trans (conjugatedSwappingConstants_ge_one n hp ha).2).trans hrSwap
  have hF : F ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top
  have hpoint (x y : Configuration n) : diagramKernel θ (α :: w) t x y ≤
      F * laplaceTimeKernel lam K x y := by
    apply le_laplaceTimeKernel_of_local_comparison K hRate ht hδ ENNReal.ofReal_ne_top x y
    intro s hts hsδ
    have hst : s ≤ 2 * t := by linarith only [hsδ, hWindow']
    simpa only [List.length_cons] using
      diagramKernel_le_on_double_time_interval θ (α :: w) ht hts hst x y
  have hLaplace := weightedFormBound_laplace_diagram_conj θ hp ha hrEndpoint hrSwap hrCollision hθ α w hword
  have hAt := (weightedFormBound_const_mul hF hLaplace).mono hpoint le_rfl
  have hP : 0 ≤ conjugatedEndpointProductConstant n hp ha := (conjugatedEndpointProductConstant_pos n hp ha).le
  have hS : 0 ≤ conjugatedSwappingConstant n hp ha := zero_le_one.trans (conjugatedSwappingConstants_ge_one n hp ha).1
  have hJ : 0 ≤ ((2 : ℝ) ^ n * (4 * Real.pi)) / (Real.log (lam - 2 * n * a ^ 2) - θ) :=
    div_nonneg (by positivity) (sub_pos.mpr hθ).le
  have hEndpoint : conjugatedEndpointLaplaceFactor n hp ha lam (1 / p) *
      conjugatedEndpointLaplaceFactor n hp ha lam (1 - 1 / p) =
      ENNReal.ofReal (conjugatedEndpointProductConstant n hp ha / (lam - conjugatedEndpointShift n hp ha)) := by
    simpa only [mul_one_div] using conjugatedEndpointLaplaceFactor_mul_complement hp ha hrEndpoint
  have hCollision : conjugatedCollisionLaplaceFactor n θ a lam =
      ENNReal.ofReal (((2 : ℝ) ^ n * (4 * Real.pi)) / (Real.log (lam - 2 * n * a ^ 2) - θ)) := by
    unfold conjugatedCollisionLaplaceFactor
    congr 1
    ring
  have hInv : δ⁻¹ = lam - conjugatedEndpointShift n hp ha := by
    dsimp [δ]
    rw [one_div, inv_inv]
  have hcoef := ennreal_average_endpoint_cancel
    (E := Real.exp (lam * (t + δ))) (K := C) w.length (sub_pos.mpr hrEndpoint)
    hP hS hJ (Real.exp_pos _).le (by dsimp [C]; positivity) hEndpoint
  change WeightedFormBound volume volume (fun x => -(a * configurationOneNorm x))
    (fun y => a * configurationOneNorm y) p (p / (p - 1)) (diagramKernel θ (α :: w) t)
    (F * (conjugatedEndpointLaplaceFactor n hp ha lam (1 / p) *
      (conjugatedCollisionLaplaceFactor n θ a lam *
        ((ENNReal.ofReal (conjugatedSwappingConstant n hp ha) *
          conjugatedCollisionLaplaceFactor n θ a lam) ^ w.length *
          conjugatedEndpointLaplaceFactor n hp ha lam (1 - 1 / p))))) at hAt
  dsimp only [F] at hAt
  rw [hInv, hCollision, hcoef] at hAt
  simpa only [mul_div_assoc] using hAt

end Critical2DKPZ.SHF.Tsai

end
