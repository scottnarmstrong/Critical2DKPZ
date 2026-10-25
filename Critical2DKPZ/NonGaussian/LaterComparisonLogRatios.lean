/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Inputs
public import Critical2DKPZ.NonGaussian.HeatStartLogMean
import Mathlib.Tactic

/-! # Log-ratio bounds for the later-SHF comparison -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.LocalSobolev
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.NonGaussian

universe u

/-- The logarithm of the ratio of the two flat heat-start masses is integrable
and its expectation has a uniform lower bound as the heat width vanishes. -/
theorem heatStart_log_ratio_integrable_lower_of (hVD : Smoothing.PropVDBound)
    (ϑ : ℝ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (hsym : ShfSymmetriesAt ϑ P Z) (hHeatStartLogInput : HeatStartLogAt ϑ P Z)
    (hsq : SmallScales.HeatStartSqAt P Z) (hdense : DenseSHFAt ϑ P Z)
    {t : ℝ} (ht : 0 < t) :
    ∃ C r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → ∀ x : Plane,
      Integrable (fun ω => Real.log
        (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω /
          shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω)) P ∧
      -C ≤ ∫ ω, Real.log
        (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω /
          shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω) ∂P := by
  obtain ⟨C, r₁, hr₁, hMeans⟩ :=
    heatStartLog_mean_asymp_of hVD ϑ P Z hZ hsym hHeatStartLogInput hsq hdense
      (by positivity : 0 < t / 6)
  let r₀ : ℝ := min r₁ (t / 6)
  have hr₀ : 0 < r₀ := lt_min hr₁ (by positivity)
  refine ⟨2 * C, r₀, hr₀, ?_⟩
  intro r hr hrr₀ x
  have hrr₁ : r < r₁ := hrr₀.trans_le (min_le_left _ _)
  have hrrt : r < t / 6 := hrr₀.trans_le (min_le_right _ _)
  have hrs : 0 ≤ r := hr.le
  have hT1lo : t / 6 ≤ t - r := by linarith
  have hT1hi : t - r ≤ t := by linarith
  have hT2lo : t / 6 ≤ t / 3 - r := by linarith
  have hT2hi : t / 3 - r ≤ t := by linarith
  have hA := hMeans r t r hrs hT1lo hT1hi hr hrr₁ x
  have hB := hMeans r (t / 3) r hrs hT2lo hT2hi hr hrr₁ x
  have hposA : ∀ᵐ ω ∂P,
      0 < shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω := by
    have hT : r < t := by linarith
    have hPackage := hsym.2.2.2.2.2.2 r t r x (0 : Plane →ᵇ ℝ) hrs hT hr
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hPackage.1
  have hposB : ∀ᵐ ω ∂P,
      0 < shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω := by
    have hT : r < t / 3 := by linarith
    have hPackage := hsym.2.2.2.2.2.2 r (t / 3) r x (0 : Plane →ᵇ ℝ) hrs hT hr
    simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, Real.exp_zero] using hPackage.1
  have hlogRatio : ∀ᵐ ω ∂P,
      Real.log
          (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω /
            shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω) =
        Real.log (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω) -
          Real.log (shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω) := by
    filter_upwards [hposA, hposB] with ω hApos hBpos
    exact Real.log_div hApos.ne' hBpos.ne'
  have hratioInt : Integrable (fun ω => Real.log
      (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω /
        shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω)) P := by
    have hsub := hA.1.sub hB.1
    exact hsub.congr (hlogRatio.mono fun ω hω => hω.symm)
  have hratioIntegral :
      (∫ ω, Real.log
        (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω /
          shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω) ∂P) =
        (∫ ω, Real.log
          (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω) ∂P) -
        (∫ ω, Real.log
          (shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω) ∂P) := by
    calc
      _ = ∫ ω, (Real.log
          (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω) -
            Real.log
              (shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω)) ∂P :=
        integral_congr_ae hlogRatio
      _ = _ := integral_sub hA.1 hB.1
  have hAlower : -C ≤ (∫ ω, Real.log
      (shfPairing Z r t (fun y => heatKernel r (y - x)) (fun _ => 1) ω) ∂P) +
      (1 / 2) * Real.log (Real.log r⁻¹) := (abs_le.mp hA.2).1
  have hBupper : (∫ ω, Real.log
      (shfPairing Z r (t / 3) (fun y => heatKernel r (y - x)) (fun _ => 1) ω) ∂P) +
      (1 / 2) * Real.log (Real.log r⁻¹) ≤ C := (abs_le.mp hB.2).2
  refine ⟨hratioInt, ?_⟩
  rw [hratioIntegral]
  linarith

end Critical2DKPZ.NonGaussian

end
