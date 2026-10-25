/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Positivity.BoundedPairingConvergence
public import Critical2DKPZ.SHF.Positivity.PolymerHeatSecondMoment
public import Critical2DKPZ.JointConvergence.MomentConvergence
import Mathlib.Tactic

/-! # Square integrability of heat-start pairings at every positive width -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter
open Critical2DKPZ.SHF.Limit Critical2DKPZ.SHF.Positivity
open scoped BoundedContinuousFunction Topology

namespace Critical2DKPZ.NonGaussian

/-- The flat-terminal heat-start mass is square integrable at every positive heat width. -/
theorem memLp_heatStart_flat (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) :
    MemLp (shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun _ => 1)) 2 P := by
  let X : ℕ → Disorder → ℝ := fun N ω => ∫ p, heatKernel δ (p.1 - x) ∂polymerMeasure ϑ N s t ω
  let Y : Ω → ℝ := shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun _ => 1)
  have hPair := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x (1 : Plane →ᵇ ℝ)
  have hD : TendstoInDistribution X atTop Y (fun _ => disorderLaw) P := by
    simpa only [X, Y, shfPairing, BoundedContinuousFunction.coe_one, Pi.one_def, Pi.one_apply, mul_one] using hPair.2.2.2
  obtain ⟨C, hC⟩ := polymer_heat_pairing_sq_integral_bounded ϑ hs hst hδ x
  have hInt : ∀ᶠ N : ℕ in atTop, Integrable (fun ω => |X N ω| ^ (2 : ℝ)) disorderLaw := by
    filter_upwards [hC] with N hN
    simpa only [X, Real.rpow_two, sq_abs] using hN.1
  have hBound : ∀ᶠ N : ℕ in atTop, (∫ ω, |X N ω| ^ (2 : ℝ) ∂disorderLaw) ≤ C := by
    filter_upwards [hC] with N hN
    simpa only [X, Real.rpow_two, sq_abs] using hN.2
  have hLimit := JointConvergence.integrable_rpow_limit_of_tendstoInDistribution hD
    (by norm_num : (0 : ℝ) < 2) hInt hBound
  apply (memLp_two_iff_integrable_sq hD.aemeasurable_limit.aestronglyMeasurable).mpr
  simpa only [Real.rpow_two, sq_abs] using hLimit.1

/-- The heat-start pairing against every bounded continuous terminal is square integrable. -/
theorem memLp_heatStart_bounded (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    {s t δ : ℝ} (hs : 0 ≤ s) (hst : s < t) (hδ : 0 < δ) (x : Plane) (g : Plane →ᵇ ℝ) :
    MemLp (shfPairing Z s t (fun y => heatKernel δ (y - x)) g) 2 P := by
  have hFlat := memLp_heatStart_flat ϑ P Z hZ hs hst hδ x
  have hFlatPair := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x (1 : Plane →ᵇ ℝ)
  have hPair := isCriticalSHF_heat_bounded_pairing ϑ P Z hZ hs hst hδ x g
  apply (hFlat.const_mul ‖g‖).mono' hPair.2.1.aestronglyMeasurable
  filter_upwards [hFlatPair.1] with ω hω
  have hInt : Integrable (fun p : Plane × Plane => heatKernel δ (p.1 - x)) (Z s t ω) := by
    simpa only [BoundedContinuousFunction.coe_one, Pi.one_apply, mul_one] using hω
  change ‖∫ p, heatKernel δ (p.1 - x) * g p.2 ∂Z s t ω‖ ≤
    ‖g‖ * shfPairing Z s t (fun y => heatKernel δ (y - x)) (fun _ => 1) ω
  calc
    _ ≤ ∫ p, ‖g‖ * heatKernel δ (p.1 - x) ∂Z s t ω := by
      apply norm_integral_le_of_norm_le (hInt.const_mul ‖g‖)
      exact Filter.Eventually.of_forall fun p => by
        rw [norm_mul, Real.norm_of_nonneg (heatKernel_nonneg hδ.le _)]
        exact (mul_le_mul_of_nonneg_left (g.norm_coe_le_norm p.2) (heatKernel_nonneg hδ.le _)).trans_eq (mul_comm _ _)
    _ = _ := by rw [integral_const_mul]; simp only [shfPairing, mul_one]

end Critical2DKPZ.NonGaussian

end
