/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.Grid
public import Critical2DKPZ.Definitions.IsCriticalKPZ
public import Critical2DKPZ.Definitions.TestFnDilate
public import Critical2DKPZ.Extensions.Definitions.ScaleRadius
import Critical2DKPZ.Extensions.ScaleLimit.L2Replacements
import Critical2DKPZ.Extensions.ScaleLimit.ArrayMoments
import Critical2DKPZ.Extensions.ScaleLimit.Centring
import Mathlib.Tactic

/-! # Replacement of canonical widths by the geometric block widths -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- On the same unit-time KPZ field, equal positive clocks allow changing the
mollifier and replacing the canonical width by the geometric width. -/
theorem replacement_reduction (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z)
    (H : ℝ → (Plane →ᵇ ℝ) → Ω → Distr) (hH : IsCriticalKPZ P Z H)
    (φ ψ : TestFn) (hφ : ∀ y, 0 ≤ φ y) (hψ : ∀ y, 0 ≤ ψ y)
    (hφ1 : (∫ y, φ y) = 1) (hψ1 : (∫ y, ψ y) = 1)
    {ρ : ℝ} (hρ : 1 < ρ) {s : ℝ} (hs : 0 < s) :
    TendstoInMeasure P (fun (L : Set.Ioi (0 : ℝ)) ω =>
      (H 1 0 ω (φ.dilate (scaleRadius L s) 0) -
        H 1 0 ω (ψ.dilate (Real.sqrt (tau ρ (nL ρ L s))) 0)) / Real.sqrt L)
      atTop (fun _ => 0) := by
  let D : Set.Ioi (0 : ℝ) → Ω → ℝ := fun L ω =>
    H 1 0 ω (φ.dilate (scaleRadius L s) 0) -
      H 1 0 ω (ψ.dilate (Real.sqrt (tau ρ (nL ρ L s))) 0)
  have hclock := tendsto_replacement_sq ϑ P Z hZ H hH 1 zero_lt_one φ ψ
    hφ hψ hφ1 hψ1 0 (fun L => scaleRadius_pos L s)
    (fun L => Real.sqrt_pos.mpr (tau_pos hρ _))
    (Filter.Eventually.of_forall fun L => scaleRadius_lt_one L s)
    (eventually_geometric_width_lt_one ρ s hρ hs) hs
    (tendsto_scaleRadius_clock s) (normalized_loglog_geometric_clock ρ s hρ hs)
  have hmem (L : Set.Ioi (0 : ℝ)) : MemLp (fun ω => D L ω / Real.sqrt L) 2 P := by
    have hi : MemLp (D L) 2 P :=
      (memLp_kpz_two ϑ P Z hZ H hH 1 zero_lt_one _).sub
        (memLp_kpz_two ϑ P Z hZ H hH 1 zero_lt_one _)
    have h : MemLp (fun ω => (Real.sqrt (L : ℝ))⁻¹ * D L ω) 2 P := hi.const_mul _
    simpa only [div_eq_mul_inv, mul_comm] using h
  apply tendstoInMeasure_zero_of_integral_sq P atTop _ hmem
  have heq (L : Set.Ioi (0 : ℝ)) : (∫ ω, (D L ω / Real.sqrt L) ^ 2 ∂P) =
      (L : ℝ)⁻¹ * ∫ ω, D L ω ^ 2 ∂P := by
    simp_rw [div_pow]
    rw [integral_div, Real.sq_sqrt L.property.le]
    ring
  simpa only [heq, D] using hclock

end Critical2DKPZ.Extensions.ScaleLimit
