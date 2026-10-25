/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
import Mathlib.Tactic

/-! # Inverse-square moments of smoothed polymer masses -/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.NonGaussian

/-- The inverse square of a smoothed polymer mass is integrable and its expectation
is bounded by the cube of the positive second moment. -/
theorem integral_inv_sq_smoothedP2Plane_le {β : ℝ} (hβ : 0 ≤ β) (s n : ℕ) (x : Site) :
    Integrable (fun ω => (smoothedP2Plane β s n x ω)⁻¹ ^ 2) disorderLaw ∧
      ∫ ω, (smoothedP2Plane β s n x ω)⁻¹ ^ 2 ∂disorderLaw ≤
        (∫ ω, smoothedP2Plane β s n x ω ^ 2 ∂disorderLaw) ^ 3 := by
  let ν : Site → ℝ := fun w => srwKernel s (w - x)
  let A : Finset Site := Polymer.endpoints x s
  have hνA : ∀ w ∉ A, ν w = 0 := fun w hw => Polymer.srwKernel_eq_zero_of_not_mem s x w hw
  have hν0 : ∀ w, 0 ≤ ν w := fun w => Polymer.kernel_nonneg s (w - x)
  have hν1 : ∑ w ∈ A, ν w = 1 := Polymer.sum_srwKernel_endpoints s x
  have hEq (ω : Disorder) : profileP2Fun β s n ν (fun _ => 1) ω = smoothedP2Plane β s n x ω :=
    Polymer.profileP2Fun_srw_flat β s n x ω
  have hPow (ω : Disorder) : smoothedP2Plane β s n x ω ^ (-2 : ℝ) =
      (smoothedP2Plane β s n x ω)⁻¹ ^ 2 := by
    rw [Real.rpow_neg (Polymer.smoothedP2Plane_pos β s n x ω).le, Real.rpow_two, inv_pow]
  have hInt := OnePoint.integrable_rpow_smoothedP2Plane β s n x (-2)
  have hBound := OnePoint.integral_rpow_neg_profileP2Fun_le hβ s n ν A hνA hν0 hν1
    (p := 2) (by norm_num)
  simp only [hEq] at hBound
  norm_num at hBound
  constructor
  · exact hInt.congr (Filter.Eventually.of_forall hPow)
  · simpa only [inv_pow] using hBound

end Critical2DKPZ.NonGaussian

end
