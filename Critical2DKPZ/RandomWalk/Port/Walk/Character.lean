/-
Copyright (c) 2026 Ahmed Bou-Rabee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ahmed Bou-Rabee
Modified for Critical2DKPZ, 2026.
-/
module

public import Mathlib

/-! # Orthogonality of circle characters

The integral of an integer-frequency exponential over a full period vanishes at every
nonzero frequency. -/

@[expose] public section

noncomputable section

namespace LatticeProb

open MeasureTheory intervalIntegral



/-- The integral of `exp(i kθ)` over `[-π,π]` vanishes for every nonzero integer `k`. -/
theorem integral_exp_int_mul_restrict (k : ℤ) (hk : k ≠ 0) :
    ∫ θ in Set.Icc (-Real.pi) Real.pi, Complex.exp (Complex.ofReal ((k:ℝ) * θ) * Complex.I) = 0 := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  have hle : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos.le]
  have huIoc : Set.Ioc (-Real.pi) Real.pi = Set.uIoc (-Real.pi) Real.pi :=
    (Set.uIoc_of_le hle).symm
  rw [huIoc]
  have hiv : ∫ (t : ℝ) in -Real.pi..Real.pi, Complex.exp (Complex.ofReal ((k:ℝ) * t) * Complex.I)
      = ∫ (t : ℝ) in Set.uIoc (-Real.pi) Real.pi, Complex.exp (Complex.ofReal ((k:ℝ) * t) * Complex.I) := by
    rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
    simp [hle]
  rw [← hiv]
  have hkc : (k:ℝ) ≠ 0 := by exact_mod_cast hk
  rw [intervalIntegral.integral_comp_mul_left (c := (k:ℝ)) (fun x => Complex.exp (x * Complex.I)) hkc]
  have hneg : (k:ℝ) * (-Real.pi) = -((k:ℝ) * Real.pi) := by ring
  rw [hneg, integral_exp_mul_I_eq_sin ((k:ℝ) * Real.pi)]
  rw [Real.sin_int_mul_pi]
  simp


end LatticeProb

end
