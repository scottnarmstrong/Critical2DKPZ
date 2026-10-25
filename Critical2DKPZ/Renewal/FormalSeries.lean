/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.Sequence
public import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.LinearCombination

/-!
# Differentiated renewal identities

Formal differentiation of the renewal resolvent gives an exact identity for the
local mass in terms of two renewal factors. This is the discrete smoothing identity
used to pass from integrated to local critical renewal convergence.
-/

@[expose] public noncomputable section

namespace Critical2DKPZ.Renewal

/-- The formal positive-step kernel. -/
def stepSeries (w : ℕ → ℝ) : PowerSeries ℝ := PowerSeries.mk (fun n => if n = 0 then 0 else w n)

/-- The formal renewal resolvent, including its constant coefficient one. -/
def renewalSeries (w : ℕ → ℝ) : PowerSeries ℝ := PowerSeries.mk (renewalMass w)

/-- A coefficient of a product of formal series is its finite convolution sum. -/
theorem coeff_mul_range (f g : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n (f * g) = ∑ r ∈ Finset.range (n + 1),
      PowerSeries.coeff r f * PowerSeries.coeff (n - r) g := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun r s => PowerSeries.coeff r f * PowerSeries.coeff s g) n

/-- The formal renewal equation. -/
theorem renewalSeries_eq (w : ℕ → ℝ) :
    renewalSeries w = 1 + stepSeries w * renewalSeries w := by
  ext n
  rw [map_add, coeff_mul_range]
  simp only [renewalSeries, stepSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  cases n with
  | zero => simp only [renewalMass_zero, ↓reduceIte, Nat.zero_add, Finset.sum_range_one, zero_mul, add_zero]
  | succ n =>
    rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < n + 1 + 1)]
    simp only [↓reduceIte, zero_mul, zero_add, Nat.add_one_ne_zero,
      Finset.Ico_add_one_right_eq_Icc]
    rw [renewalMass_succ]
    apply Finset.sum_congr rfl
    intro r hr
    rw [ite_eq_right (by have := (Finset.mem_Icc.mp hr).1; omega)]

/-- One minus the step series, multiplied by the renewal series, equals one. -/
theorem stepSeries_mul_renewalSeries (w : ℕ → ℝ) :
    (1 - stepSeries w) * renewalSeries w = 1 := by
  have h := renewalSeries_eq w
  linear_combination h

/-- The derivative of the formal renewal resolvent is `W' U²`. -/
theorem derivative_renewalSeries (w : ℕ → ℝ) :
    PowerSeries.derivative (renewalSeries w) =
      PowerSeries.derivative (stepSeries w) * (renewalSeries w * renewalSeries w) := by
  let W := stepSeries w
  let U := renewalSeries w
  have hm : (1 - W) * U = 1 := stepSeries_mul_renewalSeries w
  have hd := congrArg (PowerSeries.derivative (R := ℝ)) hm
  simp only [Derivation.leibniz, map_sub, PowerSeries.derivative_one, smul_eq_mul, zero_sub] at hd
  have he : (1 - W) * PowerSeries.derivative U = PowerSeries.derivative W * U := by
    linear_combination hd
  calc
    _ = ((1 - W) * U) * PowerSeries.derivative U := by rw [hm, one_mul]
    _ = U * ((1 - W) * PowerSeries.derivative U) := by ring
    _ = U * (PowerSeries.derivative W * U) := by rw [he]
    _ = _ := by ring

/-- Two renewal factors convolved in time. -/
def renewalSquare (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), renewalMass w j * renewalMass w (n - j)

/-- A coefficient of the squared renewal series is the convolution of renewal masses. -/
theorem coeff_renewalSeries_sq (w : ℕ → ℝ) (n : ℕ) :
    PowerSeries.coeff n (renewalSeries w * renewalSeries w) = renewalSquare w n := by
  rw [coeff_mul_range]
  simp only [renewalSeries, PowerSeries.coeff_mk, renewalSquare]

/-- The exact differentiated renewal identity, with the period convention in the kernel `w`. -/
theorem mul_renewalMass_eq (w : ℕ → ℝ) (n : ℕ) :
    ((n : ℝ) + 1) * renewalMass w (n + 1) =
      ∑ r ∈ Finset.range (n + 1), ((r : ℝ) + 1) * w (r + 1) * renewalSquare w (n - r) := by
  have h := congrArg (PowerSeries.coeff n) (derivative_renewalSeries w)
  rw [PowerSeries.coeff_derivative, coeff_mul_range] at h
  simp only [PowerSeries.coeff_derivative, stepSeries, PowerSeries.coeff_mk,
    Nat.add_one_ne_zero, ↓reduceIte] at h
  rw [show PowerSeries.coeff (n + 1) (renewalSeries w) = renewalMass w (n + 1) from
    PowerSeries.coeff_mk _ _] at h
  rw [mul_comm] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [coeff_renewalSeries_sq]
  ring

end Critical2DKPZ.Renewal

end
