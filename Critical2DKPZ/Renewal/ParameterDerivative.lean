/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.ExponentialTilt
public import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Deriv

/-!
# Collision-count marking and parameter derivatives

At a finite horizon the renewal function is a polynomial in its coupling. Marking
one of the renewal factors multiplies the coefficient with `k` collisions by `k+1`.
For nonnegative step weights, the polynomial has nonnegative coefficients and is convex
on nonnegative couplings.
-/

@[expose] public noncomputable section

namespace Critical2DKPZ.Renewal

/-- The local renewal mass with one of its `k+1` renewal factors marked. -/
def markedRenewalMass (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1) * convolutionPower w k n

/-- The cumulative renewal function with one renewal factor marked. -/
def markedRenewalFunction (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1) * cumulativePower w k n

/-- Scaling the step kernel scales its cumulative convolution powers by the corresponding power. -/
theorem cumulativePower_smul (w : ℕ → ℝ) (σ : ℝ) (k n : ℕ) :
    cumulativePower (fun r => σ * w r) k n = σ ^ k * cumulativePower w k n := by
  simp only [cumulativePower, convolutionPower_smul, Finset.mul_sum]

/-- Scaling the step kernel gives the finite polynomial representation of the renewal function. -/
theorem renewalFunction_smul (w : ℕ → ℝ) (σ : ℝ) (n : ℕ) :
    renewalFunction (fun r => σ * w r) n =
      ∑ k ∈ Finset.range (n + 1), σ ^ k * cumulativePower w k n := by
  rw [← sum_cumulativePower]
  simp only [cumulativePower_smul]

/-- The ordinary derivative of the finite renewal polynomial. -/
def renewalParameterDerivative (w : ℕ → ℝ) (σ : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((k : ℝ) * σ ^ (k - 1)) * cumulativePower w k n

/-- The scaled renewal function has the stated polynomial derivative. -/
theorem hasDerivAt_renewalFunction_smul (w : ℕ → ℝ) (σ : ℝ) (n : ℕ) :
    HasDerivAt (fun s => renewalFunction (fun r => s * w r) n)
      (renewalParameterDerivative w σ n) σ := by
  simp_rw [renewalFunction_smul]
  exact HasDerivAt.fun_sum (u := Finset.range (n + 1))
    fun k _ => (hasDerivAt_pow k σ).mul_const (cumulativePower w k n)

/-- The marked renewal function equals the renewal function plus the coupling times its derivative. -/
theorem markedRenewalFunction_eq (w : ℕ → ℝ) (σ : ℝ) (n : ℕ) :
    markedRenewalFunction (fun r => σ * w r) n =
      renewalFunction (fun r => σ * w r) n + σ * renewalParameterDerivative w σ n := by
  simp only [markedRenewalFunction, cumulativePower_smul, renewalFunction_smul,
    renewalParameterDerivative, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · simp only [hk0, Nat.cast_zero, pow_zero, zero_mul, zero_add, one_mul, add_zero, mul_zero]
  · have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)
    have hp : σ * σ ^ (k - 1) = σ ^ k := by rw [← pow_succ', hk1]
    calc
      _ = σ ^ k * cumulativePower w k n +
          (k : ℝ) * (σ * σ ^ (k - 1)) * cumulativePower w k n := by rw [hp]; ring
      _ = _ := by ring

/-- The renewal function is convex in a nonnegative scaling of a nonnegative kernel. -/
theorem convexOn_renewalFunction_smul {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (n : ℕ) :
    ConvexOn ℝ (Set.Ici 0) (fun σ => renewalFunction (fun r => σ * w r) n) := by
  simp_rw [renewalFunction_smul]
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  have hc : ConvexOn ℝ (Set.Ici 0) (fun s => s ^ k * cumulativePower w k n) := by
    simpa only [smul_eq_mul, mul_comm] using
      ConvexOn.smul (cumulativePower_nonneg hw k n) (convexOn_pow k)
  exact hc.2 hx hy ha hb hab

/-- The marked renewal mass is nonnegative. -/
theorem markedRenewalMass_nonneg {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r) (n : ℕ) :
    0 ≤ markedRenewalMass w n := Finset.sum_nonneg fun k _ =>
  mul_nonneg (by positivity) (convolutionPower_nonneg hw k n)


/-- Increasing a nonnegative kernel increases its marked renewal function. -/
theorem markedRenewalFunction_mono_kernel {w v : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    (hwv : ∀ r, w r ≤ v r) (n : ℕ) : markedRenewalFunction w n ≤ markedRenewalFunction v n := by
  unfold markedRenewalFunction
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Finset.sum_le_sum fun m hm => convolutionPower_mono hw hwv k m

end Critical2DKPZ.Renewal

end
