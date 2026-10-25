/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonBlocks
public import Critical2DKPZ.Polymer.SmoothedCovariance
import Mathlib.Probability.Moments.Variance

/-! # First-collision variance formula for the CCR linear-time windows -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- The covariance of two source window masses has the local first-collision
formula, with their free entrance time included in the walk kernel. -/
theorem covariance_freeEntranceWindowMass_eq_sum (β : ℝ) {a b : ℕ}
    (hab : a ≤ b) (x y : Site) :
    covariance (freeEntranceWindowMass β a b x) (freeEntranceWindowMass β a b y) disorderLaw =
      ∑ r ∈ Finset.Icc (a + 1) b, srwKernel (2 * r) (y - x) * Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (b - r) 0 ω ^ 2 ∂disorderLaw) := by
  rw [covariance_eq_sub (memLp_freeEntranceWindowMass β a b x 2 (by norm_num))
    (memLp_freeEntranceWindowMass β a b y 2 (by norm_num))]
  change (∫ ω, freeEntranceWindowMass β a b x ω * freeEntranceWindowMass β a b y ω ∂disorderLaw) -
    (∫ ω, freeEntranceWindowMass β a b x ω ∂disorderLaw) *
    (∫ ω, freeEntranceWindowMass β a b y ω ∂disorderLaw) = _
  rw [integral_freeEntranceWindowMass, integral_freeEntranceWindowMass, mul_one]
  simp_rw [freeEntranceWindowMass_eq_smoothedP2Plane]
  exact Polymer.local_replica_formula β a b hab x y

/-- The exact finite-start window second moment. No positivity restriction is
imposed on the entrance test or its coefficients. -/
theorem integral_sq_latticeWindowFluctuation_eq_sum (β c : ℝ) {a b : ℕ}
    (hab : a ≤ b) (S : Finset Site) (ν : Site → ℝ) :
    (∫ ω, latticeWindowFluctuation β c a b S ν ω ^ 2 ∂disorderLaw) =
      c ^ 2 * ∑ w ∈ S, ∑ v ∈ S, ν w * ν v *
        (∑ r ∈ Finset.Icc (a + 1) b, srwKernel (2 * r) (v - w) * Polymer.sigmaSq β *
          (∫ ω, pointToPlane β 0 (b - r) 0 ω ^ 2 ∂disorderLaw)) := by
  have hL2 := memLp_latticeWindowFluctuation β c a b S ν 2 (by norm_num)
  have hvar : variance (latticeWindowFluctuation β c a b S ν) disorderLaw =
      ∫ ω, latticeWindowFluctuation β c a b S ν ω ^ 2 ∂disorderLaw := by
    rw [variance_eq_sub hL2, integral_latticeWindowFluctuation]
    simp only [zero_pow (by decide : 2 ≠ 0), sub_zero, Pi.pow_apply]
  rw [← hvar]
  unfold latticeWindowFluctuation
  rw [variance_const_mul]
  have hmem (w : Site) : MemLp (fun ω => ν w * (freeEntranceWindowMass β a b w ω - 1)) 2 disorderLaw :=
    ((memLp_freeEntranceWindowMass β a b w 2 (by norm_num)).sub (memLp_const 1)).const_mul _
  rw [variance_fun_sum' (fun w _ => hmem w)]
  congr 1
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  rw [covariance_const_mul_left, covariance_const_mul_right,
    covariance_sub_const_left
      ((memLp_freeEntranceWindowMass β a b w 2 (by norm_num)).integrable (by norm_num)),
    covariance_sub_const_right
      ((memLp_freeEntranceWindowMass β a b v 2 (by norm_num)).integrable (by norm_num)),
    covariance_freeEntranceWindowMass_eq_sum β hab w v]
  ring

end Critical2DKPZ.Extensions.GffTangent
