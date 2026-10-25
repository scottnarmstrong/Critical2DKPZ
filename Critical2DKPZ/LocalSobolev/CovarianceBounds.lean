/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LocalSobolev.Inputs
public import Critical2DKPZ.Smoothing.ChapmanKolmogorov
public import Critical2DKPZ.Polymer.SmoothedCovariance
public import Critical2DKPZ.MomentBounds.CSZ25Green
import Mathlib.Tactic

/-! # Covariance estimates from replica moments -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Critical2DKPZ.LocalSobolev


/-- The logarithmic form of the first-collision estimate. Keeping the logarithm is essential
when the truncated Green function grows with the lattice scale. -/
theorem smoothedP2Plane_covariance_le_log_truncatedGreen_of
    (β : ℝ) (hβ : 0 ≤ β) (n : ℕ) (x y : Site)
    (C E : ℝ)
    (hcoeff : ∀ r ∈ Finset.Icc 1 n,
      Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) ≤ C)
    (hDx : gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β 0 n x ω)) ≤ E)
    (hDy : gaussianityDefect disorderLaw
        (fun ω => Real.log (smoothedP2Plane β 0 n y ω)) ≤ E) :
    ProbabilityTheory.covariance
        (fun ω => Real.log (smoothedP2Plane β 0 n x ω))
        (fun ω => Real.log (smoothedP2Plane β 0 n y ω)) disorderLaw ≤
      Real.log (1 + C * MomentBounds.truncatedGreen n (y - x)) + 2 * E := by
  have hcov := Smoothing.covariance_log_smoothedP2Plane_le hβ 0 n x y
  have hreplica := Polymer.local_replica_formula β 0 n (by omega) x y
  have hσ : 0 ≤ Polymer.sigmaSq β := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
  have hsumNonneg : 0 ≤ ∑ r ∈ Finset.Icc 1 n,
      srwKernel (2 * r) (y - x) * Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) :=
    Finset.sum_nonneg fun r hr =>
      mul_nonneg (mul_nonneg (Polymer.kernel_nonneg (2 * r) (y - x)) hσ)
        (integral_nonneg fun ω => sq_nonneg _)
  have hsum : ∑ r ∈ Finset.Icc 1 n,
      srwKernel (2 * r) (y - x) * Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) ≤
      C * MomentBounds.truncatedGreen n (y - x) := by
    calc
      _ ≤ ∑ r ∈ Finset.Icc 1 n, srwKernel (2 * r) (y - x) * C := by
        apply Finset.sum_le_sum
        intro r hr
        have hk := hcoeff r hr
        calc
          srwKernel (2 * r) (y - x) * Polymer.sigmaSq β *
              (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) =
            srwKernel (2 * r) (y - x) *
              (Polymer.sigmaSq β *
                ∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by ring
          _ ≤ srwKernel (2 * r) (y - x) * C :=
            mul_le_mul_of_nonneg_left hk (Polymer.kernel_nonneg _ _)
      _ = C * MomentBounds.truncatedGreen n (y - x) := by
        rw [← Finset.sum_mul]
        simp [MomentBounds.truncatedGreen, mul_comm]
  have hprod :
      ∫ ω, smoothedP2Plane β 0 n x ω * smoothedP2Plane β 0 n y ω ∂disorderLaw =
        1 + ∑ r ∈ Finset.Icc 1 n,
          srwKernel (2 * r) (y - x) * Polymer.sigmaSq β *
            (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
    linarith [hreplica]
  have hprodpos : 0 < ∫ ω, smoothedP2Plane β 0 n x ω *
      smoothedP2Plane β 0 n y ω ∂disorderLaw := by
    rw [hprod]
    linarith
  have hlog :
      Real.log (∫ ω, smoothedP2Plane β 0 n x ω *
        smoothedP2Plane β 0 n y ω ∂disorderLaw) ≤
        Real.log (1 + C * MomentBounds.truncatedGreen n (y - x)) := by
    apply Real.log_le_log hprodpos
    rw [hprod]
    linarith
  calc
    _ ≤ Real.log (∫ ω, smoothedP2Plane β 0 n x ω *
          smoothedP2Plane β 0 n y ω ∂disorderLaw) +
          gaussianityDefect disorderLaw
            (fun ω => Real.log (smoothedP2Plane β 0 n x ω)) +
          gaussianityDefect disorderLaw
            (fun ω => Real.log (smoothedP2Plane β 0 n y ω)) := hcov.2
    _ ≤ Real.log (1 + C * MomentBounds.truncatedGreen n (y - x)) + E + E := by
      exact add_le_add (add_le_add hlog hDx) hDy
    _ = _ := by ring

end Critical2DKPZ.LocalSobolev

end

end
