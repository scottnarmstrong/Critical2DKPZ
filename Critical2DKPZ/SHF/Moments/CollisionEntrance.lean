/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WalkBounds
public import Critical2DKPZ.Analysis.Lattice.Sampling
public import Critical2DKPZ.Polymer.WalkKernel
import Mathlib.Tactic

/-! # Phase-correct discrete collision entrance

The total collision mass at time `r` is the doubled-time walk kernel of the starting gap. Every microscopic time is included, and finite spatial support permits arbitrary deterministic tests. -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Polymer

/-- The tested entrance measure of two independent walks at one common time. -/
def collisionSlice (r : ℕ) (a b : Site) (f : Site → ℝ) : ℝ :=
  ∑ z ∈ endpoints a r, srwKernel r (z - a) * srwKernel r (z - b) * f z

/-- The collision slice equals the spatial sum of the two incoming walk kernels times the test. -/
theorem collisionSlice_eq_tsum (r : ℕ) (a b : Site) (f : Site → ℝ) :
    collisionSlice r a b f = ∑' z, srwKernel r (z - a) * srwKernel r (z - b) * f z := by
  symm
  apply tsum_eq_sum
  intro z hz
  rw [srwKernel_eq_zero_of_not_mem r a z hz, zero_mul, zero_mul]

/-- Exact total entrance mass, at even and odd microscopic times alike. -/
theorem collisionSlice_one (r : ℕ) (a b : Site) :
    collisionSlice r a b (fun _ => 1) = srwKernel (2 * r) (b - a) := by
  rw [collisionSlice_eq_tsum]
  simp only [mul_one]
  exact srwKernel_collision r a b

/-- A nonnegative test has a nonnegative collision slice. -/
theorem collisionSlice_nonneg (r : ℕ) (a b : Site) {f : Site → ℝ}
    (hf : ∀ z, 0 ≤ f z) : 0 ≤ collisionSlice r a b f :=
  Finset.sum_nonneg fun z _ =>
    mul_nonneg (mul_nonneg (Critical2DKPZ.srwKernel_nonneg _ _)
      (Critical2DKPZ.srwKernel_nonneg _ _)) (hf z)

/-- An absolutely bounded test controls the collision slice by the doubled-time walk kernel. -/
theorem collisionSlice_abs_le (r : ℕ) (a b : Site) {f : Site → ℝ} {M : ℝ}
    (hf : ∀ z, |f z| ≤ M) :
    |collisionSlice r a b f| ≤ M * srwKernel (2 * r) (b - a) := by
  calc
    _ ≤ ∑ z ∈ endpoints a r, |srwKernel r (z - a) * srwKernel r (z - b) * f z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ z ∈ endpoints a r, M *
        (srwKernel r (z - a) * srwKernel r (z - b)) := by
      apply Finset.sum_le_sum
      intro z _
      rw [abs_mul, abs_of_nonneg (mul_nonneg
        (Critical2DKPZ.srwKernel_nonneg _ _) (Critical2DKPZ.srwKernel_nonneg _ _)), mul_comm M]
      exact mul_le_mul_of_nonneg_left (hf z) (mul_nonneg
        (Critical2DKPZ.srwKernel_nonneg _ _) (Critical2DKPZ.srwKernel_nonneg _ _))
    _ = _ := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [collisionSlice, mul_one] using collisionSlice_one r a b


/-- The collision entrance summed over all microscopic times in an interval, with diffusive spatial scaling. -/
def collisionEntrance (N lo hi : ℕ) (a b : Site) (F : ℝ × Plane → ℝ) : ℝ :=
  ∑ r ∈ Finset.Icc lo hi,
    collisionSlice r a b (fun z => F ((r : ℝ) / N, latticeRepresentative N z))

/-- An absolutely bounded test controls the collision entrance by the sum of doubled-time walk kernels. -/
theorem collisionEntrance_abs_le (N lo hi : ℕ) (a b : Site) {F : ℝ × Plane → ℝ} {M : ℝ}
    (hF : ∀ p, |F p| ≤ M) :
    |collisionEntrance N lo hi a b F| ≤ M * ∑ r ∈ Finset.Icc lo hi,
      srwKernel (2 * r) (b - a) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ => collisionSlice_abs_le r a b (fun z => hF _)

end Critical2DKPZ.SHF.Moments
