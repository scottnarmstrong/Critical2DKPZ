/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonWindowVariance
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.Analysis.Lattice.Sampling
import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Exact cell pairings for the finite-start window variance -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- The walk energy equals the finite sum of cell masses, with no point-sampling
approximation of the compact test functions. -/
theorem integral_pair_srwKernel_eq_sum_cell (N n : ℕ)
    (f g : Plane → ℝ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (hg : Continuous g) (hgs : HasCompactSupport g)
    (S V : Finset Site)
    (hS : ∀ x, f x ≠ 0 → latticePoint N x ∈ S)
    (hV : ∀ y, g y ≠ 0 → latticePoint N y ∈ V) :
    (∫ p : Plane × Plane, f p.1 * g p.2 *
      srwKernel n (latticePoint N p.2 - latticePoint N p.1) ∂(volume.prod volume)) =
      ∑ w ∈ S, ∑ v ∈ V, (∫ x in cell N w, f x) * (∫ y in cell N v, g y) *
        srwKernel n (v - w) := by
  have hfg : Integrable (fun p : Plane × Plane => f p.1 * g p.2) (volume.prod volume) :=
    (hf.integrable_of_hasCompactSupport hfs).mul_prod
    (hg.integrable_of_hasCompactSupport hgs)
  have hKm : Measurable (fun p : Plane × Plane =>
      srwKernel n (latticePoint N p.2 - latticePoint N p.1)) :=
    (measurable_of_countable (fun z : Site => srwKernel n z)).comp
      (((measurable_latticePoint N).comp measurable_snd).sub
        ((measurable_latticePoint N).comp measurable_fst))
  have hprod : Integrable (fun p : Plane × Plane => f p.1 * g p.2 *
      srwKernel n (latticePoint N p.2 - latticePoint N p.1)) (volume.prod volume) := by
    apply hfg.norm.mono' (hfg.aestronglyMeasurable.mul hKm.aestronglyMeasurable)
    exact Eventually.of_forall fun p => by
      change ‖f p.1 * g p.2 * srwKernel n (latticePoint N p.2 - latticePoint N p.1)‖ ≤
        ‖f p.1 * g p.2‖
      rw [norm_mul]
      apply mul_le_of_le_one_right (norm_nonneg _)
      rw [Real.norm_eq_abs, abs_of_nonneg (Polymer.kernel_nonneg _ _)]
      exact Polymer.srwKernel_le_one _ _
  rw [integral_prod _ hprod]
  have hinner (x : Plane) :
      (∫ y : Plane, f x * g y * srwKernel n (latticePoint N y - latticePoint N x)) =
        f x * ∑ v ∈ V, (∫ y in cell N v, g y) *
          srwKernel n (v - latticePoint N x) := by
    rw [show (fun y : Plane => f x * g y * srwKernel n (latticePoint N y - latticePoint N x)) =
      (fun y => f x * (g y * srwKernel n (latticePoint N y - latticePoint N x))) by
        funext y; ring, integral_const_mul,
      JointConvergence.integral_mul_latticePoint_piecewise hg hgs N
        (fun v => srwKernel n (v - latticePoint N x)) V hV]
  simp_rw [hinner]
  rw [JointConvergence.integral_mul_latticePoint_piecewise hf hfs N
    (fun w => ∑ v ∈ V, (∫ y in cell N v, g y) * srwKernel n (v - w)) S hS]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Exact normalization of a window variance in terms of averaged walk
energies. In particular the even-cell area contributes the factor four. -/
theorem integral_sq_cell_window_eq_collision_sum (β c : ℝ) {a b : ℕ}
    (hab : a ≤ b) (N : ℕ) (hN : 0 < N)
    (f : Plane → ℝ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (S : Finset Site) (hS : ∀ x, f x ≠ 0 → latticePoint N x ∈ S) :
    (∫ ω, latticeWindowFluctuation β c a b S
      (fun w => ∫ x in cell N w, f x) ω ^ 2 ∂disorderLaw) =
      c ^ 2 * (4 / (N : ℝ)) * ∑ r ∈ Finset.Icc (a + 1) b,
        (∫ p : Plane × Plane, f p.1 * f p.2 *
          ((N : ℝ) / 4 * srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1))
          ∂(volume.prod volume)) * Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 (b - r) 0 ω ^ 2 ∂disorderLaw) := by
  let ν : Site → ℝ := fun w => ∫ x in cell N w, f x
  let D : ℕ → ℝ := fun r => ∑ w ∈ S, ∑ v ∈ S, ν w * ν v * srwKernel (2 * r) (v - w)
  let M : ℕ → ℝ := fun r => ∫ ω, pointToPlane β 0 (b - r) 0 ω ^ 2 ∂disorderLaw
  have henergy (r : ℕ) :
      (∫ p : Plane × Plane, f p.1 * f p.2 *
        ((N : ℝ) / 4 * srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1))
        ∂(volume.prod volume)) = (N : ℝ) / 4 * D r := by
    calc
      _ = (N : ℝ) / 4 * ∫ p : Plane × Plane, f p.1 * f p.2 *
          srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1) ∂(volume.prod volume) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun p => by dsimp only; ring
      _ = _ := congrArg ((N : ℝ) / 4 * ·)
        (integral_pair_srwKernel_eq_sum_cell N (2 * r) f f hf hfs hf hfs S S hS hS)
  have hsum : (∑ w ∈ S, ∑ v ∈ S, ν w * ν v *
      (∑ r ∈ Finset.Icc (a + 1) b, srwKernel (2 * r) (v - w) * Polymer.sigmaSq β * M r)) =
      ∑ r ∈ Finset.Icc (a + 1) b, D r * Polymer.sigmaSq β * M r := by
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ w ∈ S, ∑ r ∈ Finset.Icc (a + 1) b, ∑ v ∈ S,
          ν w * ν v * (srwKernel (2 * r) (v - w) * Polymer.sigmaSq β * M r) := by
        apply Finset.sum_congr rfl
        intro w _
        exact Finset.sum_comm
      _ = ∑ r ∈ Finset.Icc (a + 1) b, ∑ w ∈ S, ∑ v ∈ S,
          ν w * ν v * (srwKernel (2 * r) (v - w) * Polymer.sigmaSq β * M r) :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r _
        dsimp only [D]
        simp_rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro w _
        apply Finset.sum_congr rfl
        intro v _
        ring
  rw [integral_sq_latticeWindowFluctuation_eq_sum β c hab]
  change c ^ 2 * (∑ w ∈ S, ∑ v ∈ S, ν w * ν v *
    (∑ r ∈ Finset.Icc (a + 1) b, srwKernel (2 * r) (v - w) * Polymer.sigmaSq β * M r)) = _
  rw [hsum]
  simp_rw [henergy]
  rw [mul_assoc]
  apply congrArg (c ^ 2 * ·)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  dsimp only [M]
  field_simp

end Critical2DKPZ.Extensions.GffTangent
