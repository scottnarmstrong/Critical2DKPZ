/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.SinglePairWordAverage
public import Critical2DKPZ.SHF.Moments.SinglePairWordProfile
public import Critical2DKPZ.SHF.Moments.WordDominationCellSupport
public import Critical2DKPZ.SHF.Moments.PairBlockGaussianBound
public import Critical2DKPZ.Renewal.CriticalParameter
public import Critical2DKPZ.SHF.DeltaBose.ScalarBounds
public import Critical2DKPZ.Collision.SpatialGaussian
public import Mathlib.Tactic
import Critical2DKPZ.Blocks.StringSumPropagation
import Critical2DKPZ.MomentBounds.CCR25SpatialRenewalBounds
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # The continuum tested future profile for the two-particle word -/

@[expose] public section

noncomputable section

open MeasureTheory
open Filter
open scoped CompactlySupported
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

open DeltaBose






/-- Uniformly over terminal durations, one averaged terminal factor is bounded
by a single cell weight because the walk kernel has total mass one. -/
theorem abs_pairTwoFutureTerminalCellFactor_le {N k : ℕ} (hN : 0 < N)
    (φ : Fin 2 → C_c(Plane × Plane, ℝ)) (x : Fin 2 → Site)
    (w : Site) (i : Fin 2) (M : ℝ) (hM : 0 ≤ M)
    (hφ : ∀ p, |φ i p| ≤ M) :
    |pairTwoFutureTerminalCellFactor N k φ x w i| ≤ 4 * M / N := by
  classical
  let Y : Finset Site :=
    ((Critical2DKPZ.SHF.Flow.finite_support_cellPairTest N (φ i)).toFinset.image
      Prod.snd)
  have hkernel (y : Site) :
      (if w ∈ Polymer.endpoints y k then
        cellTestWeight N (φ i) (x i) y * srwKernel k (y - w) else 0) =
      cellTestWeight N (φ i) (x i) y * srwKernel k (y - w) := by
    by_cases hy : w ∈ Polymer.endpoints y k
    · simp [hy]
    · have hz := Polymer.srwKernel_eq_zero_of_not_mem k y w hy
      have hz' : srwKernel k (y - w) = 0 := by
        rw [Polymer.srwKernel_sub_swap]
        exact hz
      simp [hy, hz']
  have hsumKernel : Summable (fun y : Site => srwKernel k (y - w)) := by
    apply summable_of_hasFiniteSupport
    apply (Polymer.endpoints w k).finite_toSet.subset
    intro y hy
    change srwKernel k (y - w) ≠ 0 at hy
    by_contra hyend
    exact hy (Polymer.srwKernel_eq_zero_of_not_mem k w y hyend)
  have hkernelSum : (∑ y ∈ Y, srwKernel k (y - w)) ≤ 1 := by
    calc
      _ ≤ ∑' y : Site, srwKernel k (y - w) :=
        hsumKernel.sum_le_tsum Y (fun y hy => Polymer.kernel_nonneg k (y - w))
      _ = 1 := Polymer.tsum_srwKernel k w
  have hMweight : 0 ≤ 4 * M / N := by positivity
  unfold pairTwoFutureTerminalCellFactor
  calc
    |∑ y ∈ Y,
        (if w ∈ Polymer.endpoints y k then
          cellTestWeight N (φ i) (x i) y * srwKernel k (y - w) else 0)|
        ≤ ∑ y ∈ Y,
          |if w ∈ Polymer.endpoints y k then
            cellTestWeight N (φ i) (x i) (y) * srwKernel k (y - w) else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ Y, (4 * M / N) * srwKernel k (y - w) := by
      apply Finset.sum_le_sum
      intro y hy
      rw [hkernel y, abs_mul, abs_of_nonneg (Polymer.kernel_nonneg k (y - w))]
      exact mul_le_mul_of_nonneg_right
        (abs_cellTestWeight_le_four_mul_bound_div hN (φ i) M hM hφ (x i) y)
        (Polymer.kernel_nonneg k (y - w))
    _ = (4 * M / N) * ∑ y ∈ Y, srwKernel k (y - w) := by rw [Finset.mul_sum]
    _ ≤ 4 * M / N := by
      calc
        _ ≤ (4 * M / N) * 1 := mul_le_mul_of_nonneg_left hkernelSum hMweight
        _ = 4 * M / N := by ring















/-- The normalized cell test approximates its value at the accessible cell representatives uniformly over both sites. -/
theorem eventually_cellTestWeight_close_to_frozen_sample
    (φ : C_c(Plane × Plane, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ x y : Site, x ∈ evenLattice → y ∈ evenLattice →
      |cellTestWeight N φ x y - (4 / (N : ℝ)) *
        φ (latticeRepresentative N x, latticeRepresentative N y)| ≤
          (4 / (N : ℝ)) * ε := by
  obtain ⟨δ, hδ, hmod⟩ :=
    Metric.uniformContinuous_iff.mp
      (CompactlySupportedContinuousMapClass.uniformContinuous φ) ε hε
  have hmesh := tendsto_lattice_mesh.eventually (Iio_mem_nhds hδ)
  filter_upwards [eventually_gt_atTop 0, hmesh] with N hN hNmesh
  intro x y hx hy
  let S : Set (Plane × Plane) := cell N x ×ˢ cell N y
  let c : ℝ := φ (latticeRepresentative N x, latticeRepresentative N y)
  have hclose (p : Plane × Plane) (hp : p ∈ S) : |φ p - c| ≤ ε := by
    rcases Set.mem_prod.mp hp with ⟨hp₀, hp₁⟩
    have hdist₀ : dist p.1 (latticeRepresentative N x) ≤
        (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
      rw [← cellSample_eq_of_mem_cell hp₀]
      simpa only [dist_comm] using dist_cellSample_le hN p.1
    have hdist₁ : dist p.2 (latticeRepresentative N y) ≤
        (Real.sqrt ((N : ℝ) / 2))⁻¹ := by
      rw [← cellSample_eq_of_mem_cell hp₁]
      simpa only [dist_comm] using dist_cellSample_le hN p.2
    have hdist : dist p (latticeRepresentative N x, latticeRepresentative N y) < δ := by
      rw [Prod.dist_eq]
      exact (max_le_iff.mpr ⟨hdist₀, hdist₁⟩).trans_lt hNmesh
    have h := hmod hdist
    simpa [c, Real.dist_eq] using h.le
  have hvol : volume S = ENNReal.ofReal (4 / (N : ℝ)) *
      ENNReal.ofReal (4 / (N : ℝ)) := by
    dsimp [S]
    rw [Measure.volume_eq_prod, Measure.prod_prod,
      volume_cell hN hx, volume_cell hN hy]
  have hvolTop : volume S < ⊤ := by
    rw [hvol]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  have hvolReal : (volume S).toReal = (4 / (N : ℝ)) ^ 2 := by
    rw [hvol, ENNReal.toReal_mul]
    simp only [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 4 / (N : ℝ)), pow_two]
  have hφint : IntegrableOn (fun p : Plane × Plane => φ p) S volume :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).integrableOn
  have hcint : IntegrableOn (fun _ : Plane × Plane => c) S volume :=
    integrableOn_const hvolTop.ne
  have hdiffint : IntegrableOn (fun p : Plane × Plane => φ p - c) S volume :=
    hφint.sub hcint
  have hεint : IntegrableOn (fun _ : Plane × Plane => ε) S volume :=
    integrableOn_const hvolTop.ne
  have hmono : (∫ p in S, |φ p - c|) ≤ ∫ p in S, ε :=
    setIntegral_mono_on hdiffint.norm hεint
      ((measurableSet_cell N x).prod (measurableSet_cell N y)) hclose
  have hεintegral : (∫ p in S, ε) = ε * (4 / (N : ℝ)) ^ 2 := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul, hvolReal]
    ring
  have hdiffintegral : (∫ p in S, (φ p - c)) =
      (∫ p in S, φ p) - ∫ p in S, c := integral_sub hφint hcint
  have hconstintegral : (∫ p in S, c) =
      c * (4 / (N : ℝ)) ^ 2 := by
    rw [setIntegral_const, measureReal_def, smul_eq_mul, hvolReal]
    ring
  have hnormintegral : |∫ p in S, (φ p - c)| ≤ ∫ p in S, |φ p - c| := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (f := fun p : Plane × Plane => φ p - c)
        (μ := volume.restrict S))
  have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hscale : (N / 4 : ℝ) * (4 / (N : ℝ)) ^ 2 = 4 / (N : ℝ) := by
    field_simp
  have hconstcoef : (N / 4 : ℝ) * (∫ p in S, c) = (4 / (N : ℝ)) * c := by
    rw [hconstintegral]
    calc
      (N / 4 : ℝ) * (c * (4 / (N : ℝ)) ^ 2) =
          ((N / 4 : ℝ) * (4 / (N : ℝ)) ^ 2) * c := by ring
      _ = (4 / (N : ℝ)) * c := by rw [hscale]
  have hform : cellTestWeight N φ x y - (4 / (N : ℝ)) * c =
      (N / 4 : ℝ) * (∫ p in S, (φ p - c)) := by
    have hdecomp : (∫ p in S, φ p) =
        (∫ p in S, (φ p - c)) + (∫ p in S, c) := by linarith [hdiffintegral]
    calc
      cellTestWeight N φ x y - (4 / (N : ℝ)) * c =
          (N / 4 : ℝ) * (∫ p in S, φ p) - (4 / (N : ℝ)) * c := by
            simp [cellTestWeight, S]
      _ = (N / 4 : ℝ) * ((∫ p in S, (φ p - c)) + ∫ p in S, c) -
          (4 / (N : ℝ)) * c := by rw [hdecomp]
      _ = (N / 4 : ℝ) * (∫ p in S, (φ p - c)) := by
        calc
          _ = (N / 4 : ℝ) * (∫ p in S, (φ p - c)) +
                ((N / 4 : ℝ) * (∫ p in S, c) - (4 / (N : ℝ)) * c) := by ring
          _ = _ := by rw [hconstcoef]; ring
  rw [hform]
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ N / 4)]
  calc
    (N / 4 : ℝ) * |∫ p in S, (φ p - c)| ≤
        (N / 4 : ℝ) * ∫ p in S, |φ p - c| :=
      mul_le_mul_of_nonneg_left hnormintegral (by positivity)
    _ ≤ (N / 4 : ℝ) * ∫ p in S, ε :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (4 / (N : ℝ)) * ε := by
      rw [hεintegral]
      calc
        (N / 4 : ℝ) * (ε * (4 / (N : ℝ)) ^ 2) =
            ((N / 4 : ℝ) * (4 / (N : ℝ)) ^ 2) * ε := by ring
        _ = (4 / (N : ℝ)) * ε := by rw [hscale]

end Critical2DKPZ.SHF.Moments

end
