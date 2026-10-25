/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.FirstMoment
import Critical2DKPZ.Smoothing.GreenApproximation
import Critical2DKPZ.Smoothing.KernelVariation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Moving-time averaged walk energies for the fixed-horizon CLT -/

@[expose] public noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- The averaged even-time walk kernel has a bound uniform down to time
zero. This uses its exact row mass rather than a singular local-CLT estimate. -/
theorem integral_abs_scaled_walk_energy_le (N r : ℕ) (hN : 0 < N)
    (f g : Plane → ℝ) (hf : Integrable f) (hg : Measurable g)
    (B : ℝ) (hgB : ∀ y, |g y| ≤ B) :
    Integrable (fun p : Plane × Plane => |f p.1| * |g p.2| *
      ((N : ℝ) / 4 * srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1)))
      (volume.prod volume) ∧
    (∫ p : Plane × Plane, |f p.1| * |g p.2| *
      ((N : ℝ) / 4 * srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1))
      ∂(volume.prod volume)) ≤ B * ∫ x : Plane, |f x| := by
  let K : Plane × Plane → ℝ := fun p => (N : ℝ) / 4 *
    srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1)
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hKm : Measurable K := by
    apply Measurable.const_mul
    exact (measurable_of_countable (fun z : Site => srwKernel (2 * r) z)).comp
      (((measurable_latticePoint N).comp measurable_snd).sub
        ((measurable_latticePoint N).comp measurable_fst))
  have hK0 (p : Plane × Plane) : 0 ≤ K p :=
    mul_nonneg (by positivity) (Polymer.kernel_nonneg _ _)
  have hrow (x : Plane) : Integrable (fun y => K (x, y)) ∧
      (∫ y : Plane, K (x, y)) = 1 := by
    have hz : Even (latticePoint N x 0 + latticePoint N x 1) :=
      latticePoint_mem_evenLattice N x
    refine ⟨(Smoothing.integrable_srwKernel_latticePoint N (2 * r) hN
      ⟨r, by omega⟩ _ hz).const_mul _, ?_⟩
    dsimp only [K]
    rw [integral_const_mul, Smoothing.integral_srwKernel_latticePoint_eq N (2 * r)
      hN ⟨r, by omega⟩ _ hz]
    field_simp
  have hinner (x : Plane) : Integrable (fun y => |g y| * K (x, y)) := by
    apply (hrow x).1.bdd_mul hg.abs.aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs, abs_abs] using hgB y
  have hinner_le (x : Plane) :
      (∫ y : Plane, |g y| * K (x, y)) ≤ B := by
    calc
      _ ≤ ∫ y : Plane, B * K (x, y) :=
        integral_mono (hinner x) ((hrow x).1.const_mul B)
          (fun y => mul_le_mul_of_nonneg_right (hgB y) (hK0 (x, y)))
      _ = B := by rw [integral_const_mul, (hrow x).2, mul_one]
  have hFmeas : AEStronglyMeasurable (fun p : Plane × Plane =>
      |f p.1| * |g p.2| * K p) (volume.prod volume) :=
    (hf.abs.aestronglyMeasurable.comp_fst.mul hg.abs.aestronglyMeasurable.comp_snd).mul
      hKm.aestronglyMeasurable
  have houter : Integrable (fun x : Plane => ∫ y : Plane, |f x| * |g y| * K (x, y)) := by
    apply (hf.abs.mul_const B).mono'
    · exact hFmeas.integral_prod_right'
    · exact Eventually.of_forall fun x => by
        rw [show (fun y => |f x| * |g y| * K (x, y)) =
          (fun y => |f x| * (|g y| * K (x, y))) by funext y; ring,
          integral_const_mul, Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (abs_nonneg _) (integral_nonneg
            (fun y => mul_nonneg (abs_nonneg _) (hK0 (x, y)))))]
        exact mul_le_mul_of_nonneg_left (hinner_le x) (abs_nonneg _)
  have hFint : Integrable (fun p : Plane × Plane => |f p.1| * |g p.2| * K p)
      (volume.prod volume) := by
    apply (integrable_prod_iff hFmeas).mpr
    refine ⟨Eventually.of_forall (fun x => ?_), ?_⟩
    · simpa only [mul_assoc] using (hinner x).const_mul (|f x|)
    · simpa only [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hK0 _))] using houter
  refine ⟨hFint, ?_⟩
  rw [integral_prod _ hFint]
  calc
    _ ≤ ∫ x : Plane, |f x| * B := by
      apply integral_mono houter (hf.abs.mul_const B)
      intro x
      change (∫ y : Plane, |f x| * |g y| * K (x, y)) ≤ |f x| * B
      rw [show (fun y => |f x| * |g y| * K (x, y)) =
        (fun y => |f x| * (|g y| * K (x, y))) by funext y; ring,
        integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hinner_le x) (abs_nonneg _)
    _ = B * ∫ x : Plane, |f x| := by rw [integral_mul_const, mul_comm]

/-- Signed averaged energies satisfy the same uniform row-mass bound. -/
theorem abs_integral_scaled_walk_energy_le (N r : ℕ) (hN : 0 < N)
    (f g : Plane → ℝ) (hf : Integrable f) (hg : Measurable g)
    (B : ℝ) (hgB : ∀ y, |g y| ≤ B) :
    |∫ p : Plane × Plane, f p.1 * g p.2 *
      ((N : ℝ) / 4 * srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1))
      ∂(volume.prod volume)| ≤ B * ∫ x : Plane, |f x| := by
  obtain ⟨_, hbound⟩ := integral_abs_scaled_walk_energy_le N r hN f g hf hg B hgB
  calc
    _ ≤ ∫ p : Plane × Plane, |f p.1 * g p.2 *
        ((N : ℝ) / 4 * srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1))|
        ∂(volume.prod volume) := abs_integral_le_integral_abs
    _ = ∫ p : Plane × Plane, |f p.1| * |g p.2| *
        ((N : ℝ) / 4 * srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1))
        ∂(volume.prod volume) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun p => by
        dsimp only
        rw [abs_mul, abs_mul, abs_of_nonneg
          (mul_nonneg (by positivity) (Polymer.kernel_nonneg _ _))]
    _ ≤ _ := hbound

/-- The period-correct walk quadratic form converges at every positive moving
macroscopic time. Integrable signed tests are sufficient. -/
theorem tendsto_integral_scaled_walk_energy {r : ℕ → ℕ} {u : ℝ}
    (hu : 0 < u) (hr : Tendsto (fun N : ℕ => (r N : ℝ) / N) atTop (𝓝 u))
    (f g : Plane → ℝ) (hf : Integrable f) (hg : Integrable g) :
    Tendsto (fun N : ℕ => ∫ p : Plane × Plane,
      f p.1 * g p.2 * ((N : ℝ) / 4 *
        srwKernel (2 * r N) (latticePoint N p.2 - latticePoint N p.1))
      ∂(volume.prod volume)) atTop
      (𝓝 (∫ p : Plane × Plane,
        f p.1 * g p.2 * heatKernel (2 * u) (p.2 - p.1)
        ∂(volume.prod volume))) := by
  let μ : Measure (Plane × Plane) := volume.prod volume
  let F : ℕ → Plane × Plane → ℝ := fun N p =>
    f p.1 * g p.2 * ((N : ℝ) / 4 *
      srwKernel (2 * r N) (latticePoint N p.2 - latticePoint N p.1))
  have hfg : Integrable (fun p : Plane × Plane => f p.1 * g p.2) μ :=
    hf.mul_prod hg
  have hK (N : ℕ) : Measurable (fun p : Plane × Plane =>
      (N : ℝ) / 4 * srwKernel (2 * r N)
        (latticePoint N p.2 - latticePoint N p.1)) := by
    apply Measurable.const_mul
    exact (measurable_of_countable (fun z : Site => srwKernel (2 * r N) z)).comp
      (((measurable_latticePoint N).comp measurable_snd).sub
        ((measurable_latticePoint N).comp measurable_fst))
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ p : Plane × Plane,
      |(N : ℝ) / 4 * srwKernel (2 * r N)
        (latticePoint N p.2 - latticePoint N p.1)| ≤ 1 / u := by
    filter_upwards [eventually_gt_atTop 0,
      hr.eventually (lt_mem_nhds (half_lt_self hu))] with N hN hrN p
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hgap : u / 2 * N < (r N : ℝ) := (lt_div_iff₀ hNr).mp hrN
    rw [abs_of_nonneg (mul_nonneg (by positivity) (Polymer.kernel_nonneg _ _))]
    calc
      _ ≤ (N : ℝ) / 4 * (1 / ((r N : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (Smoothing.srwKernel_even_le_inv_succ _ _) (by positivity)
      _ ≤ 1 / u := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity : 0 < (r N : ℝ) + 1) hu]
        nlinarith
  have hp (p : Plane × Plane) : Tendsto (fun N => F N p) atTop
      (𝓝 (f p.1 * g p.2 * heatKernel (2 * u) (p.2 - p.1))) := by
    apply Tendsto.const_mul
    apply SHF.Moments.tendsto_scaled_srwKernel (by positivity : 0 < 2 * u)
    · simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc] using hr.const_mul 2
    · simp_rw [SHF.Moments.latticeRepresentative_sub]
      exact (tendsto_cellSample p.2).sub (tendsto_cellSample p.1)
    · exact Eventually.of_forall fun N =>
        SHF.Moments.latticePoint_gap_phase N (2 * r N) ⟨r N, by omega⟩ p.1 p.2
  apply tendsto_integral_filter_of_dominated_convergence
    (bound := fun p : Plane × Plane => |f p.1 * g p.2| * (1 / u))
  · exact Eventually.of_forall fun N => hfg.aestronglyMeasurable.mul (hK N).aestronglyMeasurable
  · filter_upwards [hbound] with N hN
    exact Eventually.of_forall fun p => by
      change ‖F N p‖ ≤ _
      dsimp only [F]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hN p) (abs_nonneg _)
  · exact hfg.abs.mul_const _
  · exact Eventually.of_forall hp

end Critical2DKPZ.Extensions.GffTangent
