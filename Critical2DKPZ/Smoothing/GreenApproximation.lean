/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.Basic
public import Critical2DKPZ.Analysis.Lattice.Basic
public import Critical2DKPZ.Analysis.Lattice.Sampling
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.RandomWalk.Estimates
public import Critical2DKPZ.MomentBounds.CSZ25GreenCalculus
public import Critical2DKPZ.Smoothing.EvenExtension
public import Critical2DKPZ.Polymer.Profiles
import Mathlib.MeasureTheory.Integral.Prod
import Critical2DKPZ.Collision.SpatialGaussian
import Critical2DKPZ.SHF.Moments.WalkScaling
import Critical2DKPZ.SHF.Moments.EntranceRiemann
import Critical2DKPZ.Analysis.Heat.Semigroup

/-! # Lattice Green approximation by continuum heat energy -/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open Set
open scoped ENNReal Topology Uniformity

namespace Critical2DKPZ.Smoothing

open Critical2DKPZ.Polymer

/-- The lattice-sampled even-time heat kernel has exactly one cell-volume of mass.
This is the low-time mass estimate used when proving the Green-energy limit. -/
theorem lintegral_srwKernel_latticePoint_eq (N n : ℕ) (hN : 0 < N) (hn : Even n)
    (z : Site) (hz : Even (z 0 + z 1)) :
    ∫⁻ y : Plane, ENNReal.ofReal (srwKernel n (latticePoint N y - z)) =
      ENNReal.ofReal (4 / (N : ℝ)) := by
  classical
  let E := Polymer.endpoints z n
  let F : Plane → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (srwKernel n (latticePoint N y - z))
  have hcover : (⋃ w : Site, cell N w) = (Set.univ : Set Plane) := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨latticePoint N y, mem_cell_latticePoint N y⟩
  have hcell (w : Site) :
      (∫⁻ y in cell N w, F y) =
        ENNReal.ofReal (srwKernel n (w - z)) * volume (cell N w) := by
    have hEq : (fun y : Plane => F y) =ᵐ[volume.restrict (cell N w)]
        fun _ => ENNReal.ofReal (srwKernel n (w - z)) := by
      filter_upwards [ae_restrict_mem (measurableSet_cell N w)] with y hy
      simp only [F, mem_cell_iff] at hy ⊢
      rw [hy]
    rw [lintegral_congr_ae hEq, lintegral_const, Measure.restrict_apply_univ]
  have hcellvol (w : Site) :
      volume (cell N w) = if w ∈ evenLattice then ENNReal.ofReal (4 / (N : ℝ)) else 0 := by
    by_cases hw : w ∈ evenLattice
    · simp [hw, volume_cell hN hw]
    · simp [hw, cell_eq_empty_of_not_even hw]
  have hkernelzero {w : Site} (hw : w ∉ evenLattice) :
      srwKernel n (w - z) = 0 := by
    apply Polymer.srwKernel_eq_zero_of_not_mem n z w
    intro hwmem
    exact hw (reachable_even_of_even hz hn hwmem)
  have hterm (w : Site) :
      (∫⁻ y in cell N w, F y) =
        ENNReal.ofReal (4 / (N : ℝ)) *
        ENNReal.ofReal (srwKernel n (w - z)) := by
    rw [hcell w, hcellvol w]
    by_cases hw : w ∈ evenLattice
    · simpa [hw] using
        (mul_comm (ENNReal.ofReal (srwKernel n (w - z)))
          (ENNReal.ofReal (4 / (N : ℝ))))
    · simp [hw, hkernelzero hw]
  have hlin :
      (∫⁻ y : Plane, F y) = ∑' w : Site, ∫⁻ y in cell N w, F y := by
    calc
      (∫⁻ y : Plane, F y) = ∫⁻ y in ⋃ w : Site, cell N w, F y := by
        rw [hcover]
        simp
      _ = ∑' w : Site, ∫⁻ y in cell N w, F y :=
        lintegral_iUnion (fun w => measurableSet_cell N w) (pairwise_disjoint_cell N) F
  have htsum :
      (∑' w : Site, ENNReal.ofReal
          ((4 / (N : ℝ)) * srwKernel n (w - z))) =
        ENNReal.ofReal (4 / (N : ℝ)) := by
    calc
      _ = ∑ w ∈ E, ENNReal.ofReal
            ((4 / (N : ℝ)) * srwKernel n (w - z)) := by
        apply tsum_eq_sum
        intro w hw
        have hzero : srwKernel n (w - z) = 0 :=
          Polymer.srwKernel_eq_zero_of_not_mem n z w (by simpa [E] using hw)
        simp [hzero]
      _ = ENNReal.ofReal
            (∑ w ∈ E, (4 / (N : ℝ)) * srwKernel n (w - z)) := by
        rw [ENNReal.ofReal_sum_of_nonneg]
        intro w hw
        exact mul_nonneg (by positivity) (kernel_nonneg n (w - z))
      _ = ENNReal.ofReal (4 / (N : ℝ)) := by
        rw [← Finset.mul_sum, sum_srwKernel_endpoints]
        simp
  rw [hlin]
  calc
    (∑' w : Site, ∫⁻ y in cell N w, F y) =
        ∑' w : Site, ENNReal.ofReal
          ((4 / (N : ℝ)) * srwKernel n (w - z)) := by
      apply tsum_congr
      intro w
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (4 / (N : ℝ)))]
      exact hterm w
    _ = ENNReal.ofReal (4 / (N : ℝ)) := htsum

/-- Integrability companion for the sampled even-time kernel mass identity. -/
theorem integrable_srwKernel_latticePoint (N n : ℕ) (hN : 0 < N) (hn : Even n)
    (z : Site) (hz : Even (z 0 + z 1)) :
    Integrable (fun y : Plane => srwKernel n (latticePoint N y - z)) := by
  let F : Plane → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (srwKernel n (latticePoint N y - z))
  have hFmeas : Measurable F := by
    apply (measurable_of_countable fun w : Site =>
      ENNReal.ofReal (srwKernel n (w - z))).comp
    exact measurable_latticePoint N
  have hfinite : (∫⁻ y : Plane, F y) ≠ ∞ := by
    have hmass := lintegral_srwKernel_latticePoint_eq N n hN hn z hz
    simpa only [F] using hmass ▸ ENNReal.ofReal_ne_top
  have hFint := integrable_toReal_of_lintegral_ne_top hFmeas.aemeasurable hfinite
  have hEq : (fun y : Plane => (F y).toReal) =
      fun y => srwKernel n (latticePoint N y - z) := by
    funext y
    dsimp [F]
    rw [ENNReal.toReal_ofReal (kernel_nonneg n (latticePoint N y - z))]
  rw [← hEq]
  exact hFint

/-- The Bochner integral of a sampled even-time kernel is its exact cell mass. -/
theorem integral_srwKernel_latticePoint_eq (N n : ℕ) (hN : 0 < N) (hn : Even n)
    (z : Site) (hz : Even (z 0 + z 1)) :
    ∫ y : Plane, srwKernel n (latticePoint N y - z) = 4 / (N : ℝ) := by
  let F : Plane → ℝ≥0∞ := fun y =>
    ENNReal.ofReal (srwKernel n (latticePoint N y - z))
  have hFmeas : Measurable F := by
    apply (measurable_of_countable fun w : Site =>
      ENNReal.ofReal (srwKernel n (w - z))).comp
    exact measurable_latticePoint N
  have hFfinite : ∀ᵐ y : Plane ∂volume, F y < ∞ :=
    Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top
  have hTo := integral_toReal hFmeas.aemeasurable hFfinite
  have hEq : (fun y : Plane => (F y).toReal) =
      fun y => srwKernel n (latticePoint N y - z) := by
    funext y
    dsimp [F]
    rw [ENNReal.toReal_ofReal (kernel_nonneg n (latticePoint N y - z))]
  rw [hEq, show (∫⁻ y : Plane, F y) =
      ENNReal.ofReal (4 / (N : ℝ)) by
        simpa only [F] using lintegral_srwKernel_latticePoint_eq N n hN hn z hz] at hTo
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ (4 : ℝ) / N)] at hTo
  simpa using hTo

/-- Integrating the local-CLT error against an integrable test pair preserves the
uniform pointwise error, with the product `L¹` mass as its factor. The bound
includes integrability of its integrand. -/
theorem integral_srwKernel_localCLT_error_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N n : ℕ) (hn : 1 ≤ n) (heven : Even n)
      (φ : Plane → ℝ) (hint : Integrable φ),
      Integrable (fun p : Plane × Plane => |φ p.1| * |φ p.2| *
        |srwKernel n (latticePoint N p.2 - latticePoint N p.1) -
          2 * heatKernel ((n : ℝ) / 2)
            (siteToPlane (latticePoint N p.2 - latticePoint N p.1))|) (volume.prod volume) ∧
      (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        |srwKernel n (latticePoint N p.2 - latticePoint N p.1) -
          2 * heatKernel ((n : ℝ) / 2)
            (siteToPlane (latticePoint N p.2 - latticePoint N p.1))|) ≤
        C / (n : ℝ) ^ 2 * (∫ x : Plane, |φ x|) ^ 2 := by
  obtain ⟨C, hC, hclt⟩ := Critical2DKPZ.srwKernel_localCLT
  refine ⟨C, hC, ?_⟩
  intro N n hn heven φ hint
  let z : Plane × Plane → Site := fun p => latticePoint N p.2 - latticePoint N p.1
  let F : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2|
  let B : Plane × Plane → ℝ := fun p =>
    |srwKernel n (z p) - 2 * heatKernel ((n : ℝ) / 2) (siteToPlane (z p))|
  have hφnorm : Integrable (fun x : Plane => |φ x|) := by
    simpa only [Real.norm_eq_abs] using hint.norm
  have hFint : Integrable F (volume.prod volume) := by
    simpa [F] using hφnorm.mul_prod hφnorm
  have hFnonneg (p : Plane × Plane) : 0 ≤ F p :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hzmeas : Measurable z := by
    dsimp [z]
    exact (measurable_latticePoint N).comp measurable_snd |>.sub
      ((measurable_latticePoint N).comp measurable_fst)
  have hkernelmeas : Measurable (fun p : Plane × Plane => srwKernel n (z p)) :=
    (measurable_of_countable fun w : Site => srwKernel n w).comp hzmeas
  have hsiteToPlanemeas : Measurable (fun p : Plane × Plane => siteToPlane (z p)) :=
    (measurable_of_countable siteToPlane).comp hzmeas
  have hheatmeas : Measurable (fun p : Plane × Plane =>
      heatKernel ((n : ℝ) / 2) (siteToPlane (z p))) :=
    (measurable_heatKernel ((n : ℝ) / 2)).comp hsiteToPlanemeas
  have hBmeas : Measurable B := by
    dsimp [B]
    exact continuous_abs.measurable.comp (hkernelmeas.sub (measurable_const.mul hheatmeas))
  have hparity (p : Plane × Plane) : Even (z p 0 + z p 1 + n) := by
    have hleft := latticePoint_mem_evenLattice N p.2
    have hright := latticePoint_mem_evenLattice N p.1
    change Even (latticePoint N p.2 0 + latticePoint N p.2 1) at hleft
    change Even (latticePoint N p.1 0 + latticePoint N p.1 1) at hright
    have hdiff : Even (latticePoint N p.2 0 + latticePoint N p.2 1 -
        (latticePoint N p.1 0 + latticePoint N p.1 1)) :=
      Int.even_sub.mpr ⟨fun _ => hright, fun _ => hleft⟩
    have hz : Even (z p 0 + z p 1) := by
      dsimp [z]
      convert hdiff using 1
      all_goals ring
    have hnZ : Even (n : ℤ) := by exact_mod_cast heven
    exact Int.even_add.mpr ⟨fun _ => hnZ, fun _ => hz⟩
  have hBbound (p : Plane × Plane) : B p ≤ C / (n : ℝ) ^ 2 := by
    dsimp [B]
    exact hclt n hn (z p) (hparity p)
  have hBint' : Integrable (fun p : Plane × Plane => B p * F p) (volume.prod volume) := by
    apply hFint.bdd_mul (c := C / (n : ℝ) ^ 2) hBmeas.aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)]
    exact hBbound p
  have hBint : Integrable (fun p : Plane × Plane => F p * B p) (volume.prod volume) := by
    simpa only [mul_comm] using hBint'
  have hcmpint : Integrable (fun p : Plane × Plane => F p * (C / (n : ℝ) ^ 2))
      (volume.prod volume) := hFint.mul_const _
  have hpoint (p : Plane × Plane) :
      F p * B p ≤ F p * (C / (n : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left (hBbound p) (hFnonneg p)
  have hAint : ∫ p : Plane × Plane, F p =
      (∫ x : Plane, |φ x|) ^ 2 := by
    rw [Measure.volume_eq_prod Plane Plane]
    simpa only [F, pow_two] using
      (integral_prod_mul (fun x : Plane => |φ x|) (fun x : Plane => |φ x|))
  refine ⟨?_, ?_⟩
  · simpa only [F, B, z] using hBint
  ·
    calc
      (∫ p : Plane × Plane, F p * B p) ≤
          ∫ p : Plane × Plane, F p * (C / (n : ℝ) ^ 2) :=
        integral_mono hBint hcmpint hpoint
      _ = (∫ p : Plane × Plane, F p) * (C / (n : ℝ) ^ 2) := integral_mul_const _ _
      _ = C / (n : ℝ) ^ 2 * (∫ x : Plane, |φ x|) ^ 2 := by rw [hAint]; ring

/-- The sampled truncated Green kernel is integrable and has total mass `4 * L / N`. -/
theorem integral_truncatedGreen_latticePoint_eq (N L : ℕ) (hN : 0 < N)
    (z : Site) (hz : Even (z 0 + z 1)) :
    Integrable (fun y : Plane =>
      MomentBounds.truncatedGreen L (latticePoint N y - z)) ∧
    (∫ y : Plane, MomentBounds.truncatedGreen L (latticePoint N y - z)) =
      4 * (L : ℝ) / N := by
  let I := Finset.Icc 1 L
  have hterms (r : ℕ) (hr : r ∈ I) :
      Integrable (fun y : Plane => srwKernel (2 * r) (latticePoint N y - z)) := by
    apply integrable_srwKernel_latticePoint N (2 * r) hN ?_ z hz
    exact ⟨r, by omega⟩
  have hsum : (fun y : Plane => MomentBounds.truncatedGreen L
      (latticePoint N y - z)) =
      fun y => ∑ r ∈ I, srwKernel (2 * r) (latticePoint N y - z) := by
    funext y
    simp [I, MomentBounds.truncatedGreen]
  refine ⟨?_, ?_⟩
  · rw [hsum]
    exact integrable_finsetSum I hterms
  · rw [hsum, integral_finsetSum I hterms]
    have hconst : ∀ r ∈ I,
        (∫ y : Plane, srwKernel (2 * r) (latticePoint N y - z)) = 4 / (N : ℝ) := by
      intro r hr
      exact integral_srwKernel_latticePoint_eq N (2 * r) hN ⟨r, by omega⟩ z hz
    rw [Finset.sum_congr rfl hconst]
    simp [I]
    ring

/-- Integrability of the two-point sampled truncated Green kernel for an arbitrary cutoff. -/
theorem integrable_truncatedGreen_latticePoint_of (L N : ℕ)
    (φ : Plane → ℝ) (hφ : Measurable φ) (hint : Integrable φ) :
    Integrable (fun p : Plane × Plane =>
      |φ p.1| * |φ p.2| *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1))
      (volume.prod volume) := by
  classical
  let F : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2|
  have hFInt : Integrable F (volume.prod volume) := by
    have hnorm : Integrable (fun x : Plane => |φ x|) := by
      simpa only [Real.norm_eq_abs] using hint.norm
    simpa [F] using hnorm.mul_prod hnorm
  have hF0 (p : Plane × Plane) : 0 ≤ F p :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hkernel : Measurable (fun p : Plane × Plane =>
      MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) := by
    apply (measurable_of_countable fun z : Site => MomentBounds.truncatedGreen L z).comp
    exact (measurable_latticePoint N).comp measurable_snd |>.sub
      ((measurable_latticePoint N).comp measurable_fst)
  have hmeas : Measurable (fun p : Plane × Plane => F p *
      MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) := by
    exact (hφ.abs.comp measurable_fst).mul (hφ.abs.comp measurable_snd) |>.mul hkernel
  have hdom : ∀ p : Plane × Plane,
      ‖F p * MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)‖ ≤
        ‖F p‖ * (L : ℝ) := by
    intro p
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hF0 p)
      (MomentBounds.truncatedGreen_nonneg L _))]
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 p)]
    exact mul_le_mul_of_nonneg_left (MomentBounds.truncatedGreen_le L _)
      (hF0 p)
  have hmajor : Integrable (fun p : Plane × Plane => ‖F p‖ * (L : ℝ))
      (volume.prod volume) := by
    exact hFInt.norm.mul_const (L : ℝ)
  have h := hmajor.mono' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall hdom)
  simpa [F] using h

/-- The sampled truncated Green quadratic form is integrable and bounded by its row mass times the test bounds. -/
theorem integral_truncatedGreen_latticePoint_pair_le (N L : ℕ) (hN : 0 < N)
    (φ : Plane → ℝ) (hφ : Measurable φ) (hint : Integrable φ)
    (B : ℝ) (hφB : ∀ x, |φ x| ≤ B) :
    Integrable (fun p : Plane × Plane =>
      |φ p.1| * |φ p.2| *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1))
      (volume.prod volume) ∧
    (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
      MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) ≤
      (4 * (L : ℝ) / N) * B * (∫ x : Plane, |φ x|) := by
  classical
  let F : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2|
  let K : Plane × Plane → ℝ := fun p =>
    MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)
  have hFInt : Integrable F (volume.prod volume) := by
    have hnorm : Integrable (fun x : Plane => |φ x|) := by
      simpa only [Real.norm_eq_abs] using hint.norm
    simpa [F] using hnorm.mul_prod hnorm
  have hFnonneg (p : Plane × Plane) : 0 ≤ F p :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hKmeas : Measurable K := by
    apply (measurable_of_countable fun z : Site => MomentBounds.truncatedGreen L z).comp
    exact (measurable_latticePoint N).comp measurable_snd |>.sub
      ((measurable_latticePoint N).comp measurable_fst)
  have hKnonneg (p : Plane × Plane) : 0 ≤ K p :=
    MomentBounds.truncatedGreen_nonneg L _
  have hKF : Integrable (fun p : Plane × Plane => K p * F p) (volume.prod volume) := by
    apply hFInt.bdd_mul (c := L) hKmeas.aestronglyMeasurable
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_of_nonneg (hKnonneg p)]
    exact MomentBounds.truncatedGreen_le L _
  have hFK : Integrable (fun p : Plane × Plane => F p * K p) (volume.prod volume) := by
    simpa only [mul_comm] using hKF
  have houterInt : Integrable (fun x : Plane =>
      ∫ y : Plane, F (x, y) * K (x, y)) := hFK.integral_prod_left
  have hφnorm : Integrable (fun x : Plane => |φ x|) := by
    simpa only [Real.norm_eq_abs] using hint.norm
  have houterMajor : Integrable (fun x : Plane =>
      |φ x| * (B * (4 * (L : ℝ) / N))) := hφnorm.mul_const _
  have hrow (x : Plane) :
      ∫ y : Plane, F (x, y) * K (x, y) ≤
        |φ x| * (B * (4 * (L : ℝ) / N)) := by
    let Kx : Plane → ℝ := fun y =>
      MomentBounds.truncatedGreen L (latticePoint N y - latticePoint N x)
    have hxEven : Even (latticePoint N x 0 + latticePoint N x 1) := by
      have hxmem := latticePoint_mem_evenLattice N x
      change Even (latticePoint N x 0 + latticePoint N x 1) at hxmem
      exact hxmem
    have hrowMass := integral_truncatedGreen_latticePoint_eq N L hN
      (latticePoint N x) hxEven
    have hKxInt : Integrable Kx := by
      simpa only [Kx] using hrowMass.1
    have hKxMass : (∫ y : Plane, Kx y) = 4 * (L : ℝ) / N := by
      simpa only [Kx] using hrowMass.2
    have hKxnonneg (y : Plane) : 0 ≤ Kx y :=
      MomentBounds.truncatedGreen_nonneg L _
    have hφK' : Integrable (fun y : Plane => |φ y| * Kx y) := by
      apply hKxInt.bdd_mul (c := B) hφ.abs.aestronglyMeasurable
      filter_upwards [] with y
      rw [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg (φ y))]
      exact hφB y
    have hφK : Integrable (fun y : Plane => |φ y| * Kx y) := hφK'
    have hinnerInt : Integrable (fun y : Plane =>
        |φ x| * |φ y| * Kx y) := by
      simpa [mul_assoc] using hφK.const_mul (|φ x|)
    have hinnerMajor : Integrable (fun y : Plane =>
        (|φ x| * B) * Kx y) := hKxInt.const_mul (|φ x| * B)
    have hpoint (y : Plane) :
        |φ x| * |φ y| * Kx y ≤ (|φ x| * B) * Kx y := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hφB y) (abs_nonneg _)) (hKxnonneg y)
    have hmono := integral_mono hinnerInt hinnerMajor hpoint
    change (∫ y : Plane, |φ x| * |φ y| * Kx y) ≤ _ at hmono
    calc
      ∫ y : Plane, F (x, y) * K (x, y) ≤
          ∫ y : Plane, (|φ x| * B) * Kx y := by
        simpa [F, K, Kx, mul_assoc] using hmono
      _ = (|φ x| * B) * (∫ y : Plane, Kx y) := integral_const_mul _ _
      _ = |φ x| * (B * (4 * (L : ℝ) / N)) := by rw [hKxMass]; ring
  have hpairInt : Integrable (fun p : Plane × Plane => F p * K p)
      (volume.prod volume) := hFK
  have hpairEq : (∫ p : Plane × Plane, F p * K p) =
      ∫ x : Plane, ∫ y : Plane, F (x, y) * K (x, y) := by
    rw [Measure.volume_eq_prod Plane Plane]
    exact integral_prod _ hpairInt
  refine ⟨?_, ?_⟩
  · simpa only [F, K] using hpairInt
  · rw [show (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) =
      ∫ p : Plane × Plane, F p * K p by rfl, hpairEq]
    calc
      (∫ x : Plane, ∫ y : Plane, F (x, y) * K (x, y)) ≤
          ∫ x : Plane, |φ x| * (B * (4 * (L : ℝ) / N)) :=
        integral_mono houterInt houterMajor hrow
      _ = (∫ x : Plane, |φ x|) * (B * (4 * (L : ℝ) / N)) :=
        integral_mul_const _ _
      _ = (4 * (L : ℝ) / N) * B * (∫ x : Plane, |φ x|) := by ring

/-- The heat profile of `|φ|` with lattice-sampled cell positions at time `2u`. -/
def sampledHeatProfile (N : ℕ) (φ : Plane → ℝ) (u : ℝ) : ℝ :=
  ∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
    heatKernel (2 * u) (cellSample N p.2 - cellSample N p.1)

/-- The continuum heat profile of `|φ|` at time `2u`. -/
def continuumHeatProfile (φ : Plane → ℝ) (u : ℝ) : ℝ :=
  ∫ p : Plane × Plane, |φ p.1| * |φ p.2| * heatKernel (2 * u) (p.2 - p.1)

/-- For a bounded integrable test, the absolute test pair is integrable against the positive-time heat kernel, and its integral is bounded by the sup norm times the `L¹` norm. -/
theorem continuumHeatProfile_integrable_bound (φ : Plane → ℝ)
    (hφ : Measurable φ) (hint : Integrable φ) (B : ℝ)
    (hB : ∀ x, |φ x| ≤ B) {u : ℝ} (hu : 0 < u) :
    Integrable (fun p : Plane × Plane => |φ p.1| * |φ p.2| *
      heatKernel (2 * u) (p.2 - p.1)) (volume.prod volume) ∧
    0 ≤ continuumHeatProfile φ u ∧
    continuumHeatProfile φ u ≤ B * (∫ x : Plane, |φ x|) := by
  classical
  have hB0 : 0 ≤ B := by
    have h := hB (0 : Plane)
    have habs : 0 ≤ |φ (0 : Plane)| := abs_nonneg _
    linarith
  have hnormInt : Integrable (fun x : Plane => |φ x|) := by
    simpa only [Real.norm_eq_abs] using hint.norm
  let F : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2|
  have hFmeas : Measurable F :=
    (hφ.abs.comp measurable_fst).mul (hφ.abs.comp measurable_snd)
  have hFint : Integrable F (volume.prod volume) := by
    simpa [F] using hnormInt.mul_prod hnormInt
  have hFnonneg (p : Plane × Plane) : 0 ≤ F p :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have ht : 0 < 2 * u := mul_pos (by norm_num) hu
  let K : ℝ := (2 * Real.pi * (2 * u))⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have hKernelMeas : Measurable (fun p : Plane × Plane =>
      heatKernel (2 * u) (p.2 - p.1)) :=
    (measurable_heatKernel (2 * u)).comp (measurable_snd.sub measurable_fst)
  let H : Plane × Plane → ℝ := fun p => F p * heatKernel (2 * u) (p.2 - p.1)
  have hHmeas : Measurable H := hFmeas.mul hKernelMeas
  have hmajor : Integrable (fun p : Plane × Plane => F p * K)
      (volume.prod volume) := hFint.mul_const K
  have hHint : Integrable H (volume.prod volume) := by
    apply hmajor.mono' hHmeas.aestronglyMeasurable
    filter_upwards [] with p
    dsimp [H]
    have hkernel : heatKernel (2 * u) (p.2 - p.1) ≤ K :=
      heatKernel_le_at_zero ht.le _
    have h := mul_le_mul_of_nonneg_left hkernel (hFnonneg p)
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFnonneg p),
      abs_of_nonneg (heatKernel_nonneg ht.le (p.2 - p.1)),
      abs_of_nonneg (mul_nonneg (hFnonneg p) hK.le)] using h
  have hkernelBoundY (x y : Plane) :
      0 ≤ heatKernel (2 * u) (y - x) ∧ heatKernel (2 * u) (y - x) ≤ K := by
    exact ⟨heatKernel_nonneg ht.le _, heatKernel_le_at_zero ht.le _⟩
  have hinnerInt (x : Plane) :
      Integrable (fun y : Plane => |φ y| * heatKernel (2 * u) (y - x)) := by
    let G : Plane → ℝ := fun y => |φ y| * heatKernel (2 * u) (y - x)
    have hGmeas : Measurable G := by
      apply hφ.abs.mul
      exact (measurable_heatKernel (2 * u)).comp (measurable_id.sub measurable_const)
    have hGmajor : Integrable (fun y : Plane => |φ y| * K) := hnormInt.mul_const K
    apply hGmajor.mono' hGmeas.aestronglyMeasurable
    filter_upwards [] with y
    dsimp [G]
    have h := mul_le_mul_of_nonneg_left (hkernelBoundY x y).2 (abs_nonneg (φ y))
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abs_nonneg _),
      abs_of_nonneg (hkernelBoundY x y).1,
      abs_of_nonneg (mul_nonneg (abs_nonneg _) hK.le)] using h
  have hrow (x : Plane) :
      (∫ y : Plane, |φ y| * heatKernel (2 * u) (y - x)) ≤ B := by
    have hBkernelInt : Integrable (fun y : Plane => B * heatKernel (2 * u) (y - x)) := by
      have hshift : Integrable (fun y : Plane => heatKernel (2 * u) (y - x)) := by
        let e : Plane ≃ᵐ Plane := MeasurableEquiv.subLeft x
        have heq : (fun y : Plane => heatKernel (2 * u) (y - x)) =
            fun y => heatKernel (2 * u) (x - y) := by
          funext y
          have hy : y - x = -(x - y) := by abel
          rw [hy, Critical2DKPZ.heatKernel_neg]
        rw [heq]
        change Integrable (fun y : Plane => heatKernel (2 * u) (e y))
        exact ((volume.measurePreserving_sub_left x).integrable_comp_emb
          (MeasurableEquiv.subLeft x).measurableEmbedding).mpr (integrable_heatKernel ht)
      exact hshift.const_mul B
    have hpoint (y : Plane) :
        |φ y| * heatKernel (2 * u) (y - x) ≤
          B * heatKernel (2 * u) (y - x) :=
      mul_le_mul_of_nonneg_right (hB y) (hkernelBoundY x y).1
    calc
      (∫ y : Plane, |φ y| * heatKernel (2 * u) (y - x)) ≤
          ∫ y : Plane, B * heatKernel (2 * u) (y - x) :=
        integral_mono (hinnerInt x) hBkernelInt hpoint
      _ = B := by
        rw [integral_const_mul,
          Critical2DKPZ.integral_heatKernel_sub ht x]
        ring
  have houterInt : Integrable (fun x : Plane => ∫ y : Plane, H (x, y)) :=
    hHint.integral_prod_left
  have houterPoint (x : Plane) :
      (∫ y : Plane, H (x, y)) ≤ |φ x| * B := by
    have heq : (fun y : Plane => H (x, y)) = fun y =>
        |φ x| * (|φ y| * heatKernel (2 * u) (y - x)) := by
      funext y
      simp [H, F, mul_assoc]
    rw [heq, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hrow x) (abs_nonneg _)
  have houterMajor : Integrable (fun x : Plane => |φ x| * B) :=
    hnormInt.mul_const B
  have hpairEq : (∫ p : Plane × Plane, H p) =
      ∫ x : Plane, ∫ y : Plane, H (x, y) := by
    rw [Measure.volume_eq_prod Plane Plane]
    exact integral_prod H hHint
  have hbound : (∫ x : Plane, ∫ y : Plane, H (x, y)) ≤
      B * (∫ x : Plane, |φ x|) := by
    calc
      (∫ x : Plane, ∫ y : Plane, H (x, y)) ≤
          ∫ x : Plane, |φ x| * B :=
        integral_mono houterInt houterMajor
          houterPoint
      _ = B * (∫ x : Plane, |φ x|) := by rw [integral_mul_const]; ring
  refine ⟨?_, ?_, ?_⟩
  · simpa [H, F] using hHint
  · unfold continuumHeatProfile
    apply integral_nonneg
    intro p
    exact mul_nonneg (hFnonneg p) (heatKernel_nonneg ht.le _)
  · unfold continuumHeatProfile
    rw [show (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        heatKernel (2 * u) (p.2 - p.1)) = ∫ p, H p by rfl, hpairEq]
    exact hbound

/-- The heat energy is the time integral of the continuum heat profile. -/
theorem heatEnergy_eq_profile_timeIntegral (φ : Plane → ℝ)
    (hφ : Measurable φ) (hint : Integrable φ) (B : ℝ)
    (hB : ∀ x, |φ x| ≤ B) {s : ℝ} (hs : 0 < s) :
    Integrable (fun u : ℝ => continuumHeatProfile φ u)
        (volume.restrict (Set.Icc 0 s)) ∧
      heatEnergy s φ = 4 * ∫ u in (0 : ℝ)..s, continuumHeatProfile φ u := by
  classical
  let μ : Measure ℝ := volume.restrict (Set.Icc 0 s)
  let ν : Measure (Plane × Plane) := volume.prod volume
  let g : ℝ × (Plane × Plane) → ℝ := fun z =>
    |φ z.2.1| * |φ z.2.2| * heatKernel (2 * z.1) (z.2.2 - z.2.1)
  have hgmeas : Measurable g := by
    dsimp [g, Critical2DKPZ.heatKernel]
    fun_prop
  have hgaes : AEStronglyMeasurable g (μ.prod ν) := hgmeas.aestronglyMeasurable
  have hsection : ∀ᵐ u ∂μ, Integrable (fun p : Plane × Plane => g (u, p)) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hu0 : 0 ≤ u := hu.1
    by_cases hzero : u = 0
    · simp [g, hzero, Critical2DKPZ.heatKernel_zero_time]
    · have hu' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hzero)
      simpa [g, continuumHeatProfile] using
        (continuumHeatProfile_integrable_bound φ hφ hint B hB hu').1
  have htimeMajorant : Integrable (fun u : ℝ =>
      ∫ p : Plane × Plane, ‖g (u, p)‖ ∂ν) μ := by
    have hB0 : 0 ≤ B := by
      have h := hB (0 : Plane)
      linarith [abs_nonneg (φ (0 : Plane))]
    have hstrong : AEStronglyMeasurable
        (fun u : ℝ => ∫ p : Plane × Plane, ‖g (u, p)‖ ∂ν) μ :=
      hgaes.norm.integral_prod_right'
    have hconst : Integrable (fun _ : ℝ => B * (∫ x : Plane, |φ x|)) μ :=
      integrable_const _
    apply hconst.mono' hstrong
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hu0 : 0 ≤ u := hu.1
    by_cases hzero : u = 0
    · simp [g, hzero, Critical2DKPZ.heatKernel_zero_time]
      positivity
    · have hu' : 0 < u := lt_of_le_of_ne hu0 (Ne.symm hzero)
      have hprofileNN := (continuumHeatProfile_integrable_bound φ hφ hint B hB hu').2.1
      have hbound := (continuumHeatProfile_integrable_bound φ hφ hint B hB hu').2.2
      have hnorm : (∫ p : Plane × Plane, ‖g (u, p)‖ ∂ν) =
          continuumHeatProfile φ u := by
        change (∫ p : Plane × Plane, ‖g (u, p)‖ ∂ν) =
          ∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
            heatKernel (2 * u) (p.2 - p.1) ∂volume
        dsimp [ν]
        rw [← Measure.volume_eq_prod Plane Plane]
        apply integral_congr_ae
        filter_upwards [] with p
        change |(|φ p.1| * |φ p.2| * heatKernel (2 * u) (p.2 - p.1))| = _
        exact abs_of_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          (heatKernel_nonneg (by positivity : 0 ≤ 2 * u) _))
      rw [hnorm, Real.norm_eq_abs, abs_of_nonneg hprofileNN]
      exact hbound
  have hgInt : Integrable g (μ.prod ν) :=
    (integrable_prod_iff hgaes).2 ⟨hsection, htimeMajorant⟩
  have hgSwap : Integrable (fun z : (Plane × Plane) × ℝ => g z.swap)
      (ν.prod μ) := hgInt.swap
  have hprofileInt : Integrable (fun u : ℝ => continuumHeatProfile φ u) μ := by
    have h := hgInt.integral_prod_left
    change Integrable (fun u : ℝ =>
      ∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        heatKernel (2 * u) (p.2 - p.1) ∂(volume.prod volume)) μ
    simpa [g, ν] using h
  have hswapIntegral :
      (∫ u : ℝ, ∫ p : Plane × Plane, g (u, p) ∂ν ∂μ) =
        ∫ p : Plane × Plane, ∫ u : ℝ, g (u, p) ∂μ ∂ν := by
    calc
      (∫ u : ℝ, ∫ p : Plane × Plane, g (u, p) ∂ν ∂μ) =
          ∫ z : ℝ × (Plane × Plane), g z ∂(μ.prod ν) :=
        (integral_prod g hgInt).symm
      _ = ∫ z : (Plane × Plane) × ℝ, g z.swap ∂(ν.prod μ) :=
        (integral_prod_swap g).symm
      _ = ∫ p : Plane × Plane, ∫ u : ℝ, g (u, p) ∂μ ∂ν :=
        integral_prod (fun z : (Plane × Plane) × ℝ => g z.swap) hgSwap
  have htimeKernel (p : Plane × Plane) :
      (∫ u : ℝ, g (u, p) ∂μ) =
        |φ p.1| * |φ p.2| *
          (∫ u in (0 : ℝ)..s, heatKernel (2 * u) (p.1 - p.2)) := by
    change (∫ u in Set.Icc (0 : ℝ) s,
        |φ p.1| * |φ p.2| * heatKernel (2 * u) (p.2 - p.1)) = _
    rw [integral_const_mul]
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (le_of_lt hs)]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    have hneg : p.2 - p.1 = -(p.1 - p.2) := by abel
    change heatKernel (2 * u) (p.2 - p.1) = heatKernel (2 * u) (p.1 - p.2)
    rw [hneg, Critical2DKPZ.heatKernel_neg]
  have hE : heatEnergy s φ =
      4 * (∫ p : Plane × Plane, ∫ u : ℝ, g (u, p) ∂μ ∂ν) := by
    unfold heatEnergy
    have hfactor : (fun p : Plane × Plane => |φ p.1| * |φ p.2| *
        (4 * ∫ r in (0 : ℝ)..s, heatKernel (2 * r) (p.1 - p.2))) =
        fun p => 4 * (|φ p.1| * |φ p.2| *
          ∫ r in (0 : ℝ)..s, heatKernel (2 * r) (p.1 - p.2)) := by
      funext p
      ring
    rw [hfactor, integral_const_mul]
    congr 1
    apply integral_congr_ae
    filter_upwards [] with p
    rw [htimeKernel p]
  refine ⟨hprofileInt, ?_⟩
  rw [hE, ← hswapIntegral]
  have hinnerProfile (u : ℝ) :
      (∫ p : Plane × Plane, g (u, p) ∂ν) = continuumHeatProfile φ u := by
    change (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
      heatKernel (2 * u) (p.2 - p.1) ∂ν) =
      ∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        heatKernel (2 * u) (p.2 - p.1) ∂volume
    dsimp [ν]
    rw [← Measure.volume_eq_prod Plane Plane]
  have htimeProfile : (∫ u : ℝ, continuumHeatProfile φ u ∂μ) =
      ∫ u in (0 : ℝ)..s, continuumHeatProfile φ u := by
    change (∫ u in Set.Icc (0 : ℝ) s, continuumHeatProfile φ u) = _
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (le_of_lt hs)]
  have hiter : (∫ u : ℝ, ∫ p : Plane × Plane, g (u, p) ∂ν ∂μ) =
      ∫ u : ℝ, continuumHeatProfile φ u ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with u
    exact hinnerProfile u
  rw [hiter, htimeProfile]

private theorem tendsto_sampledHeatProfile_along (φ : Plane → ℝ)
    (hφ : Measurable φ) (hint : Integrable φ) {u : ℝ} (hu : 0 < u)
    (Nseq : ℕ → ℕ) (hNseq : Tendsto Nseq atTop atTop)
    (useq : ℕ → ℝ) (huseq : Tendsto useq atTop (𝓝 u)) :
    Tendsto (fun k => sampledHeatProfile (Nseq k) φ (useq k)) atTop
      (𝓝 (continuumHeatProfile φ u)) := by
  classical
  let F : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2|
  have hFmeas : Measurable F :=
    (hφ.abs.comp measurable_fst).mul (hφ.abs.comp measurable_snd)
  have hnormInt : Integrable (fun x : Plane => |φ x|) := by
    simpa only [Real.norm_eq_abs] using hint.norm
  have hFint : Integrable F (volume.prod volume) := by
    simpa [F] using hnormInt.mul_prod hnormInt
  have hFnonneg (p : Plane × Plane) : 0 ≤ F p :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  let K : ℝ := (2 * Real.pi * u)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have htime : ∀ᶠ k : ℕ in atTop, u / 2 < useq k :=
    huseq.eventually (Ioi_mem_nhds (by linarith))
  let majorant : Plane × Plane → ℝ := fun p => ‖F p‖ * K
  have hmajorant : Integrable majorant (volume.prod volume) := by
    simpa [majorant] using hFint.norm.mul_const K
  apply tendsto_integral_filter_of_dominated_convergence majorant
  · exact Filter.Eventually.of_forall fun k => by
      have hd : Measurable (fun p : Plane × Plane =>
          cellSample (Nseq k) p.2 - cellSample (Nseq k) p.1) :=
        (measurable_cellSample (Nseq k)).comp measurable_snd |>.sub
          ((measurable_cellSample (Nseq k)).comp measurable_fst)
      exact (hFmeas.mul ((measurable_heatKernel (2 * useq k)).comp hd)).aestronglyMeasurable
  · filter_upwards [htime] with k hk
    apply Filter.Eventually.of_forall
    intro p
    have htpos : 0 < 2 * useq k := by linarith
    have hden₀ : 0 < 2 * Real.pi * u := by positivity
    have hden : 0 < 2 * Real.pi * (2 * useq k) := by positivity
    have hdenle : 2 * Real.pi * u ≤ 2 * Real.pi * (2 * useq k) := by
      gcongr
      linarith
    have hkernel : heatKernel (2 * useq k)
        (cellSample (Nseq k) p.2 - cellSample (Nseq k) p.1) ≤ K := by
      calc
        heatKernel (2 * useq k) _ ≤ (2 * Real.pi * (2 * useq k))⁻¹ :=
          heatKernel_le_at_zero htpos.le _
        _ ≤ K := (inv_le_inv₀ hden hden₀).2 hdenle
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFnonneg p)]
    calc
      F p * |heatKernel (2 * useq k)
          (cellSample (Nseq k) p.2 - cellSample (Nseq k) p.1)| ≤ F p * K :=
        mul_le_mul_of_nonneg_left (by
          rw [abs_of_nonneg (heatKernel_nonneg htpos.le _)]
          exact hkernel) (hFnonneg p)
      _ = majorant p := by
        simp [majorant, abs_of_nonneg (hFnonneg p)]
  · exact hmajorant
  · exact Filter.Eventually.of_forall fun p => by
      have hx : Tendsto (fun k => cellSample (Nseq k) p.1) atTop (𝓝 p.1) :=
        (tendsto_cellSample p.1).comp hNseq
      have hy : Tendsto (fun k => cellSample (Nseq k) p.2) atTop (𝓝 p.2) :=
        (tendsto_cellSample p.2).comp hNseq
      have hd : Tendsto (fun k => cellSample (Nseq k) p.2 -
          cellSample (Nseq k) p.1) atTop (𝓝 (p.2 - p.1)) := hy.sub hx
      have htime' : Tendsto (fun k => 2 * useq k) atTop (𝓝 (2 * u)) := by
        simpa using tendsto_const_nhds.mul huseq
      have hpair : Tendsto (fun k => (2 * useq k,
          cellSample (Nseq k) p.2 - cellSample (Nseq k) p.1)) atTop
          (𝓝 (2 * u, p.2 - p.1)) := htime'.prodMk_nhds hd
      have hkernelCont : ContinuousAt (fun q : ℝ × Plane => heatKernel q.1 q.2)
          (2 * u, p.2 - p.1) := by
        have hpos : IsOpen {q : ℝ × Plane | 0 < q.1} :=
          isOpen_lt continuous_const continuous_fst
        have hcont : ContinuousOn (fun q : ℝ × Plane => heatKernel q.1 q.2)
            {q | 0 < q.1} := Critical2DKPZ.DeltaBose.continuousOn_heatKernel
        have hmem : (2 * u, p.2 - p.1) ∈ {q : ℝ × Plane | 0 < q.1} := by
          simp
          linarith
        exact hcont.continuousAt (hpos.mem_nhds hmem)
      have hkernel := hkernelCont.tendsto.comp hpair
      have hFconstant : Tendsto (fun _k : ℕ => F p) atTop (𝓝 (F p)) :=
        tendsto_const_nhds
      simpa [sampledHeatProfile, continuumHeatProfile, F] using hFconstant.mul hkernel

private theorem tendsto_continuumHeatProfile_along (φ : Plane → ℝ)
    (hφ : Measurable φ) (hint : Integrable φ) {u : ℝ} (hu : 0 < u)
    (useq : ℕ → ℝ) (huseq : Tendsto useq atTop (𝓝 u)) :
    Tendsto (fun k => continuumHeatProfile φ (useq k)) atTop
      (𝓝 (continuumHeatProfile φ u)) := by
  classical
  let F : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2|
  have hFmeas : Measurable F :=
    (hφ.abs.comp measurable_fst).mul (hφ.abs.comp measurable_snd)
  have hnormInt : Integrable (fun x : Plane => |φ x|) := by
    simpa only [Real.norm_eq_abs] using hint.norm
  have hFint : Integrable F (volume.prod volume) := by
    simpa [F] using hnormInt.mul_prod hnormInt
  have hFnonneg (p : Plane × Plane) : 0 ≤ F p :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  let K : ℝ := (2 * Real.pi * u)⁻¹
  have hK : 0 < K := by dsimp [K]; positivity
  have htime : ∀ᶠ k : ℕ in atTop, u / 2 < useq k :=
    huseq.eventually (Ioi_mem_nhds (by linarith))
  let majorant : Plane × Plane → ℝ := fun p => ‖F p‖ * K
  have hmajorant : Integrable majorant (volume.prod volume) := by
    simpa [majorant] using hFint.norm.mul_const K
  apply tendsto_integral_filter_of_dominated_convergence majorant
  · exact Filter.Eventually.of_forall fun k => by
      have hd : Measurable (fun p : Plane × Plane => p.2 - p.1) :=
        measurable_snd.sub measurable_fst
      exact (hFmeas.mul ((measurable_heatKernel (2 * useq k)).comp hd)).aestronglyMeasurable
  · filter_upwards [htime] with k hk
    apply Filter.Eventually.of_forall
    intro p
    have htpos : 0 < 2 * useq k := by linarith
    have hden₀ : 0 < 2 * Real.pi * u := by positivity
    have hden : 0 < 2 * Real.pi * (2 * useq k) := by positivity
    have hdenle : 2 * Real.pi * u ≤ 2 * Real.pi * (2 * useq k) := by
      gcongr
      linarith
    have hkernel : heatKernel (2 * useq k) (p.2 - p.1) ≤ K := by
      calc
        heatKernel (2 * useq k) _ ≤ (2 * Real.pi * (2 * useq k))⁻¹ :=
          heatKernel_le_at_zero htpos.le _
        _ ≤ K := (inv_le_inv₀ hden hden₀).2 hdenle
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hFnonneg p)]
    calc
      F p * |heatKernel (2 * useq k) (p.2 - p.1)| ≤ F p * K :=
        mul_le_mul_of_nonneg_left (by
          rw [abs_of_nonneg (heatKernel_nonneg htpos.le _)]
          exact hkernel) (hFnonneg p)
      _ = majorant p := by simp [majorant, abs_of_nonneg (hFnonneg p)]
  · exact hmajorant
  · exact Filter.Eventually.of_forall fun p => by
      have htime' : Tendsto (fun k => 2 * useq k) atTop (𝓝 (2 * u)) := by
        simpa using tendsto_const_nhds.mul huseq
      have hpair : Tendsto (fun k => (2 * useq k, p.2 - p.1)) atTop
          (𝓝 (2 * u, p.2 - p.1)) := htime'.prodMk_nhds tendsto_const_nhds
      have hkernelCont : ContinuousAt (fun q : ℝ × Plane => heatKernel q.1 q.2)
          (2 * u, p.2 - p.1) := by
        have hpos : IsOpen {q : ℝ × Plane | 0 < q.1} :=
          isOpen_lt continuous_const continuous_fst
        have hcont : ContinuousOn (fun q : ℝ × Plane => heatKernel q.1 q.2)
            {q | 0 < q.1} := Critical2DKPZ.DeltaBose.continuousOn_heatKernel
        have hmem : (2 * u, p.2 - p.1) ∈ {q : ℝ × Plane | 0 < q.1} := by
          simp
          linarith
        exact hcont.continuousAt (hpos.mem_nhds hmem)
      have hkernel := hkernelCont.tendsto.comp hpair
      have hFconstant : Tendsto (fun _k : ℕ => F p) atTop (𝓝 (F p)) :=
        tendsto_const_nhds
      simpa [continuumHeatProfile, F] using hFconstant.mul hkernel

/-- On every compact positive-time interval, integration against an integrable
test pair makes the sampled heat profile converge uniformly in time. -/
theorem tendstoLocallyUniformlyOn_sampledHeatProfile (φ : Plane → ℝ)
    (hφ : Measurable φ) (hint : Integrable φ) :
    TendstoLocallyUniformlyOn
      (fun N u => sampledHeatProfile N φ u) (continuumHeatProfile φ)
      atTop {u : ℝ | 0 < u} := by
  have hopen : IsOpen {u : ℝ | 0 < u} := isOpen_lt continuous_const continuous_id
  apply hopen.tendstoLocallyUniformlyOn_iff_forall_tendsto.mpr
  intro u hu
  rw [tendsto_iff_seq_tendsto]
  intro p hp
  rcases (tendsto_prod_iff'.mp hp) with ⟨hN, huN⟩
  let Nseq : ℕ → ℕ := fun k => (p k).1
  let useq : ℕ → ℝ := fun k => (p k).2
  have hNseq : Tendsto Nseq atTop atTop := by simpa [Nseq] using hN
  have huseq : Tendsto useq atTop (𝓝 u) := by simpa [useq] using huN
  have hlim := tendsto_sampledHeatProfile_along φ hφ hint hu Nseq hNseq useq huseq
  have hcont := tendsto_continuumHeatProfile_along φ hφ hint hu useq huseq
  have hdist : Tendsto (fun k => dist (continuumHeatProfile φ (useq k))
      (sampledHeatProfile (Nseq k) φ (useq k))) atTop (𝓝 0) := by
    simpa using Filter.Tendsto.dist hcont hlim
  have hpair : Tendsto (fun k => (continuumHeatProfile φ (useq k),
      sampledHeatProfile (Nseq k) φ (useq k))) atTop (𝓤 ℝ) := by
    rw [Metric.uniformity_basis_dist.tendsto_right_iff]
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp hdist) ε hε] with k hk
    simpa only [dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (dist_nonneg : 0 ≤ dist _ _)] using hk
  simpa [Function.comp_def, Nseq, useq] using hpair

/-- The sampled heat profile has the expected time-Riemann limit on every
positive time slab, with the rounded even-clock endpoints used by the Green sum. -/
theorem tendsto_sampledHeatProfile_timeSum {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (φ : Plane → ℝ) (hφ : Measurable φ) (hint : Integrable φ) :
    Tendsto (fun N : ℕ => (4 / (N : ℝ)) *
      ∑ r ∈ Finset.Icc (evenCeil ((N : ℝ) * s) + 1) (evenCeil ((N : ℝ) * t)),
        sampledHeatProfile N φ ((r : ℝ) / N)) atTop
      (𝓝 (4 * ∫ u in s..t, continuumHeatProfile φ u)) := by
  classical
  let M₀ : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * s)
  let M₁ : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * t)
  let profileExt : ℝ → ℝ := fun u => continuumHeatProfile φ (max u s)
  have hprofileCont : ContinuousOn (continuumHeatProfile φ) {u : ℝ | 0 < u} := by
    intro u hu
    have hcont : ContinuousAt (continuumHeatProfile φ) u := by
      change Tendsto (continuumHeatProfile φ) (𝓝 u)
        (𝓝 (continuumHeatProfile φ u))
      rw [tendsto_iff_seq_tendsto]
      intro v hv
      exact tendsto_continuumHeatProfile_along φ hφ hint hu v hv
    exact hcont.continuousWithinAt
  have hprofileExtCont : Continuous profileExt := by
    apply hprofileCont.comp_continuous
    · fun_prop
    · intro u
      exact lt_of_lt_of_le hs (le_max_right u s)
  have hMmono : ∀ N, M₀ N ≤ M₁ N := by
    intro N
    exact Critical2DKPZ.evenCeil_mono
      (mul_le_mul_of_nonneg_left hst.le (Nat.cast_nonneg N))
  have hM₀ratio : Tendsto (fun N : ℕ => (M₀ N : ℝ) / N) atTop (𝓝 s) := by
    simpa only [M₀] using Critical2DKPZ.SHF.Moments.tendsto_evenCeil_div s hs.le
  have hM₁ratio : Tendsto (fun N : ℕ => (M₁ N : ℝ) / N) atTop (𝓝 t) := by
    simpa only [M₁] using Critical2DKPZ.SHF.Moments.tendsto_evenCeil_div t
      (le_of_lt (lt_trans hs hst))
  have hM₀lower : ∀ᶠ N : ℕ in atTop, s ≤ (M₀ N : ℝ) / N := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hceil : (N : ℝ) * s ≤ (M₀ N : ℝ) := by
      simpa only [M₀] using Critical2DKPZ.le_evenCeil ((N : ℝ) * s)
    exact (le_div_iff₀ hNr).2 (by simpa only [mul_comm] using hceil)
  have hM₁upper : ∀ᶠ N : ℕ in atTop, (M₁ N : ℝ) / N ≤ t + 1 := by
    filter_upwards [eventually_gt_atTop 1] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hNtwo : (2 : ℝ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
    have hceil : (M₁ N : ℝ) ≤ (N : ℝ) * t + 2 := by
      have h := (Critical2DKPZ.evenCeil_lt_add_two
        (mul_nonneg (Nat.cast_nonneg N) (le_of_lt (lt_trans hs hst)))).le
      simpa only [M₁] using h
    apply (div_le_iff₀ hNr).2
    calc
      (M₁ N : ℝ) ≤ (N : ℝ) * t + 2 := hceil
      _ ≤ (N : ℝ) * t + (N : ℝ) := by nlinarith [hNtwo]
      _ = (t + 1) * (N : ℝ) := by ring
  have hlocal := tendstoLocallyUniformlyOn_sampledHeatProfile φ hφ hint
  have hsubset : Set.Icc s (t + 1) ⊆ {u : ℝ | 0 < u} := by
    intro u hu
    exact lt_of_lt_of_le hs hu.1
  have huniform := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact
      (isCompact_Icc : IsCompact (Set.Icc s (t + 1)))).mp (hlocal.mono hsubset)
  have huniform' : TendstoUniformlyOn
      (fun N u => sampledHeatProfile N φ u) profileExt atTop (Set.Icc s (t + 1)) := by
    intro U hU
    filter_upwards [huniform U hU] with N hN
    intro u hu
    have huLower : s ≤ u := hu.1
    simpa [profileExt, max_eq_left huLower] using hN u hu
  have hsum := Critical2DKPZ.SHF.Moments.tendsto_scaledIntervalSum_uniformlyConverging
    hs hst hMmono hM₀ratio hM₁ratio profileExt
    (fun N u => sampledHeatProfile N φ u) hprofileExtCont huniform'
    hM₀lower hM₁upper
  have hprofileIntegral :
      (∫ u in s..t, profileExt u) = ∫ u in s..t, continuumHeatProfile φ u := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Set.Icc s t := by
      rw [uIcc_of_le hst.le] at hu
      exact hu
    simp only [profileExt]
    rw [max_eq_left hu'.1]
  have hsum4 : Tendsto (fun N : ℕ =>
      (4 : ℝ) * ((N : ℝ)⁻¹ *
        ∑ r ∈ Finset.Icc (M₀ N + 1) (M₁ N),
          sampledHeatProfile N φ ((r : ℝ) / N))) atTop
      (𝓝 (4 * ∫ u in s..t, continuumHeatProfile φ u)) := by
    have h := (tendsto_const_nhds (x := (4 : ℝ))).mul hsum
    simpa only [hprofileIntegral] using h
  apply hsum4.congr'
  filter_upwards with N
  simp only [M₀, M₁]
  ring

/-- Splitting the Green sum at a cutoff separates a short-time row-mass term,
a sampled continuum heat sum, and the integrated local-CLT remainder. The
integrand on the left is integrable by the first conjunct. -/
theorem integral_truncatedGreen_latticePoint_split_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N L R : ℕ), 0 < N → R ≤ L →
      ∀ (φ : Plane → ℝ), Measurable φ → Integrable φ →
        ∀ B : ℝ, (∀ x, |φ x| ≤ B) →
          Integrable (fun p : Plane × Plane => |φ p.1| * |φ p.2| *
            MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1))
            (volume.prod volume) ∧
          (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
            MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) ≤
            (4 * (R : ℝ) / N) * B * (∫ x : Plane, |φ x|) +
              (4 / N) * (∑ r ∈ Finset.Icc (R + 1) L,
                ∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
                  heatKernel (((2 * r : ℕ) : ℝ) / N)
                    (cellSample N p.2 - cellSample N p.1)) +
              (∑ r ∈ Finset.Icc (R + 1) L,
                C / ((2 * (r : ℝ)) ^ 2) * (∫ x : Plane, |φ x|) ^ 2) := by
  obtain ⟨C, hC, hErrorAll⟩ := integral_srwKernel_localCLT_error_le
  refine ⟨C, hC, ?_⟩
  intro N L R hN hRL φ hφ hint B hφB
  classical
  let I : Finset ℕ := Finset.Icc (R + 1) L
  let F : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2|
  let z : Plane × Plane → Site := fun p => latticePoint N p.2 - latticePoint N p.1
  let d : Plane × Plane → Plane := fun p => cellSample N p.2 - cellSample N p.1
  let Low : Plane × Plane → ℝ := fun p =>
    F p * MomentBounds.truncatedGreen R (z p)
  let Heat (r : ℕ) : Plane × Plane → ℝ := fun p =>
    F p * heatKernel (((2 * r : ℕ) : ℝ) / N) (d p)
  let Error (r : ℕ) : Plane × Plane → ℝ := fun p =>
    F p * |srwKernel (2 * r) (z p) -
      2 * heatKernel (((2 * r : ℕ) : ℝ) / 2) (siteToPlane (z p))|
  have hFInt : Integrable F (volume.prod volume) := by
    have hnorm : Integrable (fun x : Plane => |φ x|) := by
      simpa only [Real.norm_eq_abs] using hint.norm
    simpa [F] using hnorm.mul_prod hnorm
  have hFnonneg (p : Plane × Plane) : 0 ≤ F p :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hFmeas : Measurable F :=
    (hφ.abs.comp measurable_fst).mul (hφ.abs.comp measurable_snd)
  have hzmeas : Measurable z := by
    dsimp [z]
    exact (measurable_latticePoint N).comp measurable_snd |>.sub
      ((measurable_latticePoint N).comp measurable_fst)
  have hdmeas : Measurable d := by
    dsimp [d]
    exact (measurable_cellSample N).comp measurable_snd |>.sub
      ((measurable_cellSample N).comp measurable_fst)
  have hLowInt : Integrable Low (volume.prod volume) := by
    simpa [Low, F, z] using
      integrable_truncatedGreen_latticePoint_of R N φ hφ hint
  have hrowEq : ∀ p : Plane × Plane,
      latticeRepresentative N (z p) = d p := by
    intro p
    dsimp [z, d, latticeRepresentative, cellSample]
    rw [Critical2DKPZ.Collision.siteToPlane_sub]
    exact smul_sub _ _ _
  have htime (r : ℕ) (hr : r ∈ I) :
      0 < (((2 * r : ℕ) : ℝ) / N) := by
    have hr1 : 1 ≤ r := by
      change r ∈ Finset.Icc (R + 1) L at hr
      have h := (Finset.mem_Icc.mp hr).1
      omega
    have hn : (0 : ℝ) < ((2 * r : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < 2 * r by omega)
    exact div_pos hn (by exact_mod_cast hN)
  have hHeatMeas (r : ℕ) : Measurable (Heat r) := by
    dsimp [Heat]
    exact hFmeas.mul ((measurable_heatKernel _).comp hdmeas)
  have hHeatInt (r : ℕ) (hr : r ∈ I) :
      Integrable (Heat r) (volume.prod volume) := by
    let t : ℝ := ((2 * r : ℕ) : ℝ) / N
    have ht : 0 < t := by simpa [t] using htime r hr
    have hmajor : Integrable (fun p : Plane × Plane =>
        ‖F p‖ * (2 * Real.pi * t)⁻¹) (volume.prod volume) :=
      hFInt.norm.mul_const _
    apply hmajor.mono' (hHeatMeas r).aestronglyMeasurable
    filter_upwards [] with p
    dsimp [Heat, t]
    rw [abs_mul, abs_of_nonneg (hFnonneg p),
      abs_of_nonneg (heatKernel_nonneg ht.le _)]
    exact mul_le_mul_of_nonneg_left
      (heatKernel_le_at_zero ht.le _) (hFnonneg p)
  have hErrorInt (r : ℕ) (hr : r ∈ I) :
      Integrable (Error r) (volume.prod volume) := by
    have hr1 : 1 ≤ r := by
      change r ∈ Finset.Icc (R + 1) L at hr
      have h := (Finset.mem_Icc.mp hr).1
      omega
    have hEven : Even (2 * r) := ⟨r, by omega⟩
    have h := hErrorAll N (2 * r) (by omega) hEven φ hint
    simpa [Error, F, z] using h.1
  have hErrorLe (r : ℕ) (hr : r ∈ I) :
      (∫ p : Plane × Plane, Error r p) ≤
        C / ((2 * (r : ℝ)) ^ 2) * (∫ x : Plane, |φ x|) ^ 2 := by
    have hr1 : 1 ≤ r := by
      change r ∈ Finset.Icc (R + 1) L at hr
      have h := (Finset.mem_Icc.mp hr).1
      omega
    have hEven : Even (2 * r) := ⟨r, by omega⟩
    have h := hErrorAll N (2 * r) (by omega) hEven φ hint
    simpa [Error, F, z, Nat.cast_mul, Nat.cast_ofNat,
      mul_div_cancel_left₀] using h.2
  have hTermInt (r : ℕ) (hr : r ∈ I) :
      Integrable (fun p : Plane × Plane => (4 / (N : ℝ)) * Heat r p + Error r p)
        (volume.prod volume) :=
    ((hHeatInt r hr).const_mul (4 / (N : ℝ))).add (hErrorInt r hr)
  have hSumInt : Integrable (fun p : Plane × Plane =>
      ∑ r ∈ I, ((4 / (N : ℝ)) * Heat r p + Error r p)) (volume.prod volume) :=
    integrable_finsetSum I hTermInt
  have hRhsInt : Integrable (fun p : Plane × Plane =>
      Low p + ∑ r ∈ I, ((4 / (N : ℝ)) * Heat r p + Error r p))
      (volume.prod volume) := hLowInt.add hSumInt
  have hLhsInt : Integrable (fun p : Plane × Plane =>
      F p * MomentBounds.truncatedGreen L (z p)) (volume.prod volume) := by
    simpa [F, z] using integrable_truncatedGreen_latticePoint_of L N φ hφ hint
  have hset : Finset.Icc 1 L = Finset.Icc 1 R ∪ I := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union, I]
    omega
  have hdisj : Disjoint (Finset.Icc 1 R) I := by
    rw [Finset.disjoint_left]
    intro r hr1 hr2
    have hlow := (Finset.mem_Icc.mp hr1).2
    change r ∈ Finset.Icc (R + 1) L at hr2
    have hhigh := (Finset.mem_Icc.mp hr2).1
    omega
  have hsplit (w : Site) :
      MomentBounds.truncatedGreen L w = MomentBounds.truncatedGreen R w +
        ∑ r ∈ I, srwKernel (2 * r) w := by
    rw [MomentBounds.truncatedGreen, MomentBounds.truncatedGreen, hset,
      Finset.sum_union hdisj]
  have hscaled (r : ℕ) (p : Plane × Plane) :
      2 * heatKernel (((2 * r : ℕ) : ℝ) / 2) (siteToPlane (z p)) =
        (4 / (N : ℝ)) *
          heatKernel (((2 * r : ℕ) : ℝ) / N) (d p) := by
    have hs := Critical2DKPZ.SHF.Moments.heatKernel_latticeRepresentative
      hN (2 * r) (z p)
    rw [hrowEq p] at hs
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    calc
      _ = (4 / (N : ℝ)) *
          ((N : ℝ) / 2 *
            heatKernel (((2 * r : ℕ) : ℝ) / 2) (siteToPlane (z p))) := by
        field_simp [ne_of_gt hNr]
        ring
      _ = _ := by rw [← hs]
  have hkernel (r : ℕ) (p : Plane × Plane) :
      srwKernel (2 * r) (z p) ≤
        (4 / (N : ℝ)) * heatKernel (((2 * r : ℕ) : ℝ) / N) (d p) +
          |srwKernel (2 * r) (z p) -
            2 * heatKernel (((2 * r : ℕ) : ℝ) / 2) (siteToPlane (z p))| := by
    calc
      srwKernel (2 * r) (z p) =
          (srwKernel (2 * r) (z p) -
            2 * heatKernel (((2 * r : ℕ) : ℝ) / 2) (siteToPlane (z p))) +
            2 * heatKernel (((2 * r : ℕ) : ℝ) / 2) (siteToPlane (z p)) := by ring
      _ ≤ |srwKernel (2 * r) (z p) -
            2 * heatKernel (((2 * r : ℕ) : ℝ) / 2) (siteToPlane (z p))| +
            2 * heatKernel (((2 * r : ℕ) : ℝ) / 2) (siteToPlane (z p)) :=
          add_le_add_left (le_abs_self _) _
      _ = _ := by
        rw [hscaled r p]
        exact add_comm _ _
  have hpoint (p : Plane × Plane) :
      F p * MomentBounds.truncatedGreen L (z p) ≤
        Low p + ∑ r ∈ I, ((4 / (N : ℝ)) * Heat r p + Error r p) := by
    have hsum := Finset.sum_le_sum (s := I) (fun r hr => hkernel r p)
    have hgreen := hsplit (z p)
    have hgreen' := add_le_add_right hsum (MomentBounds.truncatedGreen R (z p))
    rw [← hgreen] at hgreen'
    have hmul := mul_le_mul_of_nonneg_left hgreen' (hFnonneg p)
    calc
      _ ≤ F p * (MomentBounds.truncatedGreen R (z p) +
          ∑ r ∈ I, ((4 / (N : ℝ)) * heatKernel
            (((2 * r : ℕ) : ℝ) / N) (d p) +
            |srwKernel (2 * r) (z p) -
              2 * heatKernel (((2 * r : ℕ) : ℝ) / 2) (siteToPlane (z p))|)) := by
        simpa only [F] using hmul
      _ = _ := by
        simp only [Low, Heat, Error, F, z, d, Finset.mul_sum, mul_add]
        congr 1
        apply Finset.sum_congr rfl
        intro x hx
        ring
  have hleft := integral_mono hLhsInt hRhsInt hpoint
  refine ⟨hLhsInt, ?_⟩
  calc
    (∫ p : Plane × Plane, F p * MomentBounds.truncatedGreen L (z p)) ≤
        ∫ p : Plane × Plane,
          (Low p + ∑ r ∈ I, ((4 / (N : ℝ)) * Heat r p + Error r p)) := hleft
    _ = (∫ p : Plane × Plane, Low p) +
          ∑ r ∈ I, ((4 / (N : ℝ)) * (∫ p : Plane × Plane, Heat r p) +
            ∫ p : Plane × Plane, Error r p) := by
      calc
        (∫ p : Plane × Plane, Low p + ∑ r ∈ I,
            ((4 / (N : ℝ)) * Heat r p + Error r p)) =
            (∫ p : Plane × Plane, Low p) +
              ∫ p : Plane × Plane, ∑ r ∈ I,
                ((4 / (N : ℝ)) * Heat r p + Error r p) :=
          integral_add hLowInt hSumInt
        _ = (∫ p : Plane × Plane, Low p) +
              ∑ r ∈ I, ∫ p : Plane × Plane,
                ((4 / (N : ℝ)) * Heat r p + Error r p) := by
          have hsumIntEq :
              (∫ p : Plane × Plane, ∑ r ∈ I,
                ((4 / (N : ℝ)) * Heat r p + Error r p)) =
                ∑ r ∈ I, ∫ p : Plane × Plane,
                  ((4 / (N : ℝ)) * Heat r p + Error r p) :=
            integral_finsetSum I hTermInt
          rw [hsumIntEq]
        _ = _ := by
          congr 1
          apply Finset.sum_congr rfl
          intro r hr
          calc
            (∫ p : Plane × Plane,
                (4 / (N : ℝ)) * Heat r p + Error r p) =
                (∫ p : Plane × Plane, (4 / (N : ℝ)) * Heat r p) +
                  ∫ p : Plane × Plane, Error r p :=
              integral_add ((hHeatInt r hr).const_mul (4 / (N : ℝ)))
                (hErrorInt r hr)
            _ = (4 / (N : ℝ)) * (∫ p : Plane × Plane, Heat r p) +
                  ∫ p : Plane × Plane, Error r p := by
              rw [integral_const_mul]
    _ ≤ (4 * (R : ℝ) / N) * B * (∫ x : Plane, |φ x|) +
          ∑ r ∈ I, ((4 / (N : ℝ)) * (∫ p : Plane × Plane, Heat r p) +
            C / ((2 * (r : ℝ)) ^ 2) * (∫ x : Plane, |φ x|) ^ 2) := by
      apply add_le_add
      · simpa [Low, F, z] using
          (integral_truncatedGreen_latticePoint_pair_le N R hN φ hφ hint B hφB).2
      · exact Finset.sum_le_sum fun r hr => add_le_add_right (hErrorLe r hr) _
    _ = (4 * (R : ℝ) / N) * B * (∫ x : Plane, |φ x|) +
          (4 / N) * (∑ r ∈ I, (∫ p : Plane × Plane, Heat r p)) +
          (∑ r ∈ I, C / ((2 * (r : ℝ)) ^ 2) * (∫ x : Plane, |φ x|) ^ 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      ring_nf
    _ = _ := by
      simp [I, Heat, F, d, Nat.cast_mul]

/-- Companion integrability for the lattice Green integral bound. -/
theorem integrable_truncatedGreen_latticePoint (δ : ℝ) {N : ℕ}
    (φ : Plane → ℝ) (hφ : Measurable φ) (hint : Integrable φ) :
    Integrable (fun p : Plane × Plane =>
      |φ p.1| * |φ p.2| *
        MomentBounds.truncatedGreen (evenCeil (Real.sqrt δ * N))
          (latticePoint N p.2 - latticePoint N p.1)) (volume.prod volume) :=
  integrable_truncatedGreen_latticePoint_of (evenCeil (Real.sqrt δ * N)) N φ hφ hint

private theorem continuumHeatProfile_nonneg_of_nonneg (φ : Plane → ℝ) {u : ℝ}
    (hu : 0 ≤ u) : 0 ≤ continuumHeatProfile φ u := by
  unfold continuumHeatProfile
  apply integral_nonneg
  intro p
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (heatKernel_nonneg (mul_nonneg (by norm_num) hu) _)

/-- The lattice Green energy is eventually at most the heat energy from equation (4.22) plus any positive error. -/
theorem integral_truncatedGreen_latticePoint_le (δ : ℝ) (hδ : 0 < δ) (φ : Plane → ℝ)
    (hφ : Measurable φ) (hint : Integrable φ) (hb : ∃ M : ℝ, ∀ x, |φ x| ≤ M) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
          MomentBounds.truncatedGreen (evenCeil (Real.sqrt δ * N))
            (latticePoint N p.2 - latticePoint N p.1) ≤
        heatEnergy (Real.sqrt δ) φ + ε := by
  classical
  obtain ⟨B, hB⟩ := hb
  have hB0 : 0 ≤ B := by
    have h := hB (0 : Plane)
    exact le_trans (abs_nonneg _) h
  have hnormInt : Integrable (fun x : Plane => |φ x|) := by
    simpa only [Real.norm_eq_abs] using hint.norm
  let L1 : ℝ := ∫ x : Plane, |φ x|
  have hL10 : 0 ≤ L1 := by
    dsimp [L1]
    exact integral_nonneg fun x => abs_nonneg _
  have hS := integral_truncatedGreen_latticePoint_split_le
  obtain ⟨C, hC, hsplit⟩ := hS
  have hC0 : 0 ≤ C := hC.le
  let s : ℝ := Real.sqrt δ
  have hs : 0 < s := Real.sqrt_pos.2 hδ
  intro ε hε
  let η : ℝ := min (s / 2) (ε / (8 * ((B + 1) * (L1 + 1))))
  have hη : 0 < η := by
    dsimp [η]
    apply lt_min
    · positivity
    · positivity
  have hηs : η < s := by
    dsimp [η]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hden : 0 < (B + 1) * (L1 + 1) := by
    positivity
  have hratio : B * L1 / ((B + 1) * (L1 + 1)) ≤ 1 := by
    apply (div_le_one hden).2
    have hB1 : B ≤ B + 1 := by linarith
    have hL11 : L1 ≤ L1 + 1 := by linarith
    calc
      B * L1 ≤ (B + 1) * L1 := by
        exact mul_le_mul_of_nonneg_right hB1 hL10
      _ ≤ (B + 1) * (L1 + 1) := by
        exact mul_le_mul_of_nonneg_left hL11 (by linarith)
  have hlowlim : 4 * η * B * L1 ≤ ε / 2 := by
    dsimp [η]
    have hηbound : min (s / 2) (ε / (8 * ((B + 1) * (L1 + 1)))) ≤
        ε / (8 * ((B + 1) * (L1 + 1))) := min_le_right _ _
    have hcoef : 0 ≤ 4 * B * L1 := by positivity
    have hscale : 4 * (ε / (8 * ((B + 1) * (L1 + 1)))) =
        ε / (2 * ((B + 1) * (L1 + 1))) := by
      field_simp [ne_of_gt hden]
      ring
    calc
      4 * min (s / 2) (ε / (8 * ((B + 1) * (L1 + 1)))) * B * L1 ≤
          (ε / (2 * ((B + 1) * (L1 + 1)))) * B * L1 := by
        calc
          _ = min (s / 2) (ε / (8 * ((B + 1) * (L1 + 1)))) * (4 * B * L1) := by ring
          _ ≤ (ε / (8 * ((B + 1) * (L1 + 1)))) * (4 * B * L1) :=
            mul_le_mul_of_nonneg_right hηbound hcoef
          _ = (ε / (2 * ((B + 1) * (L1 + 1)))) * B * L1 := by
            rw [← hscale]
            ring
      _ ≤ ε / 2 := by
        have hε2 : 0 ≤ ε / 2 := by positivity
        calc
          (ε / (2 * ((B + 1) * (L1 + 1)))) * B * L1 =
              (ε / 2) * ((B * L1) / ((B + 1) * (L1 + 1))) := by
                field_simp [ne_of_gt hden]
          _ ≤ ε / 2 := by simpa using mul_le_mul_of_nonneg_left hratio hε2
  let R : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * η)
  let L : ℕ → ℕ := fun N => evenCeil ((N : ℝ) * s)
  have hRratio : Tendsto (fun N : ℕ => (R N : ℝ) / N) atTop (𝓝 η) := by
    simpa only [R, mul_comm] using Critical2DKPZ.SHF.Moments.tendsto_evenCeil_div η hη.le
  have hLratio : Tendsto (fun N : ℕ => (L N : ℝ) / N) atTop (𝓝 s) := by
    simpa only [L, mul_comm] using Critical2DKPZ.SHF.Moments.tendsto_evenCeil_div s hs.le
  have hNinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hLplusRatio : Tendsto (fun N : ℕ => ((L N + 1 : ℕ) : ℝ) / N) atTop
      (𝓝 s) := by
    have h := hLratio.add hNinv
    simpa only [Nat.cast_add, Nat.cast_one, add_div, one_div, add_zero] using h
  have hRnonzero : η ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hη)
  have htailRatio : Tendsto (fun N : ℕ =>
      (((L N + 1 : ℕ) : ℝ) / N) * (N : ℝ)⁻¹ / (((R N : ℝ) / N) ^ 2)) atTop
      (𝓝 (s * 0 / η ^ 2)) := by
    have hnum := hLplusRatio.mul hNinv
    have hdenom := hRratio.pow 2
    change Tendsto
      ((fun N : ℕ => ((L N + 1 : ℕ) : ℝ) / N * (N : ℝ)⁻¹) /
        (fun N : ℕ => ((R N : ℝ) / N) ^ 2)) atTop (𝓝 (s * 0 / η ^ 2))
    simpa only [zero_mul, div_zero] using hnum.div hdenom hRnonzero
  have htailLim : Tendsto (fun N : ℕ =>
      ((C * L1 ^ 2) / 4) *
        ((((L N + 1 : ℕ) : ℝ) / N) * (N : ℝ)⁻¹ / (((R N : ℝ) / N) ^ 2))) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := (C * L1 ^ 2 / 4))).mul htailRatio
    simpa using h
  have hlowTendsto : Tendsto (fun N : ℕ =>
      (4 * (R N : ℝ) / N) * B * L1) atTop (𝓝 (4 * η * B * L1)) := by
    convert hRratio.const_mul (4 * B * L1) using 1 <;> ext N <;> ring
  have hheatTendsto := tendsto_sampledHeatProfile_timeSum hη hηs φ hφ hint
  have henergyProfile := heatEnergy_eq_profile_timeIntegral φ hφ hint B hB hs
  have hprofInterval : IntervalIntegrable (fun u => continuumHeatProfile φ u)
      volume 0 s := by
    rw [intervalIntegrable_iff]
    have hIcc : IntegrableOn (fun u => continuumHeatProfile φ u) (Set.Icc 0 s) volume :=
      henergyProfile.1
    exact hIcc.mono_set (by
      rw [uIoc_of_le hs.le]
      exact Ioc_subset_Icc_self)
  have hprof0η : IntervalIntegrable (fun u => continuumHeatProfile φ u)
      volume 0 η := hprofInterval.mono_set' (by
        intro u hu
        rw [uIoc_of_le hη.le] at hu
        rw [uIoc_of_le hs.le]
        exact Ioc_subset_Ioc_right hηs.le hu)
  have hprofηs : IntervalIntegrable (fun u => continuumHeatProfile φ u)
      volume η s := hprofInterval.mono_set' (by
        intro u hu
        rw [uIoc_of_le hηs.le] at hu
        rw [uIoc_of_le hs.le]
        exact Ioc_subset_Ioc_left (le_of_lt hη) hu)
  have hprofileNonneg : ∀ u, 0 ≤ u → 0 ≤ continuumHeatProfile φ u :=
    fun u hu => continuumHeatProfile_nonneg_of_nonneg φ hu
  have hlowIntegralNonneg : 0 ≤ ∫ u in (0 : ℝ)..η, continuumHeatProfile φ u :=
    intervalIntegral.integral_nonneg (le_of_lt hη) (fun u hu => hprofileNonneg u hu.1)
  have htimeSplit := intervalIntegral.integral_add_adjacent_intervals hprof0η hprofηs
  have hhighBelowEnergy :
      4 * (∫ u in η..s, continuumHeatProfile φ u) ≤ heatEnergy s φ := by
    rw [henergyProfile.2]
    nlinarith [htimeSplit, hlowIntegralNonneg]
  have hlimBound : 4 * η * B * L1 +
      4 * (∫ u in η..s, continuumHeatProfile φ u) ≤ heatEnergy s φ + ε / 2 := by
    linarith [hlowlim, hhighBelowEnergy]
  let upper : ℕ → ℝ := fun N =>
    (4 * (R N : ℝ) / N) * B * L1 +
      (4 / N) * (∑ r ∈ Finset.Icc (R N + 1) (L N),
        sampledHeatProfile N φ ((r : ℝ) / N)) +
      ∑ r ∈ Finset.Icc (R N + 1) (L N),
        C / ((2 * (r : ℝ)) ^ 2) * L1 ^ 2
  have htailBound : ∀ᶠ N : ℕ in atTop,
      (∑ r ∈ Finset.Icc (R N + 1) (L N),
        C / ((2 * (r : ℝ)) ^ 2) * L1 ^ 2) ≤
        ((C * L1 ^ 2) / 4) *
          ((((L N + 1 : ℕ) : ℝ) / N) * (N : ℝ)⁻¹ / (((R N : ℝ) / N) ^ 2)) := by
    filter_upwards [eventually_gt_atTop 0] with N hN
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    have hRlo : η * (N : ℝ) ≤ (R N : ℝ) := by
      simpa [R, mul_comm] using Critical2DKPZ.le_evenCeil ((N : ℝ) * η)
    have hRpos : 0 < (R N : ℝ) := lt_of_lt_of_le (mul_pos hη hNr) hRlo
    have hcount : (Finset.Icc (R N + 1) (L N)).card ≤ L N + 1 := by
      calc
        (Finset.Icc (R N + 1) (L N)).card ≤ (Finset.range (L N + 1)).card :=
          Finset.card_le_card (by
            intro r hr
            apply Finset.mem_range.mpr
            have hr' := Finset.mem_Icc.mp hr
            omega)
        _ = L N + 1 := by rw [Finset.card_range]
    have hterms : ∀ r ∈ Finset.Icc (R N + 1) (L N),
        C / ((2 * (r : ℝ)) ^ 2) * L1 ^ 2 ≤
          C / (4 * (R N : ℝ) ^ 2) * L1 ^ 2 := by
      intro r hr
      have hrR : (R N : ℝ) ≤ r := by
        have hr' := (Finset.mem_Icc.mp hr).1
        exact_mod_cast (Nat.le_trans (Nat.le_add_right _ _) hr')
      have hdenle : 4 * (R N : ℝ) ^ 2 ≤ (2 * (r : ℝ)) ^ 2 := by
        nlinarith [hRpos.le, hrR]
      have hdenpos : 0 < 4 * (R N : ℝ) ^ 2 := by positivity
      have hfrac : C / ((2 * (r : ℝ)) ^ 2) ≤ C / (4 * (R N : ℝ) ^ 2) := by
        exact div_le_div_of_nonneg_left hC0 hdenpos hdenle
      exact mul_le_mul_of_nonneg_right hfrac (sq_nonneg L1)
    calc
      _ ≤ ∑ r ∈ Finset.Icc (R N + 1) (L N),
          C / (4 * (R N : ℝ) ^ 2) * L1 ^ 2 :=
        Finset.sum_le_sum fun r hr => hterms r hr
      _ = ((Finset.Icc (R N + 1) (L N)).card : ℝ) *
          (C / (4 * (R N : ℝ) ^ 2) * L1 ^ 2) := by simp
      _ ≤ (L N + 1 : ℝ) * (C / (4 * (R N : ℝ) ^ 2) * L1 ^ 2) := by
        gcongr
        exact_mod_cast hcount
      _ = ((C * L1 ^ 2) / 4) *
          ((((L N + 1 : ℕ) : ℝ) / N) * (N : ℝ)⁻¹ / (((R N : ℝ) / N) ^ 2)) := by
        field_simp [ne_of_gt hNr, ne_of_gt hRpos]
        push_cast
        ring_nf
  have htotalTendsto : Tendsto upper atTop
      (𝓝 (4 * η * B * L1 + 4 * ∫ u in η..s, continuumHeatProfile φ u)) := by
    have htail' : Tendsto (fun N : ℕ =>
        ∑ r ∈ Finset.Icc (R N + 1) (L N),
          C / ((2 * (r : ℝ)) ^ 2) * L1 ^ 2) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htailLim
        (Filter.Eventually.of_forall fun _ => by positivity) htailBound
    have h := hlowTendsto.add (hheatTendsto.add htail')
    simpa [upper, add_assoc] using h
  have hupperEventually : ∀ᶠ N : ℕ in atTop, upper N <
      (4 * η * B * L1 + 4 * ∫ u in η..s, continuumHeatProfile φ u) + ε / 2 :=
    htotalTendsto.eventually (Iio_mem_nhds (by linarith :
      4 * η * B * L1 + 4 * ∫ u in η..s, continuumHeatProfile φ u <
        (4 * η * B * L1 + 4 * ∫ u in η..s, continuumHeatProfile φ u) + ε / 2))
  filter_upwards [eventually_gt_atTop 0, hupperEventually] with N hN hupper
  have hNr : 0 < N := hN
  have hRL : R N ≤ L N := by
    apply Critical2DKPZ.evenCeil_mono
    exact mul_le_mul_of_nonneg_left hηs.le (Nat.cast_nonneg N)
  have hsplitN := hsplit N (L N) (R N) hN hRL φ hφ hint B hB
  have hheatRewrite : (4 / (N : ℝ)) *
      (∑ r ∈ Finset.Icc (R N + 1) (L N),
        ∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
          heatKernel (((2 * r : ℕ) : ℝ) / N)
            (cellSample N p.2 - cellSample N p.1)) =
      (4 / (N : ℝ)) * (∑ r ∈ Finset.Icc (R N + 1) (L N),
        sampledHeatProfile N φ ((r : ℝ) / N)) := by
    apply congrArg (fun x : ℝ => (4 / (N : ℝ)) * x)
    apply Finset.sum_congr rfl
    intro r hr
    change (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        heatKernel (((2 * r : ℕ) : ℝ) / N)
          (cellSample N p.2 - cellSample N p.1)) =
      ∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        heatKernel (2 * ((r : ℝ) / N))
          (cellSample N p.2 - cellSample N p.1)
    apply integral_congr_ae
    filter_upwards [] with p
    congr 1
    push_cast
    ring
  have hsplitUpper :
      (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        MomentBounds.truncatedGreen (L N)
          (latticePoint N p.2 - latticePoint N p.1)) ≤ upper N := by
    have h := hsplitN.2
    rw [hheatRewrite] at h
    simpa [upper, L1, R, L] using h
  have htarget : upper N ≤ heatEnergy s φ + ε := by
    linarith [hupper, hlimBound]
  simpa [s, L, mul_comm] using hsplitUpper.trans htarget

/-- A bounded integrable test has heat energy at most four times the time horizon, its uniform
bound, and its `L¹` norm. -/
theorem heatEnergy_le_of_bounded (φ : Plane → ℝ) (hφ : Measurable φ)
    (hint : Integrable φ) (B : ℝ) (hB : ∀ x, |φ x| ≤ B) {s : ℝ} (hs : 0 < s) :
    0 ≤ heatEnergy s φ ∧
      heatEnergy s φ ≤ 4 * s * B * (∫ x : Plane, |φ x|) := by
  obtain ⟨hprofileInt, henergy⟩ := heatEnergy_eq_profile_timeIntegral φ hφ hint B hB hs
  have hB0 : 0 ≤ B := by
    have h := hB (0 : Plane)
    exact le_trans (abs_nonneg _) h
  have hL1 : 0 ≤ ∫ x : Plane, |φ x| := integral_nonneg fun x => abs_nonneg _
  have hprofileInterval : IntervalIntegrable (continuumHeatProfile φ) volume 0 s := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hs.le]
    simpa only [IntegrableOn] using hprofileInt
  have hconstInterval : IntervalIntegrable (fun _ : ℝ => B * (∫ x : Plane, |φ x|))
      volume 0 s := intervalIntegrable_const
  have hprofileNonneg : ∀ u ∈ Set.Icc (0 : ℝ) s, 0 ≤ continuumHeatProfile φ u := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [continuumHeatProfile, hu0, Critical2DKPZ.heatKernel_zero_time]
    · have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      exact (continuumHeatProfile_integrable_bound φ hφ hint B hB huPos).2.1
  have hprofileBound : ∀ u ∈ Set.Icc (0 : ℝ) s,
      continuumHeatProfile φ u ≤ B * (∫ x : Plane, |φ x|) := by
    intro u hu
    by_cases hu0 : u = 0
    · simp [continuumHeatProfile, hu0, Critical2DKPZ.heatKernel_zero_time]
      exact mul_nonneg hB0 hL1
    · have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      exact (continuumHeatProfile_integrable_bound φ hφ hint B hB huPos).2.2
  have hprofileIntegralNonneg := intervalIntegral.integral_nonneg (μ := volume)
    hs.le hprofileNonneg
  have hprofileIntegralBound := intervalIntegral.integral_mono_on hs.le hprofileInterval
    hconstInterval hprofileBound
  constructor
  · rw [henergy]
    positivity
  · rw [henergy]
    calc
      4 * ∫ u in (0 : ℝ)..s, continuumHeatProfile φ u ≤
          4 * ∫ u in (0 : ℝ)..s, (fun _ : ℝ => B * (∫ x : Plane, |φ x|)) u :=
        mul_le_mul_of_nonneg_left hprofileIntegralBound (by norm_num)
      _ = 4 * s * B * (∫ x : Plane, |φ x|) := by simp [intervalIntegral.integral_const]; ring

end Critical2DKPZ.Smoothing

end
