/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Smoothing.GreenApproximation
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.Polymer.SummableCovariance
import Mathlib.Tactic

/-! # A uniform coarse lattice Green energy bound -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.Polymer

namespace Critical2DKPZ.Smoothing


/-- The sampled truncated Green energy is bounded uniformly over tests with bounded `L¹` and
`L∞` norms. Integrability is part of the conclusion because the bound is on a Bochner integral. -/
theorem integral_truncatedGreen_latticePoint_coarse_le (N L : ℕ) (hN : 0 < N)
    (φ : Plane → ℝ) (hφ : Measurable φ) (hφint : Integrable φ)
    (M₁ M₂ : ℝ) (hL₁ : (∫ x : Plane, |φ x|) ≤ M₁)
    (hφbound : ∀ x, |φ x| ≤ M₂) :
    Integrable (fun p : Plane × Plane => |φ p.1| * |φ p.2| *
      MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1))
        (volume.prod volume) ∧
      (∫ p : Plane × Plane, |φ p.1| * |φ p.2| *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)
        ∂volume.prod volume) ≤
        4 * (((L : ℝ) + 1) / N) * M₂ * M₁ := by
  classical
  have hM₁ : 0 ≤ M₁ := by
    have h := integral_nonneg (μ := volume) fun x : Plane => abs_nonneg (φ x)
    linarith
  have hM₂ : 0 ≤ M₂ := le_trans (abs_nonneg (φ (0 : Plane))) (hφbound 0)
  have hφabs : Integrable (fun x : Plane => |φ x|) := by
    simpa only [Real.norm_eq_abs] using hφint.norm
  let F : Plane × Plane → ℝ := fun p => |φ p.1| * |φ p.2|
  have hFint : Integrable F (volume.prod volume) := by
    simpa [F] using hφabs.mul_prod hφabs
  have hFmeas : Measurable F := (hφ.abs.comp measurable_fst).mul (hφ.abs.comp measurable_snd)
  have hFnonneg (p : Plane × Plane) : 0 ≤ F p := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hterm (r : ℕ) :
      Integrable (fun p : Plane × Plane => F p *
        srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1))
        (volume.prod volume) := by
    let K : Plane × Plane → ℝ := fun p =>
      srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1)
    have hKmeas : Measurable K := by
      dsimp [K]
      exact (measurable_of_countable fun z : Site => srwKernel (2 * r) z).comp
        ((measurable_latticePoint N).comp measurable_snd |>.sub
          ((measurable_latticePoint N).comp measurable_fst))
    have h : Integrable (fun p : Plane × Plane => F p * K p) (volume.prod volume) := by
      apply hFint.mono' (hFmeas.mul hKmeas).aestronglyMeasurable
      filter_upwards with p
      change |(|φ p.1| * |φ p.2|) * srwKernel (2 * r)
        (latticePoint N p.2 - latticePoint N p.1)| ≤ F p
      rw [abs_mul, abs_of_nonneg (hFnonneg p),
        abs_of_nonneg (Critical2DKPZ.srwKernel_nonneg _ _)]
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left (srwKernel_le_one _ _) (hFnonneg p))
    simpa only [K] using h
  have htermBound (r : ℕ) :
      (∫ p : Plane × Plane, F p *
        srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1)
        ∂volume.prod volume) ≤ 4 / N * M₂ * M₁ := by
    have hcell : ∀ z : Site, (∫ y in cell N z, |φ y|) ≤ M₂ * (4 / N) := by
      intro z
      by_cases hz : z ∈ evenLattice
      · have hvol := Critical2DKPZ.volume_cell_toReal hN hz
        have hvolTop := Critical2DKPZ.volume_cell_lt_top hN hz
        have hconst : IntegrableOn (fun _ : Plane => M₂) (cell N z) volume :=
          integrableOn_const hvolTop.ne
        calc
          (∫ y in cell N z, |φ y|) ≤ ∫ y in cell N z, M₂ :=
            setIntegral_mono_on hφabs.integrableOn hconst (measurableSet_cell N z)
              (fun y _ => hφbound y)
          _ = M₂ * (4 / N) := by
            rw [setIntegral_const, measureReal_def, smul_eq_mul, hvol]
            ring
      · rw [Critical2DKPZ.cell_eq_empty_of_not_even hz]
        rw [setIntegral_empty]
        positivity
    have hcover : (⋃ z : Site, cell N z) = (Set.univ : Set Plane) := by
      apply Set.eq_univ_of_forall
      intro y
      exact Set.mem_iUnion.mpr ⟨latticePoint N y, mem_cell_latticePoint N y⟩
    have hinner (x : Plane) :
        (∫ y : Plane, |φ y| * srwKernel (2 * r)
          (latticePoint N y - latticePoint N x)) ≤ 4 / N * M₂ := by
      let g : Plane → ℝ := fun y => |φ y| * srwKernel (2 * r)
        (latticePoint N y - latticePoint N x)
      have hgmeas : Measurable g := by
        dsimp [g]
        exact hφ.abs.mul ((measurable_of_countable fun z : Site => srwKernel (2 * r) z).comp
          ((measurable_latticePoint N).sub measurable_const))
      have hgint : Integrable g := by
        apply hφabs.mono' hgmeas.aestronglyMeasurable
        filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (abs_nonneg _),
          abs_of_nonneg (Critical2DKPZ.srwKernel_nonneg _ _)]
        simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left (srwKernel_le_one _ _) (abs_nonneg _))
      have hdecomp := integral_iUnion (measurableSet_cell N) (pairwise_disjoint_cell N)
        hgint.integrableOn
      rw [hcover, setIntegral_univ] at hdecomp
      have hcellEq (z : Site) :
          (∫ y in cell N z, g y) = (∫ y in cell N z, |φ y|) *
            srwKernel (2 * r) (z - latticePoint N x) := by
        dsimp [g]
        rw [setIntegral_congr_fun (measurableSet_cell N z) (fun y hy => by
          rw [(mem_cell_iff N z y).mp hy]), integral_mul_const]
      have hsmall (z : Site) :
          (∫ y in cell N z, g y) ≤ M₂ * (4 / N) *
            srwKernel (2 * r) (z - latticePoint N x) := by
        rw [hcellEq z]
        exact mul_le_mul_of_nonneg_right (hcell z)
          (Critical2DKPZ.srwKernel_nonneg _ _)
      have hqshift : Summable (fun z : Site =>
          srwKernel (2 * r) (z - latticePoint N x)) := by
        apply summable_of_ne_finset_zero (s := Polymer.endpoints (latticePoint N x) (2 * r))
        intro z hz
        exact Polymer.srwKernel_eq_zero_of_not_mem (2 * r) (latticePoint N x) z hz
      have hqshiftone : (∑' z : Site, srwKernel (2 * r)
          (z - latticePoint N x)) = 1 := Polymer.tsum_srwKernel (2 * r) (latticePoint N x)
      calc
        _ = ∑' z : Site, ∫ y in cell N z, g y := by simpa [g] using hdecomp
        _ ≤ ∑' z : Site, M₂ * (4 / N) *
            srwKernel (2 * r) (z - latticePoint N x) := by
              let major : Site → ℝ := fun z => M₂ * (4 / N) *
                srwKernel (2 * r) (z - latticePoint N x)
              have hmajor : Summable major := by
                simpa only [major] using hqshift.mul_left (M₂ * (4 / N))
              have hleftNonneg (z : Site) : 0 ≤ ∫ y in cell N z, g y := by
                rw [hcellEq z]
                exact mul_nonneg (integral_nonneg fun y => abs_nonneg (φ y))
                  (Critical2DKPZ.srwKernel_nonneg _ _)
              have hleftSummable : Summable (fun z : Site => ∫ y in cell N z, g y) :=
                Summable.of_nonneg_of_le hleftNonneg (fun z => hsmall z) hmajor
              exact hleftSummable.tsum_le_tsum (fun z => hsmall z) hmajor
        _ = M₂ * (4 / N) := by rw [tsum_mul_left, hqshiftone, mul_one]
        _ = 4 / N * M₂ := by ring
    have hPairBound :
        (∫ p : Plane × Plane, F p *
          srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1)
          ∂volume.prod volume) ≤ (4 / N * M₂) * (∫ x : Plane, |φ x|) := by
      have hprod := hterm r
      have hdouble :
          (∫ p : Plane × Plane, F p *
            srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1)
            ∂volume.prod volume) =
          ∫ x : Plane, ∫ y : Plane, F (x, y) *
            srwKernel (2 * r) (latticePoint N y - latticePoint N x) :=
        integral_prod _ hprod
      rw [hdouble]
      calc
        _ ≤ ∫ x : Plane, |φ x| * (4 / N * M₂) := by
          apply integral_mono hprod.integral_prod_left (hφabs.mul_const (4 / N * M₂))
          intro x
          change (∫ y : Plane, |φ x| * |φ y| *
            srwKernel (2 * r) (latticePoint N y - latticePoint N x)) ≤
            |φ x| * (4 / N * M₂)
          calc
            _ = |φ x| * (∫ y : Plane, |φ y| *
                srwKernel (2 * r) (latticePoint N y - latticePoint N x)) := by
                  calc
                    _ = ∫ y : Plane, |φ x| *
                        (|φ y| * srwKernel (2 * r)
                          (latticePoint N y - latticePoint N x)) := by
                            congr 1
                            funext y
                            ring
                    _ = _ := integral_const_mul _ _
            _ ≤ |φ x| * (4 / N * M₂) :=
              mul_le_mul_of_nonneg_left (hinner x) (abs_nonneg _)
        _ = (4 / N * M₂) * (∫ x : Plane, |φ x|) := by
          rw [integral_mul_const]
          ring
    calc
      _ ≤ (4 / N * M₂) * M₁ := by
        calc
          _ ≤ (4 / N * M₂) * (∫ x : Plane, |φ x|) := hPairBound
          _ ≤ (4 / N * M₂) * M₁ :=
            mul_le_mul_of_nonneg_left hL₁ (by positivity)
      _ = 4 / N * M₂ * M₁ := by ring
  let I : Finset ℕ := Finset.Icc 1 L
  have hAllInt : Integrable (fun p : Plane × Plane => F p *
      MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1))
      (volume.prod volume) := by
    have hsum := integrable_finsetSum I (fun r hr => hterm r)
    have heq : (fun p : Plane × Plane => F p *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) =
      fun p => ∑ r ∈ I, F p * srwKernel (2 * r)
        (latticePoint N p.2 - latticePoint N p.1) := by
      funext p
      simp [I, F, MomentBounds.truncatedGreen, Finset.mul_sum]
    simpa only [heq] using hsum
  have hsumIntegral : (∫ p : Plane × Plane, F p *
      MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)
      ∂volume.prod volume) =
      ∑ r ∈ I, ∫ p : Plane × Plane, F p * srwKernel (2 * r)
        (latticePoint N p.2 - latticePoint N p.1) ∂volume.prod volume := by
    rw [show (fun p : Plane × Plane => F p *
        MomentBounds.truncatedGreen L (latticePoint N p.2 - latticePoint N p.1)) =
      fun p => ∑ r ∈ I, F p * srwKernel (2 * r)
        (latticePoint N p.2 - latticePoint N p.1) by
          funext p
          simp [I, F, MomentBounds.truncatedGreen, Finset.mul_sum]]
    exact integral_finsetSum I (fun r hr => hterm r)
  have hcount : (I.card : ℝ) ≤ (L : ℝ) + 1 := by
    have hsub : I ⊆ Finset.range (L + 1) := by
      intro r hr
      simp only [I, Finset.mem_Icc] at hr
      simp only [Finset.mem_range]
      omega
    calc
      (I.card : ℝ) ≤ (Finset.range (L + 1)).card := by
        exact_mod_cast Finset.card_le_card hsub
      _ = (L : ℝ) + 1 := by simp
  refine ⟨hAllInt, ?_⟩
  rw [hsumIntegral]
  calc
    _ ≤ ∑ r ∈ I, (4 / N * M₂ * M₁) :=
      Finset.sum_le_sum fun r hr => htermBound r
    _ = (I.card : ℝ) * (4 / N * M₂ * M₁) := by simp
    _ ≤ ((L : ℝ) + 1) * (4 / N * M₂ * M₁) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = 4 * (((L : ℝ) + 1) / N) * M₂ * M₁ := by ring

end Critical2DKPZ.Smoothing

end
