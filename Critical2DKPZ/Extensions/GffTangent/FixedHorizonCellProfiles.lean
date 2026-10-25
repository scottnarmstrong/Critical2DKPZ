/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonCellScale
public import Critical2DKPZ.Definitions.TestFn
public import Critical2DKPZ.Analysis.Lattice.Volume
public import Critical2DKPZ.SHF.Limit.LocalFinite
import Critical2DKPZ.JointConvergence.HeatStartLogFieldConvergence
import Mathlib.Tactic

/-! # Exact compact cell entrance profiles and their uniform bounds -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Extensions.GffTangent

/-- The finite set of lattice cells meeting the compact support of a test. -/
def fixedHorizonCellSites (N : ℕ) (f : TestFn) : Finset Site :=
  (SHF.Limit.finite_latticePoint_image_of_bounded (N := N) f.hasCompactSupport.isBounded).toFinset

/-- Membership records an actual point in the compact test support. -/
theorem mem_fixedHorizonCellSites_iff (N : ℕ) (f : TestFn) (w : Site) :
    w ∈ fixedHorizonCellSites N f ↔ ∃ x ∈ tsupport f, latticePoint N x = w := by
  simp only [fixedHorizonCellSites, Set.Finite.mem_toFinset, Set.mem_image]

/-- The canonical finite set covers every nonzero test value. -/
theorem latticePoint_mem_fixedHorizonCellSites (N : ℕ) (f : TestFn) {x : Plane} (hx : f x ≠ 0) :
    latticePoint N x ∈ fixedHorizonCellSites N f :=
  (mem_fixedHorizonCellSites_iff N f _).mpr
    ⟨x, subset_closure (Function.mem_support.mpr hx), rfl⟩

/-- The signed entrance coefficient is the exact integral over the lattice cell. -/
def signedCellProfile (N : ℕ) (f : TestFn) (w : Site) : ℝ := ∫ x in cell N w, f x

/-- The positive part is taken after cell integration. -/
def positiveCellProfile (N : ℕ) (f : TestFn) (w : Site) : ℝ := max (signedCellProfile N f w) 0

/-- The negative part is taken after cell integration. -/
def negativeCellProfile (N : ℕ) (f : TestFn) (w : Site) : ℝ := max (-signedCellProfile N f w) 0

/-- Absolute cell masses dominate both signs of the signed entrance profile. -/
def absoluteCellProfile (N : ℕ) (f : TestFn) (w : Site) : ℝ :=
  ∫ x in cell N w, |f x|


/-- Cells outside the canonical compact entrance set have zero mass. -/
theorem absoluteCellProfile_zero_of_not_mem (N : ℕ) (f : TestFn) {w : Site}
    (hw : w ∉ fixedHorizonCellSites N f) : absoluteCellProfile N f w = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  apply abs_eq_zero.mpr
  by_contra hfx
  have hmem := latticePoint_mem_fixedHorizonCellSites N f hfx
  rw [(mem_cell_iff N w x).mp hx] at hmem
  exact hw hmem

/-- The signed cell coefficient is dominated by its absolute mass. -/
theorem abs_integral_cell_le_absoluteCellProfile (N : ℕ) (f : TestFn) (w : Site) :
    |∫ x in cell N w, f x| ≤ absoluteCellProfile N f w := abs_integral_le_integral_abs

/-- Exact conservation of the absolute test mass over the finite cell profile. -/
theorem sum_absoluteCellProfile (N : ℕ) (f : TestFn) :
    (∑ w ∈ fixedHorizonCellSites N f, absoluteCellProfile N f w) = ∫ x : Plane, |f x| := by
  have h := JointConvergence.integral_mul_latticePoint_piecewise
    f.continuous.abs f.hasCompactSupport.abs N (fun _ => 1) (fixedHorizonCellSites N f)
      (fun x hx => latticePoint_mem_fixedHorizonCellSites N f (fun h => hx (by rw [h, abs_zero])))
  simpa only [mul_one, absoluteCellProfile] using h.symm

/-- The exact cell-area bound supplies a supremum of order 1/N. -/
theorem absoluteCellProfile_le (N : ℕ) (hN : 0 < N) (f : TestFn)
    {C : ℝ} (hC : 0 ≤ C) (hfC : ∀ x : Plane, |f x| ≤ C) (w : Site) :
    absoluteCellProfile N f w ≤ 4 * C / N := by
  by_cases hw : w ∈ fixedHorizonCellSites N f
  · obtain ⟨x, _, hx⟩ := (mem_fixedHorizonCellSites_iff N f w).mp hw
    have heven : w ∈ evenLattice := hx ▸ latticePoint_mem_evenLattice N x
    have hfin : volume (cell N w) ≠ ∞ := by
      rw [volume_cell hN heven]
      exact ENNReal.ofReal_ne_top
    have hfint : IntegrableOn (fun x : Plane => |f x|) (cell N w) :=
      (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport).abs.integrableOn
    calc
      _ ≤ ∫ x in cell N w, C :=
        integral_mono hfint (integrableOn_const hfin) hfC
      _ = 4 * C / N := by
        rw [setIntegral_const, measureReal_def, smul_eq_mul, volume_cell_toReal hN heven]
        ring
  · rw [absoluteCellProfile_zero_of_not_mem N f hw]
    positivity

/-- Compact support bounds the cell-site exponential weight uniformly in N. -/
theorem exp_fourthWeightScale_site_le (N : ℕ) (f : TestFn)
    {R : ℝ} (hR : 0 ≤ R) (hfR : ∀ x ∈ tsupport f, ‖x‖ ≤ R)
    {w : Site} (hw : w ∈ fixedHorizonCellSites N f) :
    Real.exp (fourthWeightScale N * ‖siteToPlane w‖) ≤ Real.exp (R + 2) := by
  obtain ⟨x, hx, rfl⟩ := (mem_fixedHorizonCellSites_iff N f w).mp hw
  exact Real.exp_le_exp.mpr (fourthWeightScale_norm_latticePoint_le hR (hfR x hx) N)

/-- Every nonnegative profile dominated by the absolute cell masses has the
same total-mass bound. -/
theorem sum_dominated_cell_profile_le (N : ℕ) (f : TestFn) (φ : Site → ℝ)
    (hdom : ∀ w, φ w ≤ absoluteCellProfile N f w) :
    (∑ w ∈ fixedHorizonCellSites N f, φ w) ≤ ∫ x : Plane, |f x| := by
  rw [← sum_absoluteCellProfile N f]
  exact Finset.sum_le_sum (fun w _ => hdom w)

/-- Domination by absolute cell masses automatically gives finite support. -/
theorem dominated_cell_profile_zero_of_not_mem (N : ℕ) (f : TestFn) (φ : Site → ℝ)
    (hφ : ∀ w, 0 ≤ φ w) (hdom : ∀ w, φ w ≤ absoluteCellProfile N f w)
    {w : Site} (hw : w ∉ fixedHorizonCellSites N f) : φ w = 0 := by
  apply le_antisymm _ (hφ w)
  simpa only [absoluteCellProfile_zero_of_not_mem N f hw] using hdom w

/-- The signed entrance profile preserves the test integral exactly. -/
theorem sum_signedCellProfile (N : ℕ) (f : TestFn) :
    (∑ w ∈ fixedHorizonCellSites N f, signedCellProfile N f w) = ∫ x : Plane, f x := by
  have h := JointConvergence.integral_mul_latticePoint_piecewise
    f.continuous f.hasCompactSupport N (fun _ => 1) (fixedHorizonCellSites N f)
      (fun _ hx => latticePoint_mem_fixedHorizonCellSites N f hx)
  simpa only [mul_one, signedCellProfile] using h.symm

/-- Both nonnegative signs of the cell profile have the same absolute-mass domination. -/
theorem positive_negative_cell_profile_domination (N : ℕ) (f : TestFn) (w : Site) :
    (0 ≤ positiveCellProfile N f w ∧ positiveCellProfile N f w ≤ absoluteCellProfile N f w) ∧
      (0 ≤ negativeCellProfile N f w ∧ negativeCellProfile N f w ≤ absoluteCellProfile N f w) := by
  have h := abs_integral_cell_le_absoluteCellProfile N f w
  refine ⟨⟨le_max_right _ _, ?_⟩, ⟨le_max_right _ _, ?_⟩⟩
  · exact (max_le (le_abs_self _) (abs_nonneg _)).trans h
  · exact (max_le (neg_le_abs _) (abs_nonneg _)).trans h

/-- The two nonnegative coefficient profiles reconstruct the signed one. -/
theorem positiveCellProfile_sub_negativeCellProfile (N : ℕ) (f : TestFn) (w : Site) :
    positiveCellProfile N f w - negativeCellProfile N f w = signedCellProfile N f w :=
  max_zero_sub_max_neg_zero_eq_self _

end Critical2DKPZ.Extensions.GffTangent
