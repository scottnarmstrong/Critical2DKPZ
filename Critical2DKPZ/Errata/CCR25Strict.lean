/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Algebra.Order.Round
public import Mathlib.Basic.Real.Basic
public import Critical2DKPZ.MomentBounds.LatticePowerSum
public import Critical2DKPZ.Definitions.Plane
public import Mathlib.Probability.IdentDistrib
import Mathlib.Tactic

/-! # Floor and ceiling bounds

The arithmetic step in the proof of CCR25 Lemma B.1 concerns a floor/ceiling split of a natural number. -/

public section

namespace Critical2DKPZ.Errata.CCR25

open Critical2DKPZ MeasureTheory

/-- For nonzero `c`, an integrable mean-one partition function gives distinct laws for `c * (Z - 1)` and `c * Z`. -/
theorem ccr25_03_printed_uncentred_law_false
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (hZ : Integrable Z P) (c : ℝ) (hc : c ≠ 0)
    (hmean : ∫ ω, Z ω ∂P = 1) :
    ¬ ProbabilityTheory.IdentDistrib
      (fun ω => c * (Z ω - 1)) (fun ω => c * Z ω) P P := by
  intro hlaw
  have hone : Integrable (fun _ : Ω => (1 : ℝ)) P := integrable_const 1
  have hcenter : ∫ ω, c * (Z ω - 1) ∂P = 0 := by
    rw [integral_const_mul, integral_sub hZ hone, hmean]
    simp [probReal_univ]
  have huncentered : ∫ ω, c * Z ω ∂P = c := by
    rw [integral_const_mul, hmean]
    simp
  have hEq := hlaw.integral_eq
  rw [hcenter, huncentered] at hEq
  exact hc (by linarith)

/-- At unit parameters, the lattice point `(8, 0)` lies in the proposed level-set ball but has Gaussian value below `exp(-1)`. -/
theorem ccr25_09_printed_level_set_identity_false :
    let y : Plane := EuclideanSpace.single 0 (8 : ℝ)
    let s : ℝ := Real.exp (-1)
    ¬ ((s ≤ Real.exp (-‖y‖ ^ 2 / 16)) ↔
      ‖y‖ ≤ 16 * Real.log (1 / s)) := by
  dsimp
  have hy : ‖(EuclideanSpace.single 0 (8 : ℝ) : Plane)‖ = 8 := by
    simp [EuclideanSpace.single]
  have hslog : Real.log (1 / Real.exp (-1)) = 1 := by
    rw [one_div, ← Real.exp_neg, Real.log_exp]
    norm_num
  rw [hy, hslog]
  have hright : (8 : ℝ) ≤ 16 * 1 := by norm_num
  intro h
  have hbad := h.mpr hright
  norm_num at hbad

private theorem exp_neg_le_rational_tail (u : ℝ) (hu : 0 ≤ u) :
    Real.exp (-u) ≤ 256 / (1 + u ^ 2) ^ 2 := by
  have hlin : 1 + u / 4 ≤ Real.exp (u / 4) := by
    simpa [add_comm] using Real.add_one_le_exp (u / 4)
  have hexp : (1 + u / 4) ^ 4 ≤ Real.exp u := by
    calc
      (1 + u / 4) ^ 4 ≤ Real.exp (u / 4) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hlin 4
      _ = Real.exp u := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hbase₁ : 1 + u ^ 2 ≤ (1 + u) ^ 2 := by nlinarith
  have hbase₂ : 1 + u ≤ 4 * (1 + u / 4) := by nlinarith
  have hpoly : (1 + u ^ 2) ^ 2 ≤ 256 * (1 + u / 4) ^ 4 := by
    calc
      (1 + u ^ 2) ^ 2 ≤ ((1 + u) ^ 2) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hbase₁ 2
      _ = (1 + u) ^ 4 := by ring
      _ ≤ (4 * (1 + u / 4)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbase₂ 4
      _ = 256 * (1 + u / 4) ^ 4 := by norm_num [mul_pow]
  have hrecip : (Real.exp u)⁻¹ ≤ ((1 + u / 4) ^ 4)⁻¹ :=
    (inv_le_inv₀ (Real.exp_pos u) (pow_pos (by positivity) 4)).2 hexp
  have hrecipPoly : ((1 + u / 4) ^ 4)⁻¹ ≤ 256 / (1 + u ^ 2) ^ 2 := by
    apply (le_div_iff₀ (by positivity : 0 < (1 + u ^ 2) ^ 2)).2
    calc
      ((1 + u / 4) ^ 4)⁻¹ * (1 + u ^ 2) ^ 2 ≤
          ((1 + u / 4) ^ 4)⁻¹ * (256 * (1 + u / 4) ^ 4) :=
        mul_le_mul_of_nonneg_left hpoly (inv_nonneg.mpr (pow_pos (by positivity) 4).le)
      _ = 256 := by field_simp
  rw [Real.exp_neg]
  exact hrecip.trans hrecipPoly

private theorem exp_neg_site_summable :
    Summable (fun z : Site => Real.exp (-((14 : ℝ) * ‖siteToPlane z‖))) := by
  obtain ⟨hpoly, _⟩ := MomentBounds.lattice_rpow_sum_bound
    (L := 1) (r := 2) (by norm_num) (by norm_num)
  let g : Site → ℝ := fun z => 256 * (1 + ‖siteToPlane z‖ ^ 2) ^ (-(2 : ℝ))
  have hgbase : Summable (fun z : Site => (1 + ‖siteToPlane z‖ ^ 2) ^ (-(2 : ℝ))) := by
    simpa using hpoly
  have hg : Summable g := by simpa [g] using hgbase.mul_left 256
  apply hg.of_nonneg_of_le (fun z => (Real.exp_pos _).le)
  intro z
  have hx : 0 ≤ ‖siteToPlane z‖ := norm_nonneg _
  have htail := exp_neg_le_rational_tail (14 * ‖siteToPlane z‖) (by positivity)
  have hden : 1 + ‖siteToPlane z‖ ^ 2 ≤ 1 + (14 * ‖siteToPlane z‖) ^ 2 := by nlinarith
  have hpow : (1 + ‖siteToPlane z‖ ^ 2) ^ 2 ≤
      (1 + (14 * ‖siteToPlane z‖) ^ 2) ^ 2 := by nlinarith
  have hrat : 256 / (1 + (14 * ‖siteToPlane z‖) ^ 2) ^ 2 ≤
      256 / (1 + ‖siteToPlane z‖ ^ 2) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hpow
  calc
    Real.exp (-((14 : ℝ) * ‖siteToPlane z‖)) ≤
        256 / (1 + (14 * ‖siteToPlane z‖) ^ 2) ^ 2 := htail
    _ ≤ 256 / (1 + ‖siteToPlane z‖ ^ 2) ^ 2 := hrat
    _ = g z := by
      simp [g, div_eq_mul_inv]

/-- At `q = 2` and `t = 7`, the squared lattice-sum bound is smaller than its origin term. -/
theorem ccr25_08_printed_weight_bound_false :
    ¬ (∑' z : Site, Real.exp (-((14 : ℝ) * ‖siteToPlane z‖))) ≤ 36 / 49 := by
  intro hbound
  have hsum := exp_neg_site_summable
  have hzero : siteToPlane (0 : Site) = 0 := by
    ext i
    simp [siteToPlane]
  have hterm : Real.exp (-((14 : ℝ) * ‖siteToPlane (0 : Site)‖)) = 1 := by
    simp [hzero]
  have hlower : 1 ≤ ∑' z : Site, Real.exp (-((14 : ℝ) * ‖siteToPlane z‖)) := by
    rw [← hterm]
    exact hsum.le_tsum 0 (fun z _ => (Real.exp_pos _).le)
  have hfalse : (1 : ℝ) ≤ 36 / 49 := hlower.trans hbound
  norm_num at hfalse

/-- The same counterexample in the exact `q = 2` norm form of the source. -/
theorem ccr25_08_printed_q2_t7_norm_bound_false :
    ¬ Real.sqrt (∑' z : Site, Real.exp (-((14 : ℝ) * ‖siteToPlane z‖))) ≤ 6 / 7 := by
  intro hbound
  have hsum := exp_neg_site_summable
  have hzero : siteToPlane (0 : Site) = 0 := by
    ext i
    simp [siteToPlane]
  have hterm : Real.exp (-((14 : ℝ) * ‖siteToPlane (0 : Site)‖)) = 1 := by
    simp [hzero]
  have hlower : 1 ≤ ∑' z : Site, Real.exp (-((14 : ℝ) * ‖siteToPlane z‖)) := by
    rw [← hterm]
    exact hsum.le_tsum 0 (fun z _ => (Real.exp_pos _).le)
  have hnonneg : 0 ≤ ∑' z : Site, Real.exp (-((14 : ℝ) * ‖siteToPlane z‖)) :=
    (tsum_nonneg fun z => (Real.exp_pos _).le)
  have hsqrt0 := Real.sqrt_nonneg
    (∑' z : Site, Real.exp (-((14 : ℝ) * ‖siteToPlane z‖)))
  have hsq : (Real.sqrt (∑' z : Site, Real.exp (-((14 : ℝ) * ‖siteToPlane z‖)))) ^ 2 ≤
      (6 / 7 : ℝ) ^ 2 := by nlinarith [hsqrt0, hbound]
  rw [Real.sq_sqrt hnonneg] at hsq
  have hfalse : (1 : ℝ) ≤ 36 / 49 := by nlinarith [hlower, hsq]
  norm_num at hfalse

/-- The maximum of the floor and ceiling halves exceeds the real half at `n = 1`. -/
theorem ccr25_13_printed_half_split_false :
    ¬ (max ((1 : ℕ) / 2) ((1 + 1) / 2) : ℝ) ≤ (1 : ℝ) / 2 := by
  norm_num

/-- The ceiling-adjusted estimate used for the odd case is valid. -/
theorem ccr25_13_corrected_half_split (n : ℕ) :
    max (n / 2) ((n + 1) / 2) ≤ (n + 1) / 2 := by
  apply max_le_iff.mpr
  exact ⟨by omega, le_rfl⟩

end Critical2DKPZ.Errata.CCR25

