/-
Copyright 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Sobolev.Localizers
public import Critical2DKPZ.SHF.Tsai.MollifierOperators
public import Critical2DKPZ.SHF.Tsai.HeatMollifier
public import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-! # Compact approximate identities for smoothed composition

A normalized smooth compactly supported density generates the shrinking mollifier sequence. -/

@[expose] public section

open MeasureTheory
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.SHF.Tsai

/-- The normalized smooth compact density obtained from the canonical unit localizer. -/
noncomputable def subseqDenseMollifierBase : Plane → ℝ :=
  Critical2DKPZ.localizerBump 0 |>.normed volume

/-- The base density is nonnegative, smooth, compactly supported, normalized, and square-integrable. -/
theorem subseqDenseMollifierBase_spec :
    (∀ x, 0 ≤ subseqDenseMollifierBase x) ∧
    ContDiff ℝ (⊤ : ℕ∞) subseqDenseMollifierBase ∧
    HasCompactSupport subseqDenseMollifierBase ∧
    (∫ x, subseqDenseMollifierBase x) = 1 ∧
    MemLp subseqDenseMollifierBase 2 := by
  let b := Critical2DKPZ.localizerBump 0
  refine ⟨fun x => b.nonneg_normed x, b.contDiff_normed, b.hasCompactSupport_normed,
    b.integral_normed, ?_⟩
  exact b.continuous_normed.memLp_of_hasCompactSupport b.hasCompactSupport_normed

/-- The mass-preserving rescalings `(n + 1) ^ 2 * b ((n + 1) • x)` of the fixed profile `b`. -/
noncomputable def subseqDenseMollifier (n : ℕ) : Plane → ℝ :=
  fun x => (((n : ℝ) + 1) ^ 2) * subseqDenseMollifierBase (((n : ℝ) + 1) • x)

/-- Every rescaled profile remains smooth, compactly supported, nonnegative, normalized, and in `L²`. -/
theorem subseqDenseMollifier_spec (n : ℕ) :
    (∀ x, 0 ≤ subseqDenseMollifier n x) ∧
    ContDiff ℝ (⊤ : ℕ∞) (subseqDenseMollifier n) ∧
    HasCompactSupport (subseqDenseMollifier n) ∧
    (∫ x, subseqDenseMollifier n x) = 1 ∧
    MemLp (subseqDenseMollifier n) 2 := by
  let a : ℝ := (n : ℝ) + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have ha0 : a ≠ 0 := ha.ne'
  have hd : Module.finrank ℝ Plane = 2 := by
    simp only [Plane, finrank_euclideanSpace, Fintype.card_fin]
  obtain ⟨hb0, hbcd, hbcomp, hbint, hbLp⟩ := subseqDenseMollifierBase_spec
  have hcont : Continuous (subseqDenseMollifier n) := by
    change Continuous (fun x : Plane => a ^ 2 * subseqDenseMollifierBase (a • x))
    exact continuous_const.mul (hbcd.continuous.comp
      ((continuous_const : Continuous fun _ : Plane => a).smul continuous_id))
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (subseqDenseMollifier n) := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : Plane => a ^ 2 * subseqDenseMollifierBase (a • x))
    exact contDiff_const.mul (hbcd.comp
      ((contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : Plane => a).smul contDiff_id))
  have hsupport : HasCompactSupport (subseqDenseMollifier n) := by
    have hcomp : HasCompactSupport (fun x : Plane => subseqDenseMollifierBase (a • x)) :=
      hbcomp.comp_smul ha0
    change HasCompactSupport
      (fun x : Plane => (a ^ 2 : ℝ) • subseqDenseMollifierBase (a • x))
    exact HasCompactSupport.smul_left (f := fun _ : Plane => (a ^ 2 : ℝ)) hcomp
  have hscale := Measure.integral_comp_smul volume subseqDenseMollifierBase a
  rw [hd, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg a)), smul_eq_mul] at hscale
  have hint : (∫ x, subseqDenseMollifier n x) = 1 := by
    change (∫ x, a ^ 2 * subseqDenseMollifierBase (a • x)) = 1
    rw [integral_const_mul, hscale]
    rw [hbint]
    field_simp
  exact ⟨fun x => mul_nonneg (sq_nonneg _) (hb0 _), hcd, hsupport, hint,
    hcont.memLp_of_hasCompactSupport hsupport⟩

/-- Each rescaled profile is bounded by a Gaussian at the same shrinking spatial scale, with one multiplicative constant for all indices. -/
theorem subseqDenseMollifier_le_heatKernel :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x,
      subseqDenseMollifier n x ≤ C * heatKernel
        (1 / (2 * Real.pi * (((n : ℝ) + 1) ^ 2))) x := by
  let R : Plane → ℝ := fun x => subseqDenseMollifierBase x * Real.exp (Real.pi * ‖x‖ ^ 2)
  have hRcont : Continuous R := by
    exact subseqDenseMollifierBase_spec.2.1.continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  have hRcompact : HasCompactSupport R := by
    exact subseqDenseMollifierBase_spec.2.2.1.mul_right
  obtain ⟨C₀, hC₀⟩ := hRcont.bounded_above_of_compact_support hRcompact
  let C : ℝ := max C₀ 0
  refine ⟨C, le_max_right _ _, ?_⟩
  intro n x
  let a : ℝ := (n : ℝ) + 1
  have ha : 0 < a := by dsimp [a]; positivity
  have hscaled : ‖a • x‖ ^ 2 = a ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, mul_pow]
  have hprofile : subseqDenseMollifierBase (a • x) ≤
      C * Real.exp (-(Real.pi * ‖a • x‖ ^ 2)) := by
    have hExp : 0 < Real.exp (Real.pi * ‖a • x‖ ^ 2) := Real.exp_pos _
    have hle : R (a • x) ≤ C :=
      (le_abs_self _).trans ((hC₀ (a • x)).trans (le_max_left _ _))
    have hmul : subseqDenseMollifierBase (a • x) * Real.exp (Real.pi * ‖a • x‖ ^ 2) ≤ C := by
      simpa only [R] using hle
    have hdiv : subseqDenseMollifierBase (a • x) ≤
        C / Real.exp (Real.pi * ‖a • x‖ ^ 2) := (le_div_iff₀ hExp).2 hmul
    calc
      subseqDenseMollifierBase (a • x) ≤
          C / Real.exp (Real.pi * ‖a • x‖ ^ 2) := hdiv
      _ = C * Real.exp (-(Real.pi * ‖a • x‖ ^ 2)) := by
        rw [div_eq_mul_inv, ← Real.exp_neg]
  have hheat : heatKernel (1 / (2 * Real.pi * a ^ 2)) x =
      a ^ 2 * Real.exp (-(Real.pi * ‖a • x‖ ^ 2)) := by
    rw [heatKernel_eq_exp]
    congr 1
    · field_simp
    · rw [hscaled]
      field_simp
  change a ^ 2 * subseqDenseMollifierBase (a • x) ≤
    C * heatKernel (1 / (2 * Real.pi * a ^ 2)) x
  rw [hheat]
  calc
    a ^ 2 * subseqDenseMollifierBase (a • x) ≤
        a ^ 2 * (C * Real.exp (-(Real.pi * ‖a • x‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hprofile (sq_nonneg _)
    _ = C * (a ^ 2 * Real.exp (-(Real.pi * ‖a • x‖ ^ 2))) := by ring

end Critical2DKPZ.SHF.Flow

end
