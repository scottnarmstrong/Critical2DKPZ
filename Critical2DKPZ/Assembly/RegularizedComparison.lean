/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Analysis.Heat.Basic
public import Critical2DKPZ.Definitions.KpzRegularized
import Mathlib.Tactic

/-! # Deterministic comparison for regularized fields -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

namespace Critical2DKPZ.Assembly

/-- The exponential pairings are comparable by the sup norm of their initial data. -/
theorem shfPairing_comparison {Ω : Type*} (Z : ℝ → ℝ → Ω → Measure (Plane × Plane))
    (t δ : ℝ) (h₀ h₀' : Plane →ᵇ ℝ) (x : Plane) (ω : Ω)
    (hpos : 0 < shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀' y))
      (fun y => heatKernel δ (y - x)) ω)
    (hfin : Integrable (fun p : Plane × Plane =>
      Real.exp (h₀' p.1) * heatKernel δ (p.2 - x)) (Z 0 (t - δ) ω)) :
    Real.exp (-‖h₀ - h₀'‖) *
        shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀' y))
          (fun y => heatKernel δ (y - x)) ω ≤
          shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀ y))
            (fun y => heatKernel δ (y - x)) ω ∧
      shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀ y))
        (fun y => heatKernel δ (y - x)) ω ≤
        Real.exp (‖h₀ - h₀'‖) *
          shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀' y))
            (fun y => heatKernel δ (y - x)) ω := by
  let μ := Z 0 (t - δ) ω
  let m := ‖h₀ - h₀'‖
  let f := fun p : Plane × Plane => Real.exp (h₀' p.1) * heatKernel δ (p.2 - x)
  let r := fun p : Plane × Plane => Real.exp (h₀ p.1 - h₀' p.1)
  let g := fun p : Plane × Plane => Real.exp (h₀ p.1) * heatKernel δ (p.2 - x)
  have hδ : 0 < δ := by
    by_contra hδ
    have hδ' : δ ≤ 0 := le_of_not_gt hδ
    rcases hδ'.eq_or_lt with hzero | hneg
    · subst δ
      have : shfPairing Z 0 (t - 0) (fun y => Real.exp (h₀' y))
          (fun y => heatKernel 0 (y - x)) ω = 0 := by
        simp [shfPairing, heatKernel_zero_time]
      linarith
    · have hnonpos : ∀ p : Plane × Plane, f p ≤ 0 := by
        intro p
        have hden : 2 * Real.pi * δ < 0 :=
          mul_neg_of_pos_of_neg (mul_pos (by norm_num) Real.pi_pos) hneg
        have hpref : (2 * Real.pi * δ)⁻¹ < 0 := inv_lt_zero.mpr hden
        have hexp : 0 < Real.exp (-‖p.2 - x‖ ^ 2 / (2 * δ)) := Real.exp_pos _
        have hfirst : 0 < Real.exp (h₀' p.1) := Real.exp_pos _
        dsimp [f, heatKernel]
        exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hfirst)
          (mul_nonpos_of_nonpos_of_nonneg (le_of_lt hpref) hexp.le)
      have hpair : shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀' y))
          (fun y => heatKernel δ (y - x)) ω ≤ 0 := by
        simpa [shfPairing, μ, f] using (integral_nonpos hnonpos : ∫ p, f p ∂μ ≤ 0)
      linarith
  have hbaseNonneg : ∀ p : Plane × Plane, 0 ≤ f p := by
    intro p
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (heatKernel_nonneg hδ.le (p.2 - x))
  have hratioBound (p : Plane × Plane) : ‖r p‖ ≤ Real.exp m := by
    have hd : |h₀ p.1 - h₀' p.1| ≤ m := by
      simpa [m] using (h₀ - h₀').norm_coe_le_norm p.1
    have hup : h₀ p.1 - h₀' p.1 ≤ m := (abs_le.mp hd).2
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.mpr hup
  have hratioNonneg (p : Plane × Plane) : 0 ≤ r p := le_of_lt (Real.exp_pos _)
  have hratioLower (p : Plane × Plane) : Real.exp (-m) ≤ r p := by
    have hd : |h₀ p.1 - h₀' p.1| ≤ m := by
      simpa [m] using (h₀ - h₀').norm_coe_le_norm p.1
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp hd).1])
  have hratioUpper (p : Plane × Plane) : r p ≤ Real.exp m := by
    have hd : |h₀ p.1 - h₀' p.1| ≤ m := by
      simpa [m] using (h₀ - h₀').norm_coe_le_norm p.1
    exact Real.exp_le_exp.mpr (abs_le.mp hd).2
  have hdecomp (p : Plane × Plane) : g p = r p * f p := by
    dsimp [g, r, f]
    calc
      Real.exp (h₀ p.1) * heatKernel δ (p.2 - x) =
          Real.exp ((h₀ p.1 - h₀' p.1) + h₀' p.1) * heatKernel δ (p.2 - x) := by
            congr 1
            congr 1
            ring
      _ = (Real.exp (h₀ p.1 - h₀' p.1) * Real.exp (h₀' p.1)) *
          heatKernel δ (p.2 - x) := by rw [Real.exp_add]
      _ = Real.exp (h₀ p.1 - h₀' p.1) *
          (Real.exp (h₀' p.1) * heatKernel δ (p.2 - x)) := by ring
  have hlow : ∀ p : Plane × Plane, Real.exp (-m) * f p ≤ g p := by
    intro p
    rw [hdecomp]
    exact mul_le_mul_of_nonneg_right (hratioLower p) (hbaseNonneg p)
  have hhigh : ∀ p : Plane × Plane, g p ≤ Real.exp m * f p := by
    intro p
    rw [hdecomp]
    exact mul_le_mul_of_nonneg_right (hratioUpper p) (hbaseNonneg p)
  have hratioMeas : AEStronglyMeasurable r μ := by
    have hc : Continuous r := by fun_prop
    exact hc.measurable.aestronglyMeasurable
  have hgint : Integrable g μ := by
    have hmul := hfin.bdd_mul hratioMeas (Filter.Eventually.of_forall hratioBound)
    have heq : (fun p : Plane × Plane => r p * f p) = g := by
      funext p
      exact (hdecomp p).symm
    rw [heq] at hmul
    exact hmul
  have hlowInt := integral_mono (hfin.const_mul (Real.exp (-m))) hgint hlow
  have hhighInt := integral_mono hgint (hfin.const_mul (Real.exp m)) hhigh
  constructor
  · simpa [μ, f, g, shfPairing, ← integral_const_mul, m] using hlowInt
  · simpa [μ, f, g, shfPairing, ← integral_const_mul, m] using hhighInt

/-- The logarithmic regularized fields differ by at most the sup norm of their initial data. -/
theorem kpzRegularized_comparison {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (t δ : ℝ) (h₀ h₀' : Plane →ᵇ ℝ)
    (x : Plane) (ω : Ω)
    (hpos : 0 < shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀' y))
      (fun y => heatKernel δ (y - x)) ω)
    (hfin : Integrable (fun p : Plane × Plane =>
      Real.exp (h₀' p.1) * heatKernel δ (p.2 - x)) (Z 0 (t - δ) ω)) :
    |kpzRegularized P Z t δ h₀ x ω - kpzRegularized P Z t δ h₀' x ω| ≤
      ‖h₀ - h₀'‖ := by
  let I := shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀' y))
    (fun y => heatKernel δ (y - x)) ω
  let J := shfPairing Z 0 (t - δ) (fun y => Real.exp (h₀ y))
    (fun y => heatKernel δ (y - x)) ω
  have hcmp := shfPairing_comparison Z t δ h₀ h₀' x ω hpos hfin
  have hcmp' : Real.exp (-‖h₀ - h₀'‖) * I ≤ J ∧
      J ≤ Real.exp (‖h₀ - h₀'‖) * I := by
    simpa [I, J] using hcmp
  have hJpos : 0 < J := by
    have h := hcmp'.1
    dsimp [I, J] at h ⊢
    have he : 0 < Real.exp (-‖h₀ - h₀'‖) := Real.exp_pos _
    nlinarith
  have hloglo : Real.log I - ‖h₀ - h₀'‖ ≤ Real.log J := by
    have h := Real.log_le_log (mul_pos (Real.exp_pos _) hpos) hcmp'.1
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hpos), Real.log_exp] at h
    linarith [h]
  have hloghi : Real.log J ≤ ‖h₀ - h₀'‖ + Real.log I := by
    have h := Real.log_le_log hJpos hcmp'.2
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt hpos), Real.log_exp] at h
    linarith [h]
  have hlogs : |Real.log J - Real.log I| ≤ ‖h₀ - h₀'‖ := by
    rw [abs_le]
    constructor <;> linarith
  have hcancel : kpzRegularized P Z t δ h₀ x ω - kpzRegularized P Z t δ h₀' x ω =
      Real.log J - Real.log I := by
    simp [kpzRegularized, I, J]
  rw [hcancel]
  exact hlogs

end Critical2DKPZ.Assembly

end
