/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Gaussian.DisorderLaws
import Mathlib.Tactic

/-! # The initial Gaussian slice in lattice time reversal -/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Critical2DKPZ.LocalSobolev

private theorem integral_abs_id_gaussianReal_zero_one_le :
    Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) ∧
    (∫ x : ℝ, |x| ∂gaussianReal 0 1) ≤ 1 := by
  have hidMem : MemLp id (ENNReal.ofReal 2) (gaussianReal 0 1) :=
    by simpa using (memLp_id_gaussianReal' (2 : ℝ≥0∞) (by norm_num) :
      MemLp id (2 : ℝ≥0∞) (gaussianReal 0 1))
  have habsMem : MemLp (fun x : ℝ => |x|) (ENNReal.ofReal 2) (gaussianReal 0 1) := by
    simpa only [id_eq, Real.norm_eq_abs] using hidMem.norm
  have habsInt : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
    habsMem.integrable (by norm_num)
  have hsq : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1) = 1 := by
    have hvarEq := variance_eq_integral (X := fun x : ℝ => x)
      (μ := gaussianReal 0 1) measurable_id'.aemeasurable
    have hvar : Var[fun x : ℝ => x; gaussianReal 0 1] = 1 := by simp
    rw [hvar] at hvarEq
    simpa [integral_id_gaussianReal] using hvarEq.symm
  have honeMem : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2)
      (gaussianReal 0 1) := memLp_const 1
  have honeNonneg : 0 ≤ᵐ[gaussianReal 0 1] (fun _ : ℝ => (1 : ℝ)) :=
    Filter.Eventually.of_forall fun _ => by norm_num
  have habsNonneg : 0 ≤ᵐ[gaussianReal 0 1] (fun x : ℝ => |x|) :=
    Filter.Eventually.of_forall fun x => abs_nonneg x
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := gaussianReal 0 1) (p := (2 : ℝ)) (q := (2 : ℝ)) Real.HolderConjugate.two_two
    honeNonneg habsNonneg honeMem habsMem
  have honeSq : ∫ x : ℝ, (1 : ℝ) ^ 2 ∂gaussianReal 0 1 = 1 := by simp
  have habsSq : (∫ x : ℝ, |x| ^ 2 ∂gaussianReal 0 1) =
      ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => sq_abs x
  refine ⟨habsInt, ?_⟩
  calc
    _ = ∫ x : ℝ, (1 : ℝ) * |x| ∂gaussianReal 0 1 := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun _ => by ring
    _ ≤ (∫ x : ℝ, (1 : ℝ) ^ 2 ∂gaussianReal 0 1) ^ (1 / 2 : ℝ) *
        (∫ x : ℝ, |x| ^ 2 ∂gaussianReal 0 1) ^ (1 / 2 : ℝ) := by
      simpa only [Real.rpow_two] using hHolder
    _ = 1 := by rw [honeSq, habsSq, hsq]; norm_num

/-- The logarithmic Gaussian endpoint correction is integrable, with expected absolute value at most `|β| + β² / 2`. -/
theorem integral_abs_exactReverse_initial_slice_le (β : ℝ) (m : ℕ) (x : Site) :
    Integrable (fun ω => |β * ω (m, x) - β ^ 2 / 2|) disorderLaw ∧
    (∫ ω, |β * ω (m, x) - β ^ 2 / 2| ∂disorderLaw) ≤ |β| + β ^ 2 / 2 := by
  let p : ℕ × Site := (m, x)
  let X : Disorder → ℝ := fun ω => ω p
  have hXlaw := Gaussian.hasLaw_disorder_eval p
  have hIdInt : Integrable id (gaussianReal 0 1) :=
    (memLp_one_iff_integrable).1 (memLp_id_gaussianReal' 1 (by norm_num))
  have hXInt : Integrable X disorderLaw := by
    simpa [X] using hXlaw.integrable hIdInt
  have hXabsInt : Integrable (fun ω => |X ω|) disorderLaw := hXInt.abs
  have hXabsEq : (∫ ω, |X ω| ∂disorderLaw) =
      ∫ z : ℝ, |z| ∂gaussianReal 0 1 := by
    simpa only [X, Function.comp_apply] using
      hXlaw.integral_comp (f := fun z : ℝ => |z|)
        (integral_abs_id_gaussianReal_zero_one_le.1.aestronglyMeasurable)
  have hXabsBound : (∫ ω, |X ω| ∂disorderLaw) ≤ 1 :=
    hXabsEq.trans_le integral_abs_id_gaussianReal_zero_one_le.2
  have hleftInt : Integrable (fun ω => |β * X ω - β ^ 2 / 2|) disorderLaw := by
    have hlin : Integrable (fun ω => β * X ω - β ^ 2 / 2) disorderLaw := by
      exact (hXInt.const_mul β).sub (integrable_const _)
    exact hlin.abs
  have hmulInt : Integrable (fun ω => |β| * |X ω|) disorderLaw := by
    simpa [mul_comm] using hXabsInt.const_mul |β|
  have hconstInt : Integrable (fun _ : Disorder => β ^ 2 / 2) disorderLaw :=
    integrable_const _
  have hrightInt : Integrable (fun ω => |β| * |X ω| + β ^ 2 / 2) disorderLaw :=
    hmulInt.add hconstInt
  have hpoint (ω : Disorder) :
      |β * X ω - β ^ 2 / 2| ≤ |β| * |X ω| + β ^ 2 / 2 := by
    calc
      _ ≤ |β * X ω| + |β ^ 2 / 2| := abs_sub _ _
      _ = |β| * |X ω| + β ^ 2 / 2 := by
        rw [abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg β) (by norm_num))]
  refine ⟨?_, ?_⟩
  · simpa [X, p] using hleftInt
  · have hint := integral_mono hleftInt hrightInt hpoint
    calc
      _ ≤ ∫ ω, |β| * |X ω| + β ^ 2 / 2 ∂disorderLaw := by
        simpa [X, p] using hint
      _ = |β| * (∫ ω, |X ω| ∂disorderLaw) + β ^ 2 / 2 := by
        rw [integral_add hmulInt hconstInt, integral_const_mul]
        simp
      _ ≤ |β| + β ^ 2 / 2 := by
        calc
          _ ≤ |β| * 1 + β ^ 2 / 2 :=
            add_le_add (mul_le_mul_of_nonneg_left hXabsBound (abs_nonneg β)) le_rfl
          _ = _ := by ring

end Critical2DKPZ.LocalSobolev

end
