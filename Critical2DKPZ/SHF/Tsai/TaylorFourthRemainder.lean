/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Fourth-order Taylor remainder bounds

A uniform fourth-derivative bound controls the cubic Taylor remainder with coefficient
`1/24`, and coordinate fourth powers control the fourth power of the supremum norm.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Critical2DKPZ.SHF.Tsai

/-- A global fourth derivative bound controls the remainder after the cubic Taylor polynomial. -/
theorem abs_sub_cubicTaylor_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : E → ℝ) (hH : ContDiff ℝ 4 H) (CH : ℝ)
    (hCH : ∀ x, ‖iteratedFDeriv ℝ 4 H x‖ ≤ CH) (x v : E) :
    |H (x + v) - ∑ k ∈ Finset.range 4,
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => v)| ≤ CH / 24 * ‖v‖ ^ 4 := by
  let R (t : ℝ) := (1 - t) ^ 3 * iteratedFDeriv ℝ 4 H (x + t • v) (fun _ => v)
  have hpath : Continuous (fun t : ℝ => x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hD : Continuous (fun t : ℝ => iteratedFDeriv ℝ 4 H (x + t • v) (fun _ => v)) :=
    ((hH.continuous_iteratedFDeriv (by norm_num)).comp hpath).eval_const _
  have hR : Continuous R := ((continuous_const.sub continuous_id).pow 3).mul hD
  have hRI : IntervalIntegrable R volume 0 1 := hR.intervalIntegrable _ _
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖R t‖ ≤ (1 - t) ^ 3 * (CH * ‖v‖ ^ 4) := by
    have hval : ‖iteratedFDeriv ℝ 4 H (x + t • v) (fun _ => v)‖ ≤ CH * ‖v‖ ^ 4 := by
      have h := (iteratedFDeriv ℝ 4 H (x + t • v)).le_opNorm (fun _ => v)
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
      exact h.trans (mul_le_mul_of_nonneg_right (hCH _) (pow_nonneg (norm_nonneg _) _))
    dsimp only [R]
    rw [norm_mul, Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _)]
    exact mul_le_mul_of_nonneg_left hval (pow_nonneg (sub_nonneg.mpr ht.2) _)
  have hBI : IntervalIntegrable (fun t : ℝ => (1 - t) ^ 3 * (CH * ‖v‖ ^ 4)) volume 0 1 :=
    ((((continuous_const.sub continuous_id).pow 3).mul continuous_const).intervalIntegrable _ _)
  have hI := intervalIntegral.norm_integral_le_of_norm_le (f := R) (by norm_num : (0 : ℝ) ≤ 1)
    (Filter.Eventually.of_forall fun t ht => hbound t ⟨ht.1.le, ht.2⟩) hBI
  have hpoly : (∫ t : ℝ in 0..1, (1 - t) ^ 3) = (1 / 4 : ℝ) := by
    rw [intervalIntegral.integral_comp_sub_left (f := fun t : ℝ => t ^ 3) 1]
    norm_num [integral_pow]
  rw [intervalIntegral.integral_mul_const, hpoly] at hI
  have hTaylor := map_add_eq_sum_add_integral_iteratedFDeriv (n := 3) (x := x) (y := v)
    (f := H) (fun t _ => hH.contDiffAt)
  have heq : H (x + v) - ∑ k ∈ Finset.range 4,
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => v) =
        (1 / 6 : ℝ) * ∫ t in 0..1, R t := by
    have hT : H (x + v) = (∑ k ∈ Finset.range 4,
        (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => v)) +
          (1 / 6 : ℝ) * ∫ t in 0..1, R t := by
      simpa only [show (3 + 1 : ℕ) = 4 from rfl, show (3 : ℕ).factorial = 6 from rfl,
        Nat.cast_ofNat, smul_eq_mul, one_div, R] using hTaylor
    linarith [hT]
  rw [heq, abs_mul]
  have hmul := mul_le_mul_of_nonneg_left hI (by norm_num : (0 : ℝ) ≤ 1 / 6)
  simpa only [Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 6)] using
    hmul.trans_eq (by ring)

/-- The fourth power of the finite-dimensional supremum norm is bounded by coordinate fourth powers. -/
theorem norm_pow_four_le_sum {m : ℕ} (v : Fin m → ℝ) :
    ‖v‖ ^ 4 ≤ ∑ i, v i ^ 4 := by
  classical
  by_cases hm : m = 0
  · subst m
    have hv : v = 0 := Subsingleton.elim _ _
    simp only [hv, norm_zero, zero_pow (by decide : 4 ≠ 0), Finset.univ_eq_empty, Finset.sum_empty]
    exact le_rfl
  · let : Nonempty (Fin m) := ⟨⟨0, Nat.pos_of_ne_zero hm⟩⟩
    obtain ⟨i, _, hi⟩ := (Finset.univ : Finset (Fin m)).exists_mem_eq_sup
      Finset.univ_nonempty (fun i => ‖v i‖₊)
    have hnorm : ‖v‖ = ‖v i‖ := by
      rw [Pi.norm_def, hi]
      rfl
    rw [hnorm, Real.norm_eq_abs, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ v i ^ 4)]
    exact Finset.single_le_sum (f := fun j : Fin m => v j ^ 4)
      (fun j _ => by positivity) (Finset.mem_univ i)

/-- The cubic Taylor remainder is controlled by the sum of coordinate fourth powers. -/
theorem abs_sub_cubicTaylor_le_sum_four {m : ℕ} (H : (Fin m → ℝ) → ℝ)
    (hH : ContDiff ℝ 4 H) (CH : ℝ) (hCH : ∀ x, ‖iteratedFDeriv ℝ 4 H x‖ ≤ CH)
    (x v : Fin m → ℝ) :
    |H (x + v) - ∑ k ∈ Finset.range 4,
      (k.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ k H x (fun _ => v)| ≤ CH / 24 * ∑ i, v i ^ 4 := by
  have hCH0 : 0 ≤ CH := (norm_nonneg (iteratedFDeriv ℝ 4 H 0)).trans (hCH 0)
  exact (abs_sub_cubicTaylor_le H hH CH hCH x v).trans
    (mul_le_mul_of_nonneg_left (norm_pow_four_le_sum v) (div_nonneg hCH0 (by norm_num)))

end Critical2DKPZ.SHF.Tsai

end
