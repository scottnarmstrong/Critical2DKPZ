/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! # Odd moments controlled by adjacent even moments

Young's inequality bounds the odd moment of an increment by its two adjacent even moments, with odd-moment integrability. -/

public section

open MeasureTheory

namespace Critical2DKPZ.Errata

/-- Adjacent even powers bound the absolute intervening odd power by their arithmetic mean. -/
theorem abs_pow_odd_le_mean_even_powers (x : ℝ) (k : ℕ) :
    |x ^ (2 * k + 1)| ≤ (x ^ (2 * k) + x ^ (2 * k + 2)) / 2 := by
  have he : |x| ^ (2 * k) = x ^ (2 * k) := by
    rw [pow_mul, pow_mul, sq_abs]
  have h := mul_nonneg (pow_nonneg (abs_nonneg x) (2 * k)) (sq_nonneg (|x| - 1))
  calc
    |x ^ (2 * k + 1)| = |x| ^ (2 * k) * |x| := by rw [abs_pow, pow_succ]
    _ ≤ (|x| ^ (2 * k) + |x| ^ (2 * k) * |x| ^ 2) / 2 := by
      nlinarith only [h]
    _ = _ := by rw [he, sq_abs, pow_add]

/-- Young's inequality uses ζ in both even moments and has a finite odd moment. -/
theorem abs_integral_pow_odd_le_mean_even_moments {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ζ : Ω → ℝ) (hζ : AEStronglyMeasurable ζ P) (k : ℕ)
    (hlo : Integrable (fun ω => ζ ω ^ (2 * k)) P)
    (hhi : Integrable (fun ω => ζ ω ^ (2 * k + 2)) P) :
    Integrable (fun ω => ζ ω ^ (2 * k + 1)) P ∧
      |∫ ω, ζ ω ^ (2 * k + 1) ∂P| ≤
        ((∫ ω, ζ ω ^ (2 * k) ∂P) + (∫ ω, ζ ω ^ (2 * k + 2) ∂P)) / 2 := by
  have hb := (hlo.add hhi).div_const 2
  have hpoint (ω : Ω) := abs_pow_odd_le_mean_even_powers (ζ ω) k
  have hodd : Integrable (fun ω => ζ ω ^ (2 * k + 1)) P := by
    have hm : AEStronglyMeasurable (fun ω => ζ ω ^ (2 * k + 1)) P :=
      hζ.pow (2 * k + 1)
    apply hb.mono' hm (Filter.Eventually.of_forall ?_)
    intro ω
    change |ζ ω ^ (2 * k + 1)| ≤ (ζ ω ^ (2 * k) + ζ ω ^ (2 * k + 2)) / 2
    exact hpoint ω
  refine ⟨hodd, ?_⟩
  calc
    _ ≤ ∫ ω, |ζ ω ^ (2 * k + 1)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (ζ ω ^ (2 * k) + ζ ω ^ (2 * k + 2)) / 2 ∂P :=
      integral_mono hodd.abs hb hpoint
    _ = _ := by rw [integral_div, integral_add hlo hhi]

end Critical2DKPZ.Errata
