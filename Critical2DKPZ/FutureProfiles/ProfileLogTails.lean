/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.FutureProfiles.ConditionalMoments
public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Logarithmic tails of future profiles -/

@[expose] public section

open MeasureTheory
open Critical2DKPZ.Collision
open Critical2DKPZ.OnePoint
open scoped BigOperators

namespace Critical2DKPZ.FutureProfiles

/-- The right tail of a normalized past-measurable profile is bounded by its exponential tail.
Integrability follows from bounded finite support of the past-measurable coefficients. -/
theorem measure_log_profileP2Fun_gt_le (β : ℝ) {a b : ℕ} (hab : a ≤ b)
    (η : Disorder → Site → ℝ) (A : Finset Site) (hsupp : ∀ ω w, w ∉ A → η ω w = 0)
    (hnn : ∀ ω w, 0 ≤ η ω w) (hmass : ∀ ω, ∑ w ∈ A, η ω w = 1)
    (hmeas : ∀ w, Measurable[disorderPast a] (η · w)) (u : ℝ) :
    (disorderLaw {ω | u < Real.log (profileP2Fun β a b (η ω) (fun _ => 1) ω)}).toReal ≤
      Real.exp (-u) := by
  let X : Disorder → ℝ := fun ω => profileP2Fun β a b (η ω) (fun _ => 1) ω
  have hbdd : ∃ M : ℝ, ∀ ω w, |η ω w| ≤ M := by
    refine ⟨1, fun ω w => ?_⟩
    rw [abs_of_nonneg (hnn ω w)]
    by_cases hw : w ∈ A
    · calc
        η ω w ≤ ∑ x ∈ A, η ω x := Finset.single_le_sum (fun x hx => hnn ω x) hw
        _ = 1 := hmass ω
    · rw [hsupp ω w hw]
      norm_num
  have hXint : Integrable X disorderLaw := by
    change Integrable (randomFlatProfilePolymer β a b η) disorderLaw
    exact integrable_randomTerminalProfilePolymer β a b A η (fun _ => 1) hsupp
      hbdd hmeas 1
      (by intro w; simp)
  have hXnonneg : ∀ ω, 0 ≤ X ω := by
    intro ω
    change 0 ≤ profileP2Fun β a b (η ω) (fun _ => 1) ω
    rw [Polymer.profileP2Fun_eq_sum β a b (η ω) (fun _ => 1) A (hsupp ω)]
    simp only [mul_one, Polymer.tsum_pointToPoint]
    exact Finset.sum_nonneg fun w hw =>
      mul_nonneg (hnn ω w) (Polymer.pointToPlane_pos β a (b - a) w ω).le
  have hmean : ∫ ω, X ω ∂disorderLaw = 1 := by
    have h := setIntegral_profileP2Fun_eq_sum β hab η A hsupp hbdd hmeas Set.univ
      MeasurableSet.univ
    simpa [X, hmass] using h
  let Y : Disorder → ℝ := fun ω => X ω * Real.exp (-u)
  have hYint : Integrable Y disorderLaw := by
    dsimp [Y]
    exact hXint.mul_const _
  have hYnonneg : 0 ≤ᵐ[disorderLaw] Y :=
    Filter.Eventually.of_forall fun ω => mul_nonneg (hXnonneg ω) (Real.exp_nonneg _)
  have hYmean : ∫ ω, Y ω ∂disorderLaw = Real.exp (-u) := by
    simp only [Y, integral_mul_const, hmean, one_mul]
  let S : Set Disorder := {ω | u < Real.log (X ω)}
  have hYbound : ∀ ω ∈ S, 1 ≤ Y ω := by
    intro ω hω
    have hXpos : 0 < X ω := by
      dsimp [X]
      exact profileP2Fun_pos_of_normalized β a b (η ω) A (hsupp ω) (hnn ω) (hmass ω) ω
    have hExp : Real.exp u < X ω := (Real.lt_log_iff_exp_lt hXpos).mp hω
    calc
      1 = Real.exp u * Real.exp (-u) := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      _ ≤ X ω * Real.exp (-u) := mul_le_mul_of_nonneg_right hExp.le (Real.exp_nonneg _)
      _ = Y ω := rfl
  have hmarkov : disorderLaw S ≤ ENNReal.ofReal (∫ ω, Y ω ∂disorderLaw) :=
    hYint.measure_le_integral hYnonneg hYbound
  have hbound : disorderLaw S ≤ ENNReal.ofReal (Real.exp (-u)) := by
    simpa only [hYmean] using hmarkov
  calc
    (disorderLaw S).toReal ≤ (ENNReal.ofReal (Real.exp (-u))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    _ = Real.exp (-u) := ENNReal.toReal_ofReal (Real.exp_pos _).le

end Critical2DKPZ.FutureProfiles

end
