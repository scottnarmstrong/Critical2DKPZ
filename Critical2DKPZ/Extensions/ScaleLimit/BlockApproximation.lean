/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.BlockEstimates
import Critical2DKPZ.Extensions.ScaleLimit.BlockLogBounds
import Critical2DKPZ.Extensions.ScaleLimit.FourthMomentUnion
import Mathlib.Tactic

/-! # Uniform logarithmic block approximation of the heat-start field -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped ENNReal

namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The heat-start logarithm is approximated by its independent bounded block
sum, with constants uniform in both block indices and in the tail level. -/
theorem block_approximation (ϑ : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hZ : IsCriticalSHF ϑ P Z) :
    ∃ ρ₀ : ℝ, 1 < ρ₀ ∧ ∀ ρ : ℝ, ρ₀ ≤ ρ → ∃ (C : ℝ) (ℓ₀ : ℕ),
      0 ≤ C ∧ 1 ≤ ℓ₀ ∧ ∀ n ℓ : ℕ, ℓ₀ ≤ ℓ → ℓ < n → ∀ u : ℝ, 0 ≤ u →
        P {ω | (ℓ : ℝ) * Real.log 2 + Real.log 2 + u <
          |Fheat Z (tau ρ n) 0 ω - partialSum Z ρ n ω|} ≤
            ENNReal.ofReal (C / ℓ + (1 + C * ℓ) * Real.exp (-u)) := by
  obtain ⟨ρ₀, hρ₀, hB⟩ := block_estimates ϑ P Z hZ
  refine ⟨ρ₀, hρ₀, ?_⟩
  intro ρ hρ
  have hρ1 : 1 < ρ := hρ₀.trans_le hρ
  obtain ⟨C, ℓ₀, hC0, hℓ₀, hM, hT⟩ := hB ρ hρ
  refine ⟨18 * C, by exact ℓ₀, by positivity, hℓ₀, ?_⟩
  intro n ℓ hℓ hℓn u hu
  have hℓ1 : 1 ≤ ℓ := hℓ₀.trans hℓ
  let E : Set Ω := {ω | ∃ j ∈ Finset.Ioc ℓ n, 1 / 2 < |blockMass Z ρ j ω - 1|}
  let R : Set Ω := {ω | 1 / 2 < |blockR Z ρ n ℓ ω - 1|}
  let Qlo : Set Ω := {ω | blockQ Z ρ n ℓ ω < Real.exp (-u)}
  let Qhi : Set Ω := {ω | Real.exp u < blockQ Z ρ n ℓ ω}
  have hbad : P.real E ≤ 16 * C / ℓ := by
    apply fourth_moment_union_bound P (fun j ω => blockMass Z ρ j ω - 1) _ hC0 _ _ hℓ1 hℓn.le
    · intro j hj
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      exact (measurable_blockMass ϑ P Z hZ hρ1 k).sub_const 1
    · intro j hj
      exact (hM j hj).2.1
    · intro j hj
      exact (hM j hj).2.2.2
  have hRt := (hT n ℓ hℓ hℓn).1
  have hQt := (hT n ℓ hℓ hℓn).2 u hu
  have hR : P.real R ≤ C / ℓ := ENNReal.toReal_le_of_le_ofReal (by positivity) hRt
  have hQlo : P.real Qlo ≤ C / ℓ + C * ℓ * Real.exp (-u) :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hQt.1
  have hQhi : P.real Qhi ≤ Real.exp (-u) :=
    ENNReal.toReal_le_of_le_ofReal (Real.exp_nonneg _) hQt.2
  let A : Set Ω := {ω | (ℓ : ℝ) * Real.log 2 + Real.log 2 + u <
    |Fheat Z (tau ρ n) 0 ω - partialSum Z ρ n ω|}
  have hsubset : A ≤ᵐ[P] ((E ∪ R) ∪ Qlo) ∪ Qhi := by
    filter_upwards [block_log_decomposition ϑ P Z hZ hρ1 hℓn] with ω hdec
    intro hω
    by_contra he
    change ¬ (((ω ∈ E ∨ ω ∈ R) ∨ ω ∈ Qlo) ∨ ω ∈ Qhi) at he
    simp only [not_or] at he
    have hb (j : ℕ) (hj : j ∈ Finset.Ioc ℓ n) : |blockMass Z ρ j ω - 1| ≤ 1 / 2 :=
      not_lt.mp (fun ht => he.1.1.1 ⟨j, hj, ht⟩)
    have hr : |blockR Z ρ n ℓ ω - 1| ≤ 1 / 2 := not_lt.mp he.1.1.2
    have hl : Real.exp (-u) ≤ blockQ Z ρ n ℓ ω := not_lt.mp he.1.2
    have hh : blockQ Z ρ n ℓ ω ≤ Real.exp u := not_lt.mp he.2
    exact (not_lt_of_ge (block_error_le_of_good Z ρ hℓn.le ω hdec hb hr hl hh)) hω
  have hreal : P.real A ≤ 18 * C / ℓ + (1 + 18 * C * ℓ) * Real.exp (-u) := by
    calc
      _ ≤ P.real (((E ∪ R) ∪ Qlo) ∪ Qhi) :=
        ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsubset)
      _ ≤ P.real ((E ∪ R) ∪ Qlo) + P.real Qhi := measureReal_union_le _ _
      _ ≤ (P.real (E ∪ R) + P.real Qlo) + P.real Qhi :=
        add_le_add (measureReal_union_le _ _) le_rfl
      _ ≤ ((P.real E + P.real R) + P.real Qlo) + P.real Qhi :=
        add_le_add (add_le_add (measureReal_union_le _ _) le_rfl) le_rfl
      _ ≤ ((16 * C / ℓ + C / ℓ) + (C / ℓ + C * ℓ * Real.exp (-u))) + Real.exp (-u) :=
        add_le_add (add_le_add (add_le_add hbad hR) hQlo) hQhi
      _ ≤ _ := by
        have hp := mul_nonneg (mul_nonneg hC0 (Nat.cast_nonneg ℓ)) (Real.exp_nonneg (-u))
        rw [show 18 * C / (ℓ : ℝ) = 16 * C / ℓ + C / ℓ + C / ℓ by ring]
        nlinarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top P A)]
  exact ENNReal.ofReal_le_ofReal hreal

end Critical2DKPZ.Extensions.ScaleLimit
