/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.ScaleLimit.RemainderWeights
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Exact inverse-square weight budgets on finite radius windows -/

@[expose] public section
noncomputable section
open MeasureTheory
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- The inverse-square weight has an explicit interval integral. -/
theorem remainder_weight_Icc {a α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    IntegrableOn (fun r : ℝ => a / r ^ 2) (Set.Icc α β) ∧
      (∫ r in Set.Icc α β, a / r ^ 2) = a / α - a / β := by
  obtain ⟨hi, hInt⟩ := remainder_weight_integral (a := a) hα
  have hβ : 0 < β := hα.trans_le hαβ
  have hsub : Set.Ioi β ⊆ Set.Ioi α := fun t ht => hαβ.trans_lt ht
  have hd : Set.Ioi α \ Set.Ioi β = Set.Ioc α β := by
    ext t
    simp only [Set.mem_sdiff, Set.mem_Ioi, Set.mem_Ioc, not_lt]
  have hh := setIntegral_sdiff measurableSet_Ioi hi hsub
  rw [hd, ← integral_Icc_eq_integral_Ioc, hInt, (remainder_weight_integral (a := a) hβ).2] at hh
  refine ⟨?_, hh⟩
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  exact hi.mono_set (fun _ ht => ht.1)

/-- The total weight is positive in a nondegenerate positive window and is
bounded by its half-line budget. -/
theorem remainder_weight_Icc_budget {a α β : ℝ} (ha : 0 < a) (hα : 0 < α) (hαβ : α < β) :
    0 < (∫ r in Set.Icc α β, a / r ^ 2) ∧
      (∫ r in Set.Icc α β, a / r ^ 2) ≤ a / α := by
  rw [(remainder_weight_Icc hα hαβ.le).2]
  have hβ : 0 < β := hα.trans hαβ
  constructor
  · exact sub_pos.mpr ((div_lt_div_iff_of_pos_left ha hβ hα).mpr hαβ)
  · exact sub_le_self _ (div_pos ha hβ).le

end Critical2DKPZ.Extensions.ScaleLimit
