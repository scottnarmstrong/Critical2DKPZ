/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.Inputs
public import Critical2DKPZ.SHF.Tsai.BlockMoments
import Mathlib.Tactic

/-! # Moment and independence data for three consecutive SHF increments -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory
open Critical2DKPZ.SHF.Tsai

namespace Critical2DKPZ.NonGaussian

/-- Three consecutive SHF increments at nonnegative times have the prescribed delta-Bose moments
and are mutually independent. -/
theorem threeConsecutive_moments_independent_of_dense (ϑ : ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℝ → ℝ → Ω → Measure (Plane × Plane)) (hdense : DenseSHFAt ϑ P Z)
    {r s t u : ℝ} (hr : 0 ≤ r) (hrs : r < s) (hst : s < t) (htu : t < u) :
    (HasDeltaBoseMoments (ϑ - Real.eulerMascheroniConstant) (s - r) P (Z r s) ∧
      HasDeltaBoseMoments (ϑ - Real.eulerMascheroniConstant) (t - s) P (Z s t) ∧
      HasDeltaBoseMoments (ϑ - Real.eulerMascheroniConstant) (u - t) P (Z t u)) ∧
    iIndepFun (fun k : Fin 3 => if (k : ℕ) = 0 then Z r s else if (k : ℕ) = 1 then Z s t else Z t u) P := by
  let a : Fin 4 → ℝ := ![r, s, t, u]
  have ha : StrictMono a := by
    apply Fin.strictMono_iff_lt_succ.2
    intro i
    fin_cases i
    · exact hrs
    · exact hst
    · exact htu
  have hnonneg : ∀ z ∈ Set.range a, 0 ≤ z := by
    rintro z ⟨i, rfl⟩
    exact hr.trans (ha.monotone (Fin.zero_le i))
  have hD := hdense (Set.range a) (Set.countable_range a) hnonneg
  have hm (i : Fin 3) := hD.hasDeltaBoseMoments
    (Set.mem_range_self i.castSucc) (Set.mem_range_self i.succ) (ha i.castSucc_lt_succ)
  refine ⟨⟨hm 0, hm 1, hm 2⟩, ?_⟩
  have hind := hD.2.2.1 3 a ha (fun i => Set.mem_range_self i)
  convert hind using 1
  funext k
  fin_cases k <;> rfl

end Critical2DKPZ.NonGaussian

end
