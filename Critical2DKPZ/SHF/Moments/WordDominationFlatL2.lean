/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Limit.PolymerSixthMoment
public import Critical2DKPZ.SHF.Limit.FlatBound
import Mathlib.Tactic

/-! # Flat marginal second moments from sixth-moment bounds -/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped CompactlySupported

namespace Critical2DKPZ.SHF.Moments

/-- The flat sixth-moment bound gives an integrable uniform second-moment
bound for every compact marginal cutoff. -/
theorem eventually_flatMarginal_pairing_sq_integral_le (ϑ : ℝ)
    (χ : C_c(Plane, ℝ)) {τ T : ℝ} (hτ : 0 < τ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ s t : ℝ, 0 ≤ s → τ ≤ t - s → t ≤ T →
        Integrable (fun ω =>
          (∫ x, |χ x| ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 2)
          disorderLaw ∧
        ∫ ω,
          (∫ x, |χ x| ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst)) ^ 2
          ∂disorderLaw ≤ C := by
  obtain ⟨C₆, hC₆⟩ := SHF.Limit.polymerMeasure_flat_sixth_moment_le ϑ χ hτ
  let C : ℝ := 1 + max C₆ 0
  refine ⟨C, by positivity, ?_⟩
  filter_upwards [hC₆] with N hN
  intro s t hs hst ht
  let Y : Disorder → ℝ := fun ω =>
    ∫ x, |χ x| ∂((SHF.Limit.polymerMeasure ϑ N s t ω).map Prod.fst)
  have hYnonneg (ω : Disorder) : 0 ≤ Y ω := by
    exact integral_nonneg (fun x => abs_nonneg (χ x))
  have hpow (x : ℝ) (hx : 0 ≤ x) : x ^ 2 ≤ 1 + x ^ 6 := by
    by_cases hx1 : x ≤ 1
    · have hx2 : x ^ 2 ≤ 1 := by
        calc
          x ^ 2 = x * x := by ring
          _ ≤ 1 * 1 := mul_le_mul hx1 hx1 hx (by norm_num)
          _ = 1 := by norm_num
      linarith [pow_nonneg hx 6]
    · have h1x : 1 ≤ x := le_of_not_ge hx1
      have hpow4 : 1 ≤ x ^ 4 := one_le_pow₀ h1x
      calc
        x ^ 2 = x ^ 2 * 1 := by ring
        _ ≤ x ^ 2 * x ^ 4 := mul_le_mul_of_nonneg_left hpow4 (sq_nonneg x)
        _ = x ^ 6 := by ring
        _ ≤ 1 + x ^ 6 := le_add_of_nonneg_left (by norm_num)
  have hY2int : Integrable (fun ω => Y ω ^ 2) disorderLaw := by
    simpa [Y] using
      SHF.Limit.integrable_flat_polymerMeasure_pow ϑ N s t χ 2
  have hY6int : Integrable (fun ω => Y ω ^ 6) disorderLaw := by
    simpa [Y] using
      SHF.Limit.integrable_flat_polymerMeasure_pow ϑ N s t χ 6
  have hsumint : Integrable (fun ω => 1 + Y ω ^ 6) disorderLaw :=
    (integrable_const (1 : ℝ)).add hY6int
  have hpoint (ω : Disorder) : Y ω ^ 2 ≤ 1 + Y ω ^ 6 :=
    hpow (Y ω) (hYnonneg ω)
  have hsecond :
      ∫ ω, Y ω ^ 2 ∂disorderLaw ≤ 1 + max C₆ 0 := by
    calc
      ∫ ω, Y ω ^ 2 ∂disorderLaw ≤ ∫ ω, (1 + Y ω ^ 6) ∂disorderLaw :=
        integral_mono hY2int hsumint hpoint
      _ = 1 + ∫ ω, Y ω ^ 6 ∂disorderLaw := by
        rw [integral_add (integrable_const (1 : ℝ)) hY6int]
        simp
      _ ≤ 1 + max C₆ 0 := by
        have hY6le : ∫ ω, Y ω ^ 6 ∂disorderLaw ≤ max C₆ 0 := by
          exact (show ∫ ω, Y ω ^ 6 ∂disorderLaw ≤ C₆ by
            simpa [Y] using hN s t hs hst ht).trans (le_max_left _ _)
        exact add_le_add_right hY6le 1
  refine ⟨hY2int, ?_⟩
  simpa [C, Y] using hsecond

end Critical2DKPZ.SHF.Moments

end
