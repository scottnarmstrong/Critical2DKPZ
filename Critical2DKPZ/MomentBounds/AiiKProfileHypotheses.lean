/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.MomentBounds.AiiKNormMGF
public import Critical2DKPZ.MomentBounds.AiiKProfileSpread
public import Critical2DKPZ.MomentBounds.CSZ25Green
public import Critical2DKPZ.MomentBounds.CSZ25ReturnWeights
import Mathlib.Tactic

/-! # Localization and square-sum hypotheses for walk profiles -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.MomentBounds

private theorem summable_srwKernel_finiteSupport (s : ℕ) :
    Summable (fun z : Site => srwKernel s z) := by
  apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 s)
  intro z hz
  have h := Polymer.srwKernel_eq_zero_of_not_mem s 0 z hz
  have hq : srwKernel s z = 0 := by simpa only [sub_zero] using h
  simp [hq]

/-- The simple-walk profile has mass one, exponential localization at every
diffusive scale, and a square-sum bound inverse in its exact spread. -/
theorem srwKernel_profile_hypotheses (κ : ℝ) (hκ : 0 < κ) :
    ∃ t c₁ c₂ : ℝ, 0 < t ∧ 0 < c₁ ∧ 0 < c₂ ∧ ∀ s L : ℕ,
      1 ≤ s → (s : ℝ) ≤ κ * L →
      HasSum (fun y => srwKernel s y) 1 ∧ ExpLocalized t c₁ L (fun y => srwKernel s y) ∧
        ∑' z, srwKernel s z ^ 2 ≤ c₂ / profileSpread (fun y => srwKernel s y) := by
  obtain ⟨c, hc, hmgf⟩ := tsum_exp_mul_norm_srwKernel_le
  obtain ⟨aLo, aHi, haLo, haHi, hreturn⟩ := srwKernel_two_mul_zero_bounds
  let c₁ := c * Real.exp (8 * c * κ)
  have hκ0 : 0 ≤ κ := hκ.le
  refine ⟨1, c₁, aHi, by norm_num, ?_, haLo.trans_le haHi,
    fun s L hs hsmall => ?_⟩
  · dsimp [c₁]
    positivity
  · have hLpos : 0 < (L : ℝ) := by
      by_contra hL
      have hL' : (L : ℝ) = 0 := by
        have hLnonneg : 0 ≤ (L : ℝ) := Nat.cast_nonneg _
        linarith
      have hspos : 0 < (s : ℝ) := by exact_mod_cast (show 0 < s by omega)
      have hsmall0 : (s : ℝ) ≤ 0 := by simpa [hL'] using hsmall
      exact (not_le_of_gt hspos) (by nlinarith [hκ0, hsmall0])
    have hsumT : ∑' y : Site, srwKernel s y = 1 := by
      calc
        ∑' y : Site, srwKernel s y =
            ∑ y ∈ Polymer.endpoints 0 s, srwKernel s y := by
          apply tsum_eq_sum
          intro y hy
          have h := Polymer.srwKernel_eq_zero_of_not_mem s 0 y hy
          have hq : srwKernel s y = 0 := by simpa only [sub_zero] using h
          simp [hq]
        _ = 1 := by simpa only [sub_zero] using Polymer.sum_srwKernel_endpoints s 0
    have hmass : HasSum (fun y : Site => srwKernel s y) 1 :=
      (summable_srwKernel_finiteSupport s).hasSum_iff.mpr hsumT
    let τ := 2 / Real.sqrt (L : ℝ)
    have hτpos : 0 < τ := by dsimp [τ]; positivity
    have hτsq : τ ^ 2 = 4 / (L : ℝ) := by
      dsimp [τ]
      rw [div_pow, Real.sq_sqrt (le_of_lt hLpos)]
      ring
    have hratio : (s : ℝ) / L ≤ κ := (div_le_iff₀ hLpos).2 hsmall
    have harg : 2 * c * τ ^ 2 * s ≤ 8 * c * κ := by
      rw [hτsq]
      have hmul := mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 8 * c)
      have hrewrite : 2 * c * (4 / (L : ℝ)) * s = 8 * c * ((s : ℝ) / L) := by
        field_simp [ne_of_gt hLpos]
        ring
      rw [hrewrite]
      exact hmul
    have hlocalSum :
        ∑' z : Site, srwKernel s z *
            Real.exp (2 * (1 : ℝ) * ‖siteToPlane z - (0 : Plane)‖ / Real.sqrt L) ≤ c₁ := by
      have heq :
          (∑' z : Site, srwKernel s z *
              Real.exp (2 * (1 : ℝ) * ‖siteToPlane z - (0 : Plane)‖ / Real.sqrt L)) =
            ∑' z : Site, Real.exp (τ * ‖siteToPlane z‖) * srwKernel s z := by
        apply tsum_congr
        intro z
        have hargEq : 2 * (1 : ℝ) * ‖siteToPlane z - (0 : Plane)‖ / Real.sqrt L =
            τ * ‖siteToPlane z‖ := by
          simp only [sub_zero]
          dsimp [τ]
          ring
        rw [hargEq]
        ring
      rw [heq]
      have hmgf' := (hmgf τ hτpos.le s).1
      calc
        _ ≤ c * Real.exp (2 * c * τ ^ 2 * s) := hmgf'
        _ ≤ c * Real.exp (8 * c * κ) := by
          apply mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr harg) (by linarith)
        _ = c₁ := by rfl
    have hlocalSummable : Summable (fun z : Site => srwKernel s z *
        Real.exp (2 * (1 : ℝ) * ‖siteToPlane z - (0 : Plane)‖ / Real.sqrt L)) := by
      apply summable_of_ne_finset_zero (s := Polymer.endpoints 0 s)
      intro z hz
      have h := Polymer.srwKernel_eq_zero_of_not_mem s 0 z hz
      have hq : srwKernel s z = 0 := by simpa only [sub_zero] using h
      simp [hq]
    have hlocal : ExpLocalized 1 c₁ L (fun z => srwKernel s z) := by
      refine ⟨0, hlocalSummable, ?_⟩
      simpa only [sub_zero] using hlocalSum
    have hsqReturn : (∑' z : Site, srwKernel s z ^ 2) = srwKernel (2 * s) 0 := by
      simpa [pow_two, sub_zero] using Polymer.srwKernel_collision s 0 0
    have hspread : profileSpread (fun y => srwKernel s y) = s := profileSpread_srwKernel s
    have hsqBound :
        ∑' z : Site, srwKernel s z ^ 2 ≤ aHi / profileSpread (fun y => srwKernel s y) := by
      rw [hsqReturn, hspread]
      exact (hreturn s hs).2
    exact ⟨hmass, hlocal, hsqBound⟩

end Critical2DKPZ.MomentBounds

end
