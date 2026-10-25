/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Polymer.SummableCovariance
public import Critical2DKPZ.Polymer.SmoothedCovariance
import Mathlib.Tactic

/-! With flat terminal weight, probability initial profiles give unit-mean partition functions and a polarized first-collision identity. -/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace Critical2DKPZ.Polymer

/-- A probability profile is summable. -/
theorem summable_probability_profile (ν : Site → ℝ)
    (hν : ∀ w, 0 ≤ ν w) (hm : (∑' w, ν w) = 1) :
    Summable (fun w => |ν w|) := by
  have h : Summable ν := by
    by_contra hn
    have hz := tsum_eq_zero_of_not_summable hn
    rw [hm] at hz
    exact one_ne_zero hz
  simpa only [abs_of_nonneg (hν _)] using h

/-- A probability-profile average of flat-terminal partition functions has expectation one. -/
theorem integral_profile_flat_probability (β : ℝ) (a b : ℕ) (ν : Site → ℝ)
    (hν : ∀ w, 0 ≤ ν w) (hm : (∑' w, ν w) = 1) :
    (∫ ω, profileP2Fun β a b ν (fun _ => 1) ω ∂disorderLaw) = 1 := by
  rw [integral_profileP2Fun_summable β a b ν (fun _ => 1)
    (summable_probability_profile ν hν hm) 1 zero_le_one (fun _ => by norm_num)]
  simp only [mul_one, tsum_srwKernel]
  exact hm

/-- A partition function with probability initial profile and bounded terminal weight belongs to Lᵖ for every finite exponent. -/
theorem memLp_profile_probability (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (hν : ∀ w, 0 ≤ ν w) (hm : (∑' w, ν w) = 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hf : ∀ z, |f z| ≤ M)
    (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (profileP2Fun β a b ν f) p disorderLaw :=
  memLp_profileP2Fun_summable β a b ν f
    (summable_probability_profile ν hν hm) M hM0 hf p hp

/-- With a probability initial profile and bounded terminal weight, every absolute natural power of the partition function is integrable. -/
theorem integrable_abs_pow_profile_probability (β : ℝ) (a b : ℕ) (ν f : Site → ℝ)
    (hν : ∀ w, 0 ≤ ν w) (hm : (∑' w, ν w) = 1)
    (M : ℝ) (hM0 : 0 ≤ M) (hf : ∀ z, |f z| ≤ M) (k : ℕ) :
    Integrable (fun ω => |profileP2Fun β a b ν f ω| ^ k) disorderLaw := by
  simpa only [Real.norm_eq_abs] using
    (memLp_profile_probability β a b ν f hν hm M hM0 hf k (by simp)).integrable_norm_pow'

/-- The probability-profile product moment has a first-collision formula with a sum over pairs of sites. -/
theorem probability_profile_firstCollision_absolute (β : ℝ) (s n : ℕ) (hs : s ≤ n)
    (ν ν' : Site → ℝ) (hν : ∀ w, 0 ≤ ν w) (hν' : ∀ v, 0 ≤ ν' v)
    (hm : (∑' w, ν w) = 1) (hm' : (∑' v, ν' v) = 1) :
    (∫ ω, profileP2Fun β s n ν (fun _ => 1) ω *
      profileP2Fun β s n ν' (fun _ => 1) ω ∂disorderLaw) - 1 =
      ∑ r ∈ Finset.Icc (s + 1) n, ∑' xy : Site × Site,
        ν xy.1 * ν' xy.2 * srwKernel (2 * (r - s)) (xy.2 - xy.1) *
          sigmaSq β * (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw) := by
  rw [probability_profile_firstCollision β s n hs ν ν'
    (summable_probability_profile ν hν hm) (summable_probability_profile ν' hν' hm') hm hm']
  have h := sum_Icc_shift s (n - s) (fun r =>
    ∑' xy : Site × Site, ν xy.1 * ν' xy.2 *
      srwKernel (2 * (r - s)) (xy.2 - xy.1) * sigmaSq β *
        (∫ ω, pointToPlane β 0 (n - r) 0 ω ^ 2 ∂disorderLaw))
  rw [Nat.add_sub_of_le hs] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro r _
  simp only [Nat.add_sub_cancel_left, Nat.sub_add_eq]


end Critical2DKPZ.Polymer
