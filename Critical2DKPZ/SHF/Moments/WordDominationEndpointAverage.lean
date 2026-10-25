/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Flow.WalkEndpointTail
import Mathlib.Tactic

/-! # Endpoint averaging for the compact terminal profile -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Moments

open Critical2DKPZ.Polymer Critical2DKPZ.SHF.Flow

/-- A walk of at most `N` steps, started inside a scaled ball of radius `R`,
lands inside the concentric ball of radius `R + 2` with probability at least
one half. The estimate is uniform in the starting site, including sites near
the boundary of the smaller ball. -/
theorem srwKernel_scaledEndpointInside_ball_ge_half {N k : ℕ}
    (hN : 0 < N) (hk : k ≤ N) (a : Site) (R : ℝ)
    (hstart : ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane a‖ ≤ R) :
    (1 / 2 : ℝ) ≤
      ∑ z ∈ endpoints a k,
        (if ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ≤ R + 2 then
          srwKernel k (z - a) else 0) := by
  let c : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹
  let D : Finset Site := endpoints a k
  let q : Site → ℝ := fun z => srwKernel k (z - a)
  let d : Site → ℝ := fun z =>
    ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z - a)‖
  let f : Site → ℝ := fun z => ‖c • siteToPlane z‖
  have hc : c > 0 := by
    dsimp [c]
    exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))
  have htail :
      (∑ z ∈ D, (if 2 < d z then q z else 0)) ≤ (1 / 2 : ℝ) := by
    have hkreal₀ : (k : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast hk
    have hkreal : (k : ℝ) ≤ (1 : ℝ) * (N : ℝ) := by
      simpa using hkreal₀
    have h := srwKernel_scaledEndpointTail_le a N k 1 2 hN hkreal (by norm_num)
    norm_num at h
    simpa [D, q, d] using h
  have hmass : ∑ z ∈ D, q z = 1 := by
    simpa [D, q] using Polymer.sum_srwKernel_endpoints k a
  have hsplit :
      (∑ z ∈ D, (if d z ≤ 2 then q z else 0)) +
          (∑ z ∈ D, (if 2 < d z then q z else 0)) = 1 := by
    calc
      _ = ∑ z ∈ D,
          ((if d z ≤ 2 then q z else 0) + (if 2 < d z then q z else 0)) := by
            rw [Finset.sum_add_distrib]
      _ = ∑ z ∈ D, q z := by
            apply Finset.sum_congr rfl
            intro z hz
            by_cases hz' : d z ≤ 2
            · simp [hz']
            · have hz'' : 2 < d z := lt_of_not_ge hz'
              simp [hz', hz'']
      _ = 1 := hmass
  have hnear : (1 / 2 : ℝ) ≤ ∑ z ∈ D, (if d z ≤ 2 then q z else 0) := by
    linarith
  have hscaled_add (z : Site) : c • siteToPlane z = c • siteToPlane (z - a) + c • siteToPlane a := by
    have hsite : siteToPlane z = siteToPlane (z - a) + siteToPlane a := by
      ext i
      simp [siteToPlane]
    rw [hsite, smul_add]
  have hinside (z : Site) (hz : d z ≤ 2) : f z ≤ R + 2 := by
    change ‖c • siteToPlane z‖ ≤ R + 2
    rw [hscaled_add z]
    calc
      ‖c • siteToPlane (z - a) + c • siteToPlane a‖ ≤
          ‖c • siteToPlane (z - a)‖ + ‖c • siteToPlane a‖ := norm_add_le _ _
      _ ≤ 2 + R := add_le_add hz hstart
      _ = R + 2 := by ring
  calc
    (1 / 2 : ℝ) ≤ ∑ z ∈ D, (if d z ≤ 2 then q z else 0) := hnear
    _ ≤ ∑ z ∈ D, (if f z ≤ R + 2 then q z else 0) := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hz' : d z ≤ 2
      · have hf := hinside z hz'
        simp [hz', hf]
      · by_cases hf : f z ≤ R + 2
        · have hq : 0 ≤ q z := Polymer.kernel_nonneg k (z - a)
          simp [hz', hf, hq]
        · simp [hz', hf]
    _ = ∑ z ∈ endpoints a k,
        (if ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane z‖ ≤ R + 2 then
          srwKernel k (z - a) else 0) := by
      simp [D, q, f, c]


end Critical2DKPZ.SHF.Moments

end
