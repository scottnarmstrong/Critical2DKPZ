/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.EntranceWalkMoments

/-! # Spatial tails for a finite walk segment -/

@[expose] public section

open scoped BigOperators

namespace Critical2DKPZ.SHF.Flow

open Critical2DKPZ.Polymer
open Critical2DKPZ.SHF.Moments

/-- A simple walk started at the origin leaves a large ball with probability at most its
second spatial moment divided by the squared radius. -/
theorem srwKernel_endpointTail_le_secondMoment (n : ℕ) (R : ℝ) (hR : 0 < R) :
    ∑ z ∈ endpoints 0 n,
      (if R < ‖siteToPlane z‖ then srwKernel n z else 0) ≤ (n : ℝ) / R ^ 2 := by
  let E := endpoints (0 : Site) n
  have hR2 : 0 < R ^ 2 := sq_pos_of_pos hR
  have hpoint (z : Site) (hz : z ∈ E) :
      (if R < ‖siteToPlane z‖ then srwKernel n z else 0) ≤
        srwKernel n z * ‖siteToPlane z‖ ^ 2 / R ^ 2 := by
    by_cases htail : R < ‖siteToPlane z‖
    · have hnorm : R ^ 2 ≤ ‖siteToPlane z‖ ^ 2 := by
        nlinarith [sq_nonneg (‖siteToPlane z‖ - R)]
      have hkernel : 0 ≤ srwKernel n z := Polymer.kernel_nonneg n z
      rw [ite_eq_left htail]
      rw [le_div_iff₀ hR2]
      calc
        srwKernel n z * R ^ 2 ≤ srwKernel n z * ‖siteToPlane z‖ ^ 2 :=
          mul_le_mul_of_nonneg_left hnorm hkernel
        _ = srwKernel n z * ‖siteToPlane z‖ ^ 2 := rfl
    · rw [ite_eq_right htail]
      exact div_nonneg
        (mul_nonneg (Polymer.kernel_nonneg n z) (sq_nonneg ‖siteToPlane z‖)) hR2.le
  calc
    _ ≤ ∑ z ∈ E, srwKernel n z * ‖siteToPlane z‖ ^ 2 / R ^ 2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact hpoint z (by simpa only [E] using hz)
    _ = (∑ z ∈ E, srwKernel n z * ‖siteToPlane z‖ ^ 2) / R ^ 2 := by
      rw [Finset.sum_div]
    _ = (n : ℝ) / R ^ 2 := by
      rw [show (∑ z ∈ E, srwKernel n z * ‖siteToPlane z‖ ^ 2) = n by
        simpa only [E] using sum_srwKernel_norm_sq n]

/-- The same endpoint-tail estimate for a translated walk, measured from its starting site. -/
theorem srwKernel_endpointTail_le_secondMoment_start (a : Site) (n : ℕ) (R : ℝ)
    (hR : 0 < R) :
    ∑ z ∈ endpoints a n,
      (if R < ‖siteToPlane (z - a)‖ then srwKernel n (z - a) else 0) ≤ (n : ℝ) / R ^ 2 := by
  classical
  let f : Site → ℝ := fun z => if R < ‖siteToPlane z‖ then srwKernel n z else 0
  have htranslate :
      ∑ z ∈ endpoints a n, f (z - a) = ∑ z ∈ endpoints 0 n, f z := by
    refine Finset.sum_bij (fun z _ => z - a) ?_ ?_ ?_ ?_
    · intro z hz
      obtain ⟨p, hp⟩ := (mem_endpoints_iff a z n).mp hz
      apply (mem_endpoints_iff 0 (z - a) n).mpr
      refine ⟨p, ?_⟩
      rw [Polymer.walkPosition_eq_start_add] at hp ⊢
      have hp' := congrArg (fun x : Site => x - a) hp
      simpa only [add_sub_cancel_left, zero_add] using hp'
    · intro z₁ hz₁ z₂ hz₂ heq
      apply funext
      intro i
      have hi := congrArg (fun x : Site => x i) heq
      simp only [Pi.sub_apply] at hi
      omega
    · intro z hz
      obtain ⟨p, hp⟩ := (mem_endpoints_iff 0 z n).mp hz
      refine ⟨a + z, (mem_endpoints_iff a (a + z) n).mpr ?_, ?_⟩
      · refine ⟨p, ?_⟩
        rw [Polymer.walkPosition_eq_start_add] at ⊢
        have hp' := congrArg (fun x : Site => a + x) hp
        exact hp'
      · simp
    · intro z hz
      rfl
  calc
    _ = ∑ z ∈ endpoints 0 n, f z := htranslate
    _ ≤ (n : ℝ) / R ^ 2 := by
      simpa only [f] using srwKernel_endpointTail_le_secondMoment n R hR

/-- A random-walk segment of at most `T N` steps has a uniform macroscopic endpoint tail
after the polymer scaling `sqrt(N / 2)`. -/
theorem srwKernel_scaledEndpointTail_le (a : Site) (N n : ℕ) (T R : ℝ)
    (hN : 0 < N) (hn : (n : ℝ) ≤ T * N) (hR : 0 < R) :
    ∑ z ∈ endpoints a n,
      (if R < ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z - a)‖ then
        srwKernel n (z - a) else 0) ≤ 2 * T / R ^ 2 := by
  let c : ℝ := (Real.sqrt ((N : ℝ) / 2))⁻¹
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < c := by
    dsimp [c]
    exact inv_pos.mpr (Real.sqrt_pos.2 (by positivity))
  have hcSq : c ^ 2 = 2 / N := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    field_simp
  have hnorm (z : Site) :
      ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z - a)‖ =
        c * ‖siteToPlane (z - a)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hterm (z : Site) :
      (if R < ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z - a)‖ then
          srwKernel n (z - a) else 0) ≤
        (if R / c < ‖siteToPlane (z - a)‖ then srwKernel n (z - a) else 0) := by
    by_cases hz : R < ‖(Real.sqrt ((N : ℝ) / 2))⁻¹ • siteToPlane (z - a)‖
    · have hz' : R / c < ‖siteToPlane (z - a)‖ := by
        rw [hnorm z] at hz
        exact (div_lt_iff₀ hc).2 (by simpa only [mul_comm] using hz)
      rw [ite_eq_left hz, ite_eq_left hz']
    · rw [ite_eq_right hz]
      by_cases hz' : R / c < ‖siteToPlane (z - a)‖
      · rw [ite_eq_left hz']
        have hzmul : R < c * ‖siteToPlane (z - a)‖ :=
          by simpa only [mul_comm] using (div_lt_iff₀ hc).mp hz'
        apply False.elim
        apply hz
        simpa only [hnorm z] using hzmul
      · rw [ite_eq_right hz']
  calc
    _ ≤ ∑ z ∈ endpoints a n,
        (if R / c < ‖siteToPlane (z - a)‖ then srwKernel n (z - a) else 0) := by
      apply Finset.sum_le_sum
      intro z hz
      exact hterm z
    _ ≤ (n : ℝ) / (R / c) ^ 2 :=
      srwKernel_endpointTail_le_secondMoment_start a n (R / c) (div_pos hR hc)
    _ = (n : ℝ) * c ^ 2 / R ^ 2 := by
      field_simp [ne_of_gt hR, ne_of_gt hc]
    _ ≤ 2 * T / R ^ 2 := by
      apply div_le_div_of_nonneg_right _ (sq_nonneg R)
      rw [hcSq]
      have hmul := mul_le_mul_of_nonneg_right hn
        (show 0 ≤ (2 : ℝ) / (N : ℝ) by positivity)
      have hcancel : (T * (N : ℝ)) * (2 / N) = 2 * T := by
        field_simp [ne_of_gt hNr]
      calc
        (n : ℝ) * (2 / N) ≤ (T * (N : ℝ)) * (2 / N) := hmul
        _ = 2 * T := hcancel

end Critical2DKPZ.SHF.Flow
