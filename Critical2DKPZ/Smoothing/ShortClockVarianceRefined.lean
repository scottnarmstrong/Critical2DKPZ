/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.LogNormality.LatticeInputs
public import Critical2DKPZ.Smoothing.ProfileL2Perturbation
public import Critical2DKPZ.OnePoint.SecondMoment
public import Mathlib.Tactic
public import Critical2DKPZ.Smoothing.KernelVariation
public import Critical2DKPZ.Smoothing.ShortClockProfile
public import Critical2DKPZ.Smoothing.TimeShiftEnvironment
public import Critical2DKPZ.Smoothing.Measurability
import Mathlib.Tactic

/-! # Refined variance for a bounded short clock -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.Smoothing

/-- The centered short-clock mass has a variance bound with an extra logarithmic gain. -/
theorem integrable_smoothedP2Plane_shortClock_centered_sq_le (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ d s : ℕ,
        1 ≤ d → s ≤ 6 → d + s ≤ M → ∀ x : Site,
        Integrable (fun ω =>
          (smoothedP2Plane (criticalBeta ϑ M) d (d + s) x ω - 1) ^ 2) disorderLaw ∧
        (∫ ω,
          (smoothedP2Plane (criticalBeta ϑ M) d (d + s) x ω - 1) ^ 2 ∂disorderLaw) ≤
          C / ((d : ℝ) * Real.log (M : ℝ)) := by
  obtain ⟨C₀, hC₀⟩ := OnePoint.sigmaSq_secondMoment_le_uniform A 1
  let C : ℝ := 12 * (|C₀| + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  have hEvent : ∀ᶠ M : ℕ in atTop, 36 ≤ M ∧ 0 < Real.log (M : ℝ) := by
    filter_upwards [eventually_ge_atTop 36] with M hM
    exact ⟨hM, Real.log_pos (by
      have h : (1 : ℝ) < M := by exact_mod_cast (show 1 < M by omega)
      exact h)⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hC₀, hEvent] with M hC₀M hM
  intro ϑ hϑ d s hd hs hds x
  have hlogM : 0 < Real.log (M : ℝ) := hM.2
  have hMreal : 0 < (M : ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hden (t : ℕ) (ht : t ≤ 6) :
      Real.log (M : ℝ) / 2 ≤ Real.log (1 + (M : ℝ) / ((max t 1 : ℕ) : ℝ)) := by
    have htRN : max t 1 ≤ 6 := by omega
    have htR : ((max t 1 : ℕ) : ℝ) ≤ 6 := by exact_mod_cast htRN
    have hratio : (M : ℝ) / 6 ≤ (M : ℝ) / ((max t 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_left hMreal.le (by positivity) htR
    have hbase : (M : ℝ) ≤ (1 + (M : ℝ) / 6) ^ 2 := by
      have hM36 : (36 : ℝ) ≤ M := by exact_mod_cast hM.1
      nlinarith [sq_nonneg ((M : ℝ) - 12)]
    calc
      Real.log (M : ℝ) / 2 = Real.log (Real.sqrt (M : ℝ)) := by
        rw [Real.log_sqrt hMreal.le]
      _ ≤ Real.log (1 + (M : ℝ) / 6) := by
        apply Real.log_le_log
        · positivity
        · rw [Real.sqrt_le_iff]
          exact ⟨by positivity, hbase⟩
      _ ≤ Real.log (1 + (M : ℝ) / ((max t 1 : ℕ) : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
  have hσ : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ M) := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
  have hcoeff (t : ℕ) (ht : t ≤ 6) :
      Polymer.sigmaSq (criticalBeta ϑ M) *
        (∫ ω, pointToPlane (criticalBeta ϑ M) 0 t 0 ω ^ 2 ∂disorderLaw) ≤
        (2 * (|C₀| + 1)) / Real.log (M : ℝ) := by
    let t' := max t 1
    have ht' : 1 ≤ t' := by simp [t']
    have ht'le : (t' : ℝ) ≤ (M : ℝ) := by
      have ht6 : (t' : ℝ) ≤ 6 := by
        exact_mod_cast (show t' ≤ 6 by dsimp [t']; omega)
      have hM6N : 6 ≤ M := by omega
      have hM6 : (6 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM6N
      linarith
    have hraw := hC₀M ϑ hϑ t' ht' (by
      norm_num
      exact_mod_cast ht'le)
    have hsecondMono :
        (∫ ω, pointToPlane (criticalBeta ϑ M) 0 t 0 ω ^ 2 ∂disorderLaw) ≤
        (∫ ω, pointToPlane (criticalBeta ϑ M) 0 t' 0 ω ^ 2 ∂disorderLaw) := by
      by_cases hzero : t = 0
      · subst t
        have hmem : MemLp (fun ω => pointToPlane (criticalBeta ϑ M) 0 1 0 ω) 2 disorderLaw :=
          Polymer.memLp_pointToPlane _ _ _ _ 2 (by norm_num)
        have hmean : (∫ ω, pointToPlane (criticalBeta ϑ M) 0 1 0 ω ∂disorderLaw) = 1 :=
          Polymer.integral_pointToPlane _ _ _ _
        have hv := ProbabilityTheory.variance_nonneg
          (fun ω : Disorder => pointToPlane (criticalBeta ϑ M) 0 1 0 ω) disorderLaw
        rw [ProbabilityTheory.variance_eq_sub hmem, hmean] at hv
        norm_num at hv
        calc
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 0 0 ω ^ 2 ∂disorderLaw) = 1 := by
            simp [Polymer.pointToPlane_zero]
          _ ≤ ∫ ω, pointToPlane (criticalBeta ϑ M) 0 1 0 ω ^ 2 ∂disorderLaw := by
            linarith
      · have htEq : t' = t := max_eq_left (by omega)
        rw [htEq]
    have hraw' := mul_le_mul_of_nonneg_left hsecondMono hσ
    have hC₀le : C₀ ≤ |C₀| + 1 := by linarith [le_abs_self C₀]
    have hlogden : 0 < Real.log (1 + (M : ℝ) / t') := by
      apply Real.log_pos
      have ht'pos : 0 < (t' : ℝ) := by exact_mod_cast ht'
      have hratio : 0 < (M : ℝ) / t' := div_pos hMreal ht'pos
      linarith
    calc
      _ ≤ Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 t' 0 ω ^ 2 ∂disorderLaw) := hraw'
      _ ≤ C₀ / Real.log (1 + (M : ℝ) / t') := hraw
      _ ≤ (|C₀| + 1) / Real.log (1 + (M : ℝ) / t') := by
        apply div_le_div_of_nonneg_right hC₀le
        exact hlogden.le
      _ ≤ (2 * (|C₀| + 1)) / Real.log (M : ℝ) := by
        have hden' : Real.log (M : ℝ) / 2 ≤ Real.log (1 + (M : ℝ) / t') := by
          simpa only [t'] using hden t ht
        apply (div_le_div_iff₀ hlogden hlogM).2
        have hmul := mul_le_mul_of_nonneg_left hden'
          (show 0 ≤ 2 * (|C₀| + 1) by positivity)
        nlinarith [hmul]
  have hidentity :=
    integrable_walkKernel_shortProfile_centered_sq_eq_firstCollision
      (criticalBeta ϑ M) d s x
  have hkernel (r : ℕ) (hr : r ∈ Finset.Icc 1 s) :
      srwKernel (2 * (d + r)) 0 ≤ 1 / (d : ℝ) := by
    have hk := srwKernel_even_le_inv_succ (d + r) 0
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have hden' : (d : ℝ) ≤ (d + r : ℕ) + 1 := by exact_mod_cast (by omega)
    exact hk.trans (one_div_le_one_div_of_le hdpos hden')
  have hsumBound :
      (∑ r ∈ Finset.Icc 1 s,
        srwKernel (2 * (d + r)) 0 * Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (s - r) 0 ω ^ 2 ∂disorderLaw)) ≤
        12 * (|C₀| + 1) / ((d : ℝ) * Real.log (M : ℝ)) := by
    have hterm (r : ℕ) (hr : r ∈ Finset.Icc 1 s) :
        srwKernel (2 * (d + r)) 0 * Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (s - r) 0 ω ^ 2 ∂disorderLaw) ≤
        (1 / (d : ℝ)) * ((2 * (|C₀| + 1)) / Real.log (M : ℝ)) := by
      have hcoef' := hcoeff (s - r) (by omega)
      have hkernel' := hkernel r hr
      have hnonneg : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω : Disorder,
            pointToPlane (criticalBeta ϑ M) 0 (s - r) 0 ω ^ 2 ∂disorderLaw) :=
        mul_nonneg hσ (integral_nonneg fun ω => sq_nonneg
          (pointToPlane (criticalBeta ϑ M) 0 (s - r) 0 ω))
      calc
        _ = srwKernel (2 * (d + r)) 0 *
            (Polymer.sigmaSq (criticalBeta ϑ M) *
              ∫ ω, pointToPlane (criticalBeta ϑ M) 0 (s - r) 0 ω ^ 2 ∂disorderLaw) := by ring
        _ ≤ (1 / (d : ℝ)) *
            (Polymer.sigmaSq (criticalBeta ϑ M) *
              ∫ ω, pointToPlane (criticalBeta ϑ M) 0 (s - r) 0 ω ^ 2 ∂disorderLaw) :=
          mul_le_mul_of_nonneg_right hkernel' hnonneg
        _ ≤ _ := mul_le_mul_of_nonneg_left hcoef' (by positivity)
    have hsum := Finset.sum_le_card_nsmul (Finset.Icc 1 s) _ _ hterm
    have hcard : (Finset.Icc 1 s).card ≤ 6 := by
      rw [Nat.card_Icc]
      omega
    calc
      _ ≤ ((Finset.Icc 1 s).card : ℕ) •
          ((1 / (d : ℝ)) * ((2 * (|C₀| + 1)) / Real.log (M : ℝ))) := hsum
      _ ≤ 6 * ((1 / (d : ℝ)) * ((2 * (|C₀| + 1)) / Real.log (M : ℝ))) := by
        rw [nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = 12 * (|C₀| + 1) / ((d : ℝ) * Real.log (M : ℝ)) := by
        field_simp
        ring
  have hshift :
      (∫ ω,
          (smoothedP2Plane (criticalBeta ϑ M) d (d + s) x ω - 1) ^ 2 ∂disorderLaw) =
      ∫ ω,
        (profileP2Fun (criticalBeta ϑ M) 0 s
          (fun w => srwKernel d (w - x)) (fun _ => 1) ω - 1) ^ 2 ∂disorderLaw := by
    have hflat (ω : Disorder) : smoothedP2Plane (criticalBeta ϑ M) d (d + s) x ω =
        profileP2Fun (criticalBeta ϑ M) d (d + s)
          (fun w => srwKernel d (w - x)) (fun _ => 1) ω :=
      (Polymer.profileP2Fun_srw_flat (criticalBeta ϑ M) d (d + s) x ω).symm
    have htime (ω : Disorder) : profileP2Fun (criticalBeta ϑ M) d (d + s)
        (fun w => srwKernel d (w - x)) (fun _ => 1) ω =
        profileP2Fun (criticalBeta ϑ M) 0 s (fun w => srwKernel d (w - x))
          (fun _ => 1) (shiftEnvironment d ω) := by
      simpa using profileP2Fun_timeShift (criticalBeta ϑ M) d 0 s
        (fun w => srwKernel d (w - x)) (fun _ => 1) ω
    have hmeas : Measurable (fun ω : Disorder =>
        (profileP2Fun (criticalBeta ϑ M) 0 s
          (fun w => srwKernel d (w - x))
          (fun _ => 1) ω - 1) ^ 2) := by
      exact ((measurable_profileP2Fun_param (E := Disorder) (criticalBeta ϑ M) 0 s
        (fun _ => (1 : ℝ))
        (ν := fun (_ : Disorder) w => srwKernel d (w - x)) (ξ := id)
        (fun _ => measurable_const) measurable_id).sub_const 1).pow_const 2
    calc
      _ = ∫ ω,
          (profileP2Fun (criticalBeta ϑ M) 0 s
            (fun w => srwKernel d (w - x))
            (fun _ => 1) (shiftEnvironment d ω) - 1) ^ 2 ∂disorderLaw := by
              apply integral_congr_ae
              filter_upwards [] with ω
              rw [hflat ω, htime ω]
      _ = _ := integral_shiftEnvironment d hmeas
  have hcenterInt : Integrable (fun ω =>
        (smoothedP2Plane (criticalBeta ϑ M) d (d + s) x ω - 1) ^ 2) disorderLaw := by
    have hmem := Polymer.memLp_smoothedP2Plane (criticalBeta ϑ M) d (d + s) x 2
      (by norm_num)
    have h := (hmem.sub (memLp_const 1)).integrable_norm_pow'
    simpa only [Pi.sub_apply, Real.norm_eq_abs, sq_abs] using h
  have hsumidentity :
      (∫ ω, (profileP2Fun (criticalBeta ϑ M) 0 s
        (fun w => srwKernel d (w - x)) (fun _ => 1) ω - 1) ^ 2 ∂disorderLaw) =
        ∑ r ∈ Finset.Icc 1 s,
          srwKernel (2 * (d + r)) 0 * Polymer.sigmaSq (criticalBeta ϑ M) *
            (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (s - r) 0 ω ^ 2 ∂disorderLaw) := by
    simpa only [Nat.zero_add] using hidentity.2
  refine ⟨hcenterInt, ?_⟩
  rw [hshift, hsumidentity]
  simpa [C] using hsumBound

end Critical2DKPZ.Smoothing

end
