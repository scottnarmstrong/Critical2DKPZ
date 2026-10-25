/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.Smoothing.ProfileKernelPerturbation
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

/-! # Uniform logarithmic collision sums for long horizons -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.Smoothing

/-- The second moment of the mean-one one-step point-to-plane mass is at least one. -/
theorem pointToPlane_oneStep_secondMoment_ge_one (β : ℝ) :
    1 ≤ ∫ ω, pointToPlane β 0 1 0 ω ^ 2 ∂disorderLaw := by
  let F : Disorder → ℝ := pointToPlane β 0 1 0
  have hFmem : MemLp F 2 disorderLaw := by
    exact Polymer.memLp_pointToPlane β 0 1 0 2 (by norm_num)
  have hFint : Integrable F disorderLaw := by
    exact Polymer.integrable_pointToPlane β 0 1 0
  have hF2int : Integrable (fun ω => F ω ^ 2) disorderLaw := by
    have h := hFmem.integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have hvarint : Integrable (fun ω => (F ω - 1) ^ 2) disorderLaw := by
    have h := (hFmem.sub (memLp_const (1 : ℝ))).integrable_norm_pow'
    simpa only [Real.norm_eq_abs, sq_abs, Pi.sub_apply] using h
  have hvarnonneg : 0 ≤ ∫ ω, (F ω - 1) ^ 2 ∂disorderLaw :=
    integral_nonneg fun ω => sq_nonneg (F ω - 1)
  have hvarEq : (∫ ω, (F ω - 1) ^ 2 ∂disorderLaw) =
      (∫ ω, F ω ^ 2 ∂disorderLaw) - 1 := by
    have hsub : Integrable (fun ω => F ω ^ 2 - 2 * F ω) disorderLaw :=
      hF2int.sub (hFint.const_mul 2)
    calc
      _ = ∫ ω, (F ω ^ 2 - 2 * F ω + 1) ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        dsimp [F]
        ring
      _ = (∫ ω, F ω ^ 2 - 2 * F ω ∂disorderLaw) +
          ∫ _ω : Disorder, (1 : ℝ) ∂disorderLaw :=
        integral_add hsub (integrable_const 1)
      _ = (∫ ω, F ω ^ 2 ∂disorderLaw) -
          2 * ∫ ω, F ω ∂disorderLaw + 1 := by
        rw [integral_sub hF2int (hFint.const_mul 2), integral_const_mul]
        simp [F, Polymer.integral_pointToPlane, probReal_univ]
      _ = (∫ ω, F ω ^ 2 ∂disorderLaw) - 1 := by
        rw [show (∫ ω, F ω ∂disorderLaw) = 1 by
          exact Polymer.integral_pointToPlane β 0 1 0]
        ring
  rw [hvarEq] at hvarnonneg
  linarith

/-- Uniform boundedness of the variance-weighted free second moment at any subcritical clock.
The integrability of each displayed second-moment integral is included. -/
theorem sigmaSq_pointToPlane_secondMoment_le_constant (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ t : ℕ, t ≤ M →
        Integrable (fun ω => pointToPlane (criticalBeta ϑ M) 0 t 0 ω ^ 2) disorderLaw ∧
        Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 t 0 ω ^ 2 ∂disorderLaw) ≤ C := by
  obtain ⟨Craw, hsecond⟩ := OnePoint.sigmaSq_secondMoment_le_uniform A 1
  let C0 : ℝ := |Craw| + 1
  let C : ℝ := C0 / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC0 : 0 < C0 := by dsimp [C0]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsecond, Filter.eventually_ge_atTop (1 : ℕ)] with M hsecondM hM
  intro ϑ hϑ t htM
  have hMreal : 1 ≤ (M : ℝ) := by exact_mod_cast hM
  have hint : Integrable (fun ω => pointToPlane (criticalBeta ϑ M) 0 t 0 ω ^ 2)
      disorderLaw := OnePoint.integrable_pointToPlane_sq (criticalBeta ϑ M) t
  have hσ : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ M) := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
  have hbound : Polymer.sigmaSq (criticalBeta ϑ M) *
      (∫ ω, pointToPlane (criticalBeta ϑ M) 0 t 0 ω ^ 2 ∂disorderLaw) ≤ C := by
    by_cases ht : t = 0
    · subst t
      have hsecond1 := hsecondM ϑ hϑ 1 (by norm_num) (by simpa using hMreal)
      have hlower := pointToPlane_oneStep_secondMoment_ge_one (criticalBeta ϑ M)
      have hsigma : Polymer.sigmaSq (criticalBeta ϑ M) ≤
          Polymer.sigmaSq (criticalBeta ϑ M) *
            (∫ ω, pointToPlane (criticalBeta ϑ M) 0 1 0 ω ^ 2 ∂disorderLaw) := by
        calc
          _ = Polymer.sigmaSq (criticalBeta ϑ M) * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hlower hσ
      have hraw : Polymer.sigmaSq (criticalBeta ϑ M) ≤
          Craw / Real.log (1 + (M : ℝ)) := by
        calc
          _ ≤ Polymer.sigmaSq (criticalBeta ϑ M) *
              (∫ ω, pointToPlane (criticalBeta ϑ M) 0 1 0 ω ^ 2 ∂disorderLaw) := hsigma
          _ ≤ Craw / Real.log (1 + (M : ℝ) / 1) := by simpa using hsecond1
          _ = Craw / Real.log (1 + (M : ℝ)) := by norm_num
      have hden : 0 < Real.log (1 + (M : ℝ)) := by
        apply Real.log_pos
        linarith
      have hden2 : Real.log 2 ≤ Real.log (1 + (M : ℝ)) := by
        apply Real.log_le_log (by norm_num)
        nlinarith
      have hraw' : Craw / Real.log (1 + (M : ℝ)) ≤
          C0 / Real.log (1 + (M : ℝ)) := by
        apply div_le_div_of_nonneg_right _ hden.le
        dsimp [C0]
        linarith [le_abs_self Craw]
      have hden' : C0 / Real.log (1 + (M : ℝ)) ≤ C := by
        dsimp [C]
        exact div_le_div_of_nonneg_left hC0.le hlog2 hden2
      simpa [Polymer.pointToPlane_zero] using hraw.trans (hraw'.trans hden')
    · have htpos : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht
      have htR : (t : ℝ) ≤ (M : ℝ) := by exact_mod_cast htM
      have hsecondT := hsecondM ϑ hϑ t htpos (by simpa using htR)
      have htposR : 0 < (t : ℝ) := by exact_mod_cast (show 0 < t by omega)
      have hratio : 1 ≤ (M : ℝ) / t := by
        apply (le_div_iff₀ htposR).2
        nlinarith
      have hden : 0 < Real.log (1 + (M : ℝ) / t) := by
        apply Real.log_pos
        linarith
      have hden2 : Real.log 2 ≤ Real.log (1 + (M : ℝ) / t) := by
        apply Real.log_le_log (by norm_num)
        linarith
      have hraw' : Craw / Real.log (1 + (M : ℝ) / t) ≤
          C0 / Real.log (1 + (M : ℝ) / t) := by
        apply div_le_div_of_nonneg_right _ hden.le
        dsimp [C0]
        linarith [le_abs_self Craw]
      have hden' : C0 / Real.log (1 + (M : ℝ) / t) ≤ C := by
        dsimp [C]
        exact div_le_div_of_nonneg_left hC0.le hlog2 hden2
      exact hsecondT.trans (hraw'.trans hden')
  exact ⟨hint, hbound⟩

/-- The short-clock collision sum is at most linear in the remaining horizon. The pointwise
second-moment integrability companions are recorded alongside the integral bound. -/
theorem shortClockCollision_sum_le_linear (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ T : ℕ, T ≤ M →
        (∀ r ∈ Finset.Icc 1 T,
          Integrable (fun ω => pointToPlane (criticalBeta ϑ M) 0 (T - r) 0 ω ^ 2)
            disorderLaw) ∧
        (∑ r ∈ Finset.Icc 1 T,
          Polymer.sigmaSq (criticalBeta ϑ M) *
            (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (T - r) 0 ω ^ 2 ∂disorderLaw)) ≤
          C * (M : ℝ) := by
  obtain ⟨C₀, hC₀, hmoment⟩ := sigmaSq_pointToPlane_secondMoment_le_constant A
  refine ⟨C₀, hC₀, ?_⟩
  filter_upwards [hmoment] with M hmomentM
  intro ϑ hϑ T hTM
  constructor
  · intro r hr
    exact (hmomentM ϑ hϑ (T - r) (by omega)).1
  · have hterm (r : ℕ) (hr : r ∈ Finset.Icc 1 T) :
        Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (T - r) 0 ω ^ 2 ∂disorderLaw) ≤ C₀ :=
      (hmomentM ϑ hϑ (T - r) (by omega)).2
    have hsum := Finset.sum_le_card_nsmul (Finset.Icc 1 T) _ _ hterm
    have hcard : (Finset.Icc 1 T).card ≤ M := by
      rw [Nat.card_Icc]
      omega
    calc
      _ ≤ ((Finset.Icc 1 T).card : ℕ) • C₀ := hsum
      _ ≤ M • C₀ := by
        rw [nsmul_eq_mul, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hC₀.le
      _ = C₀ * (M : ℝ) := by rw [nsmul_eq_mul]; ring

/-- The first-collision sum is logarithmic uniformly for every horizon up to the critical size.
The one-step endpoint case is controlled by the lower second-moment bound above.
Each `∫ pointToPlane²` is integrable by `OnePoint.integrable_pointToPlane_sq`. -/
theorem critical_walkKernel_collision_sum_le_log_uniform (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ T : ℕ, T ≤ M →
        ∑ r ∈ Finset.Icc 1 T,
          Polymer.sigmaSq (criticalBeta ϑ M) *
            (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
              ((r : ℝ) + 1) ≤ C * (1 + Real.log ((M : ℝ) + 1)) := by
  obtain ⟨Craw, hsecond⟩ := OnePoint.sigmaSq_secondMoment_le_uniform A 1
  let C₀ : ℝ := |Craw| + 1
  let D : ℝ := C₀ / Real.log 2
  let C : ℝ := D + 1
  have hC₀ : 0 < C₀ := by dsimp [C₀]; positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsecond, Filter.eventually_ge_atTop (1 : ℕ)] with M hsecondM hM
  intro ϑ hϑ T hTM
  have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hσ : 0 ≤ Polymer.sigmaSq (criticalBeta ϑ M) := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
  have hmoment (s : ℕ) (hsM : s ≤ M) :
      Polymer.sigmaSq (criticalBeta ϑ M) *
        (∫ ω, pointToPlane (criticalBeta ϑ M) 0 s 0 ω ^ 2 ∂disorderLaw) ≤ D := by
    by_cases hs : s = 0
    · subst s
      have hsecond1 := hsecondM ϑ hϑ 1 (by norm_num) (by simpa using hMreal)
      have hlower := pointToPlane_oneStep_secondMoment_ge_one (criticalBeta ϑ M)
      have hsigmaLe : Polymer.sigmaSq (criticalBeta ϑ M) ≤
          Polymer.sigmaSq (criticalBeta ϑ M) *
            (∫ ω, pointToPlane (criticalBeta ϑ M) 0 1 0 ω ^ 2 ∂disorderLaw) := by
        calc
          _ = Polymer.sigmaSq (criticalBeta ϑ M) * 1 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hlower hσ
      have hraw : Polymer.sigmaSq (criticalBeta ϑ M) ≤
          Craw / Real.log (1 + (M : ℝ)) := by
        calc
          _ ≤ Polymer.sigmaSq (criticalBeta ϑ M) *
              (∫ ω, pointToPlane (criticalBeta ϑ M) 0 1 0 ω ^ 2 ∂disorderLaw) := hsigmaLe
          _ ≤ Craw / Real.log (1 + (M : ℝ) / 1) := by simpa using hsecond1
          _ = Craw / Real.log (1 + (M : ℝ)) := by norm_num
      have hlogMpos : 0 < Real.log (1 + (M : ℝ)) := by
        apply Real.log_pos
        linarith
      have hraw' : Craw / Real.log (1 + (M : ℝ)) ≤
          C₀ / Real.log (1 + (M : ℝ)) := by
        have hCraw : Craw ≤ C₀ := by dsimp [C₀]; linarith [le_abs_self Craw]
        exact div_le_div_of_nonneg_right hCraw hlogMpos.le
      have hlog : Real.log 2 ≤ Real.log (1 + (M : ℝ)) := by
        apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        nlinarith
      have hdenom : C₀ / Real.log (1 + (M : ℝ)) ≤ D := by
        dsimp [D]
        exact div_le_div_of_nonneg_left hC₀.le hlog2 hlog
      have hbound : Polymer.sigmaSq (criticalBeta ϑ M) ≤ D :=
        (hraw.trans hraw').trans hdenom
      simpa [Polymer.pointToPlane_zero] using hbound
    · have hspos : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs
      have hsreal : (s : ℝ) ≤ (M : ℝ) := by exact_mod_cast hsM
      have hsecondS := hsecondM ϑ hϑ s hspos (by simpa using hsreal)
      have hsrealpos : 0 < (s : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hspos)
      have hratio : (1 : ℝ) ≤ (M : ℝ) / s := by
        apply (le_div_iff₀ hsrealpos).2
        nlinarith
      have hlog : Real.log 2 ≤ Real.log (1 + (M : ℝ) / s) := by
        apply Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        nlinarith
      have hraw :
          Polymer.sigmaSq (criticalBeta ϑ M) *
            (∫ ω, pointToPlane (criticalBeta ϑ M) 0 s 0 ω ^ 2 ∂disorderLaw) ≤
          Craw / Real.log (1 + (M : ℝ) / s) := hsecondS
      have hlogSpos : 0 < Real.log (1 + (M : ℝ) / s) := by
        apply Real.log_pos
        linarith
      have hraw' : Craw / Real.log (1 + (M : ℝ) / s) ≤
          C₀ / Real.log (1 + (M : ℝ) / s) := by
        have hCraw : Craw ≤ C₀ := by dsimp [C₀]; linarith [le_abs_self Craw]
        exact div_le_div_of_nonneg_right hCraw hlogSpos.le
      have hdenom : C₀ / Real.log (1 + (M : ℝ) / s) ≤ D := by
        dsimp [D]
        exact div_le_div_of_nonneg_left hC₀.le hlog2 hlog
      exact (hraw.trans hraw').trans hdenom
  have hrecip :
      ∑ r ∈ Finset.Icc 1 T, (1 / ((r : ℝ) + 1)) ≤
        1 + Real.log ((M : ℝ) + 1) := by
    by_cases hT : T = 0
    · simp [hT]
      have hlog0 : 0 ≤ Real.log ((M : ℝ) + 1) :=
        Real.log_nonneg (by nlinarith [hMreal])
      linarith
    · have hTpos : 0 < T := Nat.pos_of_ne_zero hT
      have hsumMono :
          ∑ r ∈ Finset.Icc 1 T, (1 / ((r : ℝ) + 1)) ≤
            ∑ r ∈ Finset.Icc 1 T, (r : ℝ)⁻¹ := by
        apply Finset.sum_le_sum
        intro r hr
        have hrpos : 0 < (r : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hr).1
        have hdenpos : 0 < (r : ℝ) + 1 := by positivity
        have hineq : (1 : ℝ) / ((r : ℝ) + 1) ≤ 1 / (r : ℝ) := by
          rw [div_le_div_iff₀ hdenpos hrpos]
          nlinarith
        simpa only [one_div] using hineq
      have hsumHarmonic :
          ∑ r ∈ Finset.Icc 1 T, (r : ℝ)⁻¹ = (harmonic T : ℝ) := by
        simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      have hTrealpos : 0 < (T : ℝ) := by exact_mod_cast hTpos
      have hlogT : Real.log (T : ℝ) ≤ Real.log ((M : ℝ) + 1) := by
        apply Real.log_le_log hTrealpos
        exact_mod_cast (Nat.le_succ_of_le hTM)
      calc
        _ ≤ (harmonic T : ℝ) := by rw [← hsumHarmonic]; exact hsumMono
        _ ≤ 1 + Real.log (T : ℝ) := harmonic_le_one_add_log T
        _ ≤ 1 + Real.log ((M : ℝ) + 1) := by linarith
  have hsum :
      ∑ r ∈ Finset.Icc 1 T,
        Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
            ((r : ℝ) + 1) ≤ D * (1 + Real.log ((M : ℝ) + 1)) := by
    calc
      _ ≤ ∑ r ∈ Finset.Icc 1 T, D / ((r : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro r hr
        have hrT : r ≤ T := (Finset.mem_Icc.mp hr).2
        have hrpos : 0 < (r : ℝ) + 1 := by positivity
        have hnum := hmoment (T - r) (by omega)
        exact div_le_div_of_nonneg_right hnum hrpos.le
      _ = D * ∑ r ∈ Finset.Icc 1 T, (1 / ((r : ℝ) + 1)) := by
        calc
          _ = ∑ r ∈ Finset.Icc 1 T, D * (1 / ((r : ℝ) + 1)) := by
            apply Finset.sum_congr rfl
            intro r hr
            ring
          _ = _ := by rw [← Finset.mul_sum]
      _ ≤ D * (1 + Real.log ((M : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hrecip hD.le
  calc
    _ ≤ D * (1 + Real.log ((M : ℝ) + 1)) := hsum
    _ ≤ C * (1 + Real.log ((M : ℝ) + 1)) := by
      apply mul_le_mul_of_nonneg_right
      · dsimp [C]
        linarith
      · have hlog0 : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by linarith)
        linarith

/-- A flat profile with a finitely supported walk-kernel initial law has a logarithmic second
moment, uniformly over the starting site and the even walk-kernel width. -/
theorem integral_walkKernel_flat_profile_sq_le_log_uniform (A : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ M : ℕ in atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ a T p : ℕ, T ≤ M → ∀ x : Site,
        Integrable (fun ω => profileP2Fun (criticalBeta ϑ M) a (a + T)
          (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω ^ 2) disorderLaw ∧
        (∫ ω, profileP2Fun (criticalBeta ϑ M) a (a + T)
          (fun w => srwKernel (2 * p) (w - x)) (fun _ => 1) ω ^ 2 ∂disorderLaw) ≤
          C * (1 + Real.log ((M : ℝ) + 1)) := by
  obtain ⟨Csum, hCsum, hsum⟩ := critical_walkKernel_collision_sum_le_log_uniform A
  let C : ℝ := Csum + 1
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsum, Filter.eventually_ge_atTop (1 : ℕ)] with M hsumM hM
  intro ϑ hϑ a T p hTM x
  let ν : Site → ℝ := fun w => srwKernel (2 * p) (w - x)
  let S : Finset Site := Polymer.endpoints x (2 * p)
  have hνS : ∀ w ∉ S, ν w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem (2 * p) x w hw
  have hν0 : ∀ w, 0 ≤ ν w := fun w => Polymer.kernel_nonneg (2 * p) (w - x)
  have hmass : ∑ w ∈ S, ν w = 1 := by
    dsimp [ν, S]
    exact Polymer.sum_srwKernel_endpoints (2 * p) x
  have hbase := integral_nonnegative_profile_sq_le (criticalBeta ϑ M) a T ν S
    hνS hν0
  rw [hmass] at hbase
  refine ⟨hbase.1, ?_⟩
  calc
    _ ≤ 1 + ∑ r ∈ Finset.Icc 1 T,
        Polymer.sigmaSq (criticalBeta ϑ M) *
          (∫ ω, pointToPlane (criticalBeta ϑ M) 0 (T - r) 0 ω ^ 2 ∂disorderLaw) /
            ((r : ℝ) + 1) := by simpa only [one_pow, one_mul] using hbase.2
    _ ≤ 1 + Csum * (1 + Real.log ((M : ℝ) + 1)) := by
      linarith [hsumM ϑ hϑ T hTM]
    _ ≤ C * (1 + Real.log ((M : ℝ) + 1)) := by
      have hlog0 : 0 ≤ Real.log ((M : ℝ) + 1) := Real.log_nonneg (by
        have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
        nlinarith [hMreal])
      dsimp [C]
      nlinarith [hlog0]

end Critical2DKPZ.Smoothing

end
