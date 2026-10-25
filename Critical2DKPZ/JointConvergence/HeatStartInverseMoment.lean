/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.FiniteProfileGaussian
public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.MomentBounds.AiiKSmoothedShift
public import Critical2DKPZ.Smoothing.TimeShiftEnvironment
public import Critical2DKPZ.FutureProfiles.EndpointTranslation
public import Critical2DKPZ.Analysis.Lattice.Basic
import Critical2DKPZ.PolymerCalculus.Clocks
import Mathlib.Tactic

/-!
# Fixed-width inverse moments for heat-start profiles

Heat-start polymer pairings have uniformly bounded inverse first moments at fixed heat width.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

namespace Critical2DKPZ.JointConvergence

/-- Fixed-width lattice heat-start fields have inverse-moment bounds with integrability supplied by `OnePoint.integrable_rpow_profileP2Fun`. -/
theorem integral_inv_profileP2Fun_heatStart_le_of_horizon_bound_constants
    (ϑ : ℝ) {s T δ U : ℝ} (hs : 0 ≤ s) (hsT : s < T)
    (hδ : 0 < δ) (hU : δ + (T - s) + 2 ≤ U) (C₂ D : ℝ)
    (hC₂ : ∀ᶠ N : ℕ in atTop, ∀ θ ∈ Set.Icc (-|ϑ|) |ϑ|, ∀ m n : ℕ,
      m ≤ n → 1 ≤ n → (n : ℝ) ≤ U * N →
      ∫ ω, smoothedP2Plane (criticalBeta θ N) m n 0 ω ^ 2 ∂disorderLaw ≤
        1 + C₂ * (replicaOverlap n - replicaOverlap m) /
          Real.log (1 + (N : ℝ) / n))
    (hD : ∀ m n : ℕ, m ≤ n →
      |Real.pi * (replicaOverlap n - replicaOverlap m) -
        Real.log (((max n 1 : ℕ) : ℝ) / ((max m 1 : ℕ) : ℝ))| ≤ D) :
    ∀ᶠ N : ℕ in atTop, ∀ x : Plane,
      ∫ ω, (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x)) (fun _ => 1) ω)⁻¹
        ∂disorderLaw ≤ 1 + |C₂| * ((Real.log (U / δ) + D) / Real.pi) /
          Real.log (1 + 1 / U) := by
  have hDnonneg : 0 ≤ D := by
    have h := hD 1 1 (by omega)
    simpa using h
  have hUpos : 0 < U := by linarith
  have hRatio : 1 ≤ U / δ := by
    rw [le_div_iff₀ hδ]
    have hsTpos : 0 < T - s := by linarith
    nlinarith [hU]
  have hLogRatio : 0 ≤ Real.log (U / δ) := Real.log_nonneg hRatio
  have hDenPos : 0 < Real.log (1 + 1 / U) := by
    apply Real.log_pos
    have : 0 < 1 / U := by positivity
    linarith
  let Q : ℝ := (Real.log (U / δ) + D) / Real.pi
  let B : ℝ := |C₂| * Q / Real.log (1 + 1 / U)
  have hQnonneg : 0 ≤ Q := by dsimp [Q]; positivity
  have hBnonneg : 0 ≤ B := by dsimp [B]; positivity
  let Kδ : ℕ := Nat.ceil (1 / δ)
  let Kt : ℕ := Nat.ceil (3 / (T - s))
  let K : ℕ := max (max Kδ Kt) 2
  change ∀ᶠ N : ℕ in atTop, ∀ x : Plane,
    ∫ ω, (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
      (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x)) (fun _ => 1) ω)⁻¹
      ∂disorderLaw ≤ 1 + B
  filter_upwards [hC₂, Filter.eventually_ge_atTop K] with N hC₂N hNK
  intro x
  let a : ℕ := evenCeil (N * s)
  let b : ℕ := evenCeil (N * T)
  let m : ℕ := evenCeil (N * δ)
  let n : ℕ := m + (b - a)
  let x₀ : Site := latticePoint N x
  let ν : Site → ℝ := fun w => srwKernel m (w - x₀)
  let ν₀ : Site → ℝ := fun w => srwKernel m w
  let F : Disorder → ℝ := fun ω => profileP2Fun (criticalBeta ϑ N) 0 (b - a) ν₀
    (fun _ => 1) ω
  let τ : Disorder → Disorder := fun ω p => ω (p.1, p.2 + x₀)
  have hTpos : 0 < T := by linarith
  have ha0 : 0 ≤ (N : ℝ) * s := mul_nonneg (Nat.cast_nonneg N) hs
  have hb0 : 0 ≤ (N : ℝ) * T := mul_nonneg (Nat.cast_nonneg N) hTpos.le
  have hm0 : 0 ≤ (N : ℝ) * δ := by positivity
  have ha_le_b : a ≤ b := by
    dsimp [a, b]
    apply evenCeil_mono
    exact mul_le_mul_of_nonneg_left hsT.le (Nat.cast_nonneg N)
  have hδceil : 1 / δ ≤ (Kδ : ℝ) := by
    exact Nat.le_ceil (1 / δ)
  have htceil : 3 / (T - s) ≤ (Kt : ℝ) := by
    exact Nat.le_ceil (3 / (T - s))
  have hNreal : 2 ≤ (N : ℝ) := by
    exact_mod_cast (show 2 ≤ N by dsimp [K] at hNK; omega)
  have hmge : 1 ≤ (m : ℝ) := by
    have hNδ : 1 ≤ (N : ℝ) * δ := by
      have hNKδ : Kδ ≤ N := by dsimp [K] at hNK; omega
      have hKδN : (Kδ : ℝ) ≤ N := by exact_mod_cast hNKδ
      have hceilmul : 1 ≤ (Kδ : ℝ) * δ := (div_le_iff₀ hδ).mp hδceil
      nlinarith [mul_le_mul_of_nonneg_right hKδN hδ.le, hceilmul]
    have hNle_m : (N : ℝ) * δ ≤ (m : ℝ) := by
      dsimp [m]
      exact le_evenCeil _
    linarith
  have hnge : 1 ≤ n := by
    have hKNt : Kt ≤ N := by dsimp [K] at hNK; omega
    have hKtN : (Kt : ℝ) ≤ N := by exact_mod_cast hKNt
    have hscale : 3 ≤ (N : ℝ) * (T - s) := by
      have hKt : 3 ≤ (Kt : ℝ) * (T - s) :=
        (div_le_iff₀ (by linarith : 0 < T - s)).mp htceil
      nlinarith [mul_le_mul_of_nonneg_right hKtN (le_of_lt (by linarith : 0 < T - s)), hKt]
    have hdur := evenCeil_duration_error ha0 hb0
    have hgap : 1 < (b : ℝ) - a := by dsimp [a, b]; rw [abs_lt] at hdur; linarith
    have hgapNat : 1 < b - a := by
      have hgap' : (1 : ℝ) < ((b - a : ℕ) : ℝ) := by
        rw [Nat.cast_sub ha_le_b]
        exact hgap
      exact_mod_cast hgap'
    dsimp [n]
    omega
  have hnupper : (n : ℝ) ≤ U * N := by
    let Uactual : ℝ := δ + (T - s) + 2
    have hmupper := evenCeil_lt_add_two hm0
    have hdur := evenCeil_duration_error ha0 hb0
    have hduration : (b : ℝ) - a ≤ (N : ℝ) * (T - s) + 2 := by
      rw [abs_lt] at hdur
      nlinarith
    have hncast : (n : ℝ) = (m : ℝ) + ((b : ℝ) - a) := by
      dsimp [n]
      rw [Nat.cast_add, Nat.cast_sub ha_le_b]
    calc
      (n : ℝ) = (m : ℝ) + ((b : ℝ) - a) := hncast
      _ ≤ (N : ℝ) * δ + 2 + ((N : ℝ) * (T - s) + 2) := by nlinarith [hmupper, hduration]
      _ ≤ Uactual * N := by dsimp [Uactual]; nlinarith [hNreal]
      _ ≤ U * N := by
        exact mul_le_mul_of_nonneg_right hU (Nat.cast_nonneg N)
  have hmn : m ≤ n := by dsimp [n]; omega
  have hϑ' : ϑ ∈ Set.Icc (-|ϑ|) |ϑ| := by
    exact Set.mem_Icc.mpr ⟨neg_abs_le ϑ, le_abs_self ϑ⟩
  have hβ : 0 ≤ criticalBeta ϑ N := Real.sqrt_nonneg _
  have hratio : (n : ℝ) / m ≤ U / δ := by
    have hmpos : 0 < (m : ℝ) := by linarith
    have hδN : (N : ℝ) * δ ≤ m := by
      dsimp [m]
      exact le_evenCeil _
    have hnN : (n : ℝ) ≤ U * N := hnupper
    apply (div_le_div_iff₀ hmpos hδ).2
    nlinarith
  have hlogratio : Real.log ((n : ℝ) / m) ≤ Real.log (U / δ) :=
    Real.log_le_log (by positivity) hratio
  have hoverlap : 0 ≤ replicaOverlap n - replicaOverlap m := by
    rw [OnePoint.replicaOverlap_sub_eq_sum m n hmn]
    apply Finset.sum_nonneg
    intro r hr
    exact srwKernel_nonneg (2 * r) 0
  have hoverlap_bound : replicaOverlap n - replicaOverlap m ≤ Q := by
    have hDmn := hD m n hmn
    have hrel : (Real.pi * (replicaOverlap n - replicaOverlap m) -
        Real.log ((n : ℝ) / m)) ≤ D := by
      have hmmax : max m 1 = m := max_eq_left (by exact_mod_cast hmge)
      have hnmax : max n 1 = n := max_eq_left (by exact_mod_cast hnge)
      have hDmn' : |Real.pi * (replicaOverlap n - replicaOverlap m) -
          Real.log ((n : ℝ) / m)| ≤ D := by
        simpa only [hmmax, hnmax] using hDmn
      exact (abs_le.mp hDmn').2
    dsimp [Q]
    apply (le_div_iff₀ Real.pi_pos).2
    nlinarith [hrel, hlogratio]
  have hdenom : Real.log (1 + (N : ℝ) / n) ≥ Real.log (1 + 1 / U) := by
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hnge
    apply Real.log_le_log (by positivity)
    have hNn : 1 / U ≤ (N : ℝ) / n := by
      apply (div_le_div_iff₀ hUpos hnreal).2
      nlinarith [hnupper]
    linarith
  have hdenompos : 0 < Real.log (1 + (N : ℝ) / n) := by
    apply Real.log_pos
    have : 0 < (N : ℝ) / n := by positivity
    linarith
  have hmoment := hC₂N ϑ hϑ' m n hmn hnge hnupper
  have hsecond :
      ∫ ω, smoothedP2Plane (criticalBeta ϑ N) m n 0 ω ^ 2 ∂disorderLaw ≤ 1 + B := by
    have hcoeff : C₂ * (replicaOverlap n - replicaOverlap m) /
        Real.log (1 + (N : ℝ) / n) ≤ B := by
      dsimp [B, Q]
      have hnum : 0 ≤ replicaOverlap n - replicaOverlap m := hoverlap
      have hq : 0 ≤ (replicaOverlap n - replicaOverlap m) /
          Real.log (1 + (N : ℝ) / n) := div_nonneg hnum hdenompos.le
      have hfrac : (replicaOverlap n - replicaOverlap m) /
          Real.log (1 + (N : ℝ) / n) ≤ Q / Real.log (1 + 1 / U) := by
        calc
          _ ≤ Q / Real.log (1 + (N : ℝ) / n) :=
            div_le_div_of_nonneg_right hoverlap_bound hdenompos.le
          _ ≤ _ := div_le_div_of_nonneg_left hQnonneg hDenPos hdenom
      calc
        C₂ * (replicaOverlap n - replicaOverlap m) / Real.log (1 + (N : ℝ) / n)
            = C₂ * ((replicaOverlap n - replicaOverlap m) /
                Real.log (1 + (N : ℝ) / n)) := by ring
        _ ≤ |C₂| * ((replicaOverlap n - replicaOverlap m) /
                Real.log (1 + (N : ℝ) / n)) :=
              mul_le_mul_of_nonneg_right (le_abs_self C₂) hq
        _ ≤ |C₂| * (Q / Real.log (1 + 1 / U)) :=
              mul_le_mul_of_nonneg_left hfrac (abs_nonneg _)
        _ = B := by ring
    exact hmoment.trans (by nlinarith)
  have hspatial (ω : Disorder) :
      profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω =
        F (τ (Smoothing.shiftEnvironment a ω)) := by
    rw [Smoothing.profileP2Fun_timeShift_sub (criticalBeta ϑ N) (le_rfl) (by exact ha_le_b)
      ν (fun _ => 1) ω]
    simp only [Nat.sub_self]
    rw [FutureProfiles.profileP2Fun_translate (criticalBeta ϑ N) 0 (b - a) x₀ ν₀
      (fun _ => 1) (Smoothing.shiftEnvironment a ω)]
  have hFmeas : Measurable (fun ω : Disorder => F ω ^ 2) := by
    dsimp [F]
    exact (Polymer.measurable_profileP2Fun _ _ _ _ _).pow_const 2
  have hτmeas : Measurable τ := by
    dsimp [τ]
    apply measurable_pi_iff.mpr
    intro p
    exact Gaussian.measurable_disorder_eval (p.1, p.2 + x₀)
  have hτMP : MeasurePreserving τ disorderLaw disorderLaw := by
    dsimp [τ]
    exact FutureProfiles.measurePreserving_disorderShift x₀
  have hτint : (∫ ω, F (τ ω) ^ 2 ∂disorderLaw) = ∫ ω, F ω ^ 2 ∂disorderLaw := by
    have h := integral_map (μ := disorderLaw) hτmeas.aemeasurable hFmeas.aestronglyMeasurable
    rw [hτMP.map_eq] at h
    exact h.symm
  have hprofileInt :
      ∫ ω, profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω ^ 2 ∂disorderLaw =
        ∫ ω, F ω ^ 2 ∂disorderLaw := by
    calc
      _ = ∫ ω, F (τ (Smoothing.shiftEnvironment a ω)) ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hspatial]
      _ = ∫ ω, F (τ ω) ^ 2 ∂disorderLaw := by
        simpa only [Function.comp_apply] using
          (Smoothing.integral_shiftEnvironment a (hFmeas.comp hτmeas))
      _ = ∫ ω, F ω ^ 2 ∂disorderLaw := hτint
  have hsmoothedInt :
      ∫ ω, smoothedP2Plane (criticalBeta ϑ N) m n 0 ω ^ 2 ∂disorderLaw =
        ∫ ω, F ω ^ 2 ∂disorderLaw := by
    have hpoint (ω : Disorder) :
        smoothedP2Plane (criticalBeta ϑ N) m n 0 ω = F (Smoothing.shiftEnvironment m ω) := by
      simpa only [F, n, Nat.add_sub_cancel_left] using
        (MomentBounds.smoothedP2Plane_eq_profileP2Fun_shift (criticalBeta ϑ N)
          (Nat.le_add_right m (b - a)) ω)
    calc
      _ = ∫ ω, F (Smoothing.shiftEnvironment m ω) ^ 2 ∂disorderLaw := by
        apply integral_congr_ae
        filter_upwards [] with ω
        rw [hpoint]
      _ = ∫ ω, F ω ^ 2 ∂disorderLaw := Smoothing.integral_shiftEnvironment m hFmeas
  have hprofileSecond :
      ∫ ω, profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω ^ 2 ∂disorderLaw ≤ 1 + B := by
    rw [hprofileInt, ← hsmoothedInt]
    exact hsecond
  have hνA : ∀ w ∉ Polymer.endpoints x₀ m, ν w = 0 := by
    intro w hw
    exact Polymer.srwKernel_eq_zero_of_not_mem m x₀ w hw
  have hν0 : ∀ w, 0 ≤ ν w := by
    intro w
    exact Polymer.kernel_nonneg m (w - x₀)
  have hν1 : ∑ w ∈ Polymer.endpoints x₀ m, ν w = 1 := by
    simpa [ν] using Polymer.sum_srwKernel_endpoints m x₀
  have hinv := OnePoint.integral_rpow_neg_profileP2Fun_le hβ a b ν
    (Polymer.endpoints x₀ m) hνA hν0 hν1 (p := 1) (by norm_num)
  have hinv' :
      ∫ ω, (profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω)⁻¹ ∂disorderLaw ≤
        ∫ ω, profileP2Fun (criticalBeta ϑ N) a b ν (fun _ => 1) ω ^ 2 ∂disorderLaw := by
    have hinv'' := hinv
    norm_num at hinv''
    simpa only [Real.rpow_neg_one, Real.rpow_one] using hinv''
  simpa [a, b, m, x₀, ν] using hinv'.trans hprofileSecond

/-- At fixed critical parameter and positive heat width, the inverse first moment is uniformly bounded over spatial centers for sufficiently large lattice scales.
The inverse is integrable by `OnePoint.integrable_rpow_profileP2Fun` with exponent `-1`. -/
theorem integral_inv_profileP2Fun_heatStart_le_of_horizon_bound
    (ϑ : ℝ) {s T δ U : ℝ} (hs : 0 ≤ s) (hsT : s < T)
    (hδ : 0 < δ) (hU : δ + (T - s) + 2 ≤ U) :
    ∃ C₂ D C : ℝ,
      0 ≤ D ∧
      C = 1 + |C₂| * ((Real.log (U / δ) + D) / Real.pi) /
        Real.log (1 + 1 / U) ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : Plane,
        ∫ ω, (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
          (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x)) (fun _ => 1) ω)⁻¹
          ∂disorderLaw ≤ C := by
  let A : ℝ := |ϑ|
  obtain ⟨C₂, hC₂⟩ := OnePoint.smoothedP2Plane_secondMoment_le_uniform A U
  obtain ⟨D, hD⟩ := OnePoint.replicaOverlap_sub_log_bounded
  have hDnonneg : 0 ≤ D := by
    have h := hD 1 1 (by omega)
    simpa using h
  let C : ℝ := 1 + |C₂| * ((Real.log (U / δ) + D) / Real.pi) /
    Real.log (1 + 1 / U)
  have hbound := integral_inv_profileP2Fun_heatStart_le_of_horizon_bound_constants
    ϑ hs hsT hδ hU C₂ D hC₂ hD
  refine ⟨C₂, D, C, hDnonneg, rfl, ?_⟩
  simpa [C] using hbound

/-- The horizon estimate at `U = δ + (T - s) + 2` gives a fixed-width inverse-moment bound.
The inverse is integrable by `OnePoint.integrable_rpow_profileP2Fun` with exponent `-1`. -/
theorem integral_inv_profileP2Fun_heatStart_le (ϑ : ℝ) {s T δ : ℝ}
    (hs : 0 ≤ s) (hsT : s < T) (hδ : 0 < δ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ x : Plane,
      ∫ ω, (profileP2Fun (criticalBeta ϑ N) (evenCeil (N * s)) (evenCeil (N * T))
        (fun w => srwKernel (evenCeil (N * δ)) (w - latticePoint N x)) (fun _ => 1) ω)⁻¹
        ∂disorderLaw ≤ C := by
  obtain ⟨C₂, D, C, _hD, _hC, hbound⟩ :=
    integral_inv_profileP2Fun_heatStart_le_of_horizon_bound ϑ hs hsT hδ le_rfl
  exact ⟨C, hbound⟩

end Critical2DKPZ.JointConvergence

end
