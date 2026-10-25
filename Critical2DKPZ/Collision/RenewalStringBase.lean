/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.CriticalWindow
public import Critical2DKPZ.Renewal.LocalBounds
public import Critical2DKPZ.Renewal.CriticalParameter
public import Critical2DKPZ.Collision.BackwardWeights
public import Critical2DKPZ.SHF.DeltaBose.CausalComposition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Critical2DKPZ.SHF.DeltaBose.Measurability
import Mathlib.Tactic

/-! # Finite renewal strings and shifted-cell comparison

Scalar renewal estimates compare discrete renewal masses with integrals over half-shifted time cells. -/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Critical2DKPZ.Collision

/-- The cumulative marked renewal mass is bounded by the square of the ordinary
cumulative renewal mass. This is the finite-coefficient consequence of the exact
renewal-square identity. -/
theorem markedRenewalFunction_le_sq_renewalFunction {w : ℕ → ℝ}
    (hw : ∀ r, 0 ≤ w r) (n : ℕ) :
    Renewal.markedRenewalFunction w n ≤ (Renewal.renewalFunction w n) ^ 2 := by
  have hm : Renewal.markedRenewalFunction w n =
      ∑ k ∈ Finset.range (n + 1), Renewal.renewalSquare w k := by
    rw [← Renewal.sum_markedRenewalMass_range w n]
    apply Finset.sum_congr rfl
    intro k hk
    exact (Renewal.renewalSquare_eq_markedRenewalMass w k).symm
  rw [hm]
  let t : Finset (ℕ × ℕ) :=
    ((Finset.range (n + 1)) ×ˢ (Finset.range (n + 1))).filter
      (fun p => p.1 + p.2 ≤ n)
  have htri :
      (∑ k ∈ Finset.range (n + 1),
        ∑ j ∈ Finset.range (k + 1), Renewal.renewalMass w j *
          Renewal.renewalMass w (k - j)) =
      ∑ p ∈ t, Renewal.renewalMass w p.1 * Renewal.renewalMass w p.2 := by
    rw [Finset.sum_sigma']
    unfold t
    apply Finset.sum_bij (fun x _ => (x.2, x.1 - x.2))
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
      constructor
      · exact ⟨by omega, by omega⟩
      · omega
    · intro x hx y hy hxy
      simp only [Prod.mk.injEq] at hxy
      simp only [Finset.mem_sigma, Finset.mem_range] at hx hy
      obtain ⟨hxk, hxj⟩ := hx
      obtain ⟨hyk, hyj⟩ := hy
      have h1 : x.2 = y.2 := hxy.1
      have h2 : x.1 - x.2 = y.1 - y.2 := hxy.2
      apply Sigma.ext
      · omega
      · simp [h1]
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
      obtain ⟨⟨hp1, hp2⟩, hsum⟩ := hp
      refine ⟨⟨p.1 + p.2, p.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_range]
        constructor <;> omega
      · simp
    · intro x hx
      simp only [Finset.mem_sigma, Finset.mem_range] at hx
      rfl
  simp_rw [Renewal.renewalSquare]
  rw [htri]
  have hsubset : t ⊆ Finset.range (n + 1) ×ˢ Finset.range (n + 1) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hnonneg : ∀ p ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      0 ≤ Renewal.renewalMass w p.1 * Renewal.renewalMass w p.2 := by
    intro p hp
    exact mul_nonneg (Renewal.renewalMass_nonneg hw _) (Renewal.renewalMass_nonneg hw _)
  calc
    (∑ p ∈ t, Renewal.renewalMass w p.1 * Renewal.renewalMass w p.2) ≤
        ∑ p ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
          Renewal.renewalMass w p.1 * Renewal.renewalMass w p.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p hp _ => hnonneg p hp)
    _ = (Renewal.renewalFunction w n) ^ 2 := by
      rw [← Renewal.sum_renewalMass_range w n]
      rw [Finset.sum_product' (Finset.range (n + 1)) (Finset.range (n + 1))
        (fun i j => Renewal.renewalMass w i * Renewal.renewalMass w j)]
      rw [pow_two, Finset.sum_mul_sum]

/-- On a compact critical-parameter interval, the coupling is eventually positive
and bounded by a fixed multiple of `1 / log N`. -/
theorem eventually_criticalSigmaSq_uniform_log_bound (A : ℝ) (_hA : 0 ≤ A) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ ϑ ∈ Set.Icc (-A) A,
      0 < criticalSigmaSq ϑ N ∧
        criticalSigmaSq ϑ N ≤ (Real.pi + 1) / Real.log N := by
  have hlim := Renewal.tendsto_sigma_mul_log A
  have hupper : ∀ᶠ N : ℕ in Filter.atTop,
      criticalSigmaSq A N * Real.log N < Real.pi + 1 :=
    hlim.eventually (isOpen_Iio.mem_nhds (show Real.pi ∈ Iio (Real.pi + 1) by
      simp))
  filter_upwards [hupper, Renewal.criticalSigmaSq_eventually_pos (-A),
    Filter.eventually_ge_atTop 2] with N hupper hlow hN
  intro ϑ hϑ
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hθpos : 0 < criticalSigmaSq ϑ N := by
    exact lt_of_lt_of_le hlow (Renewal.criticalSigmaSq_mono_parameter hN hϑ.1)
  have hθA : criticalSigmaSq ϑ N ≤ criticalSigmaSq A N :=
    Renewal.criticalSigmaSq_mono_parameter hN hϑ.2
  refine ⟨hθpos, ?_⟩
  apply (le_div_iff₀ hlog).2
  calc
    criticalSigmaSq ϑ N * Real.log N ≤
        criticalSigmaSq A N * Real.log N :=
      mul_le_mul_of_nonneg_right hθA hlog.le
    _ ≤ Real.pi + 1 := le_of_lt hupper

/-- Once the critical coupling is positive, the renewal function satisfies a logarithmic bound uniform on compact parameter intervals. -/
theorem eventually_criticalRenewalFunction_uniform_log_bound (A : ℝ) (hA : 0 ≤ A) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ k : ℕ, 1 ≤ k → k ≤ N →
        criticalSigmaSq ϑ N * Renewal.criticalRenewalFunction ϑ N k ≤
          K / Real.log (1 + (N : ℝ) / k) := by
  obtain ⟨K, hK, hbound⟩ := Renewal.criticalRenewalFunction_log_bound A
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_criticalSigmaSq_uniform_log_bound A hA,
    Filter.eventually_ge_atTop 2] with N hbound hσ hN
  intro ϑ hϑ k hk hkN
  have hA_mem : A ∈ Set.Icc (-A) A := ⟨by linarith, le_rfl⟩
  have hσA : 0 < criticalSigmaSq A N := (hσ A hA_mem).1
  have hσle : criticalSigmaSq ϑ N ≤ criticalSigmaSq A N :=
    Renewal.criticalSigmaSq_mono_parameter hN hϑ.2
  have hkernel : ∀ r : ℕ,
      criticalSigmaSq ϑ N * Renewal.returnWeight r ≤
        criticalSigmaSq A N * Renewal.returnWeight r := by
    intro r
    exact mul_le_mul_of_nonneg_right hσle (srwKernel_nonneg (2 * r) 0)
  have hF : Renewal.criticalRenewalFunction ϑ N k ≤ Renewal.criticalRenewalFunction A N k := by
    change Renewal.renewalFunction (fun r => criticalSigmaSq ϑ N *
      Renewal.returnWeight r) k ≤ _
    apply Renewal.renewalFunction_mono
    · intro r
      exact mul_nonneg (hσ ϑ hϑ).1.le (srwKernel_nonneg (2 * r) 0)
    · exact hkernel
  have hF0 : 0 ≤ Renewal.criticalRenewalFunction ϑ N k := by
    change 0 ≤ Renewal.renewalFunction (fun r => criticalSigmaSq ϑ N *
      Renewal.returnWeight r) k
    have hone := Renewal.one_le_renewalFunction (fun r =>
      mul_nonneg (hσ ϑ hϑ).1.le (srwKernel_nonneg (2 * r) 0)) k
    exact le_trans (by norm_num) hone
  calc
    criticalSigmaSq ϑ N * Renewal.criticalRenewalFunction ϑ N k ≤
        criticalSigmaSq A N * Renewal.criticalRenewalFunction ϑ N k :=
      mul_le_mul_of_nonneg_right hσle hF0
    _ ≤ criticalSigmaSq A N * Renewal.criticalRenewalFunction A N k :=
      mul_le_mul_of_nonneg_left hF hσA.le
    _ ≤ K / Real.log (1 + (N : ℝ) / k) := hbound k hk hkN

/-- The local critical renewal mass inherits a squared logarithmic bound from the
marked renewal identity and the uniform critical renewal-function estimate. -/
theorem eventually_criticalRenewalMass_scaled_log_sq_bound (A : ℝ) (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in Filter.atTop,
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ d : ℕ, 1 ≤ d → d ≤ N →
        (d : ℝ) * (criticalSigmaSq ϑ N * Renewal.criticalRenewalMass ϑ N d) ≤
          C / (Real.log (1 + (N : ℝ) / d)) ^ 2 := by
  obtain ⟨K, hK, hRF⟩ := eventually_criticalRenewalFunction_uniform_log_bound A hA
  obtain ⟨C₀, hC₀, hmoment⟩ := Renewal.exists_returnWeight_moment_bound
  let C : ℝ := C₀ * K ^ 2
  have hC : 0 < C := mul_pos hC₀ (sq_pos_of_pos hK)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hRF, eventually_criticalSigmaSq_uniform_log_bound A hA,
    Filter.eventually_ge_atTop 2] with N hRF hσ hN
  intro ϑ hϑ d hd hdN
  let σ : ℝ := criticalSigmaSq ϑ N
  let w : ℕ → ℝ := fun r => σ * Renewal.returnWeight r
  have hσpos : 0 < σ := by simpa [σ] using (hσ ϑ hϑ).1
  have hw : ∀ r, 0 ≤ w r := by
    intro r
    exact mul_nonneg hσpos.le (srwKernel_nonneg (2 * r) 0)
  have hstep : ∀ r : ℕ, 1 ≤ r → (r : ℝ) * w r ≤ C₀ * σ := by
    intro r hr
    calc
      (r : ℝ) * w r = σ * ((r : ℝ) * Renewal.returnWeight r) := by ring
      _ ≤ σ * C₀ := mul_le_mul_of_nonneg_left (hmoment r hr) hσpos.le
      _ = C₀ * σ := by ring
  have hlocal := Renewal.mul_renewalMass_le_markedRenewalFunction hw hstep (d - 1)
  have hmarked := markedRenewalFunction_le_sq_renewalFunction hw (d - 1)
  have hlocal' : (d : ℝ) * Renewal.criticalRenewalMass ϑ N d ≤
      C₀ * σ * Renewal.markedRenewalFunction w (d - 1) := by
    change (↑d) * Renewal.renewalMass w d ≤ _
    rw [← Nat.sub_add_cancel (by omega : 1 ≤ d)]
    push_cast
    exact hlocal
  have hlocalσ : (d : ℝ) * (σ * Renewal.criticalRenewalMass ϑ N d) ≤
      C₀ * (σ * Renewal.criticalRenewalFunction ϑ N (d - 1)) ^ 2 := by
    have hRFdef : Renewal.criticalRenewalFunction ϑ N (d - 1) =
        Renewal.renewalFunction w (d - 1) := by
      simp [Renewal.criticalRenewalFunction, w, σ]
    have hsq : C₀ * σ ^ 2 * Renewal.markedRenewalFunction w (d - 1) ≤
        C₀ * σ ^ 2 * (Renewal.renewalFunction w (d - 1)) ^ 2 :=
      mul_le_mul_of_nonneg_left hmarked (mul_nonneg hC₀.le (sq_nonneg σ))
    calc
      (d : ℝ) * (σ * Renewal.criticalRenewalMass ϑ N d) =
          σ * ((d : ℝ) * Renewal.criticalRenewalMass ϑ N d) := by ring
      _ ≤ σ * (C₀ * σ * Renewal.markedRenewalFunction w (d - 1)) :=
        mul_le_mul_of_nonneg_left hlocal' hσpos.le
      _ = C₀ * σ ^ 2 * Renewal.markedRenewalFunction w (d - 1) := by ring
      _ ≤ C₀ * σ ^ 2 * (Renewal.renewalFunction w (d - 1)) ^ 2 := hsq
      _ = C₀ * (σ * Renewal.criticalRenewalFunction ϑ N (d - 1)) ^ 2 := by
        rw [hRFdef]
        ring
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdenpos : 0 < Real.log (1 + (N : ℝ) / d) := by
    apply Real.log_pos
    have : 0 < (N : ℝ) / d := div_pos hNpos hdpos
    linarith
  by_cases hd1 : d = 1
  · subst d
    have hRF1 := hRF ϑ hϑ 1 (by omega) (by omega)
    have hRFnonneg : 1 ≤ Renewal.criticalRenewalFunction ϑ N 1 := by
      change 1 ≤ Renewal.renewalFunction w 1
      exact Renewal.one_le_renewalFunction hw 1
    have hσbound : σ ≤ K / Real.log (1 + (N : ℝ)) := by
      have hpos : 0 < Real.log (1 + (N : ℝ)) := by
        apply Real.log_pos
        have hNgt1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
        linarith
      have hmul : σ ≤ σ * Renewal.criticalRenewalFunction ϑ N 1 := by
        simpa using mul_le_mul_of_nonneg_left hRFnonneg hσpos.le
      have hRF1' : σ * Renewal.criticalRenewalFunction ϑ N 1 ≤
          K / Real.log (1 + (N : ℝ)) := by simpa [σ] using hRF1
      exact hmul.trans hRF1'
    have hbound : C₀ * (σ * Renewal.criticalRenewalFunction ϑ N 0) ^ 2 ≤
        C₀ * (K / Real.log (1 + (N : ℝ))) ^ 2 := by
      have hRF0 : Renewal.criticalRenewalFunction ϑ N 0 = 1 := by simp [Renewal.criticalRenewalFunction]
      rw [hRF0, mul_one]
      have hlogpos : 0 < Real.log (1 + (N : ℝ)) := by simpa using hdenpos
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hσpos.le (by positivity : 0 ≤ K / Real.log (1 + (N : ℝ)))).2
          hσbound) hC₀.le
    have hcase : σ * Renewal.criticalRenewalMass ϑ N 1 ≤
        C₀ * (K / Real.log (1 + (N : ℝ))) ^ 2 := by
      simpa [Renewal.criticalRenewalFunction] using hlocalσ.trans hbound
    have hpos : 0 < Real.log (1 + (N : ℝ)) := by
      apply Real.log_pos
      have hNgt1 : (1 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
      linarith
    have halgebra : C₀ * (K / Real.log (1 + (N : ℝ))) ^ 2 =
        C / (Real.log (1 + (N : ℝ))) ^ 2 := by
      dsimp [C]
      field_simp [ne_of_gt hpos]
    simpa [div_pow] using hcase.trans_eq halgebra
  · have hdge : 2 ≤ d := by omega
    let k : ℕ := d - 1
    have hk : 1 ≤ k := by dsimp [k]; omega
    have hkN : k ≤ N := by dsimp [k]; omega
    have hRFk := hRF ϑ hϑ k hk hkN
    have hRFnonneg : 0 ≤ Renewal.criticalRenewalFunction ϑ N k := by
      change 0 ≤ Renewal.renewalFunction w k
      have hone := Renewal.one_le_renewalFunction hw k
      linarith
    have hscaled : 0 ≤ σ * Renewal.criticalRenewalFunction ϑ N k :=
      mul_nonneg hσpos.le hRFnonneg
    have hscaledle : σ * Renewal.criticalRenewalFunction ϑ N k ≤
        K / Real.log (1 + (N : ℝ) / k) := by simpa [σ, k] using hRFk
    have hdenkle : Real.log (1 + (N : ℝ) / d) ≤
        Real.log (1 + (N : ℝ) / k) := by
      apply Real.log_le_log
      · positivity
      · have hquot : (N : ℝ) / d ≤ (N : ℝ) / k := by
          have hkpos : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
          rw [div_le_div_iff₀ hdpos hkpos]
          have hkd : (k : ℝ) ≤ d := by
            dsimp [k]
            exact_mod_cast (Nat.sub_le d 1)
          nlinarith
        simpa [add_comm] using add_le_add_left hquot 1
    have hdenklepos : 0 < Real.log (1 + (N : ℝ) / k) := by
      exact lt_of_lt_of_le hdenpos hdenkle
    have hinv : (Real.log (1 + (N : ℝ) / k))⁻¹ ≤
        (Real.log (1 + (N : ℝ) / d))⁻¹ :=
      (inv_le_inv₀ hdenklepos hdenpos).2 hdenkle
    have hratioSq : (K / Real.log (1 + (N : ℝ) / k)) ^ 2 ≤
        (K / Real.log (1 + (N : ℝ) / d)) ^ 2 := by
      apply (sq_le_sq₀ (by positivity) (by positivity)).2
      apply mul_le_mul_of_nonneg_left hinv hK.le
    have hfinal' : (d : ℝ) * (σ * Renewal.criticalRenewalMass ϑ N d) ≤
        C₀ * (K / Real.log (1 + (N : ℝ) / d)) ^ 2 := by
      calc
        _ ≤ C₀ * (σ * Renewal.criticalRenewalFunction ϑ N k) ^ 2 := by
          simpa [k, σ, Renewal.criticalRenewalFunction, Nat.sub_add_cancel (by omega : 1 ≤ d)] using hlocalσ
        _ ≤ C₀ * (K / Real.log (1 + (N : ℝ) / k)) ^ 2 :=
          mul_le_mul_of_nonneg_left ((sq_le_sq₀ hscaled (by positivity)).2 hscaledle) hC₀.le
        _ ≤ C₀ * (K / Real.log (1 + (N : ℝ) / d)) ^ 2 :=
          mul_le_mul_of_nonneg_left hratioSq hC₀.le
    have halgebra : C₀ * (K / Real.log (1 + (N : ℝ) / d)) ^ 2 =
        C / (Real.log (1 + (N : ℝ) / d)) ^ 2 := by
      dsimp [C]
      field_simp [ne_of_gt hdenpos]
    exact hfinal'.trans_eq halgebra

/-- On a compact parameter interval, the scalar collision density has a uniform
lower logarithmic envelope on `(0,1]`. -/
theorem exists_scalarDensity_lower_log (B : ℝ) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ t : ℝ, θ ∈ Set.Icc (-B) B → 0 < t → t ≤ 1 →
      c / (t * (1 - Real.log t) ^ 2) ≤ DeltaBose.scalarDensity θ t := by
  let c : ℝ := 1 / (2 * Real.exp 1 * (1 + B) ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, fun θ t hθ ht ht1 => ?_⟩
  let d : ℝ := (1 + B - Real.log t)⁻¹
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have hden : 0 < 1 + B - Real.log t := by linarith
  have hd : 0 < d := inv_pos.mpr hden
  have hdle : d ≤ 1 := by
    dsimp [d]
    rw [inv_le_one₀ hden]
    linarith
  have hslo : -(1 + B - Real.log t) ≤ θ + Real.log t := by
    have := hθ.1
    linarith
  have hsmall : ∀ u : ℝ, u ∈ Ioc 0 d →
      Real.exp ((θ + Real.log t) * u) / Real.Gamma u ≥ Real.exp (-1) * u := by
    intro u hu
    have hu0 : 0 < u := hu.1
    have hGamma : Real.Gamma (u + 1) ≤ 1 := by
      by_cases huEq : u = 1
      · subst u
        norm_num [Real.Gamma_two]
      · have hu1 : u < 1 := lt_of_le_of_ne (hu.2.trans hdle) huEq
        have h := Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma
          (s := 1) (t := 2) (a := 1 - u) (b := u)
          (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)
          (by linarith) hu0 (by ring)
        have harg : (1 - u) * 1 + u * 2 = u + 1 := by ring
        rw [harg] at h
        simpa [Real.Gamma_one, Real.Gamma_two] using h
    have hinv : u ≤ (Real.Gamma u)⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ (Real.Gamma_pos_of_pos hu0)]
      simpa only [Real.Gamma_add_one hu0.ne'] using hGamma
    have hprod : (θ + Real.log t) * u ≥ -1 := by
      have hu' : u ≤ (1 + B - Real.log t)⁻¹ := hu.2
      have hprod' : (1 + B - Real.log t) * u ≤ 1 := by
        calc
          (1 + B - Real.log t) * u ≤
              (1 + B - Real.log t) * (1 + B - Real.log t)⁻¹ :=
            mul_le_mul_of_nonneg_left hu' hden.le
          _ = 1 := mul_inv_cancel₀ hden.ne'
      have hslo' := mul_le_mul_of_nonneg_right hslo hu0.le
      nlinarith
    have hexp : Real.exp (-1) ≤ Real.exp ((θ + Real.log t) * u) :=
      Real.exp_le_exp.mpr hprod
    calc
      Real.exp (-1) * u ≤ Real.exp ((θ + Real.log t) * u) * u :=
        mul_le_mul_of_nonneg_right hexp hu0.le
      _ ≤ Real.exp ((θ + Real.log t) * u) * (Real.Gamma u)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (Real.exp_nonneg _)
      _ = _ := by ring
  have hIntGamma : IntegrableOn
      (DeltaBose.gammaLaplaceIntegrand (θ + Real.log t)) (Ioi 0) :=
    DeltaBose.integrableOn_gammaLaplaceIntegrand _
  have hId : IntegrableOn (fun u : ℝ => u) (Ioc 0 d) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hd.le).mp
      (continuous_id.intervalIntegrable 0 d)
  have hIntSmall : IntegrableOn (fun u : ℝ => Real.exp (-1) * u) (Ioc 0 d) :=
    hId.const_mul _
  have hsubset : Ioc (0 : ℝ) d ⊆ Ioi 0 := fun _ hx => hx.1
  have hsmallInt : (∫ u in Ioc 0 d, Real.exp (-1) * u) ≤
      ∫ u in Ioc 0 d, DeltaBose.gammaLaplaceIntegrand (θ + Real.log t) u := by
    apply setIntegral_mono_on hIntSmall (hIntGamma.mono_set hsubset) measurableSet_Ioc
    intro u hu
    exact hsmall u hu
  have hwhole : (∫ u in Ioc 0 d,
        DeltaBose.gammaLaplaceIntegrand (θ + Real.log t) u) ≤
      ∫ u in Ioi 0, DeltaBose.gammaLaplaceIntegrand (θ + Real.log t) u := by
    apply setIntegral_mono_set hIntGamma
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      exact (DeltaBose.gammaLaplaceIntegrand_pos _ hu).le
    · exact Filter.Eventually.of_forall hsubset
  have hbase : (Real.exp (-1) * d ^ 2 / 2) ≤
      ∫ u in Ioi 0, DeltaBose.gammaLaplaceIntegrand (θ + Real.log t) u := by
    calc
      Real.exp (-1) * d ^ 2 / 2 = ∫ u in Ioc 0 d, Real.exp (-1) * u := by
        rw [integral_const_mul]
        rw [← intervalIntegral.integral_of_le hd.le]
        rw [integral_id]
        simp
        ring
      _ ≤ _ := hsmallInt.trans hwhole
  rw [DeltaBose.scalarDensity_eq_laplace θ ht]
  have hdval : d = (1 + B - Real.log t)⁻¹ := rfl
  rw [hdval] at hbase
  have htarget : c / (t * (1 - Real.log t) ^ 2) ≤
      t⁻¹ * (Real.exp (-1) * (1 + B - Real.log t)⁻¹ ^ 2 / 2) := by
    have hpos2 : 0 < 1 - Real.log t := by linarith
    have hlogfactor : 1 + B - Real.log t ≤ (1 + B) * (1 - Real.log t) := by
      nlinarith [hlog, hB]
    have hfactor : 0 < (1 + B) * (1 - Real.log t) := by positivity
    have hinv : ((1 + B) * (1 - Real.log t))⁻¹ ≤
        (1 + B - Real.log t)⁻¹ :=
      (inv_le_inv₀ hfactor hden).2 hlogfactor
    have hsq : ((1 + B) * (1 - Real.log t))⁻¹ ^ 2 ≤
        (1 + B - Real.log t)⁻¹ ^ 2 := by
      nlinarith [hinv, inv_pos.mpr hfactor, inv_pos.mpr hden]
    dsimp [c]
    rw [one_div]
    rw [div_eq_mul_inv, show (t * (1 - Real.log t) ^ 2)⁻¹ =
      t⁻¹ * ((1 - Real.log t) ^ 2)⁻¹ by field_simp [ht.ne']]
    have hcoef : (2 * Real.exp 1 * (1 + B) ^ 2)⁻¹ *
        ((1 - Real.log t) ^ 2)⁻¹ ≤
        Real.exp (-1) * (1 + B - Real.log t)⁻¹ ^ 2 / 2 := by
      rw [Real.exp_neg]
      field_simp
      nlinarith [hsq]
    calc
      (2 * Real.exp 1 * (1 + B) ^ 2)⁻¹ *
          (t⁻¹ * ((1 - Real.log t) ^ 2)⁻¹) =
        t⁻¹ * ((2 * Real.exp 1 * (1 + B) ^ 2)⁻¹ *
          ((1 - Real.log t) ^ 2)⁻¹) := by ring
      _ ≤ t⁻¹ * (Real.exp (-1) * (1 + B - Real.log t)⁻¹ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_left hcoef (inv_nonneg.mpr ht.le)
  exact htarget.trans (mul_le_mul_of_nonneg_left hbase (inv_nonneg.mpr ht.le))

/-- On a positive gap between adjacent renewal cells, the compact scalar lower
envelope is controlled by the logarithm at the discrete gap scale. -/
theorem scalarDensity_lower_on_scaled_gap {B c : ℝ} (hc : 0 < c)
    (hscalar : ∀ θ t : ℝ, θ ∈ Set.Icc (-B) B → 0 < t → t ≤ 1 →
      c / (t * (1 - Real.log t) ^ 2) ≤ DeltaBose.scalarDensity θ t)
    (N d : ℕ) (hN : 2 ≤ N) (hd : 1 ≤ d) (hdN : d + 1 ≤ N)
    {θ : ℝ} (hθ : θ ∈ Set.Icc (-B) B) :
    ∀ u : ℝ, (d : ℝ) / N ≤ u → u ≤ ((d + 1 : ℕ) : ℝ) / N →
      c * N / (2 * d * (1 + (Real.log 2)⁻¹) ^ 2 * (Real.log (1 + (N : ℝ) / d)) ^ 2) ≤
        DeltaBose.scalarDensity θ u := by
  intro u huLower huUpper
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hdleN : (d : ℝ) ≤ N := by exact_mod_cast (by omega : d ≤ N)
  have hx : 1 ≤ (N : ℝ) / d := by
    rw [le_div_iff₀ hdpos]
    nlinarith
  have hLpos : 0 < Real.log (1 + (N : ℝ) / d) :=
    Real.log_pos (by linarith)
  have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2L : Real.log 2 ≤ Real.log (1 + (N : ℝ) / d) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogxL : Real.log ((N : ℝ) / d) ≤ Real.log (1 + (N : ℝ) / d) :=
    Real.log_le_log (by positivity) (by linarith)
  have hLover : 1 ≤ Real.log (1 + (N : ℝ) / d) / Real.log 2 := by
    apply (le_div_iff₀ hlog2pos).2
    simpa using hlog2L
  have hlogrel : Real.log ((N : ℝ) / d) = -Real.log ((d : ℝ) / N) := by
    rw [Real.log_div hNpos.ne' hdpos.ne', Real.log_div hdpos.ne' hNpos.ne']
    ring
  have huPos : 0 < u := lt_of_lt_of_le (div_pos hdpos hNpos) huLower
  have huOne : u ≤ 1 := by
    calc
      u ≤ ((d + 1 : ℕ) : ℝ) / N := huUpper
      _ ≤ 1 := (div_le_one hNpos).2 (by exact_mod_cast hdN)
  have hlogu : Real.log ((d : ℝ) / N) ≤ Real.log u :=
    Real.log_le_log (div_pos hdpos hNpos) huLower
  let M : ℝ := 1 + (Real.log 2)⁻¹
  have hM : 0 < M := by dsimp [M]; positivity
  have hfac : 0 < 1 - Real.log u := by
    have := Real.log_nonpos huPos.le huOne
    linarith
  have hfacBound : 1 - Real.log u ≤ M * Real.log (1 + (N : ℝ) / d) := by
    have hneg : -Real.log u ≤ Real.log ((N : ℝ) / d) := by linarith [hlogu, hlogrel]
    have hMmul : M * Real.log (1 + (N : ℝ) / d) =
        Real.log (1 + (N : ℝ) / d) + Real.log (1 + (N : ℝ) / d) / Real.log 2 := by
      dsimp [M]
      rw [div_eq_mul_inv]
      ring
    calc
      1 - Real.log u ≤ 1 + Real.log ((N : ℝ) / d) := by linarith
      _ ≤ 1 + Real.log (1 + (N : ℝ) / d) := by
        simpa [add_comm] using add_le_add_left hlogxL 1
      _ ≤ Real.log (1 + (N : ℝ) / d) +
          Real.log (1 + (N : ℝ) / d) / Real.log 2 := by linarith [hLover]
      _ = _ := hMmul.symm
  have huUpper' : u ≤ 2 * (d : ℝ) / N := by
    calc
      u ≤ ((d + 1 : ℕ) : ℝ) / N := huUpper
      _ ≤ 2 * (d : ℝ) / N := by
        apply div_le_div_of_nonneg_right _ hNpos.le
        exact_mod_cast (by omega : d + 1 ≤ 2 * d)
  have hdenBound : u * (1 - Real.log u) ^ 2 ≤
      (2 * (d : ℝ) / N) * (M * Real.log (1 + (N : ℝ) / d)) ^ 2 := by
    calc
      u * (1 - Real.log u) ^ 2 ≤
          (2 * (d : ℝ) / N) * (1 - Real.log u) ^ 2 :=
        mul_le_mul_of_nonneg_right huUpper' (sq_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ hfac.le (by positivity)).2 hfacBound) (by positivity)
  have hdiv : c / ((2 * (d : ℝ) / N) * (M * Real.log (1 + (N : ℝ) / d)) ^ 2) ≤
      c / (u * (1 - Real.log u) ^ 2) :=
    div_le_div_of_nonneg_left hc.le (mul_pos huPos (sq_pos_of_pos hfac)) hdenBound
  have heq : c / ((2 * (d : ℝ) / N) * (M * Real.log (1 + (N : ℝ) / d)) ^ 2) =
      c * N / (2 * d * M ^ 2 * (Real.log (1 + (N : ℝ) / d)) ^ 2) := by
    dsimp [M]
    field_simp [ne_of_gt hNpos, ne_of_gt hdpos, ne_of_gt hlog2pos, ne_of_gt hLpos]
  rw [← heq]
  exact hdiv.trans (hscalar θ u hθ huPos huOne)

/-- The lower envelope integrates to a reciprocal logarithm uniformly on a compact
parameter interval. -/
theorem exists_integral_scalarDensity_lower_log (B : ℝ) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ h : ℝ, θ ∈ Set.Icc (-B) B → 0 < h → h ≤ 1 →
      c / (1 - Real.log h) ≤ ∫ u in Ioc (0 : ℝ) h, DeltaBose.scalarDensity θ u := by
  obtain ⟨c, hc, hpoint⟩ := exists_scalarDensity_lower_log B hB
  refine ⟨c, hc, fun θ h hθ hh hh1 => ?_⟩
  have hkernel : IntegrableOn (fun u : ℝ => (u * (1 - Real.log u) ^ 2)⁻¹) (Ioc 0 h) :=
    integrableOn_inv_mul_one_sub_log_sq_Ioc hh hh1
  have hkernelC : IntegrableOn (fun u : ℝ => c * (u * (1 - Real.log u) ^ 2)⁻¹) (Ioc 0 h) :=
    hkernel.const_mul c
  have hscalar : IntegrableOn (DeltaBose.scalarDensity θ) (Ioc 0 h) :=
    Renewal.integrableOn_scalarDensity_Ioc θ h
  have hmono :
      ∫ u in Ioc (0 : ℝ) h, c * (u * (1 - Real.log u) ^ 2)⁻¹ ≤
        ∫ u in Ioc (0 : ℝ) h, DeltaBose.scalarDensity θ u := by
    apply setIntegral_mono_on hkernelC hscalar measurableSet_Ioc
    intro u hu
    simpa [div_eq_mul_inv] using hpoint θ u hθ hu.1 (hu.2.trans hh1)
  rw [integral_const_mul, integral_inv_mul_one_sub_log_sq_Ioc hh hh1] at hmono
  simpa only [mul_comm, div_eq_mul_inv] using hmono

/-- The compact-parameter scalar lower envelope, in the nonnegative integral form
used on the diagonal cells. -/
theorem exists_lintegral_scalarDensity_lower_log (B : ℝ) (hB : 0 ≤ B) :
    ∃ c : ℝ, 0 < c ∧ ∀ θ h : ℝ, θ ∈ Set.Icc (-B) B → 0 < h → h ≤ 1 →
      ENNReal.ofReal (c / (1 - Real.log h)) ≤
        ∫⁻ u in Ioo (0 : ℝ) h, ENNReal.ofReal (DeltaBose.scalarDensity θ u) := by
  obtain ⟨c, hc, hreal⟩ := exists_integral_scalarDensity_lower_log B hB
  refine ⟨c, hc, fun θ h hθ hh hh1 => ?_⟩
  rw [setLIntegral_congr (Ioo_ae_eq_Ioc : Ioo (0 : ℝ) h =ᵐ[volume] Ioc 0 h)]
  have hi : IntegrableOn (DeltaBose.scalarDensity θ) (Ioc 0 h) :=
    Renewal.integrableOn_scalarDensity_Ioc θ h
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) h)] DeltaBose.scalarDensity θ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    exact (DeltaBose.scalarDensity_pos θ hu.1).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg]
  exact ENNReal.ofReal_le_ofReal (hreal θ h hθ hh hh1)

/-- Iterating over a triangular pair cell is the same as integrating the elapsed
time over a fixed interval. -/
theorem lintegral_renewalPair_triangle_eq {l r h : ℝ}
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : ℝ × ℝ in {p | l < p.1 ∧ p.1 < r ∧ p.1 < p.2 ∧ p.2 < p.1 + h},
      F (p.2 - p.1)) =
      ENNReal.ofReal (r - l) * (∫⁻ u in Ioo (0 : ℝ) h, F u) := by
  let S : Set (ℝ × ℝ) := {p | l < p.1 ∧ p.1 < r ∧ p.1 < p.2 ∧ p.2 < p.1 + h}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  calc
    (∫⁻ p : ℝ × ℝ in S, F (p.2 - p.1)) =
        ∫⁻ s in Ioo l r, ∫⁻ t in Ioo s (s + h), F (t - s) := by
      rw [← lintegral_indicator hS, Measure.volume_eq_prod]
      change (∫⁻ p : ℝ × ℝ,
        S.indicator (F ∘ (fun p : ℝ × ℝ => p.2 - p.1)) p
          ∂(volume.prod volume)) = _
      rw [MeasureTheory.lintegral_prod (μ := volume) (ν := volume)
        (f := S.indicator (F ∘ (fun p : ℝ × ℝ => p.2 - p.1)))
        ((hF.comp (by fun_prop : Measurable (fun p : ℝ × ℝ => p.2 - p.1))).indicator hS).aemeasurable,
        ← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ Ioo l r
      · rw [indicator_of_mem hs, ← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro t
        by_cases ht : t ∈ Ioo s (s + h)
        · rw [indicator_of_mem ht]
          have hp : (s, t) ∈ S := by
            change l < s ∧ s < r ∧ s < t ∧ t < s + h
            exact ⟨hs.1, hs.2, ht.1, ht.2⟩
          rw [indicator_of_mem hp]
          rfl
        · rw [indicator_of_notMem ht]
          have hp : (s, t) ∉ S := by
            intro hp
            change l < s ∧ s < r ∧ s < t ∧ t < s + h at hp
            exact ht ⟨hp.2.2.1, hp.2.2.2⟩
          rw [indicator_of_notMem hp]
      · rw [indicator_of_notMem hs]
        have hz : (fun t : ℝ => S.indicator
            (F ∘ (fun p : ℝ × ℝ => p.2 - p.1)) (s, t)) =
            fun _ => 0 := by
          funext t
          have hp : (s, t) ∉ S := by
            intro hp
            change l < s ∧ s < r ∧ s < t ∧ t < s + h at hp
            exact hs ⟨hp.1, hp.2.1⟩
          rw [indicator_of_notMem hp]
        rw [hz, lintegral_zero]
    _ = ENNReal.ofReal (r - l) * (∫⁻ u in Ioo (0 : ℝ) h, F u) := by
      have hshift : ∀ s : ℝ,
          (∫⁻ t in Ioo s (s + h), F (t - s)) = ∫⁻ u in Ioo (0 : ℝ) h, F u := by
        intro s
        rw [← DeltaBose.lintegral_Ioo_sub_right s (s + h) F]
        simp
      simp_rw [hshift]
      simp [lintegral_const, Real.volume_Ioo, mul_comm]

/-- A pointwise lower bound on a rectangle yields its constant lower integral. -/
theorem lintegral_Ioo_prod_lower {l r u v : ℝ}
    (F : ℝ × ℝ → ℝ≥0∞) (c : ℝ≥0∞)
    (hF : ∀ p ∈ Ioo l r ×ˢ Ioo u v, c ≤ F p) :
    c * ENNReal.ofReal (r - l) * ENNReal.ofReal (v - u) ≤
      ∫⁻ p : ℝ × ℝ in Ioo l r ×ˢ Ioo u v, F p := by
  have hs : MeasurableSet (Ioo l r ×ˢ Ioo u v) := measurableSet_Ioo.prod measurableSet_Ioo
  have hvol : volume (Ioo l r ×ˢ Ioo u v) = ENNReal.ofReal (r - l) * ENNReal.ofReal (v - u) := by
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo]
  calc
    c * ENNReal.ofReal (r - l) * ENNReal.ofReal (v - u) = c * volume (Ioo l r ×ˢ Ioo u v) := by
      rw [hvol]
      ac_rfl
    _ = ∫⁻ p : ℝ × ℝ in Ioo l r ×ˢ Ioo u v, c := by
      simp [lintegral_const]
    _ ≤ ∫⁻ p : ℝ × ℝ in Ioo l r ×ˢ Ioo u v, F p := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hs] with p hp
      exact hF p hp


end Critical2DKPZ.Collision

end
