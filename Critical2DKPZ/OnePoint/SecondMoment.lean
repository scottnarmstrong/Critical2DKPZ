/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.CriticalGap
public import Critical2DKPZ.Renewal.Overshoot
public import Critical2DKPZ.Renewal.PolymerBridge
public import Critical2DKPZ.Renewal.CriticalParameter
public import Critical2DKPZ.Polymer.SmoothedCovariance
import Mathlib.Tactic

/-! # Renewal and smoothed one-point second moments -/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped Topology
open scoped BigOperators

namespace Critical2DKPZ.OnePoint

/-- The free second moment increases with the Gaussian variance parameter. -/
theorem freeSecondMoment_mono_sigmaSq {β γ : ℝ}
    (hσ : Polymer.sigmaSq β ≤ Polymer.sigmaSq γ) (n : ℕ) :
    Renewal.freeSecondMoment β n ≤ Renewal.freeSecondMoment γ n := by
  have hβ : 0 ≤ Polymer.sigmaSq β := by
    unfold Polymer.sigmaSq
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β))
  have hw : ∀ r, 0 ≤ Polymer.sigmaSq β * Renewal.returnWeight r := fun r =>
    mul_nonneg hβ (Critical2DKPZ.srwKernel_nonneg (2 * r) 0)
  have hwγ : ∀ r, Polymer.sigmaSq β * Renewal.returnWeight r ≤
      Polymer.sigmaSq γ * Renewal.returnWeight r := fun r =>
    mul_le_mul_of_nonneg_right hσ (Critical2DKPZ.srwKernel_nonneg (2 * r) 0)
  rw [Renewal.freeSecondMoment_eq_renewalFunction β,
    Renewal.freeSecondMoment_eq_renewalFunction γ]
  exact Renewal.renewalFunction_mono hw hwγ n

/-- A first-moment bound for the period-two return weights. -/
theorem returnWeight_cutoffFirstMoment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℕ,
      Renewal.cutoffFirstMoment Renewal.returnWeight s ≤ C * ((s + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hKpos, hK⟩ := Critical2DKPZ.srwKernel_two_mul_zero_localCLT
  let C := 1 / Real.pi + K
  have hKnonneg : 0 ≤ K := hKpos.le
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hterm (r : ℕ) (hr : 1 ≤ r) :
      (r : ℝ) * Renewal.returnWeight r ≤ C := by
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
    have hrone : 1 ≤ (r : ℝ) := by exact_mod_cast hr
    have hlocal :
        |Renewal.returnWeight r - (1 / Real.pi) * (r : ℝ)⁻¹| ≤
          K / (r : ℝ) ^ 2 := by
      simpa only [Renewal.returnWeight] using hK r hr
    have hupper := (abs_le.mp hlocal).2
    have hq : Renewal.returnWeight r ≤
        (1 / Real.pi) * (r : ℝ)⁻¹ + K / (r : ℝ) ^ 2 := by
      linarith only [hupper]
    calc
      (r : ℝ) * Renewal.returnWeight r ≤
          (r : ℝ) * ((1 / Real.pi) * (r : ℝ)⁻¹ + K / (r : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg r)
      _ = 1 / Real.pi + K / (r : ℝ) := by
        field_simp [ne_of_gt hrpos]
      _ ≤ C := by
        dsimp [C]
        exact add_le_add le_rfl (div_le_self hKnonneg hrone)
  have hsum (s : ℕ) :
      (∑ r ∈ Finset.Icc 1 s, (r : ℝ) * Renewal.returnWeight r) ≤
        C * ((s + 1 : ℕ) : ℝ) := by
    have hsub : Finset.Icc 1 s ⊆ Finset.range (s + 1) := by
      intro r hr
      simp only [Finset.mem_Icc] at hr
      simp only [Finset.mem_range]
      omega
    have hcard : (Finset.Icc 1 s).card ≤ s + 1 := by
      have h := Finset.card_le_card hsub
      calc
        (Finset.Icc 1 s).card ≤ (Finset.range (s + 1)).card := h
        _ = s + 1 := by simp
    calc
      _ ≤ ∑ r ∈ Finset.Icc 1 s, C :=
        Finset.sum_le_sum fun r hr => hterm r (Finset.mem_Icc.mp hr).1
      _ = ((Finset.Icc 1 s).card : ℝ) * C := by
        simp only [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((s + 1 : ℕ) : ℝ) * C :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hCpos.le
      _ = C * ((s + 1 : ℕ) : ℝ) := by ring
  exact ⟨C, hCpos, hsum⟩

/-- Below criticality, the gap between the geometric resolvent and the variance-weighted free second moment is nonnegative and bounded by the inverse squared renewal gap. -/
theorem renewalGap_secondMoment_bounds :
    ∃ C : ℝ, ∀ β : ℝ, 0 < β → ∀ s : ℕ, 0 < renewalGap β s →
      0 ≤ Real.pi / renewalGap β s - Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 s 0 ω ^ 2 ∂disorderLaw) ∧
      Real.pi / renewalGap β s - Polymer.sigmaSq β *
        (∫ ω, pointToPlane β 0 s 0 ω ^ 2 ∂disorderLaw) ≤
        C / renewalGap β s ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := returnWeight_cutoffFirstMoment_bound
  refine ⟨Real.pi ^ 2 * C₀, fun β hβ s hgap => ?_⟩
  let σ := Polymer.sigmaSq β
  let w : ℕ → ℝ := fun r => σ * Renewal.returnWeight r
  have hσpos : 0 < σ := by
    dsimp [σ, Polymer.sigmaSq]
    apply sub_pos.mpr
    rw [Real.one_lt_exp_iff]
    exact sq_pos_of_pos hβ
  have hw : ∀ r, 0 ≤ w r := fun r =>
    mul_nonneg hσpos.le (Critical2DKPZ.srwKernel_nonneg (2 * r) 0)
  have hmass : Renewal.cutoffMass w s = σ * Critical2DKPZ.replicaOverlap s := by
    calc
      Renewal.cutoffMass w s = ∑ r ∈ Finset.Icc 1 s, σ * Renewal.returnWeight r := rfl
      _ = σ * ∑ r ∈ Finset.Icc 1 s, Renewal.returnWeight r := by rw [← Finset.mul_sum]
      _ = σ * Critical2DKPZ.replicaOverlap s := by rw [Renewal.sum_returnWeight]
  have hgapEq : renewalGap β s =
      Real.pi * (1 - Renewal.cutoffMass w s) / σ := by
    change Real.pi / σ - Real.pi * Critical2DKPZ.replicaOverlap s = _
    rw [hmass]
    field_simp [ne_of_gt hσpos]
  have h1W : 0 < 1 - Renewal.cutoffMass w s := by
    have hquot : 0 < (Real.pi * (1 - Renewal.cutoffMass w s)) / σ := by
      rw [← hgapEq]
      exact hgap
    have hnum := (div_pos_iff_of_pos_right hσpos).mp hquot
    exact (mul_pos_iff_of_pos_left Real.pi_pos).mp hnum
  have hWlt : Renewal.cutoffMass w s < 1 := by linarith
  have hM_eq : Renewal.cutoffFirstMoment w s =
      σ * Renewal.cutoffFirstMoment Renewal.returnWeight s := by
    unfold Renewal.cutoffFirstMoment
    calc
      (∑ r ∈ Finset.Icc 1 s, (r : ℝ) * w r) =
          ∑ r ∈ Finset.Icc 1 s, σ * ((r : ℝ) * Renewal.returnWeight r) := by
        apply Finset.sum_congr rfl
        intro r hr
        simp only [w]
        ring
      _ = σ * ∑ r ∈ Finset.Icc 1 s, (r : ℝ) * Renewal.returnWeight r := by
        rw [Finset.mul_sum]
  have hM : Renewal.cutoffFirstMoment w s ≤
      σ * (C₀ * ((s + 1 : ℕ) : ℝ)) := by
    rw [hM_eq]
    exact mul_le_mul_of_nonneg_left (hC₀ s) hσpos.le
  have hfree :
      (∫ ω, pointToPlane β 0 s 0 ω ^ 2 ∂disorderLaw) =
        Renewal.renewalFunction w s := by
    change Renewal.freeSecondMoment β s = _
    rw [Renewal.freeSecondMoment_eq_renewalFunction]
    rfl
  have htarget : Real.pi / renewalGap β s - σ *
      (∫ ω, pointToPlane β 0 s 0 ω ^ 2 ∂disorderLaw) =
      σ * (1 / (1 - Renewal.cutoffMass w s) - Renewal.renewalFunction w s) := by
    rw [hfree, hgapEq]
    field_simp [ne_of_gt hσpos, ne_of_gt h1W, ne_of_gt hgap, ne_of_gt Real.pi_pos]
  have hlow := Renewal.geometric_sub_renewalFunction_nonneg hw s hWlt
  have hupp := Renewal.geometric_sub_renewalFunction_le hw s hWlt
  constructor
  · rw [htarget]
    exact mul_nonneg hσpos.le hlow
  · rw [htarget]
    have hdenpos : 0 < ((s + 1 : ℕ) : ℝ) * (1 - Renewal.cutoffMass w s) ^ 2 :=
      mul_pos (by positivity) (sq_pos_of_pos h1W)
    have hbound := div_le_div_of_nonneg_right hM hdenpos.le
    have hupp' :
        1 / (1 - Renewal.cutoffMass w s) - Renewal.renewalFunction w s ≤
          Renewal.cutoffFirstMoment w s /
            (((s + 1 : ℕ) : ℝ) * (1 - Renewal.cutoffMass w s) ^ 2) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hupp
    calc
      σ * (1 / (1 - Renewal.cutoffMass w s) - Renewal.renewalFunction w s)
          ≤ σ * (Renewal.cutoffFirstMoment w s /
            (((s + 1 : ℕ) : ℝ) * (1 - Renewal.cutoffMass w s) ^ 2)) :=
              mul_le_mul_of_nonneg_left hupp' hσpos.le
      _ ≤ σ * ((σ * (C₀ * ((s + 1 : ℕ) : ℝ))) /
            (((s + 1 : ℕ) : ℝ) * (1 - Renewal.cutoffMass w s) ^ 2)) :=
              mul_le_mul_of_nonneg_left hbound hσpos.le
      _ = Real.pi ^ 2 * C₀ / renewalGap β s ^ 2 := by
        rw [hgapEq]
        field_simp [ne_of_gt hσpos, ne_of_gt h1W, ne_of_gt Real.pi_pos]

/-- The variance-weighted free polymer second moment has a uniform inverse-logarithmic bound on compact critical-parameter intervals and fixed time horizons. -/
private theorem sigmaSq_secondMoment_le_uniform_pos (A T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ k : ℕ,
      1 ≤ k → (k : ℝ) ≤ T * N →
      Polymer.sigmaSq (criticalBeta ϑ N) *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw ≤
          C / Real.log (1 + (N : ℝ) / k) := by
  obtain ⟨C, hCpos, hC⟩ := Renewal.criticalRenewalFunction_log_bound_horizon A T
  have hfreeEvent := Renewal.eventually_freeSecondMoment_eq_criticalRenewalFunction A
  have hlogEvent : ∀ᶠ N : ℕ in atTop, |A| < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |A|
  refine ⟨C, hCpos, ?_⟩
  filter_upwards [hC, hlogEvent, eventually_ge_atTop 2, hfreeEvent]
    with N hNbound hlog hN hfreeA
  intro ϑ hϑ k hk hkT
  have hN1 : 1 ≤ N := by omega
  have hA0 : 0 ≤ A := by linarith only [hϑ.1, hϑ.2]
  have hAabs : A = |A| := (abs_of_nonneg hA0).symm
  have hθabs : |ϑ| ≤ A := abs_le.mpr ⟨hϑ.1, hϑ.2⟩
  have hθlog : |ϑ| < Real.log (N : ℝ) := by
    have hθabsA : |ϑ| ≤ |A| := by
      have h := hθabs
      rw [hAabs] at h
      exact h
    exact lt_of_le_of_lt hθabsA hlog
  have hAlog : |A| < Real.log (N : ℝ) := hlog
  have hσθ := criticalBeta_spec_of_abs_lt_log hN1 hθlog
  have hσA := criticalBeta_spec_of_abs_lt_log hN1 hAlog
  have hσθPolymer : Polymer.sigmaSq (criticalBeta ϑ N) =
      Critical2DKPZ.criticalSigmaSq ϑ N := by
    simpa only [Polymer.sigmaSq] using hσθ
  have hσAPolymer : Polymer.sigmaSq (criticalBeta A N) =
      Critical2DKPZ.criticalSigmaSq A N := by
    simpa only [Polymer.sigmaSq] using hσA
  have hvariance : Critical2DKPZ.criticalSigmaSq ϑ N ≤
      Critical2DKPZ.criticalSigmaSq A N :=
    Renewal.criticalSigmaSq_mono_parameter (by omega) hϑ.2
  have hvarianceβ : Polymer.sigmaSq (criticalBeta ϑ N) ≤
      Polymer.sigmaSq (criticalBeta A N) := by
    calc
      Polymer.sigmaSq (criticalBeta ϑ N) = Critical2DKPZ.criticalSigmaSq ϑ N := hσθPolymer
      _ ≤ Critical2DKPZ.criticalSigmaSq A N := hvariance
      _ = Polymer.sigmaSq (criticalBeta A N) := hσAPolymer.symm
  have hfreeMono : Renewal.freeSecondMoment (criticalBeta ϑ N) k ≤
      Renewal.freeSecondMoment (criticalBeta A N) k := by
    exact freeSecondMoment_mono_sigmaSq hvarianceβ k
  have hfreeNonneg : 0 ≤ Renewal.freeSecondMoment (criticalBeta ϑ N) k := by
    rw [Renewal.freeSecondMoment_eq_renewalFunction]
    have hw : ∀ r, 0 ≤ Polymer.sigmaSq (criticalBeta ϑ N) * Renewal.returnWeight r :=
      fun r => mul_nonneg (by
        unfold Polymer.sigmaSq
        exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _)))
        (Critical2DKPZ.srwKernel_nonneg (2 * r) 0)
    exact le_trans (by norm_num) (Renewal.one_le_renewalFunction hw k)
  have hσApos : 0 < Critical2DKPZ.criticalSigmaSq A N :=
    criticalSigmaSq_pos_of_abs_lt_log hN1 hAlog
  have hbound' : Critical2DKPZ.criticalSigmaSq A N *
      Renewal.freeSecondMoment (criticalBeta A N) k ≤
        C / Real.log (1 + (N : ℝ) / k) := by
    rw [hfreeA k]
    exact hNbound k hk hkT
  calc
    Polymer.sigmaSq (criticalBeta ϑ N) *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw =
      Critical2DKPZ.criticalSigmaSq ϑ N *
        Renewal.freeSecondMoment (criticalBeta ϑ N) k := by
          rw [hσθPolymer]
          rfl
    _ ≤ Critical2DKPZ.criticalSigmaSq A N *
        Renewal.freeSecondMoment (criticalBeta A N) k :=
      mul_le_mul hvariance hfreeMono hfreeNonneg hσApos.le
    _ ≤ C / Real.log (1 + (N : ℝ) / k) := hbound'

/-- The square of the point-to-plane polymer mass is integrable. -/
theorem integrable_pointToPlane_sq (β : ℝ) (k : ℕ) :
    Integrable (fun ω => pointToPlane β 0 k 0 ω ^ 2) disorderLaw :=
  Polymer.integrable_pow_pointToPlane β 0 k 0 2

/-- The variance-weighted free polymer second moment has a uniform inverse-logarithmic bound on fixed time horizons. -/
theorem sigmaSq_secondMoment_le_uniform (A T : ℝ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ k : ℕ,
      1 ≤ k → (k : ℝ) ≤ T * N →
      Polymer.sigmaSq (criticalBeta ϑ N) *
        ∫ ω, pointToPlane (criticalBeta ϑ N) 0 k 0 ω ^ 2 ∂disorderLaw ≤
          C / Real.log (1 + (N : ℝ) / k) := by
  obtain ⟨C, _, hC⟩ := sigmaSq_secondMoment_le_uniform_pos A T
  exact ⟨C, hC⟩

/-- A difference of replica overlaps equals the return-kernel sum over the intervening times. -/
theorem replicaOverlap_sub_eq_sum (s n : ℕ) (hsn : s ≤ n) :
    Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s =
      ∑ r ∈ Finset.Icc (s + 1) n, Renewal.returnWeight r := by
  have hsplit : Finset.Icc 1 n = Finset.Icc 1 s ∪ Finset.Icc (s + 1) n := by
    ext r
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 s) (Finset.Icc (s + 1) n) := by
    apply Finset.disjoint_left.mpr
    intro r hr hs'
    simp only [Finset.mem_Icc] at hr hs'
    omega
  have hsum :
      (∑ r ∈ Finset.Icc 1 n, Renewal.returnWeight r) =
        (∑ r ∈ Finset.Icc 1 s, Renewal.returnWeight r) +
          ∑ r ∈ Finset.Icc (s + 1) n, Renewal.returnWeight r := by
    rw [hsplit, Finset.sum_union hdisj]
  change (∑ r ∈ Finset.Icc 1 n, Renewal.returnWeight r) -
    (∑ r ∈ Finset.Icc 1 s, Renewal.returnWeight r) = _
  linarith only [hsum]

private theorem returnWeight_mul_le_constant :
    ∃ D : ℝ, 0 < D ∧ ∀ r : ℕ, 1 ≤ r → (r : ℝ) * Renewal.returnWeight r ≤ D := by
  obtain ⟨K, hKpos, hK⟩ := Critical2DKPZ.srwKernel_two_mul_zero_localCLT
  let D := 1 / Real.pi + K
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hbound (r : ℕ) (hr : 1 ≤ r) :
      (r : ℝ) * Renewal.returnWeight r ≤ D := by
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
    have hlocal :
        |Renewal.returnWeight r - (1 / Real.pi) * (r : ℝ)⁻¹| ≤ K / (r : ℝ) ^ 2 := by
      simpa only [Renewal.returnWeight] using hK r hr
    have hupper := (abs_le.mp hlocal).2
    have hq : Renewal.returnWeight r ≤
        (1 / Real.pi) * (r : ℝ)⁻¹ + K / (r : ℝ) ^ 2 := by
      linarith only [hupper]
    calc
      (r : ℝ) * Renewal.returnWeight r ≤
          (r : ℝ) * ((1 / Real.pi) * (r : ℝ)⁻¹ + K / (r : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg r)
      _ = 1 / Real.pi + K / (r : ℝ) := by field_simp
      _ ≤ D := by
        dsimp [D]
        exact add_le_add le_rfl (div_le_self hKpos.le (by exact_mod_cast hr))
  exact ⟨D, hDpos, hbound⟩

/-- A uniform boundary convolution bound for the period-two return weights. -/
private theorem returnWeight_boundary_sum_le :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℕ,
      (∑ r ∈ Finset.Icc 1 t, Renewal.returnWeight r *
        (replicaOverlap t - replicaOverlap (t - r))) ≤ B := by
  obtain ⟨D, hDpos, hD⟩ := returnWeight_mul_le_constant
  refine ⟨8 * D ^ 2, by positivity, ?_⟩
  intro t
  classical
  by_cases ht : t = 0
  · simp [ht]
    positivity
  have htpos : 0 < (t : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero ht)
  let m := t / 2
  have hqnonneg (r : ℕ) : 0 ≤ Renewal.returnWeight r :=
    Critical2DKPZ.srwKernel_nonneg (2 * r) 0
  have hqle (r : ℕ) (hr : 1 ≤ r) :
      Renewal.returnWeight r ≤ D / (r : ℝ) := by
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr)
    apply (le_div_iff₀ hrpos).2
    nlinarith [hD r hr]
  have hqhigh (r : ℕ) (hr : m < r) :
      Renewal.returnWeight r ≤ 2 * D / (t : ℝ) := by
    have hr1 : 1 ≤ r := by dsimp [m] at hr; omega
    have htrNat : t ≤ 2 * r := by dsimp [m] at hr; omega
    have htr : (t : ℝ) ≤ 2 * (r : ℝ) := by exact_mod_cast htrNat
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr1)
    calc
      Renewal.returnWeight r ≤ D / (r : ℝ) := hqle r hr1
      _ ≤ 2 * D / (t : ℝ) := (div_le_div_iff₀ hrpos htpos).2 (by nlinarith [hDpos.le, htr])
  have hcardInterval (r : ℕ) (hr : 1 ≤ r) (hrt : r ≤ t) :
      (Finset.Icc (t - r + 1) t).card = r := by
    rw [Nat.card_Icc]
    omega
  let lo := Finset.Icc 1 m
  let hi := Finset.Icc (m + 1) t
  have hOuter : Finset.Icc 1 t = lo ∪ hi := by
    ext r
    simp only [lo, hi, Finset.mem_union, Finset.mem_Icc]
    dsimp [m]
    omega
  have hOuterDisj : Disjoint lo hi := by
    apply Finset.disjoint_left.mpr
    intro r hrlo hrhi
    simp only [lo, hi, Finset.mem_Icc] at hrlo hrhi
    omega
  have hcardLo : (lo.card : ℝ) ≤ (t : ℝ) := by
    change ((Finset.Icc 1 m).card : ℝ) ≤ (t : ℝ)
    rw [Nat.card_Icc]
    dsimp [m]
    exact_mod_cast (Nat.div_le_self t 2)
  have hcardHi : (hi.card : ℝ) ≤ (t : ℝ) := by
    change ((Finset.Icc (m + 1) t).card : ℝ) ≤ (t : ℝ)
    rw [Nat.card_Icc]
    dsimp [m]
    have ht1 : 1 ≤ t := Nat.one_le_iff_ne_zero.mpr ht
    exact_mod_cast (by omega : t + 1 - (t / 2 + 1) ≤ t)
  have hlow (r : ℕ) (hrlo : r ∈ lo) :
      Renewal.returnWeight r *
        (replicaOverlap t - replicaOverlap (t - r)) ≤ 2 * D ^ 2 / (t : ℝ) := by
    have hr := Finset.mem_Icc.mp (by simpa [lo] using hrlo)
    have hrt : r ≤ t := by dsimp [m] at hr; omega
    have hinner :
        replicaOverlap t - replicaOverlap (t - r) ≤ (r : ℝ) * (2 * D / (t : ℝ)) := by
      rw [replicaOverlap_sub_eq_sum (t - r) t (Nat.sub_le t r)]
      have hlarge (v : ℕ) (hv : v ∈ Finset.Icc (t - r + 1) t) :
          Renewal.returnWeight v ≤ 2 * D / (t : ℝ) := by
        have hv' := Finset.mem_Icc.mp hv
        apply hqhigh v
        dsimp [m]
        omega
      calc
        _ ≤ ∑ v ∈ Finset.Icc (t - r + 1) t, 2 * D / (t : ℝ) :=
          Finset.sum_le_sum fun v hv => hlarge v hv
        _ = (r : ℝ) * (2 * D / (t : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcardInterval r hr.1 hrt]
    have hrpos : 0 < (r : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hr.1)
    have hinner0 : 0 ≤ replicaOverlap t - replicaOverlap (t - r) := by
      rw [replicaOverlap_sub_eq_sum (t - r) t (Nat.sub_le t r)]
      exact Finset.sum_nonneg fun v hv => hqnonneg v
    calc
      Renewal.returnWeight r * (replicaOverlap t - replicaOverlap (t - r)) ≤
          (D / (r : ℝ)) * ((r : ℝ) * (2 * D / (t : ℝ))) :=
            mul_le_mul (hqle r hr.1) hinner hinner0 (div_nonneg hDpos.le hrpos.le)
      _ = 2 * D ^ 2 / (t : ℝ) := by
        field_simp [ne_of_gt htpos, ne_of_gt hrpos]
  have hlowSum :
      (∑ r ∈ lo, Renewal.returnWeight r *
        (replicaOverlap t - replicaOverlap (t - r))) ≤ 2 * D ^ 2 := by
    calc
      _ ≤ ∑ r ∈ lo, 2 * D ^ 2 / (t : ℝ) :=
        Finset.sum_le_sum fun r hr => hlow r hr
      _ = (lo.card : ℝ) * (2 * D ^ 2 / (t : ℝ)) := by simp [lo]
      _ ≤ (t : ℝ) * (2 * D ^ 2 / (t : ℝ)) :=
        mul_le_mul_of_nonneg_right hcardLo (by positivity)
      _ = 2 * D ^ 2 := by field_simp [ne_of_gt htpos]
  have hhighHigh (r : ℕ) (hrhi : r ∈ hi) :
      Renewal.returnWeight r *
        (∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => m < v),
          Renewal.returnWeight v) ≤ 4 * D ^ 2 / (t : ℝ) := by
    have hr : m < r ∧ r ≤ t := by simpa [hi] using hrhi
    have hinner :
        (∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => m < v),
          Renewal.returnWeight v) ≤ 2 * D := by
      calc
        _ ≤ ∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => m < v),
            2 * D / (t : ℝ) := by
              apply Finset.sum_le_sum
              intro v hv
              have hv' := Finset.mem_filter.mp hv
              exact hqhigh v hv'.2
        _ = (((Finset.Icc (t - r + 1) t).filter (fun v => m < v)).card : ℝ) *
              (2 * D / (t : ℝ)) := by simp
        _ ≤ (t : ℝ) * (2 * D / (t : ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ (by positivity)
              have hsub : (Finset.Icc (t - r + 1) t).filter (fun v => m < v) ⊆
                  Finset.Icc 1 t := by
                intro v hv
                simp only [Finset.mem_filter, Finset.mem_Icc] at hv ⊢
                omega
              have hcard := Finset.card_le_card hsub
              have hcardAll : (Finset.Icc 1 t).card = t := by
                rw [Nat.card_Icc]
                omega
              exact_mod_cast hcard.trans_eq hcardAll
        _ = 2 * D := by field_simp [ne_of_gt htpos]
    have hq := hqhigh r hr.1
    have hinner0 : 0 ≤ ∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => m < v),
        Renewal.returnWeight v := Finset.sum_nonneg fun v hv => hqnonneg v
    calc
      _ ≤ (2 * D / (t : ℝ)) * (2 * D) := by
        calc
          _ ≤ (2 * D / (t : ℝ)) *
              (∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => m < v),
                Renewal.returnWeight v) := mul_le_mul_of_nonneg_right hq hinner0
          _ ≤ (2 * D / (t : ℝ)) * (2 * D) :=
              mul_le_mul_of_nonneg_left hinner (by positivity)
      _ = 4 * D ^ 2 / (t : ℝ) := by ring
  have hhighHighSum :
      (∑ r ∈ hi, Renewal.returnWeight r *
        (∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => m < v),
          Renewal.returnWeight v)) ≤ 4 * D ^ 2 := by
    calc
      _ ≤ ∑ r ∈ hi, 4 * D ^ 2 / (t : ℝ) := Finset.sum_le_sum fun r hr => hhighHigh r hr
      _ = (hi.card : ℝ) * (4 * D ^ 2 / (t : ℝ)) := by simp [hi]
      _ ≤ (t : ℝ) * (4 * D ^ 2 / (t : ℝ)) :=
        mul_le_mul_of_nonneg_right hcardHi (by positivity)
      _ = 4 * D ^ 2 := by field_simp [ne_of_gt htpos]
  have hhighLowSum :
      (∑ r ∈ hi, Renewal.returnWeight r *
        (∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => v ≤ m),
          Renewal.returnWeight v)) ≤ 2 * D ^ 2 := by
    simp_rw [Finset.mul_sum]
    let loV := Finset.Icc 1 m
    have hswap :
        (∑ r ∈ hi, ∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => v ≤ m),
          Renewal.returnWeight r * Renewal.returnWeight v) =
        ∑ v ∈ loV, ∑ r ∈ Finset.Icc (t - v + 1) t,
          Renewal.returnWeight r * Renewal.returnWeight v := by
      apply Finset.sum_comm'
      intro r v
      simp only [hi, loV, Finset.mem_Icc, Finset.mem_filter]
      omega
    rw [hswap]
    have hlowV (v : ℕ) (hv : v ∈ loV) :
        ∑ r ∈ Finset.Icc (t - v + 1) t, Renewal.returnWeight r *
          Renewal.returnWeight v ≤ 2 * D ^ 2 / (t : ℝ) := by
      have hv' := Finset.mem_Icc.mp (by simpa [loV] using hv)
      have hvpos : 0 < (v : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hv'.1)
      have hrLarge (r : ℕ) (hr : r ∈ Finset.Icc (t - v + 1) t) : m < r := by
        have hr' := Finset.mem_Icc.mp hr
        dsimp [m]
        omega
      have hsumr :
          ∑ r ∈ Finset.Icc (t - v + 1) t, Renewal.returnWeight r ≤
            (v : ℝ) * (2 * D / (t : ℝ)) := by
        calc
          _ ≤ ∑ r ∈ Finset.Icc (t - v + 1) t, 2 * D / (t : ℝ) :=
            Finset.sum_le_sum fun r hr => hqhigh r (hrLarge r hr)
          _ = (v : ℝ) * (2 * D / (t : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcardInterval v hv'.1 (by dsimp [m] at hv'; omega)]
      calc
        _ = Renewal.returnWeight v *
            (∑ r ∈ Finset.Icc (t - v + 1) t, Renewal.returnWeight r) := by
              calc
                _ = ∑ r ∈ Finset.Icc (t - v + 1) t,
                    Renewal.returnWeight v * Renewal.returnWeight r := by
                      apply Finset.sum_congr rfl
                      intro r hr
                      ring
                _ = _ := by rw [← Finset.mul_sum]
        _ ≤ (D / (v : ℝ)) * ((v : ℝ) * (2 * D / (t : ℝ))) := by
              have hsumr0 : 0 ≤
                  ∑ r ∈ Finset.Icc (t - v + 1) t, Renewal.returnWeight r :=
                Finset.sum_nonneg fun r hr => hqnonneg r
              calc
                _ ≤ (D / (v : ℝ)) *
                    (∑ r ∈ Finset.Icc (t - v + 1) t, Renewal.returnWeight r) :=
                      mul_le_mul_of_nonneg_right (hqle v hv'.1) hsumr0
                _ ≤ (D / (v : ℝ)) * ((v : ℝ) * (2 * D / (t : ℝ))) :=
                      mul_le_mul_of_nonneg_left hsumr (div_nonneg hDpos.le hvpos.le)
        _ = 2 * D ^ 2 / (t : ℝ) := by
          field_simp [ne_of_gt htpos, ne_of_gt hvpos]
    calc
      _ ≤ ∑ v ∈ loV, 2 * D ^ 2 / (t : ℝ) := Finset.sum_le_sum fun v hv => hlowV v hv
      _ = (loV.card : ℝ) * (2 * D ^ 2 / (t : ℝ)) := by simp [loV]
      _ ≤ (t : ℝ) * (2 * D ^ 2 / (t : ℝ)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        change ((Finset.Icc 1 m).card : ℝ) ≤ (t : ℝ)
        rw [Nat.card_Icc]
        dsimp [m]
        exact_mod_cast (Nat.div_le_self t 2)
      _ = 2 * D ^ 2 := by field_simp [ne_of_gt htpos]
  have hhi :
      (∑ r ∈ hi, Renewal.returnWeight r *
        (replicaOverlap t - replicaOverlap (t - r))) ≤ 6 * D ^ 2 := by
    have hsplit (r : ℕ) :
        replicaOverlap t - replicaOverlap (t - r) =
          (∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => m < v),
            Renewal.returnWeight v) +
          (∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => v ≤ m),
            Renewal.returnWeight v) := by
      classical
      rw [replicaOverlap_sub_eq_sum (t - r) t (Nat.sub_le t r)]
      calc
        _ = ∑ v ∈ Finset.Icc (t - r + 1) t,
            ((if m < v then Renewal.returnWeight v else 0) +
              (if v ≤ m then Renewal.returnWeight v else 0)) := by
                apply Finset.sum_congr rfl
                intro v hv
                by_cases hmv : m < v
                · simp [hmv]
                · have hvm : v ≤ m := by omega
                  simp [hmv, hvm]
        _ = (∑ v ∈ Finset.Icc (t - r + 1) t,
              if m < v then Renewal.returnWeight v else 0) +
            (∑ v ∈ Finset.Icc (t - r + 1) t,
              if v ≤ m then Renewal.returnWeight v else 0) := by
                rw [Finset.sum_add_distrib]
        _ = _ := by
              rw [← Finset.sum_filter, ← Finset.sum_filter]
    calc
      _ = (∑ r ∈ hi, Renewal.returnWeight r *
            (∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => m < v),
              Renewal.returnWeight v)) +
          (∑ r ∈ hi, Renewal.returnWeight r *
            (∑ v ∈ (Finset.Icc (t - r + 1) t).filter (fun v => v ≤ m),
              Renewal.returnWeight v)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro r hr
            rw [hsplit r]
            ring
      _ ≤ 4 * D ^ 2 + 2 * D ^ 2 := add_le_add hhighHighSum hhighLowSum
      _ = 6 * D ^ 2 := by ring
  calc
    (∑ r ∈ Finset.Icc 1 t, Renewal.returnWeight r *
        (replicaOverlap t - replicaOverlap (t - r))) =
        (∑ r ∈ lo, Renewal.returnWeight r *
          (replicaOverlap t - replicaOverlap (t - r))) +
        (∑ r ∈ hi, Renewal.returnWeight r *
          (replicaOverlap t - replicaOverlap (t - r))) := by
            rw [hOuter, Finset.sum_union hOuterDisj]
    _ ≤ 2 * D ^ 2 + 6 * D ^ 2 := add_le_add hlowSum hhi
    _ ≤ 8 * D ^ 2 := by nlinarith [sq_nonneg D]

/-- The smoothed second moment is bounded above by the ratio of endpoint renewal gaps, with an error bounded by the overlap increment divided by the squared terminal gap. -/
theorem smoothedP2Plane_secondMoment_renewalGap :
    ∃ C : ℝ, ∀ β : ℝ, 0 < β → ∀ s t : ℕ, s ≤ t → 0 < renewalGap β t →
      0 ≤ renewalGap β s / renewalGap β t -
          ∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw ∧
      renewalGap β s / renewalGap β t -
          ∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw ≤
        C * (1 + replicaOverlap t - replicaOverlap s) / renewalGap β t ^ 2 ∧
      (1 ≤ s → 2 * s ≤ t →
        renewalGap β s / renewalGap β t -
            ∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw ≤
          C * Real.log ((t : ℝ) / s) / renewalGap β t ^ 2) := by
  obtain ⟨Cvn, hVN⟩ := renewalGap_secondMoment_bounds
  obtain ⟨B, hBpos, hB⟩ := returnWeight_boundary_sum_le
  obtain ⟨Coverlap, hOverlap⟩ := replicaOverlap_sub_log_bounded
  have hCoverlapNonneg : 0 ≤ Coverlap := by
    have h := hOverlap 1 1 (by omega)
    exact le_trans (abs_nonneg _) h
  let Cbase := Real.pi ^ 2 * B + |Cvn|
  let K := 2 + 1 / Real.pi + (1 + Coverlap / Real.pi) / Real.log 2
  have hKge : 1 ≤ K := by
    dsimp [K]
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hpi : 0 < Real.pi := Real.pi_pos
    have hterm1 : 0 ≤ 1 / Real.pi := by positivity
    have hterm2 : 0 ≤ (1 + Coverlap / Real.pi) / Real.log 2 := by positivity
    linarith
  refine ⟨Cbase * K, fun β hβ s t hst hgap => ?_⟩
  let σ := Polymer.sigmaSq β
  have hσpos : 0 < σ := by
    dsimp [σ, Polymer.sigmaSq]
    apply sub_pos.mpr
    rw [Real.one_lt_exp_iff]
    exact sq_pos_of_pos hβ
  have hRmono (j : ℕ) (hjt : j ≤ t) :
      replicaOverlap j ≤ replicaOverlap t := by
    have hsum := replicaOverlap_sub_eq_sum j t hjt
    have hnonneg : 0 ≤ ∑ r ∈ Finset.Icc (j + 1) t, Renewal.returnWeight r :=
      Finset.sum_nonneg fun r hr =>
        Critical2DKPZ.srwKernel_nonneg (2 * r) 0
    linarith only [hsum, hnonneg]
  have hgapMono (j : ℕ) (hjt : j ≤ t) : renewalGap β t ≤ renewalGap β j := by
    have hgapDiff : renewalGap β j - renewalGap β t =
        Real.pi * (replicaOverlap t - replicaOverlap j) := by
      simp only [renewalGap]
      ring
    have hRdiff : 0 ≤ replicaOverlap t - replicaOverlap j :=
      sub_nonneg.mpr (hRmono j hjt)
    have hdiff : 0 ≤ Real.pi * (replicaOverlap t - replicaOverlap j) :=
      mul_nonneg Real.pi_pos.le hRdiff
    linarith only [hgapDiff, hdiff]
  have hRtail := replicaOverlap_sub_eq_sum s t hst
  have hRtail0 : 0 ≤ replicaOverlap t - replicaOverlap s := by
    rw [hRtail]
    exact Finset.sum_nonneg fun r hr => Critical2DKPZ.srwKernel_nonneg (2 * r) 0
  have hgapRatio : renewalGap β s / renewalGap β t =
      1 + (Real.pi / renewalGap β t) * (replicaOverlap t - replicaOverlap s) := by
    have hgapDiff : renewalGap β s = renewalGap β t +
        Real.pi * (replicaOverlap t - replicaOverlap s) := by
      simp only [renewalGap]
      ring
    rw [hgapDiff]
    field_simp [ne_of_gt hgap]
  have hmomentFormula :
      (∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw) =
        1 + ∑ r ∈ Finset.Icc (s + 1) t,
          Renewal.returnWeight r * (σ * Renewal.freeSecondMoment β (t - r)) := by
    have hformula := Polymer.local_replica_formula β s t hst (0 : Site) 0
    have hformulaSq := hformula
    simp only [← pow_two] at hformulaSq
    have hminus : (∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw) - 1 =
        ∑ r ∈ Finset.Icc (s + 1) t,
          Renewal.returnWeight r * (σ * Renewal.freeSecondMoment β (t - r)) := by
      rw [hformulaSq]
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Renewal.returnWeight, σ, Polymer.sigmaSq, Renewal.freeSecondMoment]
      ring
    linarith only [hminus]
  have herrorFormula :
      renewalGap β s / renewalGap β t -
          ∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw =
        ∑ r ∈ Finset.Icc (s + 1) t, Renewal.returnWeight r *
          (Real.pi / renewalGap β t -
            σ * Renewal.freeSecondMoment β (t - r)) := by
    rw [hgapRatio, hmomentFormula, hRtail]
    have hmul : Real.pi / renewalGap β t *
        (∑ r ∈ Finset.Icc (s + 1) t, Renewal.returnWeight r) =
          ∑ r ∈ Finset.Icc (s + 1) t,
            Renewal.returnWeight r * (Real.pi / renewalGap β t) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    rw [hmul]
    calc
      _ = (∑ r ∈ Finset.Icc (s + 1) t,
            Renewal.returnWeight r * (Real.pi / renewalGap β t)) -
          (∑ r ∈ Finset.Icc (s + 1) t,
            Renewal.returnWeight r * (σ * Renewal.freeSecondMoment β (t - r))) := by ring
      _ = ∑ r ∈ Finset.Icc (s + 1) t,
            (Renewal.returnWeight r * (Real.pi / renewalGap β t) -
              Renewal.returnWeight r * (σ * Renewal.freeSecondMoment β (t - r))) := by
            rw [← Finset.sum_sub_distrib]
      _ = _ := by
            apply Finset.sum_congr rfl
            intro r hr
            ring
  have hbracketLower (r : ℕ) (hr : r ∈ Finset.Icc (s + 1) t) :
      0 ≤ Real.pi / renewalGap β t -
        σ * Renewal.freeSecondMoment β (t - r) := by
    have hr' := Finset.mem_Icc.mp hr
    let j := t - r
    have hjt : j ≤ t := Nat.sub_le _ _
    have hgapj : 0 < renewalGap β j := lt_of_lt_of_le hgap (hgapMono j hjt)
    have hVN' := hVN β hβ j hgapj
    have hdiv : Real.pi / renewalGap β j ≤ Real.pi / renewalGap β t :=
      div_le_div_of_nonneg_left Real.pi_pos.le hgap (hgapMono j hjt)
    have hfree : Renewal.freeSecondMoment β j =
        ∫ ω, pointToPlane β 0 j 0 ω ^ 2 ∂disorderLaw := rfl
    rw [← hfree] at hVN'
    linarith only [hVN'.1, hdiv]
  have hbracketUpper (r : ℕ) (hr : r ∈ Finset.Icc (s + 1) t) :
      Real.pi / renewalGap β t - σ * Renewal.freeSecondMoment β (t - r) ≤
        (Real.pi ^ 2 * (replicaOverlap t - replicaOverlap (t - r)) + |Cvn|) /
          renewalGap β t ^ 2 := by
    have hr' := Finset.mem_Icc.mp hr
    let j := t - r
    have hjt : j ≤ t := Nat.sub_le _ _
    have hgapMono' := hgapMono j hjt
    have hgapj : 0 < renewalGap β j := lt_of_lt_of_le hgap hgapMono'
    have hVN' := hVN β hβ j hgapj
    have hgapDiff : renewalGap β j - renewalGap β t =
        Real.pi * (replicaOverlap t - replicaOverlap j) := by
      simp only [renewalGap]
      ring
    have hRj : 0 ≤ replicaOverlap t - replicaOverlap j :=
      sub_nonneg.mpr (hRmono j hjt)
    have hfirstEq : Real.pi / renewalGap β t - Real.pi / renewalGap β j =
        Real.pi ^ 2 * (replicaOverlap t - replicaOverlap j) /
          (renewalGap β t * renewalGap β j) := by
      have hposj : 0 < renewalGap β j := hgapj
      have hbase : Real.pi / renewalGap β t - Real.pi / renewalGap β j =
          Real.pi * (renewalGap β j - renewalGap β t) /
            (renewalGap β t * renewalGap β j) := by
        field_simp [ne_of_gt hgap, ne_of_gt hposj]
      rw [hbase, hgapDiff]
      ring
    have hden : renewalGap β t ^ 2 ≤ renewalGap β t * renewalGap β j := by
      nlinarith [mul_le_mul_of_nonneg_left hgapMono' hgap.le]
    have hnum0 : 0 ≤ Real.pi ^ 2 * (replicaOverlap t - replicaOverlap j) :=
      mul_nonneg (sq_nonneg _) hRj
    have hfirstBound :
        Real.pi ^ 2 * (replicaOverlap t - replicaOverlap j) /
            (renewalGap β t * renewalGap β j) ≤
          Real.pi ^ 2 * (replicaOverlap t - replicaOverlap j) /
            renewalGap β t ^ 2 :=
      div_le_div_of_nonneg_left hnum0 (sq_pos_of_pos hgap) hden
    have hgapjSq : renewalGap β t ^ 2 ≤ renewalGap β j ^ 2 := by
      nlinarith [hgap.le, hgapMono']
    have hCvnAbs : Cvn ≤ |Cvn| := le_abs_self _
    have hVNabs : Cvn / renewalGap β j ^ 2 ≤ |Cvn| / renewalGap β t ^ 2 := by
      calc
        Cvn / renewalGap β j ^ 2 ≤ |Cvn| / renewalGap β j ^ 2 :=
          div_le_div_of_nonneg_right hCvnAbs (sq_nonneg _)
        _ ≤ |Cvn| / renewalGap β t ^ 2 :=
          div_le_div_of_nonneg_left (abs_nonneg Cvn) (sq_pos_of_pos hgap) hgapjSq
    have hfree : Renewal.freeSecondMoment β j =
        ∫ ω, pointToPlane β 0 j 0 ω ^ 2 ∂disorderLaw := rfl
    rw [← hfree] at hVN'
    have hdecomp : Real.pi / renewalGap β t -
        σ * Renewal.freeSecondMoment β j =
        (Real.pi / renewalGap β t - Real.pi / renewalGap β j) +
          (Real.pi / renewalGap β j -
            σ * Renewal.freeSecondMoment β j) := by ring
    rw [hdecomp, hfirstEq]
    have hupper : Real.pi / renewalGap β j -
        σ * Renewal.freeSecondMoment β j ≤ Cvn / renewalGap β j ^ 2 := hVN'.2
    have hcombined := add_le_add hfirstBound hVNabs
    dsimp [j]
    calc
      _ ≤ (Real.pi ^ 2 * (replicaOverlap t - replicaOverlap j)) /
            renewalGap β t ^ 2 + |Cvn| / renewalGap β t ^ 2 := by
              linarith only [hcombined, hupper]
      _ = _ := by ring
  have hA_nonneg : 0 ≤
      renewalGap β s / renewalGap β t -
        ∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw := by
    rw [herrorFormula]
    exact Finset.sum_nonneg fun r hr =>
      mul_nonneg (Critical2DKPZ.srwKernel_nonneg (2 * r) 0) (hbracketLower r hr)
  have hboundarySub :
      (∑ r ∈ Finset.Icc (s + 1) t,
        Renewal.returnWeight r *
          (replicaOverlap t - replicaOverlap (t - r))) ≤ B := by
    apply (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_).trans (hB t)
    · intro r hr
      simp only [Finset.mem_Icc] at hr ⊢
      omega
    · intro r hr hnot
      have hr' := Finset.mem_Icc.mp hr
      have hRnonneg : 0 ≤ replicaOverlap t - replicaOverlap (t - r) := by
        rw [replicaOverlap_sub_eq_sum (t - r) t (Nat.sub_le t r)]
        exact Finset.sum_nonneg fun v hv => Critical2DKPZ.srwKernel_nonneg (2 * v) 0
      exact mul_nonneg (Critical2DKPZ.srwKernel_nonneg (2 * r) 0) hRnonneg
  have hnumBound :
      (∑ r ∈ Finset.Icc (s + 1) t,
        Renewal.returnWeight r *
          (Real.pi ^ 2 * (replicaOverlap t - replicaOverlap (t - r)) + |Cvn|)) ≤
        Real.pi ^ 2 * B + |Cvn| * (replicaOverlap t - replicaOverlap s) := by
    calc
      _ = Real.pi ^ 2 *
            (∑ r ∈ Finset.Icc (s + 1) t,
              Renewal.returnWeight r * (replicaOverlap t - replicaOverlap (t - r))) +
          |Cvn| * (∑ r ∈ Finset.Icc (s + 1) t, Renewal.returnWeight r) := by
            calc
              _ = ∑ r ∈ Finset.Icc (s + 1) t,
                    (Renewal.returnWeight r *
                      (Real.pi ^ 2 * (replicaOverlap t - replicaOverlap (t - r))) +
                    Renewal.returnWeight r * |Cvn|) := by
                      apply Finset.sum_congr rfl
                      intro r hr
                      ring
              _ = (∑ r ∈ Finset.Icc (s + 1) t,
                    Renewal.returnWeight r *
                      (Real.pi ^ 2 * (replicaOverlap t - replicaOverlap (t - r)))) +
                  (∑ r ∈ Finset.Icc (s + 1) t, Renewal.returnWeight r * |Cvn|) := by
                    rw [Finset.sum_add_distrib]
              _ = _ := by
                    rw [Finset.mul_sum, Finset.mul_sum]
                    apply congrArg₂ HAdd.hAdd
                    · apply Finset.sum_congr rfl
                      intro r hr
                      ring
                    · apply Finset.sum_congr rfl
                      intro r hr
                      ring
      _ ≤ Real.pi ^ 2 * B + |Cvn| * (replicaOverlap t - replicaOverlap s) := by
            rw [hRtail]
            exact add_le_add
              (mul_le_mul_of_nonneg_left hboundarySub (sq_nonneg _)) le_rfl
  have hbaseNonneg : 0 ≤ Cbase := by dsimp [Cbase]; positivity
  have hnumUpgrade : Real.pi ^ 2 * B + |Cvn| * (replicaOverlap t - replicaOverlap s) ≤
      Cbase * (1 + replicaOverlap t - replicaOverlap s) := by
    dsimp [Cbase]
    have habs : 0 ≤ |Cvn| := abs_nonneg Cvn
    have hX : 0 ≤ Real.pi ^ 2 * B := mul_nonneg (sq_nonneg _) hBpos.le
    nlinarith [hRtail0, hX, mul_nonneg hX hRtail0, mul_nonneg habs hRtail0]
  have hupperBase :
      renewalGap β s / renewalGap β t -
        ∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw ≤
      Cbase * (1 + replicaOverlap t - replicaOverlap s) / renewalGap β t ^ 2 := by
    rw [herrorFormula]
    have hsumUpper := Finset.sum_le_sum fun r hr =>
      mul_le_mul_of_nonneg_left (hbracketUpper r hr)
        (Critical2DKPZ.srwKernel_nonneg (2 * r) 0)
    calc
      _ ≤ ∑ r ∈ Finset.Icc (s + 1) t,
          Renewal.returnWeight r *
            ((Real.pi ^ 2 * (replicaOverlap t - replicaOverlap (t - r)) + |Cvn|) /
              renewalGap β t ^ 2) := hsumUpper
      _ = (∑ r ∈ Finset.Icc (s + 1) t,
            Renewal.returnWeight r *
              (Real.pi ^ 2 * (replicaOverlap t - replicaOverlap (t - r)) + |Cvn|)) /
              renewalGap β t ^ 2 := by
            calc
              _ = (∑ r ∈ Finset.Icc (s + 1) t,
                    (Renewal.returnWeight r *
                      (Real.pi ^ 2 * (replicaOverlap t - replicaOverlap (t - r)) + |Cvn|)) /
                      renewalGap β t ^ 2) := by
                        apply Finset.sum_congr rfl
                        intro r hr
                        rw [mul_div_assoc]
              _ = _ := by rw [← Finset.sum_div]
      _ ≤ (Real.pi ^ 2 * B + |Cvn| * (replicaOverlap t - replicaOverlap s)) /
            renewalGap β t ^ 2 :=
              div_le_div_of_nonneg_right hnumBound (sq_nonneg _)
      _ ≤ Cbase * (1 + replicaOverlap t - replicaOverlap s) /
            renewalGap β t ^ 2 :=
              div_le_div_of_nonneg_right hnumUpgrade (sq_nonneg _)
  have hupperAll :
      renewalGap β s / renewalGap β t -
        ∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw ≤
      (Cbase * K) * (1 + replicaOverlap t - replicaOverlap s) /
        renewalGap β t ^ 2 := by
    calc
      _ ≤ Cbase * (1 + replicaOverlap t - replicaOverlap s) /
            renewalGap β t ^ 2 := hupperBase
      _ = Cbase * ((1 + replicaOverlap t - replicaOverlap s) /
            renewalGap β t ^ 2) := by ring
      _ ≤ (Cbase * K) * ((1 + replicaOverlap t - replicaOverlap s) /
            renewalGap β t ^ 2) := by
              apply mul_le_mul_of_nonneg_right _ (div_nonneg (by linarith [hRtail0]) (sq_nonneg _))
              nlinarith [hbaseNonneg, hKge]
      _ = _ := by ring
  refine ⟨hA_nonneg, hupperAll, ?_⟩
  intro hs h2s
  have hspos : 0 < (s : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hs)
  have htscale : 2 ≤ (t : ℝ) / s := by
    apply (le_div_iff₀ hspos).2
    exact_mod_cast h2s
  have hloglower : Real.log 2 ≤ Real.log ((t : ℝ) / s) :=
    Real.log_le_log (by norm_num) htscale
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmax : max s 1 = s := max_eq_left (by omega : 1 ≤ s)
  have htmax : max t 1 = t := max_eq_left (by omega : 1 ≤ t)
  have hlogError :
      |Real.pi * (replicaOverlap t - replicaOverlap s) -
        Real.log ((t : ℝ) / s)| ≤ Coverlap := by
    simpa only [hsmax, htmax] using hOverlap s t hst
  have hlogR : Real.pi * (replicaOverlap t - replicaOverlap s) ≤
      Real.log ((t : ℝ) / s) + Coverlap := by
    have := (abs_le.mp hlogError).2
    linarith
  have hRupper : 1 + replicaOverlap t - replicaOverlap s ≤
      K * Real.log ((t : ℝ) / s) := by
    dsimp [K]
    have hRdiv : replicaOverlap t - replicaOverlap s ≤
        Real.log ((t : ℝ) / s) / Real.pi + Coverlap / Real.pi := by
      have hdiv := div_le_div_of_nonneg_right hlogR Real.pi_pos.le
      have hpi : Real.pi * (replicaOverlap t - replicaOverlap s) / Real.pi =
          replicaOverlap t - replicaOverlap s := by
        field_simp [ne_of_gt Real.pi_pos]
      rw [hpi, add_div] at hdiv
      exact hdiv
    have hconstant : 1 + Coverlap / Real.pi ≤
        ((1 + Coverlap / Real.pi) / Real.log 2) * Real.log ((t : ℝ) / s) := by
      calc
        1 + Coverlap / Real.pi =
            ((1 + Coverlap / Real.pi) / Real.log 2) * Real.log 2 := by
              field_simp [ne_of_gt hlogpos]
        _ ≤ ((1 + Coverlap / Real.pi) / Real.log 2) *
              Real.log ((t : ℝ) / s) :=
              mul_le_mul_of_nonneg_left hloglower (by positivity)
    calc
      _ ≤ 1 + Real.log ((t : ℝ) / s) / Real.pi + Coverlap / Real.pi := by
            linarith [hRdiv]
      _ = Real.log ((t : ℝ) / s) / Real.pi +
            (1 + Coverlap / Real.pi) := by ring
      _ ≤ Real.log ((t : ℝ) / s) / Real.pi +
            ((1 + Coverlap / Real.pi) / Real.log 2) *
              Real.log ((t : ℝ) / s) :=
            add_le_add le_rfl hconstant
      _ ≤ (2 + 1 / Real.pi + (1 + Coverlap / Real.pi) / Real.log 2) *
            Real.log ((t : ℝ) / s) := by
              have hlognonneg : 0 ≤ Real.log ((t : ℝ) / s) := le_trans hlogpos.le hloglower
              calc
                _ = (1 / Real.pi + (1 + Coverlap / Real.pi) / Real.log 2) *
                      Real.log ((t : ℝ) / s) := by ring
                _ ≤ (2 + 1 / Real.pi + (1 + Coverlap / Real.pi) / Real.log 2) *
                      Real.log ((t : ℝ) / s) := by
                        apply mul_le_mul_of_nonneg_right _ hlognonneg
                        norm_num
  have hupperLog :
      renewalGap β s / renewalGap β t -
        ∫ ω, smoothedP2Plane β s t 0 ω ^ 2 ∂disorderLaw ≤
      (Cbase * K) * Real.log ((t : ℝ) / s) / renewalGap β t ^ 2 := by
    calc
      _ ≤ Cbase * (1 + replicaOverlap t - replicaOverlap s) /
            renewalGap β t ^ 2 := hupperBase
      _ ≤ Cbase * (K * Real.log ((t : ℝ) / s)) / renewalGap β t ^ 2 := by
            apply div_le_div_of_nonneg_right _ (sq_nonneg _)
            exact mul_le_mul_of_nonneg_left hRupper hbaseNonneg
      _ = _ := by ring
  simpa only [mul_assoc] using hupperLog

/-- The square of the smoothed point-to-plane polymer mass is integrable. -/
theorem integrable_smoothedP2Plane_sq (β : ℝ) (s n : ℕ) :
    Integrable (fun ω => smoothedP2Plane β s n 0 ω ^ 2) disorderLaw := by
  have h := (Polymer.memLp_smoothedP2Plane β s n 0 2 (by norm_num)).integrable_norm_pow'
  have hEq : (fun ω => |smoothedP2Plane β s n 0 ω| ^ 2) =
      fun ω => smoothedP2Plane β s n 0 ω ^ 2 := by
    funext ω
    rw [abs_of_pos (Polymer.smoothedP2Plane_pos β s n 0 ω)]
  rw [← hEq]
  exact h

/-- A smoothed second-moment integral bound is controlled by the accumulated return mass and the
uniform critical-window free second-moment estimate. Its integrand is integrable by
`integrable_smoothedP2Plane_sq`. -/
theorem smoothedP2Plane_secondMoment_le_uniform (A T : ℝ) :
    ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, ∀ ϑ ∈ Set.Icc (-A) A, ∀ s n : ℕ, s ≤ n →
      1 ≤ n → (n : ℝ) ≤ T * N →
      ∫ ω, smoothedP2Plane (criticalBeta ϑ N) s n 0 ω ^ 2 ∂disorderLaw ≤
        1 + C * (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s) /
          Real.log (1 + (N : ℝ) / n) := by
  obtain ⟨C, _, hNbound⟩ := sigmaSq_secondMoment_le_uniform_pos A T
  refine ⟨C, ?_⟩
  filter_upwards [hNbound, eventually_ge_atTop 2] with N hNbound hN
  intro ϑ hϑ s n hsn hn hnT
  let β := criticalBeta ϑ N
  let σ := Polymer.sigmaSq β
  have hN1 : 1 ≤ N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hdenpos : 0 < Real.log (1 + (N : ℝ) / n) := by
    apply Real.log_pos
    have hratio : 0 < (N : ℝ) / n := div_pos hNreal hnreal
    linarith
  have hσnonneg : 0 ≤ σ := by
    dsimp [σ, β, Polymer.sigmaSq]
    exact sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
  have hfreeMono (j : ℕ) (hj : j ≤ n) :
      Renewal.freeSecondMoment β j ≤ Renewal.freeSecondMoment β n := by
    have hw : ∀ r, 0 ≤ Polymer.sigmaSq β * Renewal.returnWeight r := fun r =>
      mul_nonneg hσnonneg (Critical2DKPZ.srwKernel_nonneg (2 * r) 0)
    rw [Renewal.freeSecondMoment_eq_renewalFunction β]
    exact Renewal.renewalFunction_mono_time hw hj
  have hrawN := hNbound ϑ hϑ n hn hnT
  have hfreeboundN : σ * Renewal.freeSecondMoment β n ≤
      C / Real.log (1 + (N : ℝ) / n) := by
    simpa only [σ, β, Renewal.freeSecondMoment] using hrawN
  have hfreebound (j : ℕ) (hj : j ≤ n) :
      σ * Renewal.freeSecondMoment β j ≤ C / Real.log (1 + (N : ℝ) / n) := by
    exact (mul_le_mul_of_nonneg_left (hfreeMono j hj) hσnonneg).trans hfreeboundN
  have hformula := Polymer.local_replica_formula β s n hsn (0 : Site) 0
  have hformula' :
      (∫ ω, smoothedP2Plane β s n 0 ω ^ 2 ∂disorderLaw) - 1 =
        ∑ r ∈ Finset.Icc (s + 1) n,
          Renewal.returnWeight r * (σ * Renewal.freeSecondMoment β (n - r)) := by
    have hformulaSq := hformula
    simp only [← pow_two] at hformulaSq
    rw [hformulaSq]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [Renewal.returnWeight, σ, β, Renewal.freeSecondMoment]
    ring
  have hsum :
      (∑ r ∈ Finset.Icc (s + 1) n,
        Renewal.returnWeight r * (σ * Renewal.freeSecondMoment β (n - r))) ≤
        (C / Real.log (1 + (N : ℝ) / n)) *
          (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s) := by
    calc
      _ ≤ ∑ r ∈ Finset.Icc (s + 1) n,
          Renewal.returnWeight r * (C / Real.log (1 + (N : ℝ) / n)) := by
            apply Finset.sum_le_sum
            intro r hr
            have hrmem := Finset.mem_Icc.mp hr
            have hrle : r ≤ n := hrmem.2
            have hjle : n - r ≤ n := Nat.sub_le _ _
            have hmoment := hfreebound (n - r) hjle
            have hqnonneg : 0 ≤ Renewal.returnWeight r :=
              Critical2DKPZ.srwKernel_nonneg (2 * r) 0
            exact mul_le_mul_of_nonneg_left hmoment hqnonneg
      _ = (C / Real.log (1 + (N : ℝ) / n)) *
          (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s) := by
            rw [← Finset.sum_mul, replicaOverlap_sub_eq_sum s n hsn]
            ring
  have hformula'' :
      (∫ ω, smoothedP2Plane β s n 0 ω ^ 2 ∂disorderLaw) =
        1 + ∑ r ∈ Finset.Icc (s + 1) n,
          Renewal.returnWeight r * (σ * Renewal.freeSecondMoment β (n - r)) := by
    linarith only [hformula']
  calc
    (∫ ω, smoothedP2Plane β s n 0 ω ^ 2 ∂disorderLaw) =
        1 + ∑ r ∈ Finset.Icc (s + 1) n,
          Renewal.returnWeight r * (σ * Renewal.freeSecondMoment β (n - r)) := hformula''
    _ ≤ 1 + (C / Real.log (1 + (N : ℝ) / n)) *
          (Critical2DKPZ.replicaOverlap n - Critical2DKPZ.replicaOverlap s) :=
            add_le_add le_rfl hsum
    _ = _ := by ring

end Critical2DKPZ.OnePoint
