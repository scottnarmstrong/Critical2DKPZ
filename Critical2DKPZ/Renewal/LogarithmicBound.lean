/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.ExponentialTilt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# Logarithmic renewal bounds

An elementary exponential-tilt argument gives bounded scaled renewal functions at the
critical scale from a uniform logarithmic error bound on the return sum. This part of the
second-moment upper bound does not use the sharp Dickman local limit theorem.
-/

@[expose] public noncomputable section

namespace Critical2DKPZ.Renewal

/-- Logarithmic overlap bounds control increments of the overlap. -/
theorem cutoffMass_sub_lower (w : ℕ → ℝ) {a C : ℝ}
    (hlog : ∀ n : ℕ, 1 ≤ n → |cutoffMass w n - a * Real.log n| ≤ C)
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    a * Real.log ((n : ℝ) / m) - 2 * C ≤ cutoffMass w n - cutoffMass w m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [Real.log_div hn0.ne' hm0.ne']
  have hn' := (abs_le.mp (hlog n hn)).1
  have hm' := (abs_le.mp (hlog m hm)).2
  linarith only [hn', hm']

private theorem sum_Icc_indicator_le (f : ℕ → ℝ) {m n : ℕ} (hmn : m ≤ n) :
    (∑ r ∈ Finset.Icc 1 n, if r ≤ m then f r else 0) = ∑ r ∈ Finset.Icc 1 m, f r := by
  symm
  calc
    _ = ∑ r ∈ Finset.Icc 1 m, if r ≤ m then f r else 0 :=
      Finset.sum_congr rfl fun r hr => by rw [ite_eq_left (Finset.mem_Icc.mp hr).2]
    _ = _ := Finset.sum_subset (Finset.Icc_subset_Icc_right hmn) (fun r hr hnot => by
      have hrm : ¬r ≤ m := by
        have hr1 := (Finset.mem_Icc.mp hr).1
        simp only [Finset.mem_Icc, not_and] at hnot
        exact hnot hr1
      exact ite_eq_right hrm)

/-- Damping at rate `M log 2 / N` halves the weights after the cutoff `N/M`. -/
theorem cutoffMass_tilt_half {w : ℕ → ℝ} (hw : ∀ r, 0 ≤ w r)
    {M N : ℕ} (hM : 1 ≤ M) (hN : 1 ≤ N) :
    cutoffMass (exponentialTilt w ((M : ℝ) * Real.log 2 / N)) N ≤
      (cutoffMass w N + cutoffMass w (N / M)) / 2 := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrate : 0 ≤ (M : ℝ) * Real.log 2 / N := (div_pos (mul_pos hM0 hlog2) hN0).le
  have hpoint (r : ℕ) : exponentialTilt w ((M : ℝ) * Real.log 2 / N) r ≤
      w r / 2 + (if r ≤ N / M then w r else 0) / 2 := by
    by_cases hr : r ≤ N / M
    · rw [ite_eq_left hr]
      have he : Real.exp (-((M : ℝ) * Real.log 2 / N) * r) ≤ 1 :=
        Real.exp_le_one_iff.mpr
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hrate) (Nat.cast_nonneg r))
      exact (mul_le_mul_of_nonneg_right he (hw r)).trans_eq (by ring)
    · rw [ite_eq_right hr, zero_div, add_zero]
      have hNr : N < r * M := (Nat.div_lt_iff_lt_mul (by omega : 0 < M)).mp (by omega)
      have hNr' : (N : ℝ) ≤ (r : ℝ) * M := by exact_mod_cast hNr.le
      have hexp : -((M : ℝ) * Real.log 2 / N) * r ≤ -Real.log 2 := by
        have hmul := mul_le_mul_of_nonneg_left hNr' hlog2.le
        have hdiv : Real.log 2 ≤ (Real.log 2 * ((r : ℝ) * M)) / N :=
          (le_div_iff₀ hN0).mpr hmul
        calc
          _ = -((Real.log 2 * ((r : ℝ) * M)) / N) := by ring
          _ ≤ _ := neg_le_neg hdiv
      have he : Real.exp (-((M : ℝ) * Real.log 2 / N) * r) ≤ 1 / 2 := by
        calc
          _ ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr hexp
          _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
      exact (mul_le_mul_of_nonneg_right he (hw r)).trans_eq (by ring)
  calc
    _ ≤ ∑ r ∈ Finset.Icc 1 N, (w r / 2 + (if r ≤ N / M then w r else 0) / 2) :=
      Finset.sum_le_sum fun r _ => hpoint r
    _ = _ := by
      simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul]
      rw [sum_Icc_indicator_le w (Nat.div_le_self N M)]
      dsimp only [cutoffMass]
      ring

/-- A logarithmic overlap bound yields a bounded scaled critical-scale renewal function.
The finite parameter `D` bounds how far the coupling is above the geometric critical value. -/
theorem exists_scaled_renewalFunction_bound (w : ℕ → ℝ) (hw : ∀ r, 0 ≤ w r)
    {a C D : ℝ} (ha : 0 < a)
    (hlog : ∀ n : ℕ, 1 ≤ n → |cutoffMass w n - a * Real.log n| ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ σ : ℝ, 0 < σ →
      -D ≤ 1 / σ - cutoffMass w N →
      σ * renewalFunction (fun r => σ * w r) N ≤ K := by
  obtain ⟨M, hM2, hMlog⟩ := ((Filter.eventually_ge_atTop 2).and
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
      ((2 * D + 2 * C + 2) / a))).exists
  change (2 * D + 2 * C + 2) / a < Real.log (M : ℝ) at hMlog
  have hMlog' : 2 * D + 2 * C + 2 < a * Real.log M := by
    have := (div_lt_iff₀ ha).mp hMlog
    linarith only [this]
  let A : ℝ := M * Real.log 2
  refine ⟨Real.exp A, Real.exp_pos _, M, fun N hMN σ hσ hd => ?_⟩
  have hM : 1 ≤ M := by omega
  have hN : 1 ≤ N := by omega
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb : 1 ≤ N / M := (Nat.one_le_div_iff (by omega : 0 < M)).mpr hMN
  have hb0 : (0 : ℝ) < ((N / M : ℕ) : ℝ) := by exact_mod_cast (show 0 < N / M by omega)
  have hratio : ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / M := Nat.cast_div_le
  have hLb : Real.log ((N / M : ℕ) : ℝ) ≤ Real.log N - Real.log M := by
    rw [← Real.log_div hN0.ne' hM0.ne']
    exact Real.log_le_log hb0 hratio
  have hgap : a * Real.log M - 2 * C ≤ cutoffMass w N - cutoffMass w (N / M) := by
    have hNl := (abs_le.mp (hlog N hN)).1
    have hbu := (abs_le.mp (hlog (N / M) hb)).2
    have hmul := mul_le_mul_of_nonneg_left hLb ha.le
    linarith only [hNl, hbu, hmul]
  let R := cutoffMass (exponentialTilt w (A / N)) N
  have hhalf : R ≤ (cutoffMass w N + cutoffMass w (N / M)) / 2 := cutoffMass_tilt_half hw hM hN
  have hres : 1 ≤ 1 / σ - R := by linarith only [hd, hgap, hhalf, hMlog']
  have hden : σ ≤ 1 - σ * R := by
    have h := mul_le_mul_of_nonneg_left hres hσ.le
    simpa only [mul_one, mul_sub, one_div, mul_inv_cancel₀ hσ.ne'] using h
  have ht : cutoffMass (exponentialTilt (fun r => σ * w r) (A / N)) N = σ * R := by
    change (∑ r ∈ Finset.Icc 1 N, Real.exp (-(A / N) * r) * (σ * w r)) = _
    rw [show σ * R = ∑ r ∈ Finset.Icc 1 N, σ * (Real.exp (-(A / N) * r) * w r) from
      Finset.mul_sum _ _ _]
    exact Finset.sum_congr rfl fun r _ => by ring
  have hsub : cutoffMass (exponentialTilt (fun r => σ * w r) (A / N)) N < 1 := by
    rw [ht]
    linarith only [hden, hσ]
  have hA : 0 ≤ A / N := by
    exact div_nonneg (mul_nonneg hM0.le (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le) hN0.le
  have hF := renewalFunction_le_exp_div (fun r => mul_nonneg hσ.le (hw r)) hA N hsub
  rw [ht, div_mul_cancel₀ A hN0.ne'] at hF
  calc
    σ * renewalFunction (fun r => σ * w r) N ≤ σ * (Real.exp A / (1 - σ * R)) :=
      mul_le_mul_of_nonneg_left hF hσ.le
    _ ≤ Real.exp A := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (hσ.trans_le hden)).mpr
      have h := mul_le_mul_of_nonneg_left hden (Real.exp_nonneg A)
      convert h using 1
      ring

/-- Scaled geometric comparison, expressed in terms of the unnormalized critical distance. -/
theorem scaled_renewalFunction_le_inverse_gap (w : ℕ → ℝ) (hw : ∀ r, 0 ≤ w r)
    {σ : ℝ} (hσ : 0 < σ) (n : ℕ) (hgap : 0 < 1 / σ - cutoffMass w n) :
    σ * renewalFunction (fun r => σ * w r) n ≤ 1 / (1 / σ - cutoffMass w n) := by
  have hscale : cutoffMass (fun r => σ * w r) n = σ * cutoffMass w n :=
    (Finset.mul_sum ..).symm
  have hden : 0 < 1 - σ * cutoffMass w n := by
    have h := mul_pos hσ hgap
    simpa only [mul_sub, one_div, mul_inv_cancel₀ hσ.ne'] using h
  have hsub : cutoffMass (fun r => σ * w r) n < 1 := by rw [hscale]; linarith only [hden]
  have hgeom := renewalFunction_le_geometric (fun r => mul_nonneg hσ.le (hw r)) n hsub
  change renewalFunction (fun r => σ * w r) n ≤ 1 / (1 - cutoffMass (fun r => σ * w r) n) at hgeom
  rw [hscale] at hgeom
  calc
    _ ≤ σ * (1 / (1 - σ * cutoffMass w n)) :=
      mul_le_mul_of_nonneg_left hgeom hσ.le
    _ = _ := by field_simp

/-- The uniform logarithmic renewal bound, obtained from the return-sum logarithmic error.
The constant is uniform over all positive couplings with the indicated critical-distance bound. -/
theorem exists_scaled_renewalFunction_log_bound (w : ℕ → ℝ) (hw : ∀ r, 0 ≤ w r)
    {a C D : ℝ} (ha : 0 < a)
    (hlog : ∀ n : ℕ, 1 ≤ n → |cutoffMass w n - a * Real.log n| ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ σ : ℝ, 0 < σ →
      -D ≤ 1 / σ - cutoffMass w N → ∀ k : ℕ, 1 ≤ k → k ≤ N →
      σ * renewalFunction (fun r => σ * w r) k ≤ K / Real.log (1 + (N : ℝ) / k) := by
  obtain ⟨K₀, hK₀, N₀, hbound⟩ := exists_scaled_renewalFunction_bound w hw ha hlog (D := D)
  let S : ℝ := max (Real.log 2) (2 * (D + 2 * C) / a)
  let B : ℝ := Real.log (1 + Real.exp S)
  refine ⟨max (4 / a) (K₀ * B), (div_pos (by norm_num : (0 : ℝ) < 4) ha).trans_le
    (le_max_left _ _), N₀, fun N hN σ hσ hd k hk hkN => ?_⟩
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hx : 0 < (N : ℝ) / k := div_pos hN0 hk0
  have hx1 : 1 ≤ (N : ℝ) / k := (le_div_iff₀ hk0).mpr (by
    simpa only [one_mul] using (show (k : ℝ) ≤ N by exact_mod_cast hkN))
  have hL : 0 < Real.log (1 + (N : ℝ) / k) := Real.log_pos (by linarith only [hx])
  by_cases hlarge : S ≤ Real.log ((N : ℝ) / k)
  · have hthreshold : 2 * (D + 2 * C) ≤ Real.log ((N : ℝ) / k) * a :=
      (div_le_iff₀ ha).mp ((le_max_right _ _).trans hlarge)
    have hdiff := cutoffMass_sub_lower w hlog hk (show 1 ≤ N by omega)
    have hgap : a / 2 * Real.log ((N : ℝ) / k) ≤ 1 / σ - cutoffMass w k := by
      nlinarith only [hd, hdiff, hthreshold]
    have hlogbound : Real.log (1 + (N : ℝ) / k) ≤ 2 * Real.log ((N : ℝ) / k) := by
      have hpoint : 1 + (N : ℝ) / k ≤ 2 * ((N : ℝ) / k) := by linarith only [hx1]
      have hlog2 : Real.log 2 ≤ Real.log ((N : ℝ) / k) := (le_max_left _ _).trans hlarge
      have h := Real.log_le_log (by linarith only [hx] : 0 < 1 + (N : ℝ) / k) hpoint
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hx.ne'] at h
      linarith only [h, hlog2]
    have hgap' : a / 4 * Real.log (1 + (N : ℝ) / k) ≤ 1 / σ - cutoffMass w k := by
      have h := mul_le_mul_of_nonneg_left hlogbound (div_pos ha (by norm_num : (0 : ℝ) < 4)).le
      nlinarith only [h, hgap]
    have hgpos : 0 < a / 4 * Real.log (1 + (N : ℝ) / k) :=
      mul_pos (div_pos ha (by norm_num)) hL
    calc
      _ ≤ 1 / (1 / σ - cutoffMass w k) := scaled_renewalFunction_le_inverse_gap w hw hσ k
        (hgpos.trans_le hgap')
      _ ≤ 1 / (a / 4 * Real.log (1 + (N : ℝ) / k)) := one_div_le_one_div_of_le hgpos hgap'
      _ = (4 / a) / Real.log (1 + (N : ℝ) / k) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) hL.le
  · have hratio : (N : ℝ) / k ≤ Real.exp S := by
      calc
        _ = Real.exp (Real.log ((N : ℝ) / k)) := (Real.exp_log hx).symm
        _ ≤ _ := Real.exp_le_exp.mpr (le_of_lt (lt_of_not_ge hlarge))
    have hB : Real.log (1 + (N : ℝ) / k) ≤ B :=
      Real.log_le_log (by linarith only [hx]) (add_le_add le_rfl hratio)
    calc
      _ ≤ σ * renewalFunction (fun r => σ * w r) N :=
        mul_le_mul_of_nonneg_left (renewalFunction_mono_time (fun r => mul_nonneg hσ.le (hw r)) hkN) hσ.le
      _ ≤ K₀ := hbound N hN σ hσ hd
      _ ≤ K₀ * B / Real.log (1 + (N : ℝ) / k) :=
        (le_div_iff₀ hL).mpr (mul_le_mul_of_nonneg_left hB hK₀.le)
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_right _ _) hL.le

end Critical2DKPZ.Renewal

end
