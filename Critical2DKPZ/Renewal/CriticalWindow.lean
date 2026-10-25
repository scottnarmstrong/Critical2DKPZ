/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Renewal.Sequence
public import Critical2DKPZ.Lattice.Basic
import Critical2DKPZ.Renewal.LogarithmicBound
import Critical2DKPZ.RandomWalk.ReplicaOverlap

/-! # Critical-window scalar normalization

The return weights `q_{2r}(0)` sum to `replicaOverlap`, and the critical fugacity is
`1 + ϑ / log N`; the overlap grows as `log N / π`. -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- Period-2 collision weights; the renewal index counts positive time gaps. -/
def returnWeight (r : ℕ) : ℝ := srwKernel (2 * r) 0

/-- The critical-window renewal mass, including a unit atom at time zero. -/
def criticalRenewalMass (ϑ : ℝ) (N n : ℕ) : ℝ :=
  renewalMass (fun r => criticalSigmaSq ϑ N * returnWeight r) n

/-- The deterministic free second-moment renewal function. -/
def criticalRenewalFunction (ϑ : ℝ) (N n : ℕ) : ℝ :=
  renewalFunction (fun r => criticalSigmaSq ϑ N * returnWeight r) n

/-- The finite sum of return weights equals the replica overlap. -/
theorem sum_returnWeight (N : ℕ) :
    ∑ r ∈ Finset.Icc 1 N, returnWeight r = replicaOverlap N := rfl

/-- The normalization parameter in CSZ19a is exactly `1 + ϑ/log N`. -/
theorem criticalSigmaSq_mul_overlap (ϑ : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    criticalSigmaSq ϑ N * replicaOverlap N = 1 + ϑ / Real.log N := by
  exact div_mul_cancel₀ _ (replicaOverlap_pos hN).ne'

/-- Eventually the window numerator is positive, for every real parameter. -/
theorem criticalSigmaSq_eventually_pos (ϑ : ℝ) :
    ∀ᶠ N : ℕ in atTop, 0 < criticalSigmaSq ϑ N := by
  filter_upwards [eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop |ϑ|]
      with N hN hlog
  change |ϑ| < Real.log (N : ℝ) at hlog
  have hL : 0 < Real.log (N : ℝ) := (abs_nonneg ϑ).trans_lt hlog
  have hnum : 0 < 1 + ϑ / Real.log (N : ℝ) := by
    have : -1 < ϑ / Real.log (N : ℝ) := (lt_div_iff₀ hL).mpr (by linarith [neg_abs_le ϑ])
    linarith only [this]
  exact div_pos hnum (replicaOverlap_pos hN)

/-- One plus a fixed parameter divided by the logarithm tends to one. -/
theorem tendsto_one_add_div_log (ϑ : ℝ) :
    Tendsto (fun N : ℕ => 1 + ϑ / Real.log N) atTop (nhds 1) := by
  have hinv : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  simpa only [Pi.add_apply, Pi.mul_apply, div_eq_mul_inv, mul_zero, add_zero] using
    (tendsto_const_nhds (x := (1 : ℝ))).add ((tendsto_const_nhds (x := ϑ)).mul hinv)

/-- A bounded logarithmic error implies convergence of the normalized overlap. -/
theorem tendsto_div_log_of_bounded_error (f : ℕ → ℝ) (a C : ℝ)
    (herror : ∀ N : ℕ, 1 ≤ N → |f N - a * Real.log N| ≤ C) :
    Tendsto (fun N : ℕ => f N / Real.log N) atTop (nhds a) := by
  have hinv : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hC : Tendsto (fun N : ℕ => C / Real.log N) atTop (nhds 0) := by
    simpa only [Pi.mul_apply, div_eq_mul_inv, mul_zero] using (tendsto_const_nhds (x := C)).mul hinv
  have hz : Tendsto (fun N : ℕ => (f N - a * Real.log N) / Real.log N) atTop (nhds 0) := by
    apply squeeze_zero_norm' _ hC
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hlog]
    exact div_le_div_of_nonneg_right (herror N (by omega)) hlog.le
  have h := (tendsto_const_nhds (x := a)).add hz
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  change a + (f N - a * Real.log N) / Real.log N = f N / Real.log N
  field_simp
  ring

/-- The normalized replica overlap tends to the period-2 constant `1/π`. -/
theorem tendsto_overlap_div_log :
    Tendsto (fun N : ℕ => replicaOverlap N / Real.log N) atTop (nhds (1 / Real.pi)) := by
  obtain ⟨C, hC⟩ := replicaOverlap_log_bound
  exact tendsto_div_log_of_bounded_error replicaOverlap (1 / Real.pi) C hC


/-- `R_N / log N → 1/π` implies `σ_N² log N → π`. -/
theorem tendsto_sigma_mul_log (ϑ : ℝ) :
    Tendsto (fun N : ℕ => criticalSigmaSq ϑ N * Real.log N) atTop (nhds Real.pi) := by
  have h := (tendsto_one_add_div_log ϑ).div tendsto_overlap_div_log (one_div_pos.mpr Real.pi_pos).ne'
  have h' : Tendsto (fun N : ℕ => (1 + ϑ / Real.log N) /
      (replicaOverlap N / Real.log N)) atTop (nhds Real.pi) := by
    simpa only [one_div_one_div] using! h
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  unfold criticalSigmaSq
  field_simp

/-- The critical disorder variance tends to zero. -/
theorem tendsto_sigma_zero (ϑ : ℝ) :
    Tendsto (criticalSigmaSq ϑ) atTop (nhds 0) := by
  have hinv := tendsto_inv_atTop_zero.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have h := (tendsto_sigma_mul_log ϑ).mul hinv
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  simp only [Function.comp_def, mul_assoc, mul_inv_cancel₀ hlog, mul_one]


/-- The inverse critical distance is eventually bounded below by a constant depending only on the critical parameter. -/
theorem eventually_inverse_sigma_sub_overlap_lower (ϑ : ℝ) :
    ∀ᶠ N : ℕ in atTop, -(2 * |ϑ| / Real.pi) ≤ 1 / criticalSigmaSq ϑ N - replicaOverlap N := by
  have ht := tendsto_sigma_mul_log ϑ
  have hhalf : Real.pi / 2 < Real.pi := by linarith only [Real.pi_pos]
  filter_upwards [eventually_ge_atTop 2, criticalSigmaSq_eventually_pos ϑ,
    ht.eventually_const_lt hhalf] with N hN hσ hprod
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hid : 1 / criticalSigmaSq ϑ N - replicaOverlap N =
      -ϑ / (criticalSigmaSq ϑ N * Real.log N) := by
    have h := criticalSigmaSq_mul_overlap ϑ (by omega : 1 ≤ N)
    field_simp at h ⊢
    nlinarith only [h]
  rw [hid]
  have hdenpos : 0 < criticalSigmaSq ϑ N * Real.log N :=
    (div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 2)).trans hprod
  have hbound : |ϑ| / (criticalSigmaSq ϑ N * Real.log N) ≤ 2 * |ϑ| / Real.pi := by
    calc
      _ ≤ |ϑ| / (Real.pi / 2) := div_le_div_of_nonneg_left (abs_nonneg ϑ)
        (div_pos Real.pi_pos (by norm_num)) hprod.le
      _ = _ := by ring
  have hθ : ϑ / (criticalSigmaSq ϑ N * Real.log N) ≤
      |ϑ| / (criticalSigmaSq ϑ N * Real.log N) :=
    div_le_div_of_nonneg_right (le_abs_self ϑ) hdenpos.le
  rw [neg_div]
  linarith only [hbound, hθ]

/-- The variance-weighted critical renewal function has a uniform inverse-logarithmic bound on the unit time horizon. -/
theorem criticalRenewalFunction_log_bound (ϑ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → k ≤ N →
      criticalSigmaSq ϑ N * criticalRenewalFunction ϑ N k ≤
        C / Real.log (1 + (N : ℝ) / k) := by
  obtain ⟨C, hC⟩ := replicaOverlap_log_bound
  have hw : ∀ r, 0 ≤ returnWeight r := fun r => srwKernel_nonneg _ _
  obtain ⟨K, hK, N₀, hbound⟩ := exists_scaled_renewalFunction_log_bound returnWeight hw
    (one_div_pos.mpr Real.pi_pos) hC (D := 2 * |ϑ| / Real.pi)
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop N₀, criticalSigmaSq_eventually_pos ϑ,
    eventually_inverse_sigma_sub_overlap_lower ϑ] with N hN hσ hd
  exact hbound N hN (criticalSigmaSq ϑ N) hσ hd

/-- The inverse-logarithmic renewal bound holds through every fixed integer multiple of the scale. -/
theorem criticalRenewalFunction_log_bound_mul_horizon (ϑ : ℝ) (B : ℕ) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → k ≤ B * N →
      criticalSigmaSq ϑ N * criticalRenewalFunction ϑ N k ≤
        C / Real.log (1 + (N : ℝ) / k) := by
  obtain ⟨C, hC⟩ := replicaOverlap_log_bound
  let a := 1 / Real.pi
  let D := 2 * |ϑ| / Real.pi
  have hw : ∀ r, 0 ≤ returnWeight r := fun r => srwKernel_nonneg _ _
  obtain ⟨K, hK, N₀, hbound⟩ := exists_scaled_renewalFunction_log_bound returnWeight hw
    (one_div_pos.mpr Real.pi_pos) hC (D := D + a * Real.log B + 2 * C)
  refine ⟨K, hK, ?_⟩
  filter_upwards [eventually_ge_atTop (max N₀ 1), criticalSigmaSq_eventually_pos ϑ,
    eventually_inverse_sigma_sub_overlap_lower ϑ] with N hN hσ hd
  have hN1 : 1 ≤ N := (le_max_right _ _).trans hN
  have hNN : N ≤ B * N := by simpa only [one_mul] using Nat.mul_le_mul_right N hB
  have hBN1 : 1 ≤ B * N := hN1.trans hNN
  have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast (show B ≠ 0 by omega)
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hlogBN : Real.log ((B * N : ℕ) : ℝ) = Real.log B + Real.log N := by
    rw [Nat.cast_mul, Real.log_mul hB0 hN0]
  have hshift : replicaOverlap (B * N) - replicaOverlap N ≤ a * Real.log B + 2 * C := by
    have hu := (abs_le.mp (hC (B * N) hBN1)).2
    have hl := (abs_le.mp (hC N hN1)).1
    rw [hlogBN] at hu
    change replicaOverlap (B * N) - a * (Real.log B + Real.log N) ≤ C at hu
    change -C ≤ replicaOverlap N - a * Real.log N at hl
    linarith only [hu, hl]
  have hd' : -(D + a * Real.log B + 2 * C) ≤
      1 / criticalSigmaSq ϑ N - replicaOverlap (B * N) := by
    change -D ≤ 1 / criticalSigmaSq ϑ N - replicaOverlap N at hd
    linarith only [hd, hshift]
  intro k hk hkBN
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hden : 0 < Real.log (1 + (N : ℝ) / k) :=
    Real.log_pos (by linarith only [div_pos hNpos hk0])
  have hdenmono : Real.log (1 + (N : ℝ) / k) ≤ Real.log (1 + ((B * N : ℕ) : ℝ) / k) :=
    Real.log_le_log (by linarith only [div_pos hNpos hk0])
      (add_le_add le_rfl (div_le_div_of_nonneg_right (by exact_mod_cast hNN) hk0.le))
  exact (hbound (B * N) (((le_max_left _ _).trans hN).trans hNN)
    (criticalSigmaSq ϑ N) hσ hd' k hk hkBN).trans
    (div_le_div_of_nonneg_left hK.le hden hdenmono)

/-- The variance-weighted critical renewal function has an inverse-logarithmic bound on every fixed real time horizon. -/
theorem criticalRenewalFunction_log_bound_horizon (ϑ T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ T * N →
      criticalSigmaSq ϑ N * criticalRenewalFunction ϑ N k ≤
        C / Real.log (1 + (N : ℝ) / k) := by
  obtain ⟨B, hBT⟩ := exists_nat_gt T
  let B' := B + 1
  obtain ⟨C, hC, hbound⟩ := criticalRenewalFunction_log_bound_mul_horizon ϑ B'
    (by omega)
  refine ⟨C, hC, hbound.mono fun N hN k hk hkT => ?_⟩
  have hB'T : T ≤ (B' : ℝ) := by
    exact hBT.le.trans (Nat.cast_le.mpr (Nat.le_succ B))
  have hkB : (k : ℝ) ≤ ((B' * N : ℕ) : ℝ) := by
    rw [Nat.cast_mul]
    exact hkT.trans (mul_le_mul_of_nonneg_right hB'T (Nat.cast_nonneg N))
  exact hN k hk (by exact_mod_cast hkB)

/-- The inverse-logarithmic renewal bound with denominator time `L + 1` includes the zero horizon. -/
theorem criticalRenewalFunction_log_bound_zero_horizon (ϑ T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ L : ℕ, (L : ℝ) ≤ T * N →
      criticalSigmaSq ϑ N * criticalRenewalFunction ϑ N L ≤
        C / Real.log (1 + (N : ℝ) / (L + 1)) := by
  obtain ⟨C, hC, hbound⟩ := criticalRenewalFunction_log_bound_horizon ϑ (T + 1)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop 1, criticalSigmaSq_eventually_pos ϑ]
    with N hN hN1 hσ
  intro L hL
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hL' : ((L + 1 : ℕ) : ℝ) ≤ (T + 1) * N := by
    push_cast
    nlinarith only [hL, hNreal]
  have hm := renewalFunction_mono_time
    (fun r => mul_nonneg hσ.le (srwKernel_nonneg (2 * r) 0)) (Nat.le_succ L)
  exact (mul_le_mul_of_nonneg_left hm hσ.le).trans
    (by simpa only [Nat.cast_add, Nat.cast_one] using! hN (L + 1) (by omega) hL')

end Critical2DKPZ.Renewal

end
