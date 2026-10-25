/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonParameters
import Mathlib.Tactic

/-! # Quasi-critical variance and geometric-resolvent scales -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- The actual moving quasi-critical disorder variance has normalization pi/log N. -/
theorem tendsto_quasiCritical_sigma_mul_log (l β : ℕ → ℝ)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N) :
    Tendsto (fun N => Polymer.sigmaSq (β N) * Real.log (N : ℝ)) atTop (𝓝 Real.pi) := by
  apply (tendsto_criticalSigmaSq_neg_mul_log l hratio).congr'
  filter_upwards [hσ] with N hN
  rw [hN]

/-- The moving quasi-critical variance tends to zero. -/
theorem tendsto_quasiCritical_sigma_zero (l β : ℕ → ℝ)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N) :
    Tendsto (fun N => Polymer.sigmaSq (β N)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h := (tendsto_quasiCritical_sigma_mul_log l β hratio hσ).div_atTop hlog
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hne : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  field_simp

/-- l times the disorder variance still tends to zero in the quasi-critical regime. -/
theorem tendsto_quasiCritical_l_sigma_zero (l β : ℕ → ℝ)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N) :
    Tendsto (fun N => l N * Polymer.sigmaSq (β N)) atTop (𝓝 0) := by
  have h := hratio.mul (tendsto_quasiCritical_sigma_mul_log l β hratio hσ)
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hne : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  field_simp

/-- The variance-overlap product approaches one on any positive macroscopic horizon. -/
theorem tendsto_quasiCritical_sigma_overlap_macroscopic (l β : ℕ → ℝ)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => Polymer.sigmaSq (β N) * replicaOverlap (m N)) atTop (𝓝 1) := by
  have hfull : Tendsto (fun N => Polymer.sigmaSq (β N) * replicaOverlap N) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).sub hratio
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards [hσ, eventually_ge_atTop 2] with N hσN hN
    rw [hσN, criticalSigmaSq_neg_mul_replicaOverlap (l N) (by omega)]
    exact (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have herr := (tendsto_quasiCritical_sigma_zero l β hratio hσ).mul
    (tendsto_replicaOverlap_macroscopic_increment hc hm)
  have h := hfull.add herr
  simp only [zero_mul, add_zero] at h
  apply h.congr'
  filter_upwards [] with N
  ring

/-- Positivity of the actual variance converts the renewal gap into the
subcritical denominator exactly. -/
theorem subcritical_denominator_eq_gap (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    1 - Polymer.sigmaSq β * replicaOverlap m =
      OnePoint.renewalGap β m * Polymer.sigmaSq β / Real.pi := by
  have hσ : 0 < Polymer.sigmaSq β :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (sq_pos_of_pos hβ))
  unfold OnePoint.renewalGap
  field_simp [hσ.ne']

/-- Every fixed positive macroscopic window is eventually subcritical. -/
theorem eventually_quasiCritical_sigma_overlap_lt_one (l β : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) * replicaOverlap (m N) < 1 := by
  have hgap := tendsto_quasiCritical_renewalGap_macroscopic l β hl hratio hσ hc hm
  filter_upwards [hl.eventually_gt_atTop 0, hβ,
    hgap.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hlN hβN hgN
  have hg : 0 < OnePoint.renewalGap (β N) (m N) :=
    (div_pos_iff_of_pos_right hlN).mp hgN
  apply sub_pos.mp
  rw [subcritical_denominator_eq_gap (β N) hβN]
  exact div_pos (mul_pos hg (sub_pos.mpr (Real.one_lt_exp_iff.mpr (sq_pos_of_pos hβN)))) Real.pi_pos

/-- The geometric prefactor has normalization pi on every positive
macroscopic window, not just the full horizon. -/
theorem tendsto_quasiCritical_geometric_prefactor_macroscopic (l β : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => l N * Polymer.sigmaSq (β N) /
      (1 - Polymer.sigmaSq (β N) * replicaOverlap (m N))) atTop (𝓝 Real.pi) := by
  have hgap := tendsto_quasiCritical_renewalGap_macroscopic l β hl hratio hσ hc hm
  have hlg : Tendsto (fun N => l N / OnePoint.renewalGap (β N) (m N)) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using hgap.inv₀ one_ne_zero
  have h := hlg.const_mul Real.pi
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [hl.eventually_gt_atTop 0, hβ,
    hgap.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hlN hβN hgN
  have hg : 0 < OnePoint.renewalGap (β N) (m N) :=
    (div_pos_iff_of_pos_right hlN).mp hgN
  have hσN : 0 < Polymer.sigmaSq (β N) :=
    sub_pos.mpr (Real.one_lt_exp_iff.mpr (sq_pos_of_pos hβN))
  rw [subcritical_denominator_eq_gap (β N) hβN]
  field_simp [hg.ne', hσN.ne']

end Critical2DKPZ.Extensions.GffTangent
