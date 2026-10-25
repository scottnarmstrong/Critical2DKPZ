/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.ClockTuning
public import Critical2DKPZ.PolymerCalculus.ClockTuning
public import Critical2DKPZ.PolymerCalculus.Clocks
public import Mathlib.Tactic
import Mathlib.Topology.Sequences
import Mathlib.Topology.EMetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

/-! Along cofinal horizons with a positive limiting ratio, critical-window retuning shifts a convergent parameter by the logarithm of that ratio. -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.PolymerCalculus



private theorem tendsto_log_horizon_difference {K M : ℕ → ℕ} {D : ℝ}
    (hK : Tendsto K atTop atTop) (hM : Tendsto (fun n => (M n : ℝ) / K n) atTop (𝓝 D))
    (hD : 0 < D) :
    Tendsto (fun n => Real.log (M n) - Real.log (K n)) atTop (𝓝 (Real.log D)) := by
  have h := hM.log hD.ne'
  apply h.congr'
  filter_upwards [hM.eventually (lt_mem_nhds (show 0 < D by exact hD)),
    hK.eventually (eventually_ge_atTop 1)] with n hratio hKn
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast (show 0 < K n by omega)
  have hMpos : (0 : ℝ) < M n := by
    have := (div_pos_iff_of_pos_right hKpos).mp hratio
    exact_mod_cast this
  rw [Real.log_div hMpos.ne' hKpos.ne']

/-- The ratio of the two logarithmic horizons tends to one along cofinal clocks. -/
private theorem tendsto_log_horizon_ratio {K M : ℕ → ℕ} {D : ℝ}
    (hK : Tendsto K atTop atTop) (hM : Tendsto (fun n => (M n : ℝ) / K n) atTop (𝓝 D))
    (hD : 0 < D) :
    Tendsto (fun n => Real.log (M n) / Real.log (K n)) atTop (𝓝 1) := by
  have hlogdiff := tendsto_log_horizon_difference hK hM hD
  have hInv : Tendsto (fun n => (Real.log (K n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hK))
  have hfrac := (hlogdiff.mul hInv)
  have h := hfrac.const_add 1
  simp only [mul_zero, add_zero] at h
  apply h.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop 2),
    hM.eventually (lt_mem_nhds (show 0 < D by exact hD))] with n hKn hratio
  have hKpos : (0 : ℝ) < K n := by exact_mod_cast (show 0 < K n by omega)
  have hMpos : (0 : ℝ) < M n := by
    have := (div_pos_iff_of_pos_right hKpos).mp hratio
    exact_mod_cast this
  have hlog : Real.log (K n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < K n by omega))).ne'
  field_simp
  ring

/-- The critical variance multiplied by the logarithm of its horizon tends to `π` along cofinal horizons and convergent parameters. -/
private theorem tendsto_sigma_log_horizon {K : ℕ → ℕ} {θ : ℕ → ℝ} {ϑ : ℝ}
    (hK : Tendsto K atTop atTop) (hθ : Tendsto θ atTop (𝓝 ϑ)) :
    Tendsto (fun n => criticalSigmaSq (θ n) (K n) * Real.log (K n)) atTop (𝓝 Real.pi) := by
  have hInv : Tendsto (fun n => (Real.log (K n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp hK))
  have hnum := (hθ.mul hInv).const_add 1
  simp only [mul_zero, add_zero] at hnum
  have hR : Tendsto (fun n => replicaOverlap (K n) / Real.log (K n)) atTop
      (𝓝 (1 / Real.pi)) := Renewal.tendsto_overlap_div_log.comp hK
  have h := hnum.div hR (by positivity : (1 / Real.pi : ℝ) ≠ 0)
  have h' : Tendsto
      ((fun x => 1 + θ x * (Real.log (K x))⁻¹) /
        fun n => replicaOverlap (K n) / Real.log (K n)) atTop (𝓝 Real.pi) := by
    simpa only [show (1 : ℝ) / (1 / Real.pi) = Real.pi by field_simp] using h
  apply h'.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop 2)] with n hKn
  have hlogne : Real.log (K n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < K n by omega))).ne'
  have hRne : replicaOverlap (K n) ≠ 0 :=
    (replicaOverlap_pos (by omega : 1 ≤ K n)).ne'
  change (1 + θ n / Real.log (K n)) / (replicaOverlap (K n) / Real.log (K n)) =
    ((1 + θ n / Real.log (K n)) / replicaOverlap (K n)) * Real.log (K n)
  field_simp [hlogne, hRne]

/-- The overlap increment is logarithmic along any cofinal pair of horizons. -/
private theorem tendsto_overlap_difference_along {K M : ℕ → ℕ} {D : ℝ}
    (hK : Tendsto K atTop atTop) (hM : Tendsto (fun n => (M n : ℝ) / K n) atTop (𝓝 D))
    (hD : 0 < D) :
    Tendsto (fun n => replicaOverlap (M n) - replicaOverlap (K n)) atTop
      (𝓝 ((1 / Real.pi) * Real.log D)) := by
  have hlog := tendsto_log_horizon_difference hK hM hD
  have herr : Tendsto (fun n => replicaOverlap (M n) - replicaOverlap (K n) -
      (1 / Real.pi) * (Real.log (M n) - Real.log (K n))) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hu := replicaOverlap_increment_uniform_lower (show 0 < D / 2 by positivity) hε
    have hlower : ∀ᶠ n in atTop, (D / 2) * K n ≤ M n := by
      filter_upwards [hM.eventually (lt_mem_nhds (show D / 2 < D by linarith)),
        hK.eventually (eventually_ge_atTop 1)] with n hn hKn
      have hKpos : (0 : ℝ) < K n := by exact_mod_cast (show 0 < K n by omega)
      have h := (lt_div_iff₀ hKpos).mp hn
      exact_mod_cast h.le
    have huK := hK.eventually hu
    filter_upwards [huK, hlower] with n hn hmn
    simpa only [Real.dist_eq, sub_zero] using hn (M n) hmn
  have h := herr.add ((hlog).const_mul (1 / Real.pi))
  simpa only [sub_add_cancel, zero_add] using h

/-- Retuning cofinal horizons with a positive limiting ratio adds the logarithm of that ratio to the limiting critical-window parameter. -/
theorem tendsto_critical_clock_tuning_along {K M : ℕ → ℕ} {D : ℝ} (hD : 0 < D)
    (hK : Tendsto K atTop atTop)
    (hM : Tendsto (fun n => (M n : ℝ) / K n) atTop (𝓝 D))
    {θ : ℕ → ℝ} {ϑ : ℝ} (hθ : Tendsto θ atTop (𝓝 ϑ)) :
    Tendsto (fun n => Real.log (M n) *
      (criticalSigmaSq (θ n) (K n) * replicaOverlap (M n) - 1) -
      θ n - Real.log D) atTop (𝓝 0) := by
  have hlog := tendsto_log_horizon_ratio hK hM hD
  have hsigK := tendsto_sigma_log_horizon hK hθ
  have hsigM := hsigK.mul hlog
  have hdiff := tendsto_overlap_difference_along hK hM hD
  have hfirst := hθ.mul (hlog.sub_const 1)
  have hsecond := hsigM.mul hdiff
  have h := (hfirst.add hsecond).sub_const (Real.log D)
  have hlim : ϑ * (1 - 1) + Real.pi * 1 * ((1 / Real.pi) * Real.log D) -
      Real.log D = 0 := by field_simp; ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [hK.eventually (eventually_ge_atTop 2)] with n hn
  have ht := Renewal.criticalSigmaSq_mul_overlap (θ n) (by omega : 1 ≤ K n)
  have hlogne : Real.log (K n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < K n by omega))).ne'
  calc
    θ n * (Real.log (M n) / Real.log (K n) - 1) +
        (criticalSigmaSq (θ n) (K n) * Real.log (K n) *
          (Real.log (M n) / Real.log (K n))) *
          (replicaOverlap (M n) - replicaOverlap (K n)) - Real.log D =
        (Real.log (M n) *
          (criticalSigmaSq (θ n) (K n) * replicaOverlap (M n) - 1) -
          θ n - Real.log D) - Real.log (M n) *
            (criticalSigmaSq (θ n) (K n) * replicaOverlap (K n) -
              (1 + θ n / Real.log (K n))) := by
                  field_simp [hlogne]
                  ring
    _ = _ := by rw [ht, sub_self, mul_zero, sub_zero]


end Critical2DKPZ.PolymerCalculus
