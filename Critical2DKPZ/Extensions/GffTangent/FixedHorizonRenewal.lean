/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.OnePoint.SecondMoment
public import Critical2DKPZ.Renewal.CriticalWindow
import Critical2DKPZ.PolymerCalculus.OverlapRescaling
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! # Moving quasi-critical scalar renewal asymptotics -/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- The renewal gap has size l in the moving quasi-critical regime. The
variance relation is the source definition of that regime, not an estimate. -/
theorem tendsto_quasiCritical_renewalGap_div (l β : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N) :
    Tendsto (fun N => OnePoint.renewalGap (β N) N / l N) atTop (𝓝 1) := by
  have hnum : Tendsto (fun N : ℕ => Real.pi * (replicaOverlap N / Real.log (N : ℝ)))
      atTop (𝓝 1) := by
    simpa only [mul_one_div_cancel Real.pi_ne_zero] using
      Renewal.tendsto_overlap_div_log.const_mul Real.pi
  have hden : Tendsto (fun N : ℕ => 1 - l N / Real.log (N : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hratio
  have hquot := hnum.div hden one_ne_zero
  simp only [div_one] at hquot
  apply hquot.congr'
  filter_upwards [hσ, hl.eventually_gt_atTop 0, eventually_ge_atTop 2,
    hratio.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hσN hlN hN hsmall
  have hlog : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  have hR : replicaOverlap N ≠ 0 := (replicaOverlap_pos (by omega)).ne'
  change (Real.pi * (replicaOverlap N / Real.log (N : ℝ))) / (1 - l N / Real.log (N : ℝ)) =
    OnePoint.renewalGap (β N) N / l N
  dsimp only [OnePoint.renewalGap]
  rw [hσN]
  simp only [criticalSigmaSq, neg_div, ← sub_eq_add_neg]
  have hdiff : Real.log (N : ℝ) - l N ≠ 0 := by
    apply sub_ne_zero.mpr
    intro he
    rw [he, div_self hlN.ne'] at hsmall
    exact (lt_irrefl 1) hsmall
  simp only [one_sub_div hlog]
  field_simp [hlN.ne', hlog, hR, hdiff]
  ring

/-- A macroscopic change of lattice horizon has the corresponding finite
logarithmic effect on the replica overlap. -/
theorem tendsto_replicaOverlap_macroscopic_increment {m : ℕ → ℕ} {c : ℝ}
    (hc : 0 < c) (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => replicaOverlap (m N) - replicaOverlap N) atTop
      (𝓝 ((1 / Real.pi) * Real.log c)) := by
  have hreal := Tendsto.pos_mul_atTop hc hm (tendsto_natCast_atTop_atTop (R := ℝ))
  have hmtop : Tendsto m atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R := ℝ)).mp
    apply hreal.congr'
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact div_mul_cancel₀ _ (by exact_mod_cast (show N ≠ 0 by omega))
  obtain ⟨b, hb⟩ := PolymerCalculus.exists_tendsto_replicaOverlap_sub_log
  have hh := ((hb.comp hmtop).sub hb).add
    ((PolymerCalculus.tendsto_log_clock_ratio hc hm).const_mul (1 / Real.pi))
  simp only [sub_self, zero_add] at hh
  convert hh using 1
  funext N
  simp only [Function.comp_apply]
  ring

/-- The same gap normalization holds for every macroscopic positive horizon. -/
theorem tendsto_quasiCritical_renewalGap_macroscopic (l β : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => OnePoint.renewalGap (β N) (m N) / l N) atTop (𝓝 1) := by
  have hdiff := ((tendsto_replicaOverlap_macroscopic_increment hc hm).neg.const_mul Real.pi).div_atTop hl
  have hh := (tendsto_quasiCritical_renewalGap_div l β hl hratio hσ).add hdiff
  simp only [add_zero] at hh
  convert hh using 1
  funext N
  dsimp only [OnePoint.renewalGap]
  ring

/-- A diverging renewal gap controls the second moment uniformly enough for
a moving-horizon limit. Its gap premise is discharged by the preceding lemmas. -/
theorem tendsto_free_second_moment_of_gap (l β : ℕ → ℝ) (m : ℕ → ℕ)
    (hl : Tendsto l atTop atTop) (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hgap : Tendsto (fun N => OnePoint.renewalGap (β N) (m N) / l N) atTop (𝓝 1)) :
    Tendsto (fun N => l N * Polymer.sigmaSq (β N) *
      (∫ ω, pointToPlane (β N) 0 (m N) 0 ω ^ 2 ∂disorderLaw)) atTop (𝓝 Real.pi) := by
  let g : ℕ → ℝ := fun N => OnePoint.renewalGap (β N) (m N)
  have hg := hgap
  have hgood : ∀ᶠ N : ℕ in atTop, 0 < l N ∧ 0 < g N := by
    filter_upwards [hl.eventually_gt_atTop 0,
      hg.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with N hlN hgN
    exact ⟨hlN, (div_pos_iff_of_pos_right hlN).mp hgN⟩
  have hlg : Tendsto (fun N => l N / g N) atTop (𝓝 1) := by
    have hh := hg.inv₀ one_ne_zero
    simpa only [inv_div, inv_one] using hh
  obtain ⟨C, hC⟩ := OnePoint.renewalGap_secondMoment_bounds
  have he : Tendsto (fun N => C * (l N / g N) ^ 2 / l N) atTop (𝓝 0) :=
    Tendsto.div_atTop (tendsto_const_nhds.mul (hlg.pow 2)) hl
  have heq (N : ℕ) (hlN : 0 < l N) (hgN : 0 < g N) :
      C * (l N / g N) ^ 2 / l N = l N * (C / g N ^ 2) := by
    field_simp [hlN.ne', hgN.ne']
  let E : ℕ → ℝ := fun N => l N * (Real.pi / g N - Polymer.sigmaSq (β N) *
    (∫ ω, pointToPlane (β N) 0 (m N) 0 ω ^ 2 ∂disorderLaw))
  have hE : Tendsto E atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ he
    · filter_upwards [hgood, hβ] with N hN hβN
      exact mul_nonneg hN.1.le (hC (β N) hβN (m N) hN.2).1
    · filter_upwards [hgood, hβ] with N hN hβN
      rw [heq N hN.1 hN.2]
      exact mul_le_mul_of_nonneg_left (hC (β N) hβN (m N) hN.2).2 hN.1.le
  have hmain := (hlg.const_mul Real.pi).sub hE
  have hh : Tendsto (fun N => Real.pi * (l N / g N) - E N) atTop (𝓝 Real.pi) := by
    simpa only [mul_one, sub_zero] using hmain
  apply hh.congr'
  filter_upwards [] with N
  dsimp only [E]
  ring


/-- Scalar resolvent asymptotics at a positive macroscopic fraction of the
lattice scale, as required inside a fixed linear-time block. -/
theorem tendsto_quasiCritical_free_second_moment_macroscopic (l β : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    Tendsto (fun N => l N * Polymer.sigmaSq (β N) *
      (∫ ω, pointToPlane (β N) 0 (m N) 0 ω ^ 2 ∂disorderLaw)) atTop (𝓝 Real.pi) :=
  tendsto_free_second_moment_of_gap l β m hl hβ
    (tendsto_quasiCritical_renewalGap_macroscopic l β hl hratio hσ hc hm)

/-- The unscaled free second moment increases with the available duration. -/
theorem integral_sq_pointToPlane_mono_time (β : ℝ) {k m : ℕ} (hkm : k ≤ m) :
    (∫ ω, pointToPlane β 0 k 0 ω ^ 2 ∂disorderLaw) ≤
      ∫ ω, pointToPlane β 0 m 0 ω ^ 2 ∂disorderLaw := by
  change Renewal.freeSecondMoment β k ≤ Renewal.freeSecondMoment β m
  rw [Renewal.freeSecondMoment_eq_renewalFunction β]
  apply Renewal.renewalFunction_mono_time _ hkm
  intro r
  exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (sq_nonneg β)))
    (Critical2DKPZ.srwKernel_nonneg (2 * r) 0)

/-- The quasi-critical scalar resolvent is uniformly bounded throughout a
macroscopic horizon, including the zero-duration endpoint. -/
theorem eventually_quasiCritical_free_second_moment_le (l β : ℕ → ℝ)
    (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {m : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hm : Tendsto (fun N : ℕ => (m N : ℝ) / N) atTop (𝓝 c)) :
    ∀ᶠ N : ℕ in atTop, ∀ k ≤ m N,
      |l N * Polymer.sigmaSq (β N) *
        (∫ ω, pointToPlane (β N) 0 k 0 ω ^ 2 ∂disorderLaw)| ≤ Real.pi + 1 := by
  have hlim := tendsto_quasiCritical_free_second_moment_macroscopic
    l β hl hratio hβ hσ hc hm
  filter_upwards [hl.eventually (eventually_gt_atTop 0),
    hlim.eventually (gt_mem_nhds (lt_add_one Real.pi))] with N hlN hlimN k hk
  have hσ0 : 0 ≤ Polymer.sigmaSq (β N) :=
    sub_nonneg.mpr (Real.one_le_exp (sq_nonneg _))
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg hlN.le hσ0)
    (integral_nonneg (fun _ => sq_nonneg _)))]
  exact (mul_le_mul_of_nonneg_left (integral_sq_pointToPlane_mono_time (β N) hk)
    (mul_nonneg hlN.le hσ0)).trans hlimN.le

end Critical2DKPZ.Extensions.GffTangent
