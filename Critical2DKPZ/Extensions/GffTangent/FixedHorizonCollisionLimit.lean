/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonRenewal
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonWalkEnergy
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonTimeLimit
import Mathlib.Tactic

/-! # Quasi-critical first-collision variance limits on a fixed window -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- The spatially averaged first-collision sum has the CCR heat-form limit on
any fixed macroscopic window. Both the renewal and walk factors are the actual
polymer quantities. -/
theorem tendsto_quasiCritical_averaged_first_collision
    (l β : ℕ → ℝ) (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (A B : ℕ → ℕ)
    (hA : Tendsto (fun N : ℕ => (A N : ℝ) / N) atTop (𝓝 a))
    (hB : Tendsto (fun N : ℕ => (B N : ℝ) / N) atTop (𝓝 b))
    (f g : Plane → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hgm : Measurable g) (Cg : ℝ) (hgB : ∀ y, |g y| ≤ Cg) :
    Tendsto (fun N : ℕ =>
      (∑ r ∈ Finset.Icc (A N + 1) (B N),
        (∫ p : Plane × Plane, f p.1 * g p.2 *
          ((N : ℝ) / 4 * srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1))
          ∂(volume.prod volume)) *
        (l N * Polymer.sigmaSq (β N) *
          (∫ ω, pointToPlane (β N) 0 (B N - r) 0 ω ^ 2 ∂disorderLaw))) / N)
      atTop (𝓝 (Real.pi * ∫ t in Ioo a b, ∫ p : Plane × Plane,
        f p.1 * g p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume))) := by
  let E : ℕ → ℕ → ℝ := fun N r => ∫ p : Plane × Plane, f p.1 * g p.2 *
    ((N : ℝ) / 4 * srwKernel (2 * r) (latticePoint N p.2 - latticePoint N p.1))
      ∂(volume.prod volume)
  let R : ℕ → ℕ → ℝ := fun N k => l N * Polymer.sigmaSq (β N) *
    (∫ ω, pointToPlane (β N) 0 k 0 ω ^ 2 ∂disorderLaw)
  have hb : 0 < b := ha.trans_lt hab
  have hCg : 0 ≤ Cg := (abs_nonneg (g 0)).trans (hgB 0)
  have hL1 : 0 ≤ ∫ x : Plane, |f x| := integral_nonneg (fun _ => abs_nonneg _)
  have hR := eventually_quasiCritical_free_second_moment_le l β hl hratio hβ hσ hb hB
  have hbound : ∀ᶠ N : ℕ in atTop, ∀ r ∈ Finset.Icc (A N + 1) (B N),
      |E N r * R N (B N - r)| ≤ (Cg * ∫ x : Plane, |f x|) * (Real.pi + 1) := by
    filter_upwards [eventually_gt_atTop 0, hR] with N hN hRN r hr
    rw [abs_mul]
    exact mul_le_mul (abs_integral_scaled_walk_energy_le N r hN f g hf hgm Cg hgB)
      (hRN _ (Nat.sub_le _ _)) (abs_nonneg _) (mul_nonneg hCg hL1)
  have hpoint (t : ℝ) (ht : t ∈ Ioo a b) :
      Tendsto (fun N => E N (fixedHorizonClock N t) * R N (B N - fixedHorizonClock N t))
        atTop (𝓝 (Real.pi * ∫ p : Plane × Plane,
          f p.1 * g p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume))) := by
    have ht0 : 0 < t := ha.trans_lt ht.1
    have hc := tendsto_fixedHorizonClock_div ht0
    have hfit : ∀ᶠ N : ℕ in atTop, fixedHorizonClock N t ≤ B N := by
      filter_upwards [hc.eventually_lt hB ht.2, eventually_gt_atTop 0] with N hlt hN
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      exact (show fixedHorizonClock N t < B N by
        exact_mod_cast (div_lt_div_iff_of_pos_right hNr).mp hlt).le
    have hremain : Tendsto (fun N : ℕ => ((B N - fixedHorizonClock N t : ℕ) : ℝ) / N)
        atTop (𝓝 (b - t)) := by
      apply (hB.sub hc).congr'
      filter_upwards [hfit] with N hN
      rw [Nat.cast_sub hN, sub_div]
    have hres := tendsto_quasiCritical_free_second_moment_macroscopic
      l β hl hratio hβ hσ (sub_pos.mpr ht.2) hremain
    simpa only [E, R, mul_comm] using
      (tendsto_integral_scaled_walk_energy ht0 hc f g hf hg).mul hres
  have hlim := tendsto_fixedHorizon_time_sum ha A B hA hB
    (fun N r => E N r * R N (B N - r))
    (fun t => Real.pi * ∫ p : Plane × Plane,
      f p.1 * g p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume))
    ((Cg * ∫ x : Plane, |f x|) * (Real.pi + 1))
    (mul_nonneg (mul_nonneg hCg hL1) (by positivity)) hbound hpoint
  rw [integral_const_mul] at hlim
  exact hlim

end Critical2DKPZ.Extensions.GffTangent
