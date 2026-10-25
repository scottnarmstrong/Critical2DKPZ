/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonCellPairing
public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonCollisionLimit
import Mathlib.Tactic

/-! # Quasi-critical variance limits for actual finite-start windows -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped Topology BigOperators

namespace Critical2DKPZ.Extensions.GffTangent

/-- The CCR variance limit for a compact test averaged over the library's even
lattice cells. The normalization is sqrt(l) times the exact cell integral. -/
theorem tendsto_integral_sq_quasiCritical_cell_window
    (l β : ℕ → ℝ) (hl : Tendsto l atTop atTop)
    (hratio : Tendsto (fun N => l N / Real.log (N : ℝ)) atTop (𝓝 0))
    (hβ : ∀ᶠ N : ℕ in atTop, 0 < β N)
    (hσ : ∀ᶠ N : ℕ in atTop, Polymer.sigmaSq (β N) = criticalSigmaSq (-l N) N)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (A B : ℕ → ℕ)
    (hA : Tendsto (fun N : ℕ => (A N : ℝ) / N) atTop (𝓝 a))
    (hB : Tendsto (fun N : ℕ => (B N : ℝ) / N) atTop (𝓝 b))
    (f : Plane → ℝ) (hf : Continuous f) (hfs : HasCompactSupport f)
    (S : ℕ → Finset Site) (hS : ∀ N x, f x ≠ 0 → latticePoint N x ∈ S N) :
    Tendsto (fun N : ℕ => ∫ ω,
      latticeWindowFluctuation (β N) (Real.sqrt (l N)) (A N) (B N) (S N)
        (fun w => ∫ x in cell N w, f x) ω ^ 2 ∂disorderLaw)
      atTop (𝓝 (4 * Real.pi * ∫ t in Ioo a b, ∫ p : Plane × Plane,
        f p.1 * f p.2 * heatKernel (2 * t) (p.2 - p.1) ∂(volume.prod volume))) := by
  obtain ⟨C, hC⟩ := hfs.exists_bound_of_continuous hf
  have hfint := hf.integrable_of_hasCompactSupport hfs (μ := volume)
  have hpointbound (x : Plane) : |f x| ≤ C := by simpa only [Real.norm_eq_abs] using hC x
  have hlim := (tendsto_quasiCritical_averaged_first_collision l β hl hratio hβ hσ
    ha hab A B hA hB f f hfint hfint hf.measurable C hpointbound).const_mul 4
  rw [← mul_assoc 4 Real.pi] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop 0, hl.eventually (eventually_gt_atTop 0),
    hA.eventually_lt hB hab] with N hN hlN hAB
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hAB' : A N ≤ B N := (show A N < B N by
    exact_mod_cast (div_lt_div_iff_of_pos_right hNr).mp hAB).le
  rw [integral_sq_cell_window_eq_collision_sum (β N) (Real.sqrt (l N)) hAB' N hN
    f hf hfs (S N) (hS N), Real.sq_sqrt hlN.le]
  simp only [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

end Critical2DKPZ.Extensions.GffTangent
