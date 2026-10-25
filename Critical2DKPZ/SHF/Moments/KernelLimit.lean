/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.WalkScaling
public import Critical2DKPZ.SHF.Moments.TimeRounding
import Critical2DKPZ.SHF.DeltaBose.KernelBlocks
import Mathlib.Tactic

/-! # Moving-site and moving-time period-correct kernel limits -/

public section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- The moving walk local limit along any diverging sequence of lattice scales. -/
theorem tendsto_scaled_srwKernel_along (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) {n : ℕ → ℕ} {z : ℕ → Site} {t : ℝ} {x : Plane}
    (ht : 0 < t)
    (hn : Tendsto (fun N : ℕ => (n N : ℝ) / M N) atTop (𝓝 t))
    (hz : Tendsto (fun N : ℕ => latticeRepresentative (M N) (z N)) atTop (𝓝 x))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (z N 0 + z N 1 + n N)) :
    Tendsto (fun N : ℕ => ((M N : ℝ) / 4) * srwKernel (n N) (z N)) atTop (𝓝 (heatKernel t x)) := by
  obtain ⟨C, _, hC⟩ := srwKernel_scaled_localCLT_away_zero (half_pos ht)
  have herr : Tendsto (fun N : ℕ => ((M N : ℝ) / 4) * srwKernel (n N) (z N) -
      heatKernel ((n N : ℝ) / M N) (latticeRepresentative (M N) (z N))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ ((tendsto_const_div_nat C).comp hM)
    filter_upwards [hM.eventually (eventually_gt_atTop 0), hn.eventually (lt_mem_nhds (half_lt_self ht)),
      hphase] with N hN hgap hpar
    have hNr : (0 : ℝ) < M N := by exact_mod_cast hN
    have hgap' : (t / 2) * M N < (n N : ℝ) := (lt_div_iff₀ hNr).mp hgap
    have hnn : 0 < n N := by
      exact_mod_cast (mul_pos (half_pos ht) hNr).trans hgap'
    simpa only [Real.norm_eq_abs, Function.comp_apply] using hC (M N) (n N) hN hnn hgap'.le (z N) hpar
  have hc : ContinuousAt (fun p : ℝ × Plane => heatKernel p.1 p.2) (t, x) :=
    DeltaBose.continuousOn_heatKernel.continuousAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds ht)
  have hh := hc.tendsto.comp (hn.prodMk_nhds hz)
  have hh' : Tendsto (fun N : ℕ => heatKernel ((n N : ℝ) / M N)
      (latticeRepresentative (M N) (z N))) atTop (𝓝 (heatKernel t x)) := hh
  simpa only [sub_add_cancel, zero_add] using herr.add hh'

/-- The allowed-parity local CLT applies directly to moving microscopic checkpoints. -/

theorem tendsto_scaled_srwKernel {n : ℕ → ℕ} {z : ℕ → Site} {t : ℝ} {x : Plane}
    (ht : 0 < t)
    (hn : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 t))
    (hz : Tendsto (fun N : ℕ => latticeRepresentative N (z N)) atTop (𝓝 x))
    (hphase : ∀ᶠ N : ℕ in atTop, Even (z N 0 + z N 1 + n N)) :
    Tendsto (fun N : ℕ => ((N : ℝ) / 4) * srwKernel (n N) (z N)) atTop (𝓝 (heatKernel t x)) := by
  exact tendsto_scaled_srwKernel_along id tendsto_id ht hn hz hphase

end Critical2DKPZ.SHF.Moments
