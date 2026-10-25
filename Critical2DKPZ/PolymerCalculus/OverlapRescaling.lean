/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.PolymerCalculus.OverlapConstant
public import Critical2DKPZ.Renewal.CriticalWindow
import Mathlib.Tactic

/-! # Uniform overlap increments and macroscopic clock rescaling -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.PolymerCalculus

/-- The logarithmic overlap-increment error tends to zero uniformly over horizons bounded below by a fixed positive multiple of `N`. -/
theorem replicaOverlap_increment_uniform_lower {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ M : ℕ, d * N ≤ M →
      |replicaOverlap M - replicaOverlap N -
        (1 / Real.pi) * (Real.log M - Real.log N)| < ε := by
  obtain ⟨K, hK⟩ := replicaOverlap_increment_uniform hε
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop ⌈(K : ℝ) / d⌉₊] with N hN hNd
  intro M hM
  apply hK M N _ hN
  have hdiv : (K : ℝ) / d ≤ N := (Nat.le_ceil _).trans (Nat.cast_le.mpr hNd)
  have hKN : (K : ℝ) ≤ d * N := by
    have h := (div_le_iff₀ hd).mp hdiv
    simpa only [mul_comm] using h
  exact_mod_cast hKN.trans hM

/-- A positive limiting clock ratio gives a uniform eventual lower horizon bound. -/
theorem eventually_clock_ratio_lower {M : ℕ → ℕ} {D : ℝ} (hD : 0 < D)
    (hM : Tendsto (fun N : ℕ => (M N : ℝ) / N) atTop (𝓝 D)) :
    ∀ᶠ N : ℕ in atTop, (D / 2) * N ≤ M N := by
  filter_upwards [hM.eventually (lt_mem_nhds (show D / 2 < D by linarith)),
    eventually_ge_atTop 1] with N hr hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h := (lt_div_iff₀ hn).mp hr
  exact h.le

/-- If `M_N/N → D > 0`, then `log M_N - log N → log D`. -/
theorem tendsto_log_clock_ratio {M : ℕ → ℕ} {D : ℝ} (hD : 0 < D)
    (hM : Tendsto (fun N : ℕ => (M N : ℝ) / N) atTop (𝓝 D)) :
    Tendsto (fun N : ℕ => Real.log (M N) - Real.log N) atTop (𝓝 (Real.log D)) := by
  apply (hM.log hD.ne').congr'
  filter_upwards [eventually_clock_ratio_lower hD hM, eventually_ge_atTop 1] with N hN hN1
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm : (0 : ℝ) < M N := lt_of_lt_of_le (mul_pos (by positivity) hn) hN
  exact Real.log_div hm.ne' hn.ne'


end Critical2DKPZ.PolymerCalculus
