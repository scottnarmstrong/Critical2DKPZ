/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonSlowDiagonal
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # Transfer from full-scale joint limits to iterated limits -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- Fixed-parameter convergence and all full-scale slowly varying joint
limits imply the iterated limit. The proof retains the original lattice scale
N throughout; it does not apply a full-scale limit to an arbitrary subsequence. -/
theorem tendsto_of_slow_quasiCritical_limits (l B : ℕ → ℝ) (A : ℕ → ℕ → ℝ)
    (hA : ∀ k, Tendsto (A k) atTop (𝓝 (B k))) (b : ℝ)
    (hjoint : ∀ q : ℕ → ℕ, Tendsto q atTop atTop →
      Tendsto (fun N => l (q N) / Real.log (N : ℝ)) atTop (𝓝 0) →
      Tendsto (fun N => A (q N) N) atTop (𝓝 b)) :
    Tendsto B atTop (𝓝 b) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  by_contra hn
  push Not at hn
  choose u hu using hn
  have hutop : Tendsto u atTop atTop :=
    tendsto_atTop_mono (fun k => (hu k).1) tendsto_id
  let d : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hP : ∀ j, ∀ᶠ N : ℕ in atTop,
      |A (u j) N - B (u j)| ≤ d j ∧ |l (u j) / Real.log (N : ℝ)| ≤ d j := by
    intro j
    have herror := ((hA (u j)).sub_const (B (u j))).abs
    simp only [sub_self, abs_zero] at herror
    have hratio := ((tendsto_const_nhds (x := l (u j))).div_atTop hlog).abs
    simp only [abs_zero] at hratio
    have hd : 0 < d j := by dsimp [d]; positivity
    filter_upwards [herror.eventually (gt_mem_nhds hd), hratio.eventually (gt_mem_nhds hd)] with N he hr
    exact ⟨he.le, hr.le⟩
  obtain ⟨k, hk, _, hdiag⟩ := exists_slow_diagonal _ hP
  have hdz : Tendsto (fun N => d (k N)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  have herror : Tendsto (fun N => A (u (k N)) N - B (u (k N))) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      (hdiag.mono (fun N hN => hN.1)) hdz
  have hratio : Tendsto (fun N => l (u (k N)) / Real.log (N : ℝ)) atTop (𝓝 0) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).mpr
    exact squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _))
      (hdiag.mono (fun N hN => hN.2)) hdz
  have hlim := (hjoint (fun N => u (k N)) (hutop.comp hk) hratio).sub herror
  simp only [sub_zero, sub_sub_cancel] at hlim
  have hdist := hlim.dist (tendsto_const_nhds (x := b))
  simp only [dist_self] at hdist
  obtain ⟨N, hN⟩ := (hdist.eventually (gt_mem_nhds hε)).exists
  exact (not_lt_of_ge (hu (k N)).2) hN

end Critical2DKPZ.Extensions.GffTangent
