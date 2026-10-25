/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.Extensions.GffTangent.FixedHorizonSlowDiagonal
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! # A common slow partition for the three triangular-array estimates -/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.Extensions.GffTangent

/-- Diagonalize the L2 approximation, total variance and total fourth moment
without passing to a subsequence of the original lattice scale. -/
theorem exists_slow_array_partition (R V F : ℕ → ℕ → ℝ) (v C : ℝ)
    (hR0 : ∀ M N, 0 ≤ R M N) (hF0 : ∀ M N, 0 ≤ F M N)
    (hR : ∀ M > 0, Tendsto (R M) atTop (𝓝 0))
    (hV : ∀ M > 0, Tendsto (V M) atTop (𝓝 v))
    (hF : ∀ M > 0, ∀ ε > 0, ∀ᶠ N : ℕ in atTop, F M N ≤ C / M + ε) :
    ∃ M : ℕ → ℕ, (∀ N, 0 < M N) ∧ Tendsto M atTop atTop ∧
      Tendsto (fun N => R (M N) N) atTop (𝓝 0) ∧
      Tendsto (fun N => V (M N) N) atTop (𝓝 v) ∧
      Tendsto (fun N => F (M N) N) atTop (𝓝 0) := by
  let d : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
  have hd (k : ℕ) : 0 < d k := by dsimp [d]; positivity
  let P : ℕ → ℕ → Prop := fun k N =>
    R (k + 1) N ≤ d k ∧ |V (k + 1) N - v| ≤ d k ∧
      F (k + 1) N ≤ C / (k + 1) + d k
  have hP : ∀ k, ∀ᶠ N : ℕ in atTop, P k N := by
    intro k
    have hr := (hR (k + 1) (by omega)).eventually (gt_mem_nhds (hd k))
    have hv := ((hV (k + 1) (by omega)).sub_const v).abs
    simp only [sub_self, abs_zero] at hv
    filter_upwards [hr, hv.eventually (gt_mem_nhds (hd k)),
      hF (k + 1) (by omega) (d k) (hd k)] with N hrN hvN hfN
    exact ⟨hrN.le, hvN.le, by simpa only [Nat.cast_add, Nat.cast_one] using hfN⟩
  obtain ⟨k, hk, _, hdiag⟩ := exists_slow_diagonal P hP
  have hdz : Tendsto (fun N => d (k N)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hk
  have hcz : Tendsto (fun N => C / ((k N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [d, mul_zero, mul_one_div] using hdz.const_mul C
  refine ⟨fun N => k N + 1, fun _ => Nat.succ_pos _, ?_, ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun N => Nat.le_succ (k N)) hk
  · apply squeeze_zero' (Eventually.of_forall (fun N => hR0 _ _)) ?_ hdz
    exact hdiag.mono (fun N hN => hN.1)
  · apply (tendsto_iff_norm_sub_tendsto_zero).2
    apply squeeze_zero' (Eventually.of_forall (fun N => norm_nonneg _)) ?_ hdz
    simpa only [Real.norm_eq_abs] using hdiag.mono (fun N hN => hN.2.1)
  · have hlim := hcz.add hdz
    simp only [add_zero] at hlim
    apply squeeze_zero' (Eventually.of_forall (fun N => hF0 _ _)) ?_ hlim
    simpa only [Nat.cast_add, Nat.cast_one] using hdiag.mono (fun N hN => hN.2.2)

end Critical2DKPZ.Extensions.GffTangent
