/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.ClockTail
import Mathlib.Tactic

/-! # Uniform clock tails across a compact critical window -/

@[expose] public section

noncomputable section

open Filter Critical2DKPZ.Renewal
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- The critical renewal clock has uniformly small tails over compact critical-window parameter ranges. -/
theorem exists_criticalWindow_convolutionPower_clock_tail_le
    (A B M : ℝ) (hA : 0 ≤ A) (hB : 0 < B) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ ϑ ∈ Set.Icc (-A) A, ∀ k : ℕ,
        ∑ n ∈ Finset.range (⌊B * N⌋₊ + 1),
          convolutionPower
            (fun r => if r ≤ N then criticalSigmaSq ϑ N * returnWeight r else 0) k n ≤
          C * Real.exp (-M * k / Real.log N) := by
  let M₀ : ℝ := M + A
  have hM₀ : 0 < M₀ := by dsimp [M₀]; linarith
  obtain ⟨C₀, Ntail, htail⟩ := criticalClock_tail_le B M₀ hB hM₀
  let C : ℝ := max C₀ 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hlogEventually : ∀ᶠ N : ℕ in atTop, A < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop A
  obtain ⟨Nlog, hlogAtTop⟩ := eventually_atTop.1 hlogEventually
  refine ⟨C, hC, max Nlog (max Ntail 2), ?_⟩
  intro N hN ϑ hϑ k
  have hNlog : Nlog ≤ N := (le_max_left _ _).trans hN
  have hNtail : Ntail ≤ N :=
    (le_trans (le_max_left Ntail 2) (le_max_right Nlog (max Ntail 2))).trans hN
  have hNtwo : 2 ≤ N :=
    (le_trans (le_max_right Ntail 2) (le_max_right Nlog (max Ntail 2))).trans hN
  have hlogA : A < Real.log (N : ℝ) := hlogAtTop N hNlog
  have hlog : 0 < Real.log (N : ℝ) := lt_of_le_of_lt hA hlogA
  have hR : 0 < replicaOverlap N := replicaOverlap_pos (by omega)
  let factor : ℝ := 1 + ϑ / Real.log N
  let w₀ : ℕ → ℝ := fun r =>
    if r ≤ N then returnWeight r / replicaOverlap N else 0
  let wϑ : ℕ → ℝ := fun r =>
    if r ≤ N then criticalSigmaSq ϑ N * returnWeight r else 0
  have hϑlo : -A ≤ ϑ := (Set.mem_Icc.mp hϑ).1
  have hϑhi : ϑ ≤ A := (Set.mem_Icc.mp hϑ).2
  have hfactorNonneg : 0 ≤ factor := by
    dsimp [factor]
    have hquot : -1 ≤ ϑ / Real.log N := by
      rw [le_div_iff₀ hlog]
      linarith
    linarith
  have hfactorLe : factor ≤ Real.exp (A / Real.log N) := by
    have hquot : ϑ / Real.log N ≤ A / Real.log N :=
      div_le_div_of_nonneg_right hϑhi hlog.le
    have hexp : 1 + A / Real.log N ≤ Real.exp (A / Real.log N) := by
      have h := Real.add_one_le_exp (A / Real.log N)
      linarith
    dsimp [factor]
    linarith
  have hstep (r : ℕ) : wϑ r = factor * w₀ r := by
    by_cases hr : r ≤ N
    · simp [wϑ, w₀, factor, hr]
      have hσ := criticalSigmaSq_mul_overlap ϑ (by omega : 1 ≤ N)
      calc
        criticalSigmaSq ϑ N * returnWeight r =
            ((criticalSigmaSq ϑ N * replicaOverlap N) * returnWeight r) /
              replicaOverlap N := by field_simp [hR.ne']
        _ = (1 + ϑ / Real.log N) * (returnWeight r / replicaOverlap N) := by
          rw [hσ]
          ring
    · simp [wϑ, w₀, hr]
  have hw₀ : ∀ r, 0 ≤ w₀ r := by
    intro r
    dsimp [w₀]
    split_ifs with hr
    · exact div_nonneg (srwKernel_nonneg (2 * r) 0) hR.le
    · exact le_rfl
  have hconv (n : ℕ) :
      convolutionPower wϑ k n = factor ^ k * convolutionPower w₀ k n := by
    calc
      convolutionPower wϑ k n =
          convolutionPower (fun r => factor * w₀ r) k n :=
        convolutionPower_congr k n (fun r _ _ => hstep r)
      _ = factor ^ k * convolutionPower w₀ k n := convolutionPower_smul w₀ factor k n
  have hsum :
      (∑ n ∈ Finset.range (⌊B * N⌋₊ + 1), convolutionPower wϑ k n) =
        factor ^ k *
          ∑ n ∈ Finset.range (⌊B * N⌋₊ + 1), convolutionPower w₀ k n := by
    calc
      _ = ∑ n ∈ Finset.range (⌊B * N⌋₊ + 1),
          factor ^ k * convolutionPower w₀ k n := by
            apply Finset.sum_congr rfl
            intro n hn
            exact hconv n
      _ = _ := by rw [Finset.mul_sum]
  have hbase :
      (∑ n ∈ Finset.range (⌊B * N⌋₊ + 1), convolutionPower w₀ k n) ≤
        C * Real.exp (-M₀ * k / Real.log N) := by
    calc
      _ ≤ C₀ * Real.exp (-M₀ * k / Real.log N) := by
        simpa only [w₀] using htail N hNtail k
      _ ≤ C * Real.exp (-M₀ * k / Real.log N) :=
        mul_le_mul_of_nonneg_right (le_max_left C₀ 1) (Real.exp_pos _).le
  have hbaseNonneg :
      0 ≤ ∑ n ∈ Finset.range (⌊B * N⌋₊ + 1), convolutionPower w₀ k n :=
    Finset.sum_nonneg fun n hn => convolutionPower_nonneg hw₀ k n
  have hfactorPow : factor ^ k ≤ Real.exp (A * k / Real.log N) := by
    have h := pow_le_pow_left₀ hfactorNonneg hfactorLe k
    rw [← Real.exp_nat_mul] at h
    have harg : (k : ℝ) * (A / Real.log N) = A * k / Real.log N := by ring
    simpa only [harg] using h
  calc
    _ = factor ^ k *
        ∑ n ∈ Finset.range (⌊B * N⌋₊ + 1), convolutionPower w₀ k n := hsum
    _ ≤ Real.exp (A * k / Real.log N) *
        (C * Real.exp (-M₀ * k / Real.log N)) :=
      mul_le_mul hfactorPow hbase hbaseNonneg (by positivity)
    _ = C * Real.exp (-M * k / Real.log N) := by
      have harg : A * k / Real.log N + -(M₀ * k / Real.log N) =
          -M * k / Real.log N := by dsimp [M₀]; ring
      calc
        _ = C * (Real.exp (A * k / Real.log N) *
            Real.exp (-(M₀ * k / Real.log N))) := by ring_nf
        _ = C * Real.exp (-M * k / Real.log N) := by
          rw [← Real.exp_add, harg]

end Critical2DKPZ.SHF.Moments

end
