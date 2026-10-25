/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Moments.CriticalWindowClockTail
import Mathlib.Tactic

/-! # Long-composition tails for critical pair blocks -/

@[expose] public section

noncomputable section

open Filter Critical2DKPZ.Renewal
open scoped Topology

namespace Critical2DKPZ.SHF.Moments

/-- Long convolution orders carry negligible normalized mass uniformly in a compact critical
window. The cutoff `(ceil log N)^2` is chosen so the clock-tail estimate beats both the number of
orders up to `n` and the pair-block normalization `N / log N`. -/
theorem exists_eventually_scaled_criticalWindow_longComposition_tail_le
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ ϑ : ℝ, ϑ ∈ Set.Icc (-A) A → ∀ n : ℕ, n ≤ ⌊B * N⌋₊ →
        (N / Real.log N) *
            ∑ k ∈ Finset.Icc (⌈Real.log (N : ℝ)⌉₊ ^ 2) n,
              convolutionPower
                (fun r => if r ≤ N then criticalSigmaSq ϑ N * returnWeight r else 0)
                k n ≤
          (N / Real.log N) * ((n : ℝ) + 1) * C * Real.exp (-4 * Real.log N) := by
  obtain ⟨Ctail, hCtail, Ntail, htail⟩ :=
    exists_criticalWindow_convolutionPower_clock_tail_le A B 4 hA hB (by norm_num)
  have hlogEventually : ∀ᶠ N : ℕ in atTop, max A 1 < Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop (max A 1)
  obtain ⟨Nlog, hlogAtTop⟩ := eventually_atTop.1 hlogEventually
  let C : ℝ := Ctail
  have hC : 0 < C := hCtail
  refine ⟨C, hC, max Ntail Nlog, ?_⟩
  intro N hN ϑ hϑ n hn
  have hNtail : Ntail ≤ N := (le_max_left Ntail Nlog).trans hN
  have hNlog : Nlog ≤ N := (le_max_right Ntail Nlog).trans hN
  have hlogA : max A 1 < Real.log (N : ℝ) := hlogAtTop N hNlog
  have hlogOne : 1 < Real.log (N : ℝ) := lt_of_le_of_lt (le_max_right A 1) hlogA
  have hlog : 0 < Real.log (N : ℝ) := by linarith
  have hNtwo : 2 ≤ N := by
    have hlogN : 0 < Real.log (N : ℝ) := hlog
    have h1N : (1 : ℝ) < N := by
      by_contra h
      have h' : (N : ℝ) ≤ 1 := not_lt.mp h
      have hlog' : Real.log (N : ℝ) ≤ 0 := Real.log_nonpos (by positivity) (by exact_mod_cast h')
      linarith
    exact_mod_cast h1N
  have hR : 0 < replicaOverlap N := replicaOverlap_pos (by omega)
  have hϑlo : -A ≤ ϑ := (Set.mem_Icc.mp hϑ).1
  have hAlog : A < Real.log (N : ℝ) := (le_max_left A 1).trans_lt hlogA
  have hfactor : 0 ≤ 1 + ϑ / Real.log N := by
    have hquot : -1 ≤ ϑ / Real.log N := by
      rw [le_div_iff₀ hlog]
      linarith
    linarith
  have hσ : 0 ≤ criticalSigmaSq ϑ N := by
    have hmul := criticalSigmaSq_mul_overlap ϑ (by omega : 1 ≤ N)
    have heq : criticalSigmaSq ϑ N =
        (1 + ϑ / Real.log N) / replicaOverlap N := by
      calc
        _ = (criticalSigmaSq ϑ N * replicaOverlap N) / replicaOverlap N := by
          field_simp [hR.ne']
        _ = _ := by rw [hmul]
    rw [heq]
    exact div_nonneg hfactor hR.le
  let w : ℕ → ℝ := fun r =>
    if r ≤ N then criticalSigmaSq ϑ N * returnWeight r else 0
  have hw : ∀ r, 0 ≤ w r := by
    intro r
    dsimp [w]
    split_ifs
    · exact mul_nonneg hσ (srwKernel_nonneg _ _)
    · exact le_rfl
  have htailPoint (k : ℕ) :
      convolutionPower w k n ≤ C * Real.exp (-4 * (k : ℝ) / Real.log N) := by
    have hsum := htail N hNtail ϑ hϑ k
    have hnmem : n ∈ Finset.range (⌊B * N⌋₊ + 1) := by
      simp only [Finset.mem_range]
      omega
    have hsingle : convolutionPower w k n ≤
        ∑ j ∈ Finset.range (⌊B * N⌋₊ + 1), convolutionPower w k j :=
      Finset.single_le_sum (fun j hj => convolutionPower_nonneg hw k j) hnmem
    calc
      _ ≤ ∑ j ∈ Finset.range (⌊B * N⌋₊ + 1), convolutionPower w k j := hsingle
      _ ≤ C * Real.exp (-4 * (k : ℝ) / Real.log N) := by
        simpa [C, w] using hsum
  let K : ℕ := ⌈Real.log (N : ℝ)⌉₊ ^ 2
  have hceil : Real.log (N : ℝ) ≤ (⌈Real.log (N : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
  have hKlower : (Real.log (N : ℝ)) ^ 2 ≤ (K : ℝ) := by
    dsimp [K]
    have hlogNonneg : 0 ≤ Real.log (N : ℝ) := hlog.le
    have hceilDiff : 0 ≤ (⌈Real.log (N : ℝ)⌉₊ : ℝ) - Real.log (N : ℝ) :=
      sub_nonneg.mpr hceil
    have hceilSum : 0 ≤ (⌈Real.log (N : ℝ)⌉₊ : ℝ) + Real.log (N : ℝ) := by
      positivity
    rw [Nat.cast_pow]
    nlinarith [mul_nonneg hceilDiff hceilSum]
  have hKexp (k : ℕ) (hk : K ≤ k) :
      Real.exp (-4 * (k : ℝ) / Real.log N) ≤ Real.exp (-4 * Real.log N) := by
    apply Real.exp_le_exp.mpr
    have hkcast : (K : ℝ) ≤ k := by exact_mod_cast hk
    have hklog : (Real.log (N : ℝ)) ^ 2 ≤ (k : ℝ) := le_trans hKlower hkcast
    have hdiv : Real.log (N : ℝ) ≤ (k : ℝ) / Real.log N :=
      (le_div_iff₀ hlog).2 (by nlinarith)
    have hmul : -4 * ((k : ℝ) / Real.log N) ≤ -4 * Real.log N := by nlinarith
    calc
      -4 * (k : ℝ) / Real.log N = -4 * ((k : ℝ) / Real.log N) := by ring
      _ ≤ -4 * Real.log N := hmul
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc K n) :
      convolutionPower w k n ≤ C * Real.exp (-4 * Real.log N) := by
    have hklo : K ≤ k := (Finset.mem_Icc.mp hk).1
    calc
      _ ≤ C * Real.exp (-4 * (k : ℝ) / Real.log N) := htailPoint k
      _ ≤ C * Real.exp (-4 * Real.log N) :=
        mul_le_mul_of_nonneg_left (hKexp k hklo) hC.le
  have hD : 0 ≤ C * Real.exp (-4 * Real.log N) := by positivity
  have hsub : Finset.Icc K n ⊆ Finset.range (n + 1) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  have hsum :
      (∑ k ∈ Finset.Icc K n, convolutionPower w k n) ≤
        ((n : ℝ) + 1) * (C * Real.exp (-4 * Real.log N)) := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc K n, C * Real.exp (-4 * Real.log N) := by
        apply Finset.sum_le_sum
        intro k hk
        exact hterm k hk
      _ ≤ ∑ k ∈ Finset.range (n + 1), C * Real.exp (-4 * Real.log N) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => hD)
      _ = ((n : ℝ) + 1) * (C * Real.exp (-4 * Real.log N)) := by simp
  have hscale : 0 ≤ (N : ℝ) / Real.log N := div_nonneg (Nat.cast_nonneg _) hlog.le
  calc
    _ = (N / Real.log N) * ∑ k ∈ Finset.Icc K n, convolutionPower w k n := by
      rfl
    _ ≤ (N / Real.log N) * (((n : ℝ) + 1) *
          (C * Real.exp (-4 * Real.log N))) := by
      exact mul_le_mul_of_nonneg_left hsum hscale
    _ = (N / Real.log N) * ((n : ℝ) + 1) *
          (C * Real.exp (-4 * Real.log N)) := by ring
    _ = (N / Real.log N) * ((n : ℝ) + 1) * C *
          Real.exp (-4 * Real.log N) := by ring

end Critical2DKPZ.SHF.Moments

end
