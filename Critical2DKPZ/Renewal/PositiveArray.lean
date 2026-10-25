/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Convergent kernels against escaping positive arrays

A finite positive array whose total mass converges and whose individual columns vanish
tests a convergent scalar kernel at its limit. The arbitrary-filter formulation applies
directly to joint cutoff/parameter limits and therefore preserves local uniformity.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Critical2DKPZ.Renewal

/-- A weighted kernel-sum error is controlled by finitely many early errors and a uniform tail error. -/
theorem abs_sum_kernel_sub_le (s : Finset ℕ) (a e : ℕ → ℝ) (ha : ∀ r, 0 ≤ a r)
    (c δ : ℝ) (hδ : 0 ≤ δ) (M : ℕ) (he : ∀ r, M ≤ r → |e r - c| ≤ δ) :
    |(∑ r ∈ s, e r * a r) - c * ∑ r ∈ s, a r| ≤
      (∑ r ∈ Finset.range M, |e r - c| * a r) + δ * ∑ r ∈ s, a r := by
  have herr : (∑ r ∈ s, e r * a r) - c * ∑ r ∈ s, a r =
      ∑ r ∈ s, (e r - c) * a r := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    ring
  rw [herr]
  calc
    _ ≤ ∑ r ∈ s, |e r - c| * a r := by
      simpa only [abs_mul, abs_of_nonneg (ha _)] using
        (Finset.abs_sum_le_sum_abs (fun r => (e r - c) * a r) s)
    _ ≤ ∑ r ∈ s, ((if r ∈ Finset.range M then |e r - c| * a r else 0) + δ * a r) := by
      apply Finset.sum_le_sum
      intro r hr
      by_cases h : r ∈ Finset.range M
      · rw [ite_eq_left h]
        exact le_add_of_nonneg_right (mul_nonneg hδ (ha r))
      · rw [ite_eq_right h, zero_add]
        exact mul_le_mul_of_nonneg_right (he r (by simp only [Finset.mem_range] at h; omega)) (ha r)
    _ ≤ _ := by
      rw [Finset.sum_add_distrib, Finset.sum_ite_mem, ← Finset.mul_sum]
      have hsub : s ∩ Finset.range M ⊆ Finset.range M := Finset.inter_subset_right
      have hprefix :
          (∑ r ∈ s ∩ Finset.range M, |e r - c| * a r) ≤
            ∑ r ∈ Finset.range M, |e r - c| * a r :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun r _ _ => mul_nonneg (abs_nonneg (e r - c)) (ha r))
      linarith only [hprefix]

/-- A positive triangular array with vanishing columns tests any convergent scalar kernel. -/
theorem tendsto_sum_kernel_of_positive_array {ι : Type*} {L : Filter ι}
    {s : ι → Finset ℕ} {a : ι → ℕ → ℝ} {e : ℕ → ℝ} {A c : ℝ}
    (ha : ∀ᶠ i in L, ∀ r, 0 ≤ a i r)
    (hcol : ∀ r, Tendsto (fun i => a i r) L (nhds 0))
    (hmass : Tendsto (fun i => ∑ r ∈ s i, a i r) L (nhds A))
    (he : Tendsto e atTop (nhds c)) :
    Tendsto (fun i => ∑ r ∈ s i, e r * a i r) L (nhds (c * A)) := by
  have herror : Tendsto (fun i => (∑ r ∈ s i, e r * a i r) - c * ∑ r ∈ s i, a i r)
      L (nhds 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let K := |A| + 1
    have hK : 0 < K := add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
    have hAK : A < K := lt_add_of_le_of_pos (le_abs_self _) zero_lt_one
    let δ := ε / (2 * K)
    have hδ : 0 < δ := div_pos hε (mul_pos (by norm_num) hK)
    obtain ⟨M, hM⟩ := eventually_atTop.mp
      (he.eventually (Metric.ball_mem_nhds c hδ))
    have hbound : ∀ r, M ≤ r → |e r - c| ≤ δ := fun r hr => by
      have hb : dist (e r) c < δ := hM r hr
      simpa only [Real.dist_eq] using hb.le
    have hpref : Tendsto (fun i => ∑ r ∈ Finset.range M, |e r - c| * a i r) L (nhds 0) := by
      simpa only [mul_zero, Finset.sum_const_zero] using
        tendsto_finsetSum (Finset.range M) (fun r _ => (hcol r).const_mul |e r - c|)
    filter_upwards [ha, hmass.eventually (eventually_lt_nhds hAK),
      hpref.eventually (eventually_lt_nhds (half_pos hε))] with i hai hmi hpi
    rw [Real.dist_eq, sub_zero]
    have h := abs_sum_kernel_sub_le (s i) (a i) e hai c δ hδ.le M hbound
    have hδK : δ * K = ε / 2 := by dsimp only [δ]; field_simp
    have ht := mul_le_mul_of_nonneg_left hmi.le hδ.le
    linarith only [h, ht, hpi, hδK]
  have h := herror.add (hmass.const_mul c)
  rw [zero_add] at h
  apply h.congr
  intro i
  exact sub_add_cancel _ _

end Critical2DKPZ.Renewal

end
