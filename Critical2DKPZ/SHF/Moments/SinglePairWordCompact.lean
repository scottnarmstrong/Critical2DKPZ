/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-! # A compact moving-sequence criterion for two-particle approximations -/

@[expose] public section
noncomputable section
namespace Critical2DKPZ.SHF.Moments
open Filter
open scoped Topology

private theorem tendsto_extend_strictMono {X : Type*} [MetricSpace X]
    {m : ℕ → ℕ} (hm : StrictMono m) {v : ℕ → X} {a : X}
    (hv : Tendsto v atTop (𝓝 a)) :
    Tendsto (Function.extend m v (fun _ => a)) atTop (𝓝 a) := by
  classical
  rw [Metric.tendsto_atTop] at hv ⊢
  intro ε hε
  obtain ⟨j₀, hj₀⟩ := hv ε hε
  refine ⟨m j₀, ?_⟩
  intro N hN
  by_cases h : ∃ j, m j = N
  · obtain ⟨j, rfl⟩ := h
    rw [hm.injective.extend_apply]
    exact hj₀ j (hm.le_iff_le.mp hN)
  · rw [Function.extend_apply' _ _ _ h, dist_self]
    exact hε

/-- On a compact metric set, convergence for every converging full-scale
choice of tests implies uniform convergence. This avoids imposing any
continuity on the microscopic approximations. -/
theorem tendstoUniformlyOn_of_moving_tests {X : Type*} [MetricSpace X]
    {K : Set X} (hK : IsCompact K) {f : ℕ → X → ℝ} {g : X → ℝ}
    (hg : ContinuousOn g K)
    (h : ∀ a ∈ K, ∀ v : ℕ → X, (∀ N, v N ∈ K) →
      Tendsto v atTop (𝓝 a) → Tendsto (fun N => f N (v N)) atTop (𝓝 (g a))) :
    TendstoUniformlyOn f g atTop K := by
  classical
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  by_contra he
  have hbad : ∃ᶠ N : ℕ in atTop, ∃ x ∈ K, ε ≤ dist (g x) (f N x) := by
    simpa only [Filter.not_eventually, not_forall, not_lt, exists_prop] using he
  obtain ⟨n, hn, hnbad⟩ := extraction_of_frequently_atTop hbad
  choose v hvK hvbad using hnbad
  obtain ⟨a, haK, k, hk, hv⟩ := hK.tendsto_subseq hvK
  let m : ℕ → ℕ := n ∘ k
  have hm : StrictMono m := hn.comp hk
  let w : ℕ → X := Function.extend m (v ∘ k) (fun _ => a)
  have hw : Tendsto w atTop (𝓝 a) := tendsto_extend_strictMono hm hv
  have hwK (N : ℕ) : w N ∈ K := by
    by_cases he : ∃ j, m j = N
    · obtain ⟨j, rfl⟩ := he
      rw [show w (m j) = v (k j) from hm.injective.extend_apply _ _ j]
      exact hvK (k j)
    · rw [show w N = a from Function.extend_apply' _ _ _ he]
      exact haK
  have hf := h a haK w hwK hw
  have hgw : Tendsto (fun N => g (w N)) atTop (𝓝 (g a)) :=
    (hg a haK).tendsto.comp (tendsto_nhdsWithin_iff.mpr
      ⟨hw, Eventually.of_forall hwK⟩)
  have hd : Tendsto (fun N => dist (g (w N)) (f N (w N))) atTop (𝓝 0) := by
    simpa only [dist_self] using hgw.dist hf
  have he := (hd.comp hm.tendsto_atTop).eventually (Iio_mem_nhds hε)
  obtain ⟨j, hj⟩ := he.exists
  have hwj : w (m j) = v (k j) := hm.injective.extend_apply _ _ j
  dsimp only [Function.comp_apply] at hj
  rw [hwj] at hj
  exact (not_lt_of_ge (hvbad (k j))) hj

end Critical2DKPZ.SHF.Moments
