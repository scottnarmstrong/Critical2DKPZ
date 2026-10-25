/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.AddContent
public import Mathlib.Topology.Compactness.CompactSystem
import Mathlib.Analysis.SpecificLimits.Basic

/-! Compact inner approximation of a finite content gives continuity at the empty set and countable subadditivity. -/

@[expose] public noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal Topology

namespace Critical2DKPZ.RandomMeasure.Kolmogorov

/-- Inner approximation by a compact system makes a content continuous at the empty set. -/
theorem tendsto_content_zero_of_compactSystem {Y : Type*} {C K : Set (Set Y)}
    (hC : IsSetRing C) (hK : IsCompactSystem K) (hKC : K ⊆ C)
    (m : AddContent ℝ≥0∞ C)
    (hinner : ∀ s ∈ C, ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ k ∈ K, k ⊆ s ∧ m (s \ k) ≤ ε)
    {s : ℕ → Set Y} (hs : ∀ n, s n ∈ C) (hanti : Antitone s) (hempty : ⋂ n, s n = ∅) :
    Tendsto (fun n => m (s n)) atTop (𝓝 0) := by
  classical
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨δ, hδ, hsum⟩ := ENNReal.exists_pos_sum_of_countable' hε.ne' ℕ
  choose k hk hks herr using fun i => hinner (s i) (hs i) (δ i) (hδ i)
  have hkempty : ⋂ i, k i = ∅ := by
    apply subset_empty_iff.mp
    intro x hx
    have hxs : x ∈ ⋂ i, s i := mem_iInter.mpr fun i => hks i (mem_iInter.mp hx i)
    simp only [hempty, mem_empty_iff_false] at hxs
  obtain ⟨n, hn⟩ := hK k hk hkempty
  let d : ℕ → Set Y := fun i => s i \ k i
  have hd (i : ℕ) : d i ∈ C := hC.sdiff_mem (hs i) (hKC (hk i))
  have hcover : s n ⊆ ⋃ i ∈ Finset.range (n + 1), d i := by
    intro x hx
    by_contra hnot
    have hxk : x ∈ dissipate k n := by
      simp only [dissipate, mem_iInter]
      intro i hi
      by_contra hki
      exact hnot (mem_iUnion_of_mem i (mem_iUnion_of_mem (Finset.mem_range.mpr (by omega))
        ⟨hanti hi hx, hki⟩))
    simp only [hn, mem_empty_iff_false] at hxk
  have hbound : m (s n) ≤ ε := by
    calc
      _ ≤ m (⋃ i ∈ Finset.range (n + 1), d i) :=
        addContent_mono hC.isSetSemiring (hs n)
          (hC.biUnion_mem _ (fun i _ => hd i)) hcover
      _ ≤ ∑ i ∈ Finset.range (n + 1), m (d i) :=
        addContent_biUnion_le hC (fun i _ => hd i)
      _ ≤ ∑ i ∈ Finset.range (n + 1), δ i := Finset.sum_le_sum fun i _ => herr i
      _ ≤ ∑' i, δ i := ENNReal.sum_le_tsum _
      _ ≤ ε := hsum.le
  filter_upwards [eventually_ge_atTop n] with j hj
  exact (addContent_mono hC.isSetSemiring (hs j) (hs n) (hanti hj)).trans hbound

/-- A finite content with compact inner approximation is countably subadditive. -/
theorem isSigmaSubadditive_of_compactSystem {Y : Type*} {C K : Set (Set Y)}
    (hC : IsSetRing C) (hK : IsCompactSystem K) (hKC : K ⊆ C)
    (m : AddContent ℝ≥0∞ C) (hfinite : ∀ s ∈ C, m s ≠ ⊤)
    (hinner : ∀ s ∈ C, ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ k ∈ K, k ⊆ s ∧ m (s \ k) ≤ ε) :
    m.IsSigmaSubadditive := by
  apply isSigmaSubadditive_of_addContent_iUnion_eq_tsum hC
  intro f hf hUf hdisj
  exact addContent_iUnion_eq_sum_of_tendsto_zero hC m hfinite
    (fun {s} hs hanti hempty => tendsto_content_zero_of_compactSystem hC hK hKC m hinner hs hanti hempty)
    hf hUf hdisj

end Critical2DKPZ.RandomMeasure.Kolmogorov

end
