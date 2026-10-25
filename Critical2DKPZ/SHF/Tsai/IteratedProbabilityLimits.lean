/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith

/-! # Joint and iterated probability limits

A joint probability limit controls all sufficiently large pairs of indices.
For each large outer index, choose a sufficiently large inner index from its
fiber limit. The triangle inequality then identifies the outer probability
limit, without exchanging any unbounded expectations.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- A joint probability limit and all fixed-outer-index inner limits identify the outer probability limit. -/
theorem tendstoInMeasure_of_joint_of_iterated {Ω E : Type*}
    [MeasurableSpace Ω] [PseudoMetricSpace E] (P : Measure Ω) [IsFiniteMeasure P]
    (X : ℕ × ℕ → Ω → E) (Y : ℕ → Ω → E) (F : Ω → E)
    (hJoint : TendstoInMeasure P X atTop F)
    (hInner : ∀ n, TendstoInMeasure P (fun ℓ => X (ℓ, n)) atTop (Y n)) :
    TendstoInMeasure P Y atTop F := by
  rw [tendstoInMeasure_iff_measureReal_dist]
  intro ε hε
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Eventually.of_forall (fun n => ha.trans_le measureReal_nonneg)
  · intro δ hδ
    have hJ := (tendstoInMeasure_iff_measureReal_dist.1 hJoint) (ε / 2) (by positivity)
    obtain ⟨q0, hq0⟩ := eventually_atTop.1
      (hJ.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by positivity)))
    apply eventually_atTop.2
    refine ⟨q0.2, fun n hn => ?_⟩
    have hI := (tendstoInMeasure_iff_measureReal_dist.1 (hInner n)) (ε / 2) (by positivity)
    obtain ⟨L, hL⟩ := eventually_atTop.1
      (hI.eventually (gt_mem_nhds (show (0 : ℝ) < δ / 2 by positivity)))
    let ℓ := max q0.1 L
    have hIbound := hL ℓ (le_max_right _ _)
    have hJbound := hq0 (ℓ, n) ⟨le_max_left _ _, hn⟩
    have hsub : {ω | ε ≤ dist (Y n ω) (F ω)} ⊆
        {ω | ε / 2 ≤ dist (X (ℓ, n) ω) (Y n ω)} ∪
          {ω | ε / 2 ≤ dist (X (ℓ, n) ω) (F ω)} := by
      intro ω hω
      by_contra hout
      have hfirst : dist (X (ℓ, n) ω) (Y n ω) < ε / 2 := by
        exact lt_of_not_ge (fun h => hout (Or.inl h))
      have hsecond : dist (X (ℓ, n) ω) (F ω) < ε / 2 := by
        exact lt_of_not_ge (fun h => hout (Or.inr h))
      have htri := dist_triangle (Y n ω) (X (ℓ, n) ω) (F ω)
      rw [dist_comm (Y n ω) (X (ℓ, n) ω)] at htri
      change ε ≤ dist (Y n ω) (F ω) at hω
      linarith
    calc
      _ ≤ P.real ({ω | ε / 2 ≤ dist (X (ℓ, n) ω) (Y n ω)} ∪
          {ω | ε / 2 ≤ dist (X (ℓ, n) ω) (F ω)}) := measureReal_mono hsub
      _ ≤ P.real {ω | ε / 2 ≤ dist (X (ℓ, n) ω) (Y n ω)} +
          P.real {ω | ε / 2 ≤ dist (X (ℓ, n) ω) (F ω)} := measureReal_union_le _ _
      _ < δ := by linarith

end Critical2DKPZ.SHF.Tsai

end
