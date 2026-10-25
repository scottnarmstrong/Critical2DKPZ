/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Sequences
import Mathlib.Tactic

/-! # Oscillation control from a countable dense family of decompositions -/

@[expose] public section
noncomputable section
open MeasureTheory Filter TopologicalSpace
namespace Critical2DKPZ.Extensions.ScaleLimit

/-- A closed scalar bound holding on the selected countable dense sequence
holds everywhere for a continuous function. -/
theorem abs_sub_le_of_denseSeq {T : Type*} [TopologicalSpace T]
    [SeparableSpace T] [Nonempty T] (f : T → ℝ) (hf : Continuous f)
    (c C : ℝ) (h : ∀ n, |f (denseSeq T n) - c| ≤ C) :
    ∀ t, |f t - c| ≤ C := by
  have hc : IsClosed {t : T | |f t - c| ≤ C} :=
    isClosed_le (hf.sub continuous_const).abs continuous_const
  have hs : Set.range (denseSeq T) ⊆ {t : T | |f t - c| ≤ C} := by
    rintro t ⟨n, rfl⟩
    exact h n
  intro t
  apply closure_minimal hs hc
  rw [(denseRange_denseSeq T).closure_range]
  trivial

/-- Three uniformly bounded terms in a dense decomposition control every
increment of a continuous path. -/
theorem oscillation_le_of_dense_decomposition {T : Type*} [TopologicalSpace T]
    [SeparableSpace T] [Nonempty T] (X Y U W : T → ℝ) (c Λ : ℝ)
    (hX : Continuous X)
    (hdec : ∀ n, X (denseSeq T n) = Y (denseSeq T n) + c + U (denseSeq T n) + W (denseSeq T n))
    (hY : ∀ t, |Y t| ≤ Λ) (hU : ∀ t, |U t| ≤ Λ) (hW : ∀ t, |W t| ≤ Λ) :
    ∀ s t, |X s - X t| ≤ 6 * Λ := by
  have hb : ∀ t, |X t - c| ≤ 3 * Λ := by
    apply abs_sub_le_of_denseSeq X hX c (3 * Λ)
    intro n
    let q := denseSeq T n
    have heq : X q - c = Y q + U q + W q := by rw [hdec n]; ring
    rw [heq]
    calc
      _ ≤ (|Y q| + |U q|) + |W q| :=
        (abs_add_le (Y q + U q) (W q)).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 3 * Λ := by linarith only [hY q, hU q, hW q]
  intro s t
  have heq : X s - X t = (X s - c) - (X t - c) := by ring
  rw [heq]
  exact (abs_sub _ _).trans (by linarith only [hb s, hb t])

/-- An a.e. decomposition at each fixed time is sufficient for a continuum
oscillation bound: only the countable dense family of null sets is intersected.
The two remainders enter through integrable square envelopes. -/
theorem oscillation_measure_le_of_dense_decomposition
    {Ω T : Type*} [MeasurableSpace Ω] [TopologicalSpace T] [SeparableSpace T] [Nonempty T]
    (P : Measure Ω) (X Y U W : T → Ω → ℝ) (c ZU ZW : Ω → ℝ) (M : Set Ω)
    {Λ : ℝ} (hΛ : 0 ≤ Λ) (hX : ∀ ω, Continuous (fun t => X t ω))
    (hdec : ∀ t, ∀ᵐ ω ∂P, X t ω = Y t ω + c ω + U t ω + W t ω)
    (hU : ∀ᵐ ω ∂P, ∀ t, U t ω ^ 2 ≤ ZU ω)
    (hW : ∀ᵐ ω ∂P, ∀ t, W t ω ^ 2 ≤ ZW ω)
    (hY : ∀ ω, ω ∉ M → ∀ t, |Y t ω| ≤ Λ) :
    P {ω | ∃ s t, 6 * Λ < |X s ω - X t ω|} ≤
      P M + P {ω | Λ ^ 2 < ZU ω} + P {ω | Λ ^ 2 < ZW ω} := by
  have hdec' : ∀ᵐ ω ∂P, ∀ n : ℕ, X (denseSeq T n) ω =
      Y (denseSeq T n) ω + c ω + U (denseSeq T n) ω + W (denseSeq T n) ω :=
    ae_all_iff.mpr fun n => hdec (denseSeq T n)
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | ∃ s t, 6 * Λ < |X s ω - X t ω|} →
      ω ∈ (M ∪ {ω | Λ ^ 2 < ZU ω}) ∪ {ω | Λ ^ 2 < ZW ω} := by
    filter_upwards [hdec', hU, hW] with ω hd hu hw
    intro hevent
    by_cases hm : ω ∈ M
    · exact Or.inl (Or.inl hm)
    by_cases hzu : Λ ^ 2 < ZU ω
    · exact Or.inl (Or.inr hzu)
    by_cases hzw : Λ ^ 2 < ZW ω
    · exact Or.inr hzw
    have hu' (t : T) : |U t ω| ≤ Λ := by
      apply (sq_le_sq₀ (abs_nonneg _) hΛ).mp
      rw [sq_abs]
      exact (hu t).trans (le_of_not_gt hzu)
    have hw' (t : T) : |W t ω| ≤ Λ := by
      apply (sq_le_sq₀ (abs_nonneg _) hΛ).mp
      rw [sq_abs]
      exact (hw t).trans (le_of_not_gt hzw)
    rcases hevent with ⟨s, t, hst⟩
    exact False.elim (not_lt_of_ge
      (oscillation_le_of_dense_decomposition (fun t => X t ω) (fun t => Y t ω)
        (fun t => U t ω) (fun t => W t ω) (c ω) Λ (hX ω) hd (hY ω hm) hu' hw' s t) hst)
  calc
    _ ≤ P ((M ∪ {ω | Λ ^ 2 < ZU ω}) ∪ {ω | Λ ^ 2 < ZW ω}) := measure_mono_ae hsub
    _ ≤ (P M + P {ω | Λ ^ 2 < ZU ω}) + P {ω | Λ ^ 2 < ZW ω} :=
      (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)

end Critical2DKPZ.Extensions.ScaleLimit
