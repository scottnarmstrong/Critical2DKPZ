/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Sequences

/-! # Weak subsequences in separable Hilbert spaces -/

@[expose] public section

noncomputable section

open Filter TopologicalSpace
open scoped Topology

namespace Critical2DKPZ.CovarianceKernel

/-- A norm-bounded sequence in a separable real Hilbert space has a weakly convergent
subsequence, expressed through convergence of all inner products. -/
theorem exists_strictMono_subseq_inner_tendsto_of_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E]
    (u : ℕ → E) {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ n, ‖u n‖ ≤ B) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ v : E, ∀ x : E,
      Tendsto (fun n => inner ℝ (u (s n)) x) atTop (𝓝 (inner ℝ v x)) := by
  let F : ℕ → WeakDual ℝ E := fun n =>
    StrongDual.toWeakDual ((InnerProductSpace.toDual ℝ E) (u n))
  let S : Set (WeakDual ℝ E) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ E) B
  have hFn (n : ℕ) : F n ∈ S := by
    change WeakDual.toStrongDual (F n) ∈
      Metric.closedBall (0 : StrongDual ℝ E) B
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖(InnerProductSpace.toDual ℝ E) (u n)‖ ≤ B
    simpa using hbound n
  have hseq : ∀ n, F n ∈ S := fun n => hFn n
  have hcompact : IsSeqCompact S := by
    exact WeakDual.isSeqCompact_closedBall ℝ E (0 : StrongDual ℝ E) B
  obtain ⟨w, hw, s, hs, hlim⟩ := hcompact hseq
  let v : E := (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual w)
  refine ⟨s, hs, v, fun x => ?_⟩
  have heval : Continuous (fun q : WeakDual ℝ E => q x) :=
    WeakBilin.eval_continuous _ x
  have hcoord : Tendsto (fun n => F (s n) x) atTop (𝓝 (w x)) :=
    heval.continuousAt.tendsto.comp hlim
  have hleft (n : ℕ) : F (s n) x = inner ℝ (u (s n)) x := by
    simp [F, InnerProductSpace.toDual_apply_apply]
  have hright : w x = inner ℝ v x := by
    dsimp [v]
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  simpa only [hleft, hright] using hcoord

end Critical2DKPZ.CovarianceKernel

end
