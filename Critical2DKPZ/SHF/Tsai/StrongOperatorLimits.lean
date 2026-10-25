/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Topology.Order.LiminfLimsup

/-! # Strong limits of finite operator chains

Banach–Steinhaus makes a strongly convergent sequence uniformly bounded. It
therefore acts continuously on converging input sequences. Iterating this
fact handles the varying connectors in a finite chain of fixed block operators.
-/

@[expose] public noncomputable section

open Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Strongly convergent operator sequences have one common finite norm bound. -/
theorem exists_operator_uniform_bound_of_tendsto {A : ℕ → E →L[ℝ] F} {B : E →L[ℝ] F}
    (hA : ∀ x, Tendsto (fun j => A j x) atTop (𝓝 (B x))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j, ‖A j‖ ≤ C := by
  have hpoint (x : E) : ∃ C : ℝ, ∀ j, ‖A j x‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hA x).norm.bddAbove_range
    exact ⟨C, fun j => hC (Set.mem_range_self j)⟩
  obtain ⟨C, hC⟩ := banach_steinhaus (g := A) hpoint
  exact ⟨C, (norm_nonneg (A 0)).trans (hC 0), hC⟩

/-- Strong convergence also holds on a converging sequence of input vectors. -/
theorem tendsto_operator_apply_of_tendsto {A : ℕ → E →L[ℝ] F} {B : E →L[ℝ] F}
    (hA : ∀ x, Tendsto (fun j => A j x) atTop (𝓝 (B x)))
    {xs : ℕ → E} {x : E} (hx : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun j => A j (xs j)) atTop (𝓝 (B x)) := by
  obtain ⟨C, _, hC⟩ := exists_operator_uniform_bound_of_tendsto hA
  have hbound (j) : ‖A j (xs j - x)‖ ≤ C * ‖xs j - x‖ :=
    ((A j).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC j) (norm_nonneg _))
  have hlim := ((hx.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))).norm).const_mul C
  simp only [sub_self, norm_zero, mul_zero] at hlim
  have hzero := squeeze_zero (fun j => norm_nonneg (A j (xs j - x))) hbound hlim
  have hsmall : Tendsto (fun j => A j (xs j - x)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hzero
  have heq : (fun j => A j (xs j)) = fun j => A j (xs j - x) + A j x := by
    funext j
    rw [map_sub, sub_add_cancel]
  rw [heq]
  simpa only [zero_add] using hsmall.add (hA x)

/-- Fixed block operators joined by a finite sequence of connector operators. -/
def operatorChain (Q W : ℕ → E →L[ℝ] E) : ℕ → E →L[ℝ] E
  | 0 => Q 0
  | K + 1 => (operatorChain Q W K).comp ((W K).comp (Q (K + 1)))

/-- Strong convergence of each connector gives strong convergence of the entire finite chain. -/
theorem tendsto_operatorChain (Q : ℕ → E →L[ℝ] E) (W : ℕ → ℕ → E →L[ℝ] E)
    (hW : ∀ k x, Tendsto (fun j => W k j x) atTop (𝓝 x)) (K : ℕ) (x : E) :
    Tendsto (fun j => operatorChain Q (fun k => W k j) K x) atTop
      (𝓝 (operatorChain Q (fun _ => ContinuousLinearMap.id ℝ E) K x)) := by
  induction K generalizing x with
  | zero => exact tendsto_const_nhds
  | succ K ih =>
    have h := tendsto_operator_apply_of_tendsto (fun y => ih y) (hW K (Q (K + 1) x))
    simpa only [operatorChain, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h

end Critical2DKPZ.SHF.Tsai

end
