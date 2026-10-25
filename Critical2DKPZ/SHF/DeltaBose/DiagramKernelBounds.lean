/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.DeltaBose.PathDominatingFormBounds
public import Critical2DKPZ.SHF.DeltaBose.PathKernel
public import Critical2DKPZ.SHF.DeltaBose.DiagramSeries
public import Critical2DKPZ.SHF.DeltaBose.CollisionWords
import Mathlib.Tactic

/-! # Form bounds for individual collision diagrams -/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Critical2DKPZ.DeltaBose

/-- Each fixed collision diagram has a form bound uniform over its word, with
one logarithmic factor for each collision block. -/
theorem exists_formBound_diagramKernel (n : ℕ) (A : ℝ) :
    ∃ C c rate₀ : ℝ, 0 < C ∧ 0 < c ∧ Real.exp (A + 1) ≤ rate₀ ∧
      ∀ θ : ℝ, θ ≤ A → ∀ rate : ℝ, rate₀ ≤ rate →
        ∀ (m : ℕ) (w : CollisionWord n (m + 1)), ∀ h : ℝ, 0 < h →
          FormBound volume volume (diagramKernel θ (List.ofFn w.1) h)
            (ENNReal.ofReal (C * Real.exp (rate * h) * min h 1 ^ (-(n : ℝ)) *
              (c / (Real.log rate - A)) ^ m)) := by
  obtain ⟨C, c, rate₀, hC, hc, hrate₀, hdom⟩ :=
    exists_formBound_pathDominatingKernel n A
  refine ⟨C, c, rate₀, hC, hc, hrate₀, ?_⟩
  intro θ hθ rate hrate m w h hh
  let word : List (CollisionPair n) := List.ofFn w.1
  have hlen : word.length = m + 1 := by
    simp [word]
  have hword_ne : word ≠ [] := by
    intro he
    have hzero := congrArg List.length he
    simp [hlen] at hzero
  have hchain : word.IsChain (· ≠ ·) := by
    apply (List.isChain_ofFn).2
    intro i hi
    let i' : Fin (m + 1) := ⟨i, by omega⟩
    let j' : Fin (m + 1) := ⟨i + 1, by omega⟩
    exact w.2 i' j' (by simp [i', j'])
  let τ₀ : ℝ := min h 1
  have hτ₀ : 0 < τ₀ := by
    dsimp [τ₀]
    exact lt_min hh (by norm_num)
  have hτ₀_le_one : τ₀ ≤ 1 := by
    dsimp [τ₀]
    exact min_le_right _ _
  have hτ₀_le_h : τ₀ ≤ h := by
    dsimp [τ₀]
    exact min_le_left _ _
  have hdom' := hdom θ hθ rate hrate word hword_ne hchain τ₀ hτ₀ hτ₀_le_one
  have hscale :
      FormBound volume volume
        (fun x y => ENNReal.ofReal (Real.exp (rate * h)) *
          pathDominatingKernel θ rate word id τ₀ x y)
        (ENNReal.ofReal (Real.exp (rate * h)) *
          ENNReal.ofReal (C * τ₀ ^ (-(n : ℝ)) *
            (c / (Real.log rate - A)) ^ (word.length - 1))) := by
    exact FormBound.const_mul_left ENNReal.ofReal_ne_top hdom'
  have hpoint : ∀ x y : Configuration n,
      diagramKernel θ word h x y ≤
        ENNReal.ofReal (Real.exp (rate * h)) *
          pathDominatingKernel θ rate word id τ₀ x y := by
    intro x y
    have hD2 := pathTimeKernel_le_pathDominatingKernel θ rate word
      measurable_id hτ₀ hτ₀_le_h x y
    have hcancel : ENNReal.ofReal (Real.exp (rate * h)) *
        laplaceTimeWeight rate h = 1 := by
      unfold laplaceTimeWeight
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      have hexp : rate * h + -(rate * h) = 0 := by ring
      rw [hexp, Real.exp_zero, ENNReal.ofReal_one]
    have hscaled := mul_le_mul'
      (le_rfl : ENNReal.ofReal (Real.exp (rate * h)) ≤
        ENNReal.ofReal (Real.exp (rate * h))) hD2
    have hpath : pathTimeKernel θ word id id (h, x, y) = diagramKernel θ word h x y := by
      rw [pathTimeKernel_eq_diagram θ word measurable_id measurable_id,
        causalKernel_of_pos _ hh]
      rfl
    rw [← hpath]
    calc
      pathTimeKernel θ word id id (h, x, y) =
          1 * pathTimeKernel θ word id id (h, x, y) := by simp
      _ = (ENNReal.ofReal (Real.exp (rate * h)) * laplaceTimeWeight rate h) *
            pathTimeKernel θ word id id (h, x, y) := by rw [← hcancel]
      _ = ENNReal.ofReal (Real.exp (rate * h)) *
            (laplaceTimeWeight rate h * pathTimeKernel θ word id id (h, x, y)) := by ac_rfl
      _ ≤ ENNReal.ofReal (Real.exp (rate * h)) *
          pathDominatingKernel θ rate word id τ₀ x y := hscaled
  have hτpow : τ₀ ^ (-(n : ℝ)) = min h 1 ^ (-(n : ℝ)) := by
    rfl
  have hconst :
      ENNReal.ofReal (Real.exp (rate * h)) *
          ENNReal.ofReal (C * τ₀ ^ (-(n : ℝ)) *
            (c / (Real.log rate - A)) ^ (word.length - 1)) ≤
        ENNReal.ofReal (C * Real.exp (rate * h) * min h 1 ^ (-(n : ℝ)) *
            (c / (Real.log rate - A)) ^ m) := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    rw [hτpow, hlen]
    have hlenpow : (m + 1 - 1) = m := by omega
    rw [hlenpow]
    exact le_of_eq (by ac_rfl)
  exact (hscale.mono hpoint hconst)

end Critical2DKPZ.DeltaBose
