/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Fourth moments of finite sums from mixed fourth moments

The multinomial expansion is indexed by four ordered choices of summands.
Integrability is proved term by term before passing the finite sum through
expectation, so equality of mixed moments gives equality of actual moments.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- Matching integrable mixed fourth moments determine the fourth moment of a finite sum. -/
theorem integral_sum_pow_four_eq_of_mixed_moments {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') {r : ℕ}
    (X : Fin r → Ω → ℝ) (Y : Fin r → Ω' → ℝ)
    (hX : ∀ q : Fin 4 → Fin r, Integrable (fun ω => ∏ i, X (q i) ω) P)
    (hY : ∀ q : Fin 4 → Fin r, Integrable (fun ω => ∏ i, Y (q i) ω) P')
    (hEq : ∀ q : Fin 4 → Fin r,
      (∫ ω, ∏ i, X (q i) ω ∂P) = ∫ ω, ∏ i, Y (q i) ω ∂P') :
    Integrable (fun ω => (∑ b, X b ω) ^ 4) P ∧
      Integrable (fun ω => (∑ b, Y b ω) ^ 4) P' ∧
      (∫ ω, (∑ b, X b ω) ^ 4 ∂P) = ∫ ω, (∑ b, Y b ω) ^ 4 ∂P' := by
  have heqX : (fun ω => (∑ b, X b ω) ^ 4) =
      fun ω => ∑ q : Fin 4 → Fin r, ∏ i, X (q i) ω := by
    funext ω
    exact Fintype.sum_pow (fun b => X b ω) 4
  have heqY : (fun ω => (∑ b, Y b ω) ^ 4) =
      fun ω => ∑ q : Fin 4 → Fin r, ∏ i, Y (q i) ω := by
    funext ω
    exact Fintype.sum_pow (fun b => Y b ω) 4
  rw [heqX, heqY]
  refine ⟨integrable_finsetSum _ (fun q _ => hX q),
    integrable_finsetSum _ (fun q _ => hY q), ?_⟩
  rw [integral_finsetSum _ (fun q _ => hX q), integral_finsetSum _ (fun q _ => hY q)]
  exact Finset.sum_congr rfl (fun q _ => hEq q)

end Critical2DKPZ.SHF.Tsai

end
