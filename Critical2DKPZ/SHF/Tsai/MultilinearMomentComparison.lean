/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Multilinear expectations from finite coordinate moments

Expanding each argument in the coordinate basis reduces a multilinear
observable to finitely many mixed scalar products. This identifies the
Taylor coefficients in the moment replacement argument.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace Critical2DKPZ.SHF.Tsai

/-- A finite-dimensional multilinear map expands into its coordinate mixed monomials. -/
theorem multilinear_apply_eq_sum_coordinate_products {m k : ℕ}
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin m → ℝ) ℝ) (v : Fin m → ℝ) :
    M (fun _ => v) = ∑ q : Fin k → Fin m,
      (∏ i, v (q i)) * M (fun i => Pi.single (q i) 1) := by
  classical
  have hv : v = ∑ j : Fin m, v j • Pi.single j 1 := by
    funext a
    simp [Pi.single_apply]
  calc
    M (fun _ => v) = M (fun _ : Fin k => ∑ j : Fin m, v j • Pi.single j 1) :=
      congrArg M (funext (fun _ => hv))
    _ = ∑ q : Fin k → Fin m, M (fun i => v (q i) • Pi.single (q i) 1) :=
      M.toMultilinearMap.map_sum _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q _
      exact M.toMultilinearMap.map_smul_univ (fun i => v (q i)) (fun i => Pi.single (q i) 1)

/-- Matching integrable coordinate moments identify the expectation of every fixed multilinear observable. -/
theorem integral_multilinear_eq_of_coordinate_moments {Ω Ω' : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') {m k : ℕ}
    (X : Ω → Fin m → ℝ) (Y : Ω' → Fin m → ℝ)
    (hX : ∀ q : Fin k → Fin m, Integrable (fun ω => ∏ i, X ω (q i)) P)
    (hY : ∀ q : Fin k → Fin m, Integrable (fun ω => ∏ i, Y ω (q i)) P')
    (hEq : ∀ q : Fin k → Fin m,
      (∫ ω, ∏ i, X ω (q i) ∂P) = ∫ ω, ∏ i, Y ω (q i) ∂P')
    (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Fin m → ℝ) ℝ) :
    Integrable (fun ω => M (fun _ => X ω)) P ∧
      Integrable (fun ω => M (fun _ => Y ω)) P' ∧
      (∫ ω, M (fun _ => X ω) ∂P) = ∫ ω, M (fun _ => Y ω) ∂P' := by
  have heqX : (fun ω => M (fun _ => X ω)) = fun ω => ∑ q : Fin k → Fin m,
      (∏ i, X ω (q i)) * M (fun i => Pi.single (q i) 1) := by
    funext ω
    exact multilinear_apply_eq_sum_coordinate_products M (X ω)
  have heqY : (fun ω => M (fun _ => Y ω)) = fun ω => ∑ q : Fin k → Fin m,
      (∏ i, Y ω (q i)) * M (fun i => Pi.single (q i) 1) := by
    funext ω
    exact multilinear_apply_eq_sum_coordinate_products M (Y ω)
  have hXI (q : Fin k → Fin m) := (hX q).mul_const (M (fun i => Pi.single (q i) 1))
  have hYI (q : Fin k → Fin m) := (hY q).mul_const (M (fun i => Pi.single (q i) 1))
  rw [heqX, heqY]
  refine ⟨integrable_finsetSum _ (fun q _ => hXI q),
    integrable_finsetSum _ (fun q _ => hYI q), ?_⟩
  rw [integral_finsetSum _ (fun q _ => hXI q), integral_finsetSum _ (fun q _ => hYI q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [integral_mul_const, integral_mul_const, hEq q]

end Critical2DKPZ.SHF.Tsai

end
