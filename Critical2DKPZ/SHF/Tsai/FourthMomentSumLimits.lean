/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.FourthMomentComparison
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Finite fourth-moment expansions and limits

The ordered fourfold expansion is integrable term by term. Finite sums can
therefore pass through expectation and limits without any uniform domination
or higher moment assumption.
-/

@[expose] public noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Critical2DKPZ.SHF.Tsai

/-- Integrable mixed fourth moments give the actual fourth moment as their finite sum. -/
theorem integral_sum_pow_four_eq_sum_integral_prod {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {r : ℕ} (X : Fin r → Ω → ℝ)
    (hI : ∀ q : Fin 4 → Fin r, Integrable (fun ω => ∏ i, X (q i) ω) P) :
    Integrable (fun ω => (∑ b, X b ω) ^ 4) P ∧
      (∫ ω, (∑ b, X b ω) ^ 4 ∂P) = ∑ q : Fin 4 → Fin r, ∫ ω, ∏ i, X (q i) ω ∂P := by
  classical
  have heq : (fun ω => (∑ b, X b ω) ^ 4) = fun ω => ∑ q : Fin 4 → Fin r, ∏ i, X (q i) ω := by
    funext ω
    exact Fintype.sum_pow (fun b => X b ω) 4
  rw [heq]
  exact ⟨integrable_finsetSum _ (fun q _ => hI q), integral_finsetSum _ (fun q _ => hI q)⟩

/-- Convergent integrable mixed fourth moments give convergence of the fourth moment of a finite sum. -/
theorem tendsto_integral_sum_pow_four_of_mixed_limits {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {r : ℕ} (X : ℕ → Fin r → Ω → ℝ) (L : (Fin 4 → Fin r) → ℝ)
    (hI : ∀ ℓ (q : Fin 4 → Fin r), Integrable (fun ω => ∏ i, X ℓ (q i) ω) P)
    (hconv : ∀ q : Fin 4 → Fin r, Tendsto (fun ℓ => ∫ ω, ∏ i, X ℓ (q i) ω ∂P) atTop (𝓝 (L q))) :
    (∀ ℓ, Integrable (fun ω => (∑ b, X ℓ b ω) ^ 4) P) ∧
      Tendsto (fun ℓ => ∫ ω, (∑ b, X ℓ b ω) ^ 4 ∂P) atTop (𝓝 (∑ q : Fin 4 → Fin r, L q)) := by
  classical
  have hData (ℓ : ℕ) := integral_sum_pow_four_eq_sum_integral_prod P (X ℓ) (hI ℓ)
  refine ⟨fun ℓ => (hData ℓ).1, ?_⟩
  have hsum := tendsto_finsetSum Finset.univ (fun q _ => hconv q)
  exact hsum.congr (fun ℓ => (hData ℓ).2.symm)

/-- A finite sum of fourth moments converges to the sum of its mixed-product limits, with integrability. -/
theorem tendsto_integral_sum_sum_pow_four_of_mixed_limits {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {m r : ℕ} (X : ℕ → Fin m → Fin r → Ω → ℝ)
    (L : Fin m → (Fin 4 → Fin r) → ℝ)
    (hI : ∀ ℓ a (q : Fin 4 → Fin r), Integrable (fun ω => ∏ i, X ℓ a (q i) ω) P)
    (hconv : ∀ a (q : Fin 4 → Fin r), Tendsto (fun ℓ => ∫ ω, ∏ i, X ℓ a (q i) ω ∂P) atTop (𝓝 (L a q))) :
    (∀ ℓ, Integrable (fun ω => ∑ a, (∑ b, X ℓ a b ω) ^ 4) P) ∧
      Tendsto (fun ℓ => ∫ ω, ∑ a, (∑ b, X ℓ a b ω) ^ 4 ∂P) atTop (𝓝 (∑ a, ∑ q : Fin 4 → Fin r, L a q)) := by
  classical
  have hData (a : Fin m) := tendsto_integral_sum_pow_four_of_mixed_limits P
    (fun ℓ => X ℓ a) (L a) (fun ℓ q => hI ℓ a q) (hconv a)
  refine ⟨fun ℓ => integrable_finsetSum _ (fun a _ => (hData a).1 ℓ), ?_⟩
  have hsum := tendsto_finsetSum Finset.univ (fun a _ => (hData a).2)
  apply hsum.congr
  intro ℓ
  exact (integral_finsetSum _ (fun a _ => (hData a).1 ℓ)).symm

end Critical2DKPZ.SHF.Tsai

end
