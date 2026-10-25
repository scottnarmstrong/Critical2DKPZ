/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.SHF.Tsai.MixedBlockFormBounds
public import Critical2DKPZ.SHF.Tsai.ChainMomentFormBounds

/-! # Uniform connector bounds for partially heat-replaced chains

The selected mixed block has a finite form constant, and every remaining
block uses the existing moment-kernel bound. The general chain calculus
chooses its resulting constant before the connector index and endpoint tests.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped ENNReal
open Critical2DKPZ.DeltaBose

namespace Critical2DKPZ.SHF.Tsai

/-- Every time block in the partially heat-replaced kernel family is measurable. -/
theorem measurable_momentKernel_update_mixed (n : ℕ) (θ : ℝ) (τ : ℕ → ℝ)
    (j : ℕ) (S : Finset (Fin n)) (k : ℕ) :
    Measurable (Function.uncurry (Function.update (fun k => momentKernel n θ (τ k)) j
      (mixedBlockKernel n θ (τ j) S) k)) := by
  classical
  by_cases hk : k = j
  · subst k
    simpa only [Function.update_self] using measurable_mixedBlockKernel n θ (τ j) S
  · rw [Function.update_of_ne hk]
    exact Measurable.comp
      (g := fun p : (ℝ × ℝ) × Configuration n × Configuration n =>
        momentKernel n p.1.1 p.1.2 p.2.1 p.2.2)
      (f := fun q : Configuration n × Configuration n => ((θ, τ k), q))
      (measurable_momentKernel n) (measurable_const.prodMk measurable_id)

/-- The mixed block family has finite form constants at every block of a fixed finite chain. -/
theorem exists_formBounds_momentKernel_update_mixed (θ : ℝ) (K j : ℕ) (hj : j ≤ K)
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) {n : ℕ} (S : Finset (Fin n)) :
    ∃ c : ℕ → ℝ≥0∞, (∀ k ≤ K, c k ≠ ⊤) ∧ ∀ k ≤ K, FormBound volume volume
      (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S) k)
      (c k) := by
  classical
  obtain ⟨d, hd, hD⟩ := exists_formBound_mixedBlockKernel n S θ (hτ j hj)
  obtain ⟨C, rate, _, hC⟩ := exists_formBound_momentKernel n θ
  let c (k : ℕ) := if k = j then d else
    ENNReal.ofReal (C * Real.exp (rate * τ k) * min (τ k) 1 ^ (-(n : ℝ)))
  have hc (k) (_ : k ≤ K) : c k ≠ ⊤ := by
    dsimp only [c]
    split_ifs
    · exact hd
    · exact ENNReal.ofReal_ne_top
  have hQ (k) (hk : k ≤ K) : FormBound volume volume
      (Function.update (fun k => momentKernel n θ (τ k)) j (mixedBlockKernel n θ (τ j) S) k)
      (c k) := by
    by_cases hkj : k = j
    · subst k
      simpa only [Function.update_self, c, ite_eq_left rfl] using hD
    · simpa only [Function.update_of_ne hkj, c, ite_eq_right hkj] using hC θ le_rfl (τ k) (hτ k hk)
  exact ⟨c, hc, hQ⟩

/-- A partially heat-replaced chain has one finite form constant uniform over all connector indices. -/
theorem exists_formBound_mixedChainKernel_uniform (θ : ℝ) (K j : ℕ) (hj : j ≤ K)
    (τ : ℕ → ℝ) (hτ : ∀ k ≤ K, 0 < τ k) {n : ℕ} (S : Finset (Fin n))
    (w : Fin n → ℕ → ℕ → Plane → ℝ) (hw : ∀ i k, IsL2ApplicableMollifier (w i k)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ ℓ, FormBound volume volume
      (chainKernel n (Function.update (fun k => momentKernel n θ (τ k)) j
        (mixedBlockKernel n θ (τ j) S)) (fun i k => w i k ℓ) K) C := by
  obtain ⟨c, hc, hQ⟩ := exists_formBounds_momentKernel_update_mixed θ K j hj τ hτ S
  exact exists_formBound_chainKernel_uniform K _ (measurable_momentKernel_update_mixed n θ τ j S)
    c hc hQ w hw

end Critical2DKPZ.SHF.Tsai

end
