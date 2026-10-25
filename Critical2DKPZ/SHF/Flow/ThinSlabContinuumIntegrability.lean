/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Critical2DKPZ.NonGaussian.NonnegativeFatou
import Mathlib.Tactic

/-! # Integrability from finite limits of nonnegative cutoff integrals -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace Critical2DKPZ.SHF.Flow

/-- Fatou's lemma gives integrability of a nonnegative pointwise limit whose
approximating nonnegative integrals have a finite real limit. -/
theorem integrable_of_nonnegative_cutoff_integral_limit {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (f : ℕ → X → ℝ) (F : X → ℝ) (L : ℝ)
    (hF : Measurable F)
    (hfn : ∀ n x, 0 ≤ f n x)
    (hInt : ∀ n, Integrable (f n) μ)
    (hPointwise : ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (F x)))
    (hIntegral : Tendsto (fun n => ∫ x, f n x ∂μ) atTop (𝓝 L)) :
    Integrable F μ := by
  let C : ℝ := |L| + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hBound : ∀ᶠ n : ℕ in atTop, (∫ x, f n x ∂μ) ≤ C := by
    filter_upwards [(Metric.tendsto_nhds.mp hIntegral) 1 one_pos] with n hn
    rw [Real.dist_eq] at hn
    have hu := (abs_lt.mp hn).2
    dsimp [C]
    linarith only [hu, le_abs_self L]
  obtain ⟨N, hN⟩ := eventually_atTop.mp hBound
  have h := Critical2DKPZ.NonGaussian.integrable_and_integral_le_of_ae_tendsto_nonneg
    μ (fun n => f (n + N)) (fun n => hInt (n + N))
    (fun n => Eventually.of_forall (hfn (n + N))) F hF.aemeasurable
    (Eventually.of_forall fun x => (hPointwise x).comp (tendsto_add_atTop_nat N))
    C hC (fun n => hN (n + N) (Nat.le_add_left N n))
  exact h.2.1

end Critical2DKPZ.SHF.Flow
end
